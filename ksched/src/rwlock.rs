//! Read-write lock.

use crate::slpque::SleepQueue;
use crate::sync::Spinlock;
use core::fmt;
use core::mem;
use core::ops::{Deref, DerefMut};
use core::{
    cell::UnsafeCell,
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

const ONE_READER: usize = 4;

#[derive(Clone, Copy, Debug)]
enum RwType {
    Reader,
    Writer,
    UpgradableReader,
}

struct RwLockInner {
    /// Bit 0 indicates if there is an active writer. If this is true, the other bits must be zero.
    /// Bit 1 indicates if there is an active upgradable reader. If this is true, bit 0 must be zero.
    /// Other bits indicates the number of normal readers that are reading.
    state: usize,
    /// Since it is write-preferring, we need to know whether some writers are sleeping.
    waiting_writer: usize,
    slpque: SleepQueue<RwType>,
}

/// An async reader-writer lock.
///
/// This type of lock allows multiple readers or one writer at any point in time.
///
/// The locking strategy is write-preferring, which means writers are never starved.
/// Releasing a write lock wakes the next blocked reader and the next blocked writer.
///
/// # Examples
///
/// ```
/// # ksched::task::spawn(0, async {
/// use ksched::sync::RwLock;
///
/// let lock = RwLock::new(5);
///
/// // Multiple read locks can be held at a time.
/// let r1 = lock.read().await;
/// let r2 = lock.read().await;
/// assert_eq!(*r1, 5);
/// assert_eq!(*r2, 5);
/// drop((r1, r2));
///
/// // Only one write lock can be held at a time.
/// let mut w = lock.write().await;
/// *w += 1;
/// assert_eq!(*w, 6);
/// # });
/// # ksched::task::run_all();
/// ```
pub struct RwLock<T: ?Sized> {
    /// Guard towards status and waiting queue.
    inner: Spinlock<RwLockInner>,

    /// The inner value.
    value: UnsafeCell<T>,
}

unsafe impl<T: Send + ?Sized> Send for RwLock<T> {}
unsafe impl<T: Send + Sync + ?Sized> Sync for RwLock<T> {}

impl<T> RwLock<T> {
    /// Creates a new reader-writer lock.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::sync::RwLock;
    ///
    /// let lock = RwLock::new(0);
    /// ```
    pub const fn new(t: T) -> RwLock<T> {
        RwLock {
            inner: Spinlock::new(RwLockInner {
                state: 0,
                waiting_writer: 0,
                slpque: SleepQueue::new(),
            }),
            value: UnsafeCell::new(t),
        }
    }

    /// Unwraps the lock and returns the inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::sync::RwLock;
    ///
    /// let lock = RwLock::new(5);
    /// assert_eq!(lock.into_inner(), 5);
    /// ```
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }
}

fn try_read(g: &mut RwLockInner, wait_writer: bool) -> bool {
    if g.state & 1 == 0 && (!wait_writer || g.waiting_writer == 0) {
        g.state += ONE_READER;
        true
    } else {
        false
    }
}
fn try_upread(g: &mut RwLockInner, wait_writer: bool) -> bool {
    if g.state & 3 == 0 && (!wait_writer || g.waiting_writer == 0) {
        g.state |= 2;
        true
    } else {
        false
    }
}
fn try_write(g: &mut RwLockInner, wait_writer: bool) -> bool {
    if g.state == 0 && (!wait_writer || g.waiting_writer == 0) {
        g.state |= 1;
        true
    } else {
        false
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Attempts to acquire a read lock.
    ///
    /// If a read lock could not be acquired at this time, then [`None`] is returned. Otherwise, a
    /// guard is returned that releases the lock when dropped.
    ///
    /// See also [read](`Self::read`)
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T>> {
        let mut g = self.inner.lock();
        if try_read(&mut g, true) {
            Some(RwLockReadGuard(self))
        } else {
            None
        }
    }

    /// Acquires a read lock.
    ///
    /// Returns a guard that releases the lock when dropped.
    ///
    /// Note that attempts to acquire a read lock will block if there are also concurrent attempts
    /// to acquire a write lock.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::RwLock;
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let reader = lock.read().await;
    /// assert_eq!(*reader, 1);
    ///
    /// assert!(lock.try_read().is_some());
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn read(&self) -> RwLockReadGuard<'_, T> {
        struct Lock<'a, T: ?Sized> {
            lk: &'a RwLock<T>,
            first: bool,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockReadGuard<'a, T>;

            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                    if try_read(&mut g, true) {
                        Poll::Ready(RwLockReadGuard(self.lk))
                    } else {
                        g.slpque.sleep(RwType::Reader, cx.waker().clone());
                        Poll::Pending
                    }
                } else {
                    Poll::Ready(RwLockReadGuard(self.lk))
                }
            }
        }

        Lock {
            lk: self,
            first: true,
        }
        .await
    }

    /// Attempts to acquire a read lock with the possiblity to upgrade to a write lock.
    ///
    /// If a read lock could not be acquired at this time, then [`None`] is returned. Otherwise, a
    /// guard is returned that releases the lock when dropped.
    ///
    /// Upgradable read lock reserves the right to be upgraded to a write lock, which means there
    /// can be at most one upgradable read lock at a time.
    ///
    /// See also [upgradable_read](`Self::upgradable_read`)
    pub fn try_upgradable_read(&self) -> Option<RwLockUpgradableReadGuard<'_, T>> {
        let mut g = self.inner.lock();
        if try_upread(&mut g, true) {
            Some(RwLockUpgradableReadGuard(self))
        } else {
            None
        }
    }

    /// Attempts to acquire a read lock with the possiblity to upgrade to a write lock.
    ///
    /// Returns a guard that releases the lock when dropped.
    ///
    /// Upgradable read lock reserves the right to be upgraded to a write lock, which means there
    /// can be at most one upgradable read lock at a time.
    ///
    /// Note that attempts to acquire an upgradable read lock will block if there are concurrent
    /// attempts to acquire another upgradable read lock or a write lock.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::{RwLock, RwLockUpgradableReadGuard};
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let reader = lock.upgradable_read().await;
    /// assert_eq!(*reader, 1);
    /// assert_eq!(*lock.try_read().unwrap(), 1);
    ///
    /// let mut writer = RwLockUpgradableReadGuard::upgrade(reader).await;
    /// *writer = 2;
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn upgradable_read(&self) -> RwLockUpgradableReadGuard<'_, T> {
        struct Lock<'a, T: ?Sized> {
            lk: &'a RwLock<T>,
            first: bool,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockUpgradableReadGuard<'a, T>;

            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                    if try_upread(&mut g, true) {
                        Poll::Ready(RwLockUpgradableReadGuard(self.lk))
                    } else {
                        g.slpque.sleep(RwType::UpgradableReader, cx.waker().clone());
                        Poll::Pending
                    }
                } else {
                    Poll::Ready(RwLockUpgradableReadGuard(self.lk))
                }
            }
        }

        Lock {
            lk: self,
            first: true,
        }
        .await
    }

    /// Attempts to acquire a write lock.
    ///
    /// If a write lock could not be acquired at this time, then [`None`] is returned. Otherwise, a
    /// guard is returned that releases the lock when dropped.
    ///
    /// See also [write](`Self::write`)
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_, T>> {
        let mut g = self.inner.lock();
        if try_write(&mut g, true) {
            Some(RwLockWriteGuard(self))
        } else {
            None
        }
    }

    /// Acquires a write lock.
    ///
    /// Returns a guard that releases the lock when dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::RwLock;
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let writer = lock.write().await;
    /// assert!(lock.try_read().is_none());
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn write(&self) -> RwLockWriteGuard<'_, T> {
        struct Lock<'a, T: ?Sized> {
            first: bool,
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockWriteGuard<'a, T>;

            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                    if try_write(&mut g, true) {
                        Poll::Ready(RwLockWriteGuard(self.lk))
                    } else {
                        g.slpque.sleep(RwType::Writer, cx.waker().clone());
                        g.waiting_writer += 1;
                        Poll::Pending
                    }
                } else {
                    Poll::Ready(RwLockWriteGuard(self.lk))
                }
            }
        }

        Lock {
            lk: self,
            first: true,
        }
        .await
    }

    /// Returns a mutable reference to the inner value.
    ///
    /// Since this call borrows the lock mutably, no actual locking takes place. The mutable borrow
    /// statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::RwLock;
    ///
    /// let mut lock = RwLock::new(1);
    ///
    /// *lock.get_mut() = 2;
    /// assert_eq!(*lock.read().await, 2);
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.value.get() }
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for RwLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Locked;
        impl fmt::Debug for Locked {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("<locked>")
            }
        }

        match self.try_read() {
            None => f.debug_struct("RwLock").field("value", &Locked).finish(),
            Some(guard) => f.debug_struct("RwLock").field("value", &&*guard).finish(),
        }
    }
}

impl<T> From<T> for RwLock<T> {
    fn from(val: T) -> RwLock<T> {
        RwLock::new(val)
    }
}

impl<T: Default + ?Sized> Default for RwLock<T> {
    fn default() -> RwLock<T> {
        RwLock::new(Default::default())
    }
}

/// A guard that releases the read lock when dropped.
pub struct RwLockReadGuard<'a, T: ?Sized>(&'a RwLock<T>);

unsafe impl<T: Sync + ?Sized> Send for RwLockReadGuard<'_, T> {}
unsafe impl<T: Sync + ?Sized> Sync for RwLockReadGuard<'_, T> {}

/// Try to wake up waiters.
fn extend_wake(g: &mut RwLockInner) {
    while let Some((t, w)) = g.slpque.que.pop_front() {
        let try_wake = match t {
            RwType::Reader => try_read(g, false),
            RwType::UpgradableReader => try_upread(g, false),
            RwType::Writer => try_write(g, false)
                .then(|| {
                    g.waiting_writer -= 1;
                })
                .is_some(),
        };
        #[cfg(test)]
        println!("extend_wake: {:?}, try_wake {}", t, try_wake);
        if try_wake {
            w.wake()
        } else {
            g.slpque.sleep_front(t, w);
            break;
        }
    }
}

impl<T: ?Sized> Drop for RwLockReadGuard<'_, T> {
    fn drop(&mut self) {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state & 1, 0);
        debug_assert_ne!(g.state, 0);
        // Decrement the number of readers.
        g.state -= ONE_READER;
        // If this was the last reader.
        if g.state == 0 {
            extend_wake(&mut g);
        }
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for RwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: fmt::Display + ?Sized> fmt::Display for RwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized> Deref for RwLockReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.0.value.get() }
    }
}

/// A guard that releases the upgradable read lock when dropped.
pub struct RwLockUpgradableReadGuard<'a, T: ?Sized>(&'a RwLock<T>);

unsafe impl<T: Send + Sync + ?Sized> Send for RwLockUpgradableReadGuard<'_, T> {}
unsafe impl<T: Sync + ?Sized> Sync for RwLockUpgradableReadGuard<'_, T> {}

impl<'a, T: ?Sized> RwLockUpgradableReadGuard<'a, T> {
    /// Converts this guard into a writer guard.
    fn into_writer(self) -> RwLockWriteGuard<'a, T> {
        let g = RwLockWriteGuard(self.0);
        mem::forget(self);
        g
    }

    /// Downgrades into a regular reader guard.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::{RwLock, RwLockUpgradableReadGuard};
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let reader = lock.upgradable_read().await;
    /// assert_eq!(*reader, 1);
    ///
    /// assert!(lock.try_upgradable_read().is_none());
    ///
    /// let reader = RwLockUpgradableReadGuard::downgrade(reader);
    ///
    /// assert!(lock.try_upgradable_read().is_some());
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub fn downgrade(self) -> RwLockReadGuard<'a, T> {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state & 3, 2);
        g.state += ONE_READER - 2;
        extend_wake(&mut g);
        drop(g);

        let g = RwLockReadGuard(self.0);
        mem::forget(self);
        g
    }

    /// Attempts to upgrade into a write lock.
    ///
    /// If a write lock could not be acquired at this time, then [`None`] is returned. Otherwise,
    /// an upgraded guard is returned that releases the write lock when dropped.
    ///
    /// This function can only fail if there are other active read locks.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::{RwLock, RwLockUpgradableReadGuard};
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let reader = lock.upgradable_read().await;
    /// assert_eq!(*reader, 1);
    ///
    /// let reader2 = lock.read().await;
    /// let reader = RwLockUpgradableReadGuard::try_upgrade(reader).unwrap_err();
    ///
    /// drop(reader2);
    /// let writer = RwLockUpgradableReadGuard::try_upgrade(reader).unwrap();
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub fn try_upgrade(self) -> Result<RwLockWriteGuard<'a, T>, Self> {
        // If there are no readers, grab the write lock.
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state & 3, 2);
        // If it is the last one.
        if g.state == 2 {
            g.state = 1;
            Ok(self.into_writer())
        } else {
            Err(self)
        }
    }

    /// Upgrades into a write lock.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::{RwLock, RwLockUpgradableReadGuard};
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let reader = lock.upgradable_read().await;
    /// assert_eq!(*reader, 1);
    ///
    /// let mut writer = RwLockUpgradableReadGuard::upgrade(reader).await;
    /// *writer = 2;
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn upgrade(self) -> RwLockWriteGuard<'a, T> {
        struct Lock<'a, T: ?Sized> {
            first: bool,
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockWriteGuard<'a, T>;

            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                if self.first {
                    self.first = false;

                    debug_assert_eq!(g.state & 1, 0);
                    debug_assert_eq!(g.state & 2, 2);
                    g.state -= 2;
                    if try_write(&mut g, false) {
                        Poll::Ready(RwLockWriteGuard(self.lk))
                    } else {
                        g.slpque.sleep_front(RwType::Writer, cx.waker().clone());
                        g.waiting_writer += 1;
                        Poll::Pending
                    }
                } else {
                    Poll::Ready(RwLockWriteGuard(self.lk))
                }
            }
        }

        let ret = Lock {
            lk: self.0,
            first: true,
        }
        .await;
        mem::forget(self);
        ret
    }
}

impl<T: ?Sized> Drop for RwLockUpgradableReadGuard<'_, T> {
    fn drop(&mut self) {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state & 3, 2);
        g.state -= 2;
        extend_wake(&mut g);
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for RwLockUpgradableReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: fmt::Display + ?Sized> fmt::Display for RwLockUpgradableReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized> Deref for RwLockUpgradableReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.0.value.get() }
    }
}

/// A guard that releases the write lock when dropped.
pub struct RwLockWriteGuard<'a, T: ?Sized>(&'a RwLock<T>);

unsafe impl<T: Send + ?Sized> Send for RwLockWriteGuard<'_, T> {}
unsafe impl<T: Sync + ?Sized> Sync for RwLockWriteGuard<'_, T> {}

impl<'a, T: ?Sized> RwLockWriteGuard<'a, T> {
    /// Create a writer guard without acquiring the lock.
    ///
    /// You need to guarantee that you are actually the writer before.
    pub unsafe fn from_raw(lock: &'a RwLock<T>) -> Self {
        Self(lock)
    }

    /// Downgrades into a regular reader guard.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::{RwLock, RwLockWriteGuard};
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let mut writer = lock.write().await;
    /// *writer += 1;
    ///
    /// assert!(lock.try_read().is_none());
    ///
    /// let reader = RwLockWriteGuard::downgrade(writer);
    /// assert_eq!(*reader, 2);
    ///
    /// assert!(lock.try_read().is_some());
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub fn downgrade(self) -> RwLockReadGuard<'a, T> {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state, 1);
        g.state = ONE_READER;
        extend_wake(&mut g);
        drop(g);

        let g = RwLockReadGuard(self.0);
        mem::forget(self);
        g
    }

    /// Downgrades into an upgradable reader guard.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(0, async {
    /// use ksched::sync::{RwLock, RwLockUpgradableReadGuard, RwLockWriteGuard};
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let mut writer = lock.write().await;
    /// *writer += 1;
    ///
    /// assert!(lock.try_read().is_none());
    ///
    /// let reader = RwLockWriteGuard::downgrade_to_upgradable(writer);
    /// assert_eq!(*reader, 2);
    ///
    /// assert!(lock.try_write().is_none());
    /// assert!(lock.try_read().is_some());
    ///
    /// assert!(RwLockUpgradableReadGuard::try_upgrade(reader).is_ok())
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub fn downgrade_to_upgradable(self) -> RwLockUpgradableReadGuard<'a, T> {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state, 1);
        g.state = 2;
        extend_wake(&mut g);
        drop(g);

        let g = RwLockUpgradableReadGuard(self.0);
        mem::forget(self);
        g
    }
}

impl<T: ?Sized> Drop for RwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state, 1);
        g.state = 0;
        extend_wake(&mut g);
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for RwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: fmt::Display + ?Sized> fmt::Display for RwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized> Deref for RwLockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.0.value.get() }
    }
}

impl<T: ?Sized> DerefMut for RwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.0.value.get() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::run_multi;
    use crate::*;
    use alloc::sync::Arc;

    #[test]
    fn test_readers() {
        const N: usize = 100;
        let x = Arc::new(RwLock::new(10usize));
        for _ in 0..N {
            let x = x.clone();
            task::spawn(0, async move {
                let g = x.read().await;
                assert_eq!(*g, 10);
            })
            .unwrap();
        }
        run_multi(10);
    }

    #[test]
    fn test_writers() {
        const N: usize = 100;
        let x = Arc::new(RwLock::new(0usize));
        for _ in 0..N {
            let x = x.clone();
            task::spawn(0, async move {
                let mut g = x.write().await;
                *g += 1;
                println!("{}", *g);
            })
            .unwrap();
        }
        run_multi(10);
        task::spawn(0, async move {
            let g = x.read().await;
            assert_eq!(*g, N);
        })
        .unwrap();
        run_multi(1);
    }

    #[test]
    fn test_readwrite() {
        const N: usize = 100;
        let x = Arc::new(RwLock::new(0usize));
        for _ in 0..N {
            let x = x.clone();
            let x2 = x.clone();
            task::spawn(0, async move {
                let mut g = x.write().await;
                *g += 1;
            })
            .unwrap();
            task::spawn(0, async move {
                let g = x2.read().await;
                assert!(*g >= 1);
            })
            .unwrap();
        }
        run_multi(10);

        task::spawn(0, async move {
            let g = x.read().await;
            assert_eq!(*g, N);
        })
        .unwrap();
        run_multi(1);
    }

    #[test]
    fn test_upgradable_read() {
        const N: usize = 100;
        let x = Arc::new(RwLock::new(0usize));
        for _ in 0..N {
            let x = x.clone();
            let x2 = x.clone();
            task::spawn(0, async move {
                let mut g = x.write().await;
                *g += 1;
            })
            .unwrap();

            task::spawn(0, async move {
                let g = x2.upgradable_read().await;
                let mut g = g.upgrade().await;
                *g += 1;
            })
            .unwrap();
        }

        run_multi(10);
        task::spawn(0, async move {
            let g = x.read().await;
            assert_eq!(*g, 2 * N);
        })
        .unwrap();
        run_multi(1);
    }
}
