//! Read-write lock.

use core::mem;
use core::ops::{Deref, DerefMut};
use core::{alloc::AllocError, fmt};
use core::{
    cell::UnsafeCell,
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};
// use std::process;
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::slpque::SleepQueue;
use kcore::error::Result;
use spin::{Mutex as Spinlock, MutexGuard as SpinlockGuard};

const ONE_READER: usize = 4;

struct RwLockInner {
    /// Bit 0 indicates if there is an active writer. If this is true, the other bits must be zero.
    /// Bit 1 indicates if there is an active upgradable reader. If this is true, bit 0 must be zero.
    /// Other bits indicates the number of normal readers that are reading.
    state: usize,
    /// Since it is write-preferring, we need to know whether some writers are sleeping.
    waiting_writer: usize,
    slpque: SleepQueue,
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
/// let r1 = lock.read().await.unwrap();
/// let r2 = lock.read().await.unwrap();
/// assert_eq!(*r1, 5);
/// assert_eq!(*r2, 5);
/// drop((r1, r2));
///
/// // Only one write lock can be held at a time.
/// let mut w = lock.write().await.unwrap();
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

fn try_read(g: &mut SpinlockGuard<RwLockInner>) -> bool {
    if g.state & 1 == 0 && g.waiting_writer == 0 {
        g.state += ONE_READER;
        true
    } else {
        false
    }
}
fn try_upread(g: &mut SpinlockGuard<RwLockInner>) -> bool {
    if g.state & 3 == 0 && g.waiting_writer == 0 {
        g.state |= 2;
        true
    } else {
        false
    }
}
fn try_write(g: &mut SpinlockGuard<RwLockInner>) -> bool {
    if g.waiting_writer == 0 && g.state == 0 {
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
        if try_read(&mut g) {
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
    /// let reader = lock.read().await.unwrap();
    /// assert_eq!(*reader, 1);
    ///
    /// assert!(lock.try_read().is_some());
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn read(&self) -> Result<RwLockReadGuard<'_, T>> {
        struct Lock<'a, T: ?Sized> {
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = Result<RwLockReadGuard<'a, T>>;

            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                let result = if try_read(&mut g) {
                    Poll::Ready(Ok(RwLockReadGuard(self.lk)))
                } else {
                    match g.slpque.sleep(cx.waker().clone()) {
                        Ok(_) => Poll::Pending,
                        Err(e) => Poll::Ready(Err(e)),
                    }
                };
                result
            }
        }

        Lock { lk: self }.await
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
        if try_upread(&mut g) {
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
    /// let reader = lock.upgradable_read().await.unwrap();
    /// assert_eq!(*reader, 1);
    /// assert_eq!(*lock.try_read().unwrap(), 1);
    ///
    /// let mut writer = RwLockUpgradableReadGuard::upgrade(reader).await.unwrap();
    /// *writer = 2;
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn upgradable_read(&self) -> Result<RwLockUpgradableReadGuard<'_, T>> {
        struct Lock<'a, T: ?Sized> {
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = Result<RwLockUpgradableReadGuard<'a, T>>;

            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                let result = if try_upread(&mut g) {
                    Poll::Ready(Ok(RwLockUpgradableReadGuard(self.lk)))
                } else {
                    match g.slpque.sleep(cx.waker().clone()) {
                        Ok(_) => Poll::Pending,
                        Err(e) => Poll::Ready(Err(e)),
                    }
                };
                result
            }
        }

        Lock { lk: self }.await
    }

    /// Attempts to acquire a write lock.
    ///
    /// If a write lock could not be acquired at this time, then [`None`] is returned. Otherwise, a
    /// guard is returned that releases the lock when dropped.
    ///
    /// See also [write](`Self::write`)
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_, T>> {
        let mut g = self.inner.lock();
        if try_write(&mut g) {
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
    /// let writer = lock.write().await.unwrap();
    /// assert!(lock.try_read().is_none());
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn write(&self) -> Result<RwLockWriteGuard<'_, T>> {
        struct Lock<'a, T: ?Sized> {
            first: bool,
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = Result<RwLockWriteGuard<'a, T>>;

            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                } else {
                    g.waiting_writer -= 1;
                }
                let result = if try_write(&mut g) {
                    Poll::Ready(Ok(RwLockWriteGuard(self.lk)))
                } else {
                    match g.slpque.sleep(cx.waker().clone()) {
                        Ok(_) => {
                            g.waiting_writer += 1;
                            Poll::Pending
                        }
                        Err(e) => Poll::Ready(Err(e)),
                    }
                };
                result
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
    /// assert_eq!(*lock.read().await.unwrap(), 2);
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

impl<T: ?Sized> Drop for RwLockReadGuard<'_, T> {
    fn drop(&mut self) {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state & 1, 0);
        debug_assert_ne!(g.state, 0);
        // Decrement the number of readers.
        g.state -= ONE_READER;
        // If this was the last reader
        if g.state == 0 {
            g.slpque.wakeup_one();
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
    /// let reader = lock.upgradable_read().await.unwrap();
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
    pub fn downgrade(guard: Self) -> RwLockReadGuard<'a, T> {
        let mut g = guard.0.inner.lock();
        debug_assert_eq!(g.state & 3, 2);
        g.state += ONE_READER - 2;
        let g = RwLockReadGuard(guard.0);
        mem::forget(guard);
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
    /// let reader = lock.upgradable_read().await.unwrap();
    /// assert_eq!(*reader, 1);
    ///
    /// let reader2 = lock.read().await.unwrap();
    /// let reader = RwLockUpgradableReadGuard::try_upgrade(reader).unwrap_err();
    ///
    /// drop(reader2);
    /// let writer = RwLockUpgradableReadGuard::try_upgrade(reader).unwrap();
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub fn try_upgrade(guard: Self) -> core::result::Result<RwLockWriteGuard<'a, T>, Self> {
        // If there are no readers, grab the write lock.
        let mut g = guard.0.inner.lock();
        debug_assert_eq!(g.state & 3, 2);
        if g.state == 2 {
            g.state = 1;
            Ok(guard.into_writer())
        } else {
            Err(guard)
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
    /// let reader = lock.upgradable_read().await.unwrap();
    /// assert_eq!(*reader, 1);
    ///
    /// let mut writer = RwLockUpgradableReadGuard::upgrade(reader).await.unwrap();
    /// *writer = 2;
    /// # });
    /// # ksched::task::run_all();
    /// ```
    pub async fn upgrade(guard: Self) -> Result<RwLockWriteGuard<'a, T>> {
        struct Lock<'a, T: ?Sized> {
            first: bool,
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = Result<RwLockWriteGuard<'a, T>>;

            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.lk.inner.lock();
                if self.first {
                    debug_assert_eq!(g.state, 2);
                    g.state -= 2;
                    self.first = false;
                } else {
                    g.waiting_writer -= 1;
                }
                let result = if try_write(&mut g) {
                    Poll::Ready(Ok(RwLockWriteGuard(self.lk)))
                } else {
                    match g.slpque.sleep_front(cx.waker().clone()) {
                        Ok(_) => {
                            g.waiting_writer += 1;
                            Poll::Pending
                        }
                        Err(e) => Poll::Ready(Err(e)),
                    }
                };
                result
            }
        }

        let ret = Lock {
            lk: guard.0,
            first: true,
        }
        .await;
        mem::forget(guard);
        ret
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

struct RwLockWriteGuardInner<'a, T: ?Sized>(&'a RwLock<T>);

impl<T: ?Sized> Drop for RwLockWriteGuardInner<'_, T> {
    fn drop(&mut self) {
        let mut g = self.0.inner.lock();
        debug_assert_eq!(g.state, 1);
        g.state = 0;
        g.slpque.wakeup_one();
    }
}

/// A guard that releases the write lock when dropped.
pub struct RwLockWriteGuard<'a, T: ?Sized>(&'a RwLock<T>);

unsafe impl<T: Send + ?Sized> Send for RwLockWriteGuard<'_, T> {}
unsafe impl<T: Sync + ?Sized> Sync for RwLockWriteGuard<'_, T> {}

impl<'a, T: ?Sized> RwLockWriteGuard<'a, T> {
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
    /// let mut writer = lock.write().await.unwrap();
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
    pub fn downgrade(guard: Self) -> RwLockReadGuard<'a, T> {
        let mut g = guard.0.inner.lock();
        debug_assert_eq!(g.state, 1);
        g.state = ONE_READER;
        drop(g);
        RwLockReadGuard(guard.0)
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
    /// let mut writer = lock.write().await.unwrap();
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
    pub fn downgrade_to_upgradable(guard: Self) -> RwLockUpgradableReadGuard<'a, T> {
        let mut g = guard.0.inner.lock();
        debug_assert_eq!(g.state, 1);
        g.state = 2;
        drop(g);
        RwLockUpgradableReadGuard(guard.0)
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
