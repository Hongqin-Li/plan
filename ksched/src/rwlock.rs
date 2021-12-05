//! Read-write lock.

use crate::sleep_queue::SleepQueue;
use crate::sync::Spinlock;
use crate::task::SleepKind;
use crate::task::Task;
use core::fmt;
use core::mem;
use core::ops::{Deref, DerefMut};
use core::{
    cell::UnsafeCell,
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

const ONE_WRITER: usize = 1;
const ONE_UPGRADABLE_READER: usize = 2;
const ONE_READER: usize = 4;

struct RwLockInner {
    /// Bit 0 indicates if there is an active writer. If this is true, other bits must be zero.
    /// Bit 1 indicates if there is an active upgradable reader. If this is true, bit 0 must be
    /// zero.
    /// Other bits indicates the number of normal readers that are reading.
    state: usize,
    /// Since it is write-preferring, we need to know whether some writers are sleeping.
    waiting_writer: usize,
    slpque: SleepQueue,
}

impl RwLockInner {
    fn active_writer_cnt(&self) -> usize {
        self.state & ONE_WRITER
    }

    fn active_upgradable_reader_cnt(&self) -> usize {
        (self.state & ONE_UPGRADABLE_READER) / ONE_UPGRADABLE_READER
    }

    fn active_reader_cnt(&self) -> usize {
        self.state / ONE_READER
    }

    fn try_read(&mut self, wait_writer: bool) -> Result<(), ()> {
        if self.active_writer_cnt() == 0 && (!wait_writer || self.waiting_writer == 0) {
            self.state += ONE_READER;
            Ok(())
        } else {
            Err(())
        }
    }

    fn try_write(&mut self, wait_writer: bool) -> Result<(), ()> {
        if self.active_writer_cnt() == 0
            && self.active_reader_cnt() == 0
            && self.active_upgradable_reader_cnt() == 0
            && (!wait_writer || self.waiting_writer == 0)
        {
            self.state += ONE_WRITER;
            Ok(())
        } else {
            Err(())
        }
    }

    fn try_upgradable_read(&mut self, wait_writer: bool) -> Result<(), ()> {
        if self.active_writer_cnt() == 0
            && self.active_upgradable_reader_cnt() == 0
            && (!wait_writer || self.waiting_writer == 0)
        {
            self.state += ONE_UPGRADABLE_READER;
            Ok(())
        } else {
            Err(())
        }
    }

    fn try_to_wakeup(&mut self) {
        while let Some(sleep_kind) = self.slpque.peek_front() {
            let try_wake = match sleep_kind {
                SleepKind::Reader => self.try_read(false),
                SleepKind::Writer => self.try_write(false),
                SleepKind::UpgradableReader => self.try_upgradable_read(false),
                _ => unreachable!("invalid sleep kind"),
            };
            if try_wake.is_ok() {
                if let Some(SleepKind::Writer) = Task::wakeup_front(&mut self.slpque) {
                    self.waiting_writer -= 1;
                }
            } else {
                break;
            }
        }
    }
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
/// # ksched::task::spawn(async {
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
/// # ksched::task::run();
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
    pub const fn new(value: T) -> RwLock<T> {
        RwLock {
            inner: Spinlock::new(RwLockInner {
                state: 0,
                waiting_writer: 0,
                slpque: SleepQueue::new(),
            }),
            value: UnsafeCell::new(value),
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

impl<T: ?Sized> RwLock<T> {
    /// Attempts to acquire a read lock.
    ///
    /// If a read lock could not be acquired at this time, then [`None`] is returned. Otherwise, a
    /// guard is returned that releases the lock when dropped.
    ///
    /// See also [read](`Self::read`)
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T>> {
        let mut inner = self.inner.lock();
        if inner.try_read(true).is_ok() {
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
    /// # ksched::task::spawn(async {
    /// use ksched::sync::RwLock;
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let reader = lock.read().await;
    /// assert_eq!(*reader, 1);
    ///
    /// assert!(lock.try_read().is_some());
    /// # });
    /// # ksched::task::run();
    /// ```
    pub async fn read(&self) -> RwLockReadGuard<'_, T> {
        struct Lock<'a, T: ?Sized> {
            lk: &'a RwLock<T>,
            first: bool,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockReadGuard<'a, T>;
            fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut inner = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                    if inner.try_read(true).is_ok() {
                        Poll::Ready(RwLockReadGuard(self.lk))
                    } else {
                        Task::sleep_back(&mut inner.slpque, SleepKind::Reader, ctx);
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
        let mut inner = self.inner.lock();
        if inner.try_upgradable_read(true).is_ok() {
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
    /// # ksched::task::spawn(async {
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
    /// # ksched::task::run();
    /// ```
    pub async fn upgradable_read(&self) -> RwLockUpgradableReadGuard<'_, T> {
        struct Lock<'a, T: ?Sized> {
            lk: &'a RwLock<T>,
            first: bool,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockUpgradableReadGuard<'a, T>;
            fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut inner = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                    if inner.try_upgradable_read(true).is_ok() {
                        Poll::Ready(RwLockUpgradableReadGuard(self.lk))
                    } else {
                        Task::sleep_back(&mut inner.slpque, SleepKind::UpgradableReader, ctx);
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
        let mut inner = self.inner.lock();
        if inner.try_write(true).is_ok() {
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
    /// # ksched::task::spawn(async {
    /// use ksched::sync::RwLock;
    ///
    /// let lock = RwLock::new(1);
    ///
    /// let writer = lock.write().await;
    /// assert!(lock.try_read().is_none());
    /// # });
    /// # ksched::task::run();
    /// ```
    pub async fn write(&self) -> RwLockWriteGuard<'_, T> {
        struct Lock<'a, T: ?Sized> {
            first: bool,
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = RwLockWriteGuard<'a, T>;
            fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut inner = self.lk.inner.lock();
                if self.first {
                    self.first = false;
                    if inner.try_write(true).is_ok() {
                        Poll::Ready(RwLockWriteGuard(self.lk))
                    } else {
                        Task::sleep_back(&mut inner.slpque, SleepKind::Writer, ctx);
                        inner.waiting_writer += 1;
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
    /// # ksched::task::spawn(async {
    /// use ksched::sync::RwLock;
    ///
    /// let mut lock = RwLock::new(1);
    ///
    /// *lock.get_mut() = 2;
    /// assert_eq!(*lock.read().await, 2);
    /// # });
    /// # ksched::task::run();
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
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.active_writer_cnt(), 0);
        debug_assert_ne!(inner.active_reader_cnt(), 0);
        inner.state -= ONE_READER;
        if inner.state == 0 {
            inner.try_to_wakeup();
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
    /// Downgrades into a regular reader guard.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
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
    /// # ksched::task::run();
    /// ```
    pub fn downgrade(self) -> RwLockReadGuard<'a, T> {
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.active_writer_cnt(), 0);
        debug_assert_eq!(inner.active_upgradable_reader_cnt(), 1);
        inner.state -= ONE_UPGRADABLE_READER;
        inner.state += ONE_READER;
        inner.try_to_wakeup();
        drop(inner);

        let guard = RwLockReadGuard(self.0);
        mem::forget(self);
        guard
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
    /// # ksched::task::spawn(async {
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
    /// # ksched::task::run();
    /// ```
    pub fn try_upgrade(self) -> Result<RwLockWriteGuard<'a, T>, Self> {
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.active_writer_cnt(), 0);
        debug_assert_eq!(inner.active_upgradable_reader_cnt(), 1);
        if inner.active_reader_cnt() == 0 {
            inner.state = ONE_WRITER;
            drop(inner);

            let guard = RwLockWriteGuard(self.0);
            mem::forget(self);
            Ok(guard)
        } else {
            Err(self)
        }
    }

    /// Upgrades into a write lock.
    ///
    /// No writer can acquire this lock until the upgrade has finished.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
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
    /// # ksched::task::run();
    /// ```
    pub async fn upgrade(self) -> RwLockWriteGuard<'a, T> {
        struct Upgrade<'a, T: ?Sized> {
            first: bool,
            lk: &'a RwLock<T>,
        }

        impl<'a, T: ?Sized> Future for Upgrade<'a, T> {
            type Output = RwLockWriteGuard<'a, T>;
            fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut inner = self.lk.inner.lock();
                if self.first {
                    self.first = false;

                    debug_assert_eq!(inner.active_writer_cnt(), 0);
                    debug_assert_eq!(inner.active_upgradable_reader_cnt(), 1);
                    inner.state -= ONE_UPGRADABLE_READER;
                    if inner.try_write(false).is_ok() {
                        Poll::Ready(RwLockWriteGuard(self.lk))
                    } else {
                        Task::sleep_front(&mut inner.slpque, SleepKind::Writer, ctx);
                        inner.waiting_writer += 1;
                        Poll::Pending
                    }
                } else {
                    Poll::Ready(RwLockWriteGuard(self.lk))
                }
            }
        }

        let guard = Upgrade {
            first: true,
            lk: self.0,
        }
        .await;
        mem::forget(self);
        guard
    }
}

impl<T: ?Sized> Drop for RwLockUpgradableReadGuard<'_, T> {
    fn drop(&mut self) {
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.active_writer_cnt(), 0);
        debug_assert_eq!(inner.active_upgradable_reader_cnt(), 1);
        inner.state -= ONE_UPGRADABLE_READER;
        inner.try_to_wakeup();
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
    /// # ksched::task::spawn(async {
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
    /// # ksched::task::run();
    /// ```
    pub fn downgrade(self) -> RwLockReadGuard<'a, T> {
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.state, ONE_WRITER);
        inner.state = ONE_READER;
        inner.try_to_wakeup();
        drop(inner);

        let guard = RwLockReadGuard(self.0);
        mem::forget(self);
        guard
    }

    /// Downgrades into an upgradable reader guard.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
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
    /// # ksched::task::run();
    /// ```
    pub fn downgrade_to_upgradable(self) -> RwLockUpgradableReadGuard<'a, T> {
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.state, ONE_WRITER);
        inner.state = ONE_UPGRADABLE_READER;
        inner.try_to_wakeup();
        drop(inner);

        let guard = RwLockUpgradableReadGuard(self.0);
        mem::forget(self);
        guard
    }
}

impl<T: ?Sized> Drop for RwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        let mut inner = self.0.inner.lock();
        debug_assert_eq!(inner.state, ONE_WRITER);
        inner.state = 0;
        inner.try_to_wakeup();
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
            task::spawn(async move {
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
            task::spawn(async move {
                let mut g = x.write().await;
                *g += 1;
                println!("{}", *g);
            })
            .unwrap();
        }
        run_multi(10);
        task::spawn(async move {
            let g = x.read().await;
            assert_eq!(*g, N);
        })
        .unwrap();
        run_multi(1);
    }

    #[test]
    fn test_readwrite() {
        const N: isize = 100;
        let x = Arc::new(RwLock::new(0isize));
        for _ in 0..N {
            let x = x.clone();
            let x2 = x.clone();
            task::spawn(async move {
                let mut g = x.write().await;
                *g += 1;
            })
            .unwrap();
            task::spawn(async move {
                let g = x2.read().await;
                assert!(*g >= 0);
            })
            .unwrap();
        }
        run_multi(10);

        task::spawn(async move {
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
            task::spawn(async move {
                let mut g = x.write().await;
                *g += 1;
            })
            .unwrap();

            task::spawn(async move {
                let g = x2.upgradable_read().await;
                let mut g = g.upgrade().await;
                *g += 1;
            })
            .unwrap();
        }

        run_multi(10);
        task::spawn(async move {
            let g = x.read().await;
            assert_eq!(*g, 2 * N);
        })
        .unwrap();
        run_multi(1);
    }
}
