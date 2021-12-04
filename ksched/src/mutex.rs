//! Sleep lock or mutex implementation.

use crate::{
    sleep_queue::SleepQueue,
    sync::Spinlock,
    task::{SleepKind, Task},
};
use core::{
    cell::UnsafeCell,
    fmt,
    future::Future,
    ops::{Deref, DerefMut},
    pin::Pin,
    task::{Context, Poll},
};

/// Inner sleep queue and lock state of Mutex.
struct MutexInner {
    /// If this mutex has been locked.
    locked: bool,
    /// The sleep queue of waiting tasks.
    sleep_queue: SleepQueue,
}

/// An async mutex.
///
/// The locking mechanism uses a FIFO wait queue to avoid starvation.
///
/// # Examples
///
/// ```
/// # ksched::task::spawn(async {
/// use ksched::sync::Mutex;
///
/// let m: Mutex<usize> = Mutex::new(1);
///
/// let mut guard = m.lock().await;
/// *guard = 2;
/// drop(guard);
///
/// let guard = m.lock().await;
/// assert_eq!(*guard, 2);
/// # });
/// # ksched::task::run();
/// ```
pub struct Mutex<T: ?Sized> {
    /// Guard towards status and waiting queue.
    inner: Spinlock<MutexInner>,

    /// The value inside the mutex.
    data: UnsafeCell<T>,
}

// Note that inner is already send and sync by [spin::Mutex]
unsafe impl<T: Send + ?Sized> Send for Mutex<T> {}
unsafe impl<T: Send + ?Sized> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    /// Creates a new async mutex.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::sync::Mutex;
    ///
    /// let mutex: Mutex<usize> = Mutex::new(0);
    /// ```
    pub const fn new(data: T) -> Mutex<T> {
        Mutex {
            inner: Spinlock::new(MutexInner {
                locked: false,
                sleep_queue: SleepQueue::new(),
            }),
            data: UnsafeCell::new(data),
        }
    }

    /// Consumes the mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::sync::Mutex;
    ///
    /// let mutex: Mutex<usize> = Mutex::new(10);
    /// assert_eq!(mutex.into_inner(), 10);
    /// ```
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Acquire the mutex, which must be release manually by [`Self::release`]
    pub async fn acquire(&self) {
        struct Lock<'a, T: ?Sized>(&'a Mutex<T>);

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = ();

            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut inner = self.0.inner.lock();
                let result = if inner.locked {
                    Task::sleep_back(&mut inner.sleep_queue, SleepKind::Mutex, ctx);
                    Poll::Pending
                } else {
                    inner.locked = true;
                    Poll::Ready(())
                };
                result
            }
        }
        Lock(self).await
    }

    /// Unlock manually.
    pub unsafe fn release(&self) {
        let mut inner = self.inner.lock();
        debug_assert_eq!(inner.locked, true);
        Task::wakeup_front(&mut inner.sleep_queue);
        inner.locked = false;
    }

    /// Acquires the mutex.
    ///
    /// Since inserting current task to the wait queue requires memory
    /// allocation, this function may return [AllocError] on oom.
    /// Otherwise, returns a guard that releases the mutex when dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::Mutex;
    ///
    /// let mutex: Mutex<usize> = Mutex::new(10);
    /// let guard = mutex.lock().await;
    /// assert_eq!(*guard, 10);
    /// # });
    /// # ksched::task::run();
    /// ```
    #[inline]
    pub async fn lock(&self) -> MutexGuard<'_, T> {
        self.acquire().await;
        MutexGuard(self)
    }

    /// Attempts to acquire the mutex.
    ///
    /// If the mutex could not be acquired at this time, then [`None`] is returned. Otherwise, a
    /// guard is returned that releases the mutex when dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::sync::Mutex;
    ///
    /// let mutex = Mutex::new(10);
    /// if let Some(guard) = mutex.try_lock() {
    ///     assert_eq!(*guard, 10);
    /// }
    /// # ;
    /// ```
    #[inline]
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T>> {
        let mut g = self.inner.lock();
        if g.locked {
            None
        } else {
            g.locked = true;
            Some(MutexGuard(self))
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the mutex mutably, no actual locking takes place -- the mutable
    /// borrow statically guarantees the mutex is not already acquired.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::Mutex;
    ///
    /// let mut mutex: Mutex<usize> = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    /// assert_eq!(*mutex.lock().await, 10);
    /// # });
    /// # ksched::task::run();
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Locked;
        impl fmt::Debug for Locked {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("<locked>")
            }
        }

        match self.try_lock() {
            None => f.debug_struct("Mutex").field("data", &Locked).finish(),
            Some(guard) => f.debug_struct("Mutex").field("data", &&*guard).finish(),
        }
    }
}

impl<T> From<T> for Mutex<T> {
    fn from(val: T) -> Mutex<T> {
        Mutex::new(val)
    }
}

impl<T: Default + ?Sized> Default for Mutex<T> {
    fn default() -> Mutex<T> {
        Mutex::new(Default::default())
    }
}

/// A guard that releases the mutex when dropped.
pub struct MutexGuard<'a, T: ?Sized>(&'a Mutex<T>);

unsafe impl<T: Send + ?Sized> Send for MutexGuard<'_, T> {}
unsafe impl<T: Sync + ?Sized> Sync for MutexGuard<'_, T> {}

impl<'a, T: ?Sized> MutexGuard<'a, T> {
    /// Returns a reference to the mutex a guard came from.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use ksched::sync::{Mutex, MutexGuard};
    ///
    /// let mutex = Mutex::new(10i32);
    /// let guard = mutex.lock().await;
    /// dbg!(MutexGuard::source(&guard));
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    pub fn source(guard: &MutexGuard<'a, T>) -> &'a Mutex<T> {
        guard.0
    }
}

impl<T: ?Sized> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        unsafe { self.0.release() }
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for MutexGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: fmt::Display + ?Sized> fmt::Display for MutexGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.0.data.get() }
    }
}

impl<T: ?Sized> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.0.data.get() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::task;
    use crate::tests::run_multi;
    use std::sync::Arc;

    #[test]
    fn test_mutex() {
        const N: usize = 100;
        const NCPU: usize = 4;
        let data: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));
        for _i in 0..N {
            let data = data.clone();
            task::spawn(async move {
                let mut lk = data.lock().await;
                task::yield_now().await;
                *lk += 1;
                task::yield_now().await;
            })
            .unwrap();
        }
        run_multi(NCPU);
        let guard = data.try_lock().unwrap();
        assert_eq!(*guard, N);
    }
}
