use core::ops::{Deref, DerefMut};
use core::{alloc::AllocError, fmt};
use core::{
    borrow::BorrowMut,
    cell::{Cell, UnsafeCell},
    future::Future,
    pin::Pin,
    sync::atomic::AtomicBool,
    task::{Context, Poll, Waker},
};
// use std::process;
use core::sync::atomic::{AtomicUsize, Ordering};
/// FIXME: Use falliable_collection.
extern crate alloc;
use alloc::{collections::VecDeque, sync::Arc};
/// use core::time::{Duration, Instant};
use core::usize;
use spin::{Mutex as Spinlock};


struct MutexInner {
    locked: bool,
    waiter: WakerSet,
}

/// An async mutex.
///
/// The locking mechanism uses a FIFO wait queue to avoid starvation.
///
/// # Examples
///
/// ```
/// # ksched::sched::spawn(async {
/// use ksched::mutex::Mutex;
///
/// let m: Mutex<usize> = Mutex::new(1);
///
/// let mut guard = m.lock().await.expect("oom");
/// *guard = 2;
/// drop(guard);
///
/// let guard = m.lock().await.expect("oom");
/// assert_eq!(*guard, 2);
/// # });
/// # ksched::sched::run_all();
/// ```
pub struct Mutex<T: ?Sized> {
    /// Guard towards status and waiting queue.
    inner: Spinlock<MutexInner>,

    /// The value inside the mutex.
    data: UnsafeCell<T>,
}

unsafe impl<T: Send + ?Sized> Send for Mutex<T> {}
unsafe impl<T: Send + ?Sized> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    /// Creates a new async mutex.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::mutex::Mutex;
    ///
    /// let mutex: Mutex<usize> = Mutex::new(0);
    /// ```
    pub fn new(data: T) -> Mutex<T> {
        Mutex {
            inner: Spinlock::new(MutexInner{locked: false, waiter: WakerSet::new()}),
            data: UnsafeCell::new(data),
        }
    }

    /// Consumes the mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::mutex::Mutex;
    ///
    /// let mutex: Mutex<usize> = Mutex::new(10);
    /// assert_eq!(mutex.into_inner(), 10);
    /// ```
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Acquires the mutex.
    ///
    /// Since inserting current task to the wait queue requires memory
    /// allocation, this function may return [AllocError] on oom.
    /// Otherwise, returns a guard that releases the mutex when dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::sched::spawn(async {
    /// use ksched::mutex::Mutex;
    ///
    /// let mutex: Mutex<usize> = Mutex::new(10);
    /// let guard = mutex.lock().await.expect("oom");
    /// assert_eq!(*guard, 10);
    /// # });
    /// # ksched::sched::run_all();
    /// ```
    #[inline]
    pub async fn lock(&self) -> Result<MutexGuard<'_, T>, AllocError> {
        struct Lock<'a, T: ?Sized> {
            mutex: &'a Mutex<T>,
        }

        impl<'a, T: ?Sized> Future for Lock<'a, T> {
            type Output = Result<MutexGuard<'a, T>, AllocError>;

            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let mut g = self.mutex.inner.lock();
                let result = if g.locked {
                    match g.waiter.insert(cx) {
                        Ok(_) => Poll::Pending,
                        Err(_) => Poll::Ready(Err(AllocError)),
                    }
                } else {
                    g.locked = true;
                    Poll::Ready(Ok(MutexGuard(self.mutex)))
                };
                result
            }
        }

        Lock { mutex: self }.await
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the mutex mutably, no actual locking takes place -- the mutable
    /// borrow statically guarantees the mutex is not already acquired.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::sched::spawn(async {
    /// use ksched::mutex::Mutex;
    ///
    /// let mut mutex: Mutex<usize> = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    /// assert_eq!(*mutex.lock().await.expect("oom"), 10);
    /// # });
    /// # ksched::sched::run_all();
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
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

impl<T: ?Sized> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        // Notify waiters.
        let mut g = self.0.inner.lock();
        g.waiter.notify_one();
        g.locked = false;

        #[cfg(test)]
        println!("mutex guard drop");
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

// NOTE this should only ever be used in "Thread mode"
pub struct WakerSet {
    inner: UnsafeCell<Inner>,
}

impl WakerSet {
    pub fn new() -> Self {
        Self {
            inner: UnsafeCell::new(Inner::new()),
        }
    }
    pub fn notify_all(&self) {
        // Safe since UnsafeCell is not sync.
        unsafe { (*self.inner.get()).notify_all() }
    }

    pub fn notify_one(&self) {
        // Safe since UnsafeCell is not sync.
        unsafe { (*self.inner.get()).notify_one() }
    }

    pub fn insert(&self, cx: &Context<'_>) -> Result<(), AllocError> {
        // Safe since UnsafeCell is not sync.
        unsafe { (*self.inner.get()).insert(cx) }
    }
}

struct Inner {
    // NOTE the number of entries is capped at `NTASKS`
    entries: VecDeque<Waker>,
}

impl Inner {
    fn new() -> Self {
        Self {
            entries: VecDeque::new(),
        }
    }

    /// Notifies at most one blocked operation.
    fn notify_one(&mut self) {
        if let Some(w) = self.entries.pop_front() {
            w.wake();
        }
    }

    /// Notifies all blocked operations.
    fn notify_all(&mut self) {
        while let Some(w) = self.entries.pop_front() {
            w.wake();
        }
    }

    fn insert(&mut self, cx: &Context<'_>) -> Result<(), AllocError> {
        let w = cx.waker().clone();
        self.entries.try_reserve(1).map_err(|e| AllocError)?;
        self.entries.push_back(w);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::thread;

    use super::*;
    use crate::sched::{spawn, run_all};
    use crate::yield_now::yield_now;

    #[test]
    fn test_mutex() {
        const N: usize = 100;
        const NCPU: usize = 4;
        let data: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));
        for i in 0..N {
            let data = data.clone();
            spawn(async move {
                println!("task {}: start", i);
                let mut lk = data.lock().await.unwrap();
                yield_now().await;
                *lk += 1;
                yield_now().await;
                println!("task {}: end", i);
            }).unwrap();
        }

        let mut handles = vec![];
        for _ in 0..NCPU {
            let data = data.clone();
            handles.push(thread::spawn(|| {
                run_all();
                spawn(async move {
                    let g = data.lock().await.unwrap();
                    assert_eq!(*g, N);
                }).unwrap();
                run_all();
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        
    }
}
