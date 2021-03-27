use core::pin::Pin;
use core::{
    alloc::AllocError,
    fmt,
    task::{Context, Poll},
};

use futures::Future;

use super::mutex::MutexGuard;
use spin::Mutex as Spinlock;

use crate::slpque::SleepQueue;

/// A Condition Variable
///
/// This type is an async version of [`std::sync::Condvar`].
///
/// [`std::sync::Condvar`]: https://doc.rust-lang.org/std/sync/struct.Condvar.html
///
/// # Examples
///
/// ```
/// # ksched::task::spawn(async {
/// #
/// use std::sync::Arc;
///
/// use ksched::sync::{Mutex, Condvar};
/// use ksched::task;
///
/// let pair = Arc::new((Mutex::new(false), Condvar::new()));
/// let pair2 = pair.clone();
///
/// // Inside of our lock, spawn a new thread, and then wait for it to start.
/// task::spawn(async move {
///     let (lock, cvar) = &*pair2;
///     let mut started = lock.lock().await.expect("oom");
///     *started = true;
///     // We notify the condvar that the value has changed.
///     cvar.wakeup_one();
/// }).expect("oom");
///
/// // Wait for the thread to start up.
/// let (lock, cvar) = &*pair;
/// let mut started = lock.lock().await.expect("oom");
/// while !*started {
///     started = cvar.wait(started).await.expect("oom");
/// }
///
/// # }).expect("oom");
/// # ksched::task::run_all();
/// ```
pub struct Condvar {
    slpque: Spinlock<SleepQueue>,
}

impl Default for Condvar {
    fn default() -> Self {
        Condvar::new()
    }
}

impl Condvar {
    /// Creates a new condition variable
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::sync::Condvar;
    ///
    /// let cvar = Condvar::new();
    /// ```
    pub fn new() -> Self {
        Condvar {
            slpque: Spinlock::new(SleepQueue::new()),
        }
    }

    /// Blocks the current task until this condition variable receives a notification.
    ///
    /// Unlike the std equivalent, this does not check that a single mutex is used at runtime.
    /// However, as a best practice avoid using with multiple mutexes.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use std::sync::Arc;
    ///
    /// use ksched::sync::{Mutex, Condvar};
    /// use ksched::task;
    ///
    /// let pair = Arc::new((Mutex::new(false), Condvar::new()));
    /// let pair2 = pair.clone();
    ///
    /// task::spawn(async move {
    ///     let (lock, cvar) = &*pair2;
    ///     let mut started = lock.lock().await.expect("oom");
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.wakeup_one();
    /// });
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock().await.expect("oom");
    /// while !*started {
    ///     started = cvar.wait(started).await.expect("oom");
    /// }
    /// # }).expect("oom");
    /// # ksched::task::run_all();
    /// ```
    #[allow(clippy::needless_lifetimes)]
    pub async fn wait<'a, T>(
        &self,
        guard: MutexGuard<'a, T>,
    ) -> Result<MutexGuard<'a, T>, AllocError> {
        let mutex = MutexGuard::source(&guard);
        self.await_notify(guard).await?;
        mutex.lock().await
    }

    fn await_notify<'a, T>(&self, guard: MutexGuard<'a, T>) -> AwaitNotify<'_, 'a, T> {
        AwaitNotify {
            cond: self,
            guard: Some(guard),
        }
    }

    /// Blocks the current taks until this condition variable receives a notification and the
    /// required condition is met. Spurious wakeups are ignored and this function will only
    /// return once the condition has been met.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// #
    /// use std::sync::Arc;
    ///
    /// use ksched::sync::{Mutex, Condvar};
    /// use ksched::task;
    ///
    /// let pair = Arc::new((Mutex::new(false), Condvar::new()));
    /// let pair2 = pair.clone();
    ///
    /// task::spawn(async move {
    ///     let (lock, cvar) = &*pair2;
    ///     let mut started = lock.lock().await.expect("oom");
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.wakeup_one();
    /// }).expect("oom");
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// // As long as the value inside the `Mutex<bool>` is `false`, we wait.
    /// let _guard = cvar.wait_until(
    ///     lock.lock().await.expect("oom"),
    ///     |started| { *started }
    /// ).await.expect("oom");
    /// #
    /// # }).expect("oom");
    /// # ksched::task::run_all();
    /// ```
    #[allow(clippy::needless_lifetimes)]
    pub async fn wait_until<'a, T, F>(
        &self,
        mut guard: MutexGuard<'a, T>,
        mut condition: F,
    ) -> Result<MutexGuard<'a, T>, AllocError>
    where
        F: FnMut(&mut T) -> bool,
    {
        while !condition(&mut *guard) {
            guard = self.wait(guard).await?;
        }
        Ok(guard)
    }

    /// Wakes up one blocked task on this condvar.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use std::sync::Arc;
    ///
    /// use ksched::sync::{Mutex, Condvar};
    /// use ksched::task;
    ///
    /// let pair = Arc::new((Mutex::new(false), Condvar::new()));
    /// let pair2 = pair.clone();
    ///
    /// task::spawn(async move {
    ///     let (lock, cvar) = &*pair2;
    ///     let mut started = lock.lock().await.expect("oom");
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.wakeup_one();
    /// }).expect("oom");
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock().await.expect("oom");
    /// while !*started {
    ///     started = cvar.wait(started).await.expect("oom");
    /// }
    /// # }).expect("oom");
    /// # ksched::task::run_all();
    /// ```
    pub fn wakeup_one(&self) {
        self.slpque.lock().wakeup_one();
    }

    /// Wakes up all blocked tasks on this condvar.
    ///
    /// # Examples
    /// ```
    /// # ksched::task::spawn(async {
    /// #
    /// use std::sync::Arc;
    ///
    /// use ksched::sync::{Mutex, Condvar};
    /// use ksched::task;
    ///
    /// let pair = Arc::new((Mutex::new(false), Condvar::new()));
    /// let pair2 = pair.clone();
    ///
    /// task::spawn(async move {
    ///     let (lock, cvar) = &*pair2;
    ///     let mut started = lock.lock().await.expect("oom");
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.wakeup_all();
    /// });
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock().await.expect("oom");
    /// // As long as the value inside the `Mutex<bool>` is `false`, we wait.
    /// while !*started {
    ///     started = cvar.wait(started).await.expect("oom");
    /// }
    /// #
    /// # }).expect("oom");
    /// # ksched::task::run_all();
    /// ```
    pub fn wakeup_all(&self) {
        self.slpque.lock().wakeup_all();
    }
}

impl fmt::Debug for Condvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Condvar { .. }")
    }
}

/// A future that waits for another task to notify the condition variable.
///
/// This is an internal future that `wait` and `wait_until` await on.
struct AwaitNotify<'a, 'b, T> {
    /// The condition variable that we are waiting on
    cond: &'a Condvar,
    /// The lock used with `cond`.
    /// This will be released the first time the future is polled,
    /// after registering the context to be notified.
    guard: Option<MutexGuard<'b, T>>,
}

impl<'a, 'b, T> Future for AwaitNotify<'a, 'b, T> {
    type Output = Result<(), AllocError>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.guard.take() {
            Some(_) => {
                // The guard is dropped when we return, which frees the lock.
                match self.cond.slpque.lock().sleep(cx.waker().clone()) {
                    Ok(()) => Poll::Pending,
                    Err(_) => Poll::Ready(Err(AllocError)),
                }
            }
            None => {
                // Only happen if it is polled twice after receiving a notification.
                Poll::Ready(Ok(()))
            }
        }
    }
}

impl<'a, 'b, T> Drop for AwaitNotify<'a, 'b, T> {
    fn drop(&mut self) {}
}
