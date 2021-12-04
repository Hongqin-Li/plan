//! Condition variable.

use crate::sleep_queue::SleepQueue;
use crate::sync::{MutexGuard, Spinlock, SpinlockGuard};
use crate::task::{SleepKind, Task};
use core::{
    fmt,
    pin::Pin,
    task::{Context, Poll},
};
use futures::Future;

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
///     let mut started = lock.lock().await;
///     *started = true;
///     // We notify the condvar that the value has changed.
///     cvar.notify_one();
/// }).unwrap();
///
/// // Wait for the thread to start up.
/// let (lock, cvar) = &*pair;
/// let mut started = lock.lock().await;
/// while !*started {
///     started = cvar.wait(started).await;
/// }
///
/// # }).unwrap();
/// # ksched::task::run();
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
    ///     let mut started = lock.lock().await;
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.notify_one();
    /// });
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock().await;
    /// while !*started {
    ///     started = cvar.wait(started).await;
    /// }
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    #[allow(clippy::needless_lifetimes)]
    pub async fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> MutexGuard<'a, T> {
        let lk = MutexGuard::source(&guard);
        self.await_notify(guard).await;
        lk.lock().await
    }

    /// Wait for a notification and release the lock.
    pub async fn await_notify<'a, T>(&self, guard: MutexGuard<'a, T>) {
        AwaitNotify {
            cond: self,
            guard: Some(guard),
        }
        .await;
    }

    /// Blocks the current task until this condition variable receives a notification.
    ///
    /// If failed, return the guard. It is guaranteed that the lock is still held.
    ///
    /// # Examples
    ///
    /// ```
    /// # ksched::task::spawn(async {
    /// use std::sync::Arc;
    ///
    /// use ksched::sync::{Spinlock, Condvar};
    /// use ksched::task;
    ///
    /// let pair = Arc::new((Spinlock::new(false), Condvar::new()));
    /// let pair2 = pair.clone();
    ///
    /// task::spawn(async move {
    ///     let (lock, cvar) = &*pair2;
    ///     let mut started = lock.lock();
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.notify_one();
    /// }).unwrap();
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock();
    /// while !*started {
    ///     started = cvar.spin_wait(started).await;
    /// }
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    #[allow(clippy::needless_lifetimes)]
    pub async fn spin_wait<'a, 'b, T>(
        &'a self,
        guard: SpinlockGuard<'b, T>,
    ) -> SpinlockGuard<'b, T> {
        let lk = SpinlockGuard::mutex(&guard);
        self.spin_await_notify(guard).await;
        lk.lock()
    }

    /// Wait for a notification and release the lock.
    pub async fn spin_await_notify<'a, 'b, T>(&'a self, guard: SpinlockGuard<'b, T>) {
        AwaitNotify {
            cond: self,
            guard: Some(guard),
        }
        .await;
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
    ///     let mut started = lock.lock().await;
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.notify_one();
    /// }).unwrap();
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// // As long as the value inside the `Mutex<bool>` is `false`, we wait.
    /// let _guard = cvar.wait_until(
    ///     lock.lock().await,
    ///     |started| { *started }
    /// ).await;
    /// #
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    #[allow(clippy::needless_lifetimes)]
    pub async fn wait_until<'a, T, F>(
        &self,
        mut guard: MutexGuard<'a, T>,
        mut condition: F,
    ) -> MutexGuard<'a, T>
    where
        F: FnMut(&mut T) -> bool,
    {
        while !condition(&mut *guard) {
            guard = self.wait(guard).await;
        }
        guard
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
    /// use ksched::sync::{Spinlock, Condvar};
    /// use ksched::task;
    ///
    /// let pair = Arc::new((Spinlock::new(false), Condvar::new()));
    /// let pair2 = pair.clone();
    ///
    /// task::spawn(async move {
    ///     let (lock, cvar) = &*pair2;
    ///     let mut started = lock.lock();
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.notify_one();
    /// }).unwrap();
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// // As long as the value inside the `Mutex<bool>` is `false`, we wait.
    /// let _guard = cvar.spin_wait_until(
    ///     lock.lock(),
    ///     |started| { *started }
    /// ).await;
    /// #
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    #[allow(clippy::needless_lifetimes)]
    pub async fn spin_wait_until<'a, 'b, T, F>(
        &'a self,
        mut guard: SpinlockGuard<'b, T>,
        mut condition: F,
    ) -> SpinlockGuard<'b, T>
    where
        F: FnMut(&mut T) -> bool,
    {
        while !condition(&mut *guard) {
            guard = self.spin_wait(guard).await;
        }
        guard
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
    ///     let mut started = lock.lock().await;
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.notify_one();
    /// }).unwrap();
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock().await;
    /// while !*started {
    ///     started = cvar.wait(started).await;
    /// }
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    pub fn notify_one(&self) {
        let mut sleep_queue = self.slpque.lock();
        Task::wakeup_front(&mut sleep_queue);
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
    ///     let mut started = lock.lock().await;
    ///     *started = true;
    ///     // We notify the condvar that the value has changed.
    ///     cvar.notify_all();
    /// });
    ///
    /// // Wait for the thread to start up.
    /// let (lock, cvar) = &*pair;
    /// let mut started = lock.lock().await;
    /// // As long as the value inside the `Mutex<bool>` is `false`, we wait.
    /// while !*started {
    ///     started = cvar.wait(started).await;
    /// }
    /// #
    /// # }).unwrap();
    /// # ksched::task::run();
    /// ```
    pub fn notify_all(&self) {
        let mut sleep_queue = self.slpque.lock();
        Task::wakeup_all(&mut sleep_queue);
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
struct AwaitNotify<'a, T> {
    /// The condition variable that we are waiting on
    cond: &'a Condvar,
    /// The lock used with `cond`.
    /// This will be released the first time the future is polled,
    /// after registering the context to be notified.
    guard: Option<T>,
}

impl<'a, T> Future for AwaitNotify<'a, T>
where
    T: Unpin,
{
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.guard.take() {
            Some(guard) => {
                let mut sleep_queue = self.cond.slpque.lock();
                Task::sleep_back(&mut sleep_queue, SleepKind::Any, ctx);
                drop(sleep_queue);
                drop(guard);
                Poll::Pending
            }
            // Only happen if it is polled twice after receiving a notification.
            None => Poll::Ready(()),
        }
    }
}
