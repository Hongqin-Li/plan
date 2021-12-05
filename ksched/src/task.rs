//! Async executor and some basic futures.

use crate::sync::Spinlock;
use crate::waker;
use crate::{
    executor::{ExecuteWeight, Executor, LocalExecutor, DEFAULT_EXECUTOR},
    sleep_queue::SleepQueue,
};
use alloc::{boxed::Box, sync::Arc};
use core::{
    alloc::AllocError,
    future::Future,
    pin::Pin,
    sync::atomic::{AtomicU8, AtomicUsize, Ordering},
    task::{Context, Poll},
};
use intrusive_collections::{intrusive_adapter, LinkedListLink};
use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::{FromPrimitive, ToPrimitive};

pub(crate) struct Task {
    sleep_kind: AtomicU8,
    /// Quantum(= weight < MAX_QUANTUM) for time-sharing tasks or
    /// priority(= weight - MAX_QUANTUM) for real-time tasks.
    weight: AtomicUsize,
    /// Quantum in this round.
    quantum: AtomicUsize,
    /// Timestamp of last tick, used to measure how long this task has been executed.
    timestamp: AtomicUsize,
    /// Index of its local executor, only used for time-sharing tasks.
    local_executor_id: AtomicUsize,
    ctx: &'static Executor,
    future: Spinlock<Pin<Box<dyn Future<Output = ()> + Send + 'static>>>,
    /// SAFETY: Guarded by the lock of task queue.
    link: LinkedListLink,
}

intrusive_adapter!(pub(crate) TaskAdapter = Arc<Task>: Task { link: LinkedListLink });

#[derive(Debug, Clone, Copy, FromPrimitive, ToPrimitive)]
pub(crate) enum SleepKind {
    Any,
    Mutex,
    Reader,
    Writer,
    UpgradableReader,
}

impl Drop for Task {
    fn drop(&mut self) {
        self.ctx.ntasks.fetch_sub(1, Ordering::SeqCst);
    }
}

impl Task {
    pub fn new(
        ctx: &'static Executor,
        local_executor_id: usize,
        weight: ExecuteWeight,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<Arc<Self>, AllocError> {
        let boxed_future = Box::try_new(future)?;
        let raw_weight = weight.into_raw_weight();
        let task = Arc::try_new(Task {
            sleep_kind: AtomicU8::new(0),
            future: Spinlock::new(Box::into_pin(boxed_future)),
            link: LinkedListLink::new(),
            weight: AtomicUsize::new(raw_weight),
            quantum: AtomicUsize::new(raw_weight),
            local_executor_id: AtomicUsize::new(local_executor_id),
            ctx,
            timestamp: AtomicUsize::new(0),
        })?;
        ctx.ntasks.fetch_add(1, Ordering::SeqCst);
        Ok(task)
    }

    pub fn get_sleep_kind(&self) -> SleepKind {
        let raw_sleep_kind = self.sleep_kind.load(Ordering::Relaxed);
        SleepKind::from_u8(raw_sleep_kind).unwrap()
    }

    pub fn set_sleep_kind(&self, sleep_kind: SleepKind) {
        self.sleep_kind
            .store(sleep_kind.to_u8().unwrap(), Ordering::Relaxed);
    }

    pub fn set_weight(&self, weight: ExecuteWeight) {
        self.weight
            .store(weight.into_raw_weight(), Ordering::Relaxed);
    }

    pub fn get_weight(&self) -> ExecuteWeight {
        ExecuteWeight::from_raw_weight(self.weight.load(Ordering::Relaxed))
    }

    pub fn get_local_executor(&self) -> &'static LocalExecutor {
        let idx = self.local_executor_id.load(Ordering::Relaxed);
        &self.ctx.local_executors[idx]
    }

    pub fn switch_executor(&self, executor_id: usize, from_round: usize, to_round: usize) {
        let diff_round = to_round - from_round;
        let weight = self.weight.load(Ordering::Relaxed) as usize;
        let quantum = self.quantum.load(Ordering::Relaxed);
        self.quantum
            .store(quantum + diff_round * weight, Ordering::Relaxed);
        self.local_executor_id.store(executor_id, Ordering::Relaxed);
    }

    pub fn reload_quantum(&self) {
        let quantum = self.weight.load(Ordering::Relaxed) as usize;
        self.quantum.store(quantum, Ordering::Relaxed);
    }

    /// TODO: use hardware timestamp.
    fn get_current_timestamp(&self) -> usize {
        self.timestamp.load(Ordering::Relaxed) + 1
    }

    pub fn tick_begin(&self) {
        self.timestamp
            .store(self.get_current_timestamp(), Ordering::Relaxed);
    }

    /// Return if the task still have some quantum.
    pub fn tick(&self) -> Option<usize> {
        let timestamp = self.timestamp.load(Ordering::Relaxed);
        let diff = self.get_current_timestamp() - timestamp;
        let mut quantum = self.quantum.load(Ordering::Relaxed);
        quantum = quantum.checked_sub(diff).unwrap_or(0);
        self.quantum.store(quantum, Ordering::Relaxed);
        self.timestamp.store(timestamp + diff, Ordering::Relaxed);
        if quantum == 0 {
            None
        } else {
            Some(quantum)
        }
    }

    pub fn poll(self: &Arc<Self>) -> Poll<()> {
        let waker = waker::waker(self.clone());
        let context = &mut Context::from_waker(&waker);
        let mut future = self.future.lock();
        self.tick_begin();
        future.as_mut().poll(context)
    }
}

impl Task {
    fn from_ctx(ctx: &mut Context<'_>) -> Arc<Task> {
        waker::get_task(ctx.waker())
    }

    pub fn sleep_back(queue: &mut SleepQueue, sleep_kind: SleepKind, ctx: &mut Context<'_>) {
        let task = Task::from_ctx(ctx);
        task.set_sleep_kind(sleep_kind);
        queue.push_back(task);
    }

    pub fn sleep_front(queue: &mut SleepQueue, sleep_kind: SleepKind, ctx: &mut Context<'_>) {
        let task = Task::from_ctx(ctx);
        task.set_sleep_kind(sleep_kind);
        queue.push_front(task);
    }

    pub fn wakeup_front(queue: &mut SleepQueue) -> Option<SleepKind> {
        let task = queue.pop_front()?;
        let sleep_kind = task.get_sleep_kind();
        let executor = task.get_local_executor();
        executor.reschedule(task, false);
        Some(sleep_kind)
    }

    pub fn wakeup_all(queue: &mut SleepQueue) {
        while let Some(_) = Task::wakeup_front(queue) {}
    }
}

/// SAFETY: See [`Task`].
unsafe impl Sync for Task {}

/// Spawn a task to the default executor.
///
/// Note that it doesn't mean to execute the task, just spawn it.
///
/// # Examples
///
/// ```
/// use ksched::task;
///
/// task::spawn(async {
///    println!("hello, world");
/// }).expect("oom");
/// ```
pub fn spawn<T>(future: T) -> Result<(), AllocError>
where
    T: Future<Output = ()> + Send + 'static,
{
    DEFAULT_EXECUTOR.local_executors[0].spawn(future)
}

/// Run until all tasks in default executor are done.
///
/// # Examples
///
/// ```
/// use ksched::task;
///
/// task::spawn(async move {
///     println!("hello, world");
/// }).unwrap();
/// task::run();
/// ```
pub fn run() {
    DEFAULT_EXECUTOR.local_executors[0].run();
}

/// Cooperatively gives up a timeslice to the task scheduler.
///
/// Calling this function will move the currently executing future to the back
/// of the execution queue, making room for other futures to execute. This is
/// especially useful after running CPU-intensive operations inside a future.
///
/// # Examples
///
/// ```
/// # ksched::task::spawn(async {
/// #
/// ksched::task::yield_now().await;
/// #
/// # });
/// # ksched::task::run();
/// ```
pub async fn yield_now() {
    struct YieldNow(bool);

    impl Future for YieldNow {
        type Output = ();
        fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
            let task = Task::from_ctx(ctx);
            if !self.0 {
                self.0 = true;
                let executor = task.get_local_executor();
                executor.reschedule(task, false);
                Poll::Pending
            } else {
                Poll::Ready(())
            }
        }
    }

    YieldNow(false).await
}

/// Make a task into a time-sharing task with specific quantum per round.
pub async fn set_quantum(quantum: usize) {
    struct SetQuantum(ExecuteWeight);

    impl Future for SetQuantum {
        type Output = ();
        fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
            let task = Task::from_ctx(ctx);
            task.set_weight(self.0);
            Poll::Ready(())
        }
    }

    SetQuantum(ExecuteWeight::from_quantum(quantum)).await
}

/// Retrieve the quantum of a time-sharing task.
///
/// Return [None] if this is a real-time task.
pub async fn get_quantum() -> Option<usize> {
    struct GetQuantum;

    impl Future for GetQuantum {
        type Output = Option<usize>;
        fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
            let task = Task::from_ctx(ctx);
            let result = if let ExecuteWeight::TimeSharing(quantum) = task.get_weight() {
                Some(quantum)
            } else {
                None
            };
            Poll::Ready(result)
        }
    }

    GetQuantum.await
}

/// Make a task into a real-time one with specific priority.
pub async fn set_priority(priority: usize) {
    struct SetPriority(ExecuteWeight);

    impl Future for SetPriority {
        type Output = ();
        fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
            let task = Task::from_ctx(ctx);
            task.set_weight(self.0);
            Poll::Ready(())
        }
    }

    SetPriority(ExecuteWeight::from_priority(priority)).await
}

/// Retrieve the priority of a real-time task.
///
/// Return [None] if this is a time-sharing task.
pub async fn get_priority() -> Option<usize> {
    struct GetPriority;

    impl Future for GetPriority {
        type Output = Option<usize>;
        fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
            let task = Task::from_ctx(ctx);
            let result = if let ExecuteWeight::RealTime(priority) = task.get_weight() {
                Some(priority)
            } else {
                None
            };
            Poll::Ready(result)
        }
    }

    GetPriority.await
}

/// Inject a preemptable point for fair scheduling and real-time scheduling.
///
/// If you have NCPU local executors and preemptable points are carefully injected into your code
/// so that the time consumed between any two sequential preemptable points is O(1), then for each
/// executor, the real-time tasks with highest priority is guaranteed to be waken up in O(NCPU).
pub async fn preempt_point() {
    struct PreemptPoint;

    impl Future for PreemptPoint {
        type Output = ();
        fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
            let task = Task::from_ctx(ctx);
            let executor = task.get_local_executor();
            if executor.try_preempt(task).is_ok() {
                Poll::Pending
            } else {
                Poll::Ready(())
            }
        }
    }

    PreemptPoint.await
}

pub async fn sleep(_key: usize) {
    todo!()
}
