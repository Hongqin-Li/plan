use core::alloc::AllocError;

use futures::task::ArcWake;
use lazy_static::*;
use {
    alloc::{boxed::Box, collections::vec_deque::VecDeque, sync::Arc},
    core::{
        future::Future,
        pin::Pin,
        task::{Context, Poll},
    },
    spin::Mutex,
};

/// Executor holds a list of tasks to be processed
pub struct Executor {
    tasks: VecDeque<Arc<Task>>,
    ntasks: usize,
}

impl Default for Executor {
    fn default() -> Self {
        Executor {
            tasks: VecDeque::new(),
            ntasks: 0,
        }
    }
}

/// Task is our unit of execution and holds a future are waiting on
struct Task {
    pub future: Mutex<Pin<Box<dyn Future<Output = ()> + Send + 'static>>>,
}

/// Wake by rescheduling.
impl ArcWake for Task {
    fn wake_by_ref(t: &Arc<Self>) {
        DEFAULT_EXECUTOR.lock().resched(t.clone());
    }
}

impl Task {
    fn poll(self: &Arc<Self>) -> Poll<()> {
        // Task may be in poll.
        while alloc::sync::Arc::<Task>::strong_count(self) != 1 {}

        let mut future = self.future.lock();

        // Poll our future and give it a waker
        let w = futures::task::waker(self.clone());
        let context = &mut Context::from_waker(&w);
        future.as_mut().poll(context)
    }
}

impl Executor {
    fn resched(&mut self, t: Arc<Task>) {
        debug_assert!(self.tasks.len() < self.ntasks);
        debug_assert!(self.tasks.capacity() >= self.ntasks);
        // Won't panic since we have reserved in spawn.
        self.tasks.push_back(t);
    }

    /// Create a new task and add to the executor.
    ///
    /// Here, we increment `ntasks`, which is the number of unfinished tasks
    /// and is always greater or equal to length of `tasks` queue. The decrement
    /// is done in [run].
    ///
    /// If allocation failed when pushing back to the tasks queue, it returns [AllocError].
    fn spawn(
        &mut self,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<(), AllocError> {
        let t = Arc::try_new(Task {
            future: Mutex::new(Box::pin(future)),
        })?;
        debug_assert!(self.tasks.len() <= self.ntasks);
        self.ntasks += 1;
        self.tasks
            .try_reserve(self.ntasks - self.tasks.len())
            .map_err(|_| AllocError)?;
        self.resched(t);
        Ok(())
    }
}

lazy_static! {
    static ref DEFAULT_EXECUTOR: Mutex<Box<Executor>> = {
        let m = Executor::default();
        Mutex::new(Box::new(m))
    };
}

/// Spawn a new task to be run.
///
/// # Examples
///
/// ```
/// ksched::task::spawn(async {
///    println!("hello, world");
/// }).expect("oom");
/// ```
pub fn spawn(future: impl Future<Output = ()> + 'static + Send) -> Result<(), AllocError> {
    DEFAULT_EXECUTOR.lock().spawn(future)
}

/// Run tasks until idle.
///
/// # Examples
///
/// ```
/// use ksched::task;
///
/// task::spawn(async {
///     task::yield_now().await;
/// }).expect("oom");
/// task::run();
/// ```
pub fn run() {
    loop {
        let t = DEFAULT_EXECUTOR.lock().tasks.pop_front();
        if let Some(t) = t {
            if t.poll().is_ready() {
                DEFAULT_EXECUTOR.lock().ntasks -= 1;
            }
        } else {
            break;
        }
    }
}

/// Run until all tasks are finished.
///
/// # Examples
///
/// ```
/// ksched::task::run_all();
/// ```
pub fn run_all() {
    while DEFAULT_EXECUTOR.lock().ntasks > 0 {
        run();
    }
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
/// # ksched::task::run_all();
/// ```
pub async fn yield_now() {
    struct YieldNow(bool);

    impl Future for YieldNow {
        type Output = ();
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            if !self.0 {
                self.0 = true;
                cx.waker().wake_by_ref();
                Poll::Pending
            } else {
                Poll::Ready(())
            }
        }
    }

    YieldNow(false).await
}
