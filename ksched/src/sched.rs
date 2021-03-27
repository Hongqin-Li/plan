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
/// ksched::sched::spawn(async {
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
/// use ksched::sched::{spawn, run};
/// use ksched::yield_now::yield_now;
///
/// ksched::sched::spawn(async {
///     yield_now().await;
/// }).expect("oom");
/// ksched::sched::run();
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
/// ksched::sched::run_all();
/// ```
pub fn run_all() {
    while DEFAULT_EXECUTOR.lock().ntasks > 0 {
        run();
    }
}
