use core::alloc::AllocError;

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
use futures::task::ArcWake;

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
    /// Block on task
    fn block_on(&mut self, future: Box<dyn Future<Output = ()> + 'static + Send + Unpin>)
    {
        // FIXME: Arc::new() may panic
        let task = Arc::new(Task {
            future: Mutex::new(Box::pin(future)),
        });
        loop {
            let result = task.poll();
            if let Poll::Ready(val) = result {
                return val;
            }
        }
    }

    fn resched(&mut self, t: Arc<Task>) {
        debug_assert!(self.tasks.len() < self.ntasks);
        debug_assert!(self.tasks.capacity() >= self.ntasks);
        // Won't panic since we have reserve in spawn.
        self.tasks.push_back(t);
    }

    fn spawn(&mut self, future: impl Future<Output = ()> + 'static + Send) -> Result<(), AllocError> {
        let t = Arc::try_new(Task {
            future: Mutex::new(Box::pin(future)),
        })?;
        debug_assert!(self.tasks.len() <= self.ntasks);
        self.ntasks += 1;
        self.tasks.try_reserve(self.ntasks - self.tasks.len()).map_err(|_| AllocError)?;
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
pub fn spawn(future: impl Future<Output = ()> + 'static + Send) -> Result<(), AllocError> {
    DEFAULT_EXECUTOR.lock().spawn(future)
}

/// Run tasks until idle.
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

/// Run until all tasks are ready.
pub fn run_all() {
    while DEFAULT_EXECUTOR.lock().ntasks > 0 {
        run();
    }
}