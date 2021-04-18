//! Async executor and some basic futures.
use core::alloc::AllocError;

use futures::task::ArcWake;

use super::prique::{Prique64 as Prique, PriqueTrait};
use kcore::error::Error;
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
    schedque: Prique<Arc<Task>>,
    /// Tasks encountering oom when being woken up.
    waitque: VecDeque<Arc<Task>>,
    ntasks: usize,
}

impl Default for Executor {
    fn default() -> Self {
        Executor {
            schedque: Prique::new().unwrap(),
            waitque: VecDeque::new(),
            ntasks: 0,
        }
    }
}

/// Task is our unit of execution and holds a future are waiting on
struct Task {
    pub future: Mutex<Pin<Box<dyn Future<Output = ()> + Send + 'static>>>,
    pub nice: usize,
}

/// Wake by rescheduling.
impl ArcWake for Task {
    fn wake_by_ref(t: &Arc<Self>) {
        DEFAULT_EXECUTOR.lock().resched(t.clone(), false);
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
    fn resched(&mut self, t: Arc<Task>, from_wait: bool) {
        debug_assert!(self.schedque.len() + self.waitque.len() < self.ntasks);
        debug_assert!(self.waitque.capacity() >= self.ntasks);
        match self.schedque.push(t.nice, t.clone()) {
            Err(Error::OutOfMemory) => {
                // Won't panic since we have reserved in spawn.
                if from_wait {
                    self.waitque.push_front(t);
                } else {
                    self.waitque.push_back(t);
                }
            }
            _ => {}
        }
    }

    /// Create a new task and add to the executor.
    ///
    /// Here, we increment `ntasks`, which is the number of unfinished tasks
    /// and is always greater or equal to length of `tasks` queue. The decrement
    /// is done in [run].
    ///
    /// If allocation failed when pushing back to the tasks queue, it returns [Error].
    fn spawn(
        &mut self,
        nice: usize,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<(), Error> {
        debug_assert!(self.schedque.len() + self.waitque.len() <= self.ntasks);

        let t = Arc::try_new(Task {
            nice,
            future: Mutex::new(Box::into_pin(Box::try_new(future)?)),
        })?;
        self.ntasks += 1;
        self.waitque.try_reserve(self.ntasks - self.waitque.len())?;
        self.resched(t, false);
        Ok(())
    }

    /// Called when one task is terminating.
    fn exit1(&mut self) {
        self.ntasks -= 1;
        self.waitque.shrink_to(self.ntasks);
        // TODO: shrink schedque.
    }
}

lazy_static! {
    static ref DEFAULT_EXECUTOR: Mutex<Box<Executor>> = {
        let m = Executor::default();
        Mutex::new(Box::try_new(m).unwrap())
    };
}

/// Spawn a new task to be run.
///
/// # Examples
///
/// ```
/// ksched::task::spawn(0, async {
///    println!("hello, world");
/// }).expect("oom");
/// ```
pub fn spawn(nice: usize, future: impl Future<Output = ()> + 'static + Send) -> Result<(), Error> {
    DEFAULT_EXECUTOR.lock().spawn(nice, future)
}

/// Run tasks until idle.
///
/// # Examples
///
/// ```
/// use ksched::task;
///
/// task::spawn(0, async {
///     task::yield_now().await;
/// }).expect("oom");
/// task::run();
/// ```
pub fn run() {
    loop {
        let mut e = DEFAULT_EXECUTOR.lock();
        while let Some(t) = e.waitque.pop_front() {
            e.resched(t, true);
        }
        let t = e.schedque.pop();
        drop(e);
        if let Some((nice, t)) = t {
            if t.poll().is_ready() {
                DEFAULT_EXECUTOR.lock().exit1();
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
/// # ksched::task::spawn(0, async {
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
