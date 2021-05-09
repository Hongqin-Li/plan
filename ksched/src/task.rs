//! Async executor and some basic futures.
#![allow(missing_docs)]
use core::{alloc::AllocError, cell::UnsafeCell};
use futures::task::ArcWake;

use intrusive_collections::intrusive_adapter;
use intrusive_collections::{LinkedList, LinkedListLink};

use super::prique::{PriqueTrait, Pritask64 as Prique};
use crate::sync::Spinlock;
use lazy_static::*;
use {
    alloc::{boxed::Box, sync::Arc},
    core::{
        future::Future,
        pin::Pin,
        task::{Context, Poll},
    },
};

/// Executor holds a list of tasks to be processed
pub struct Executor {
    schedque: Prique,
    ntasks: usize,
}

impl Default for Executor {
    fn default() -> Self {
        Executor {
            schedque: Prique::new(),
            ntasks: 0,
        }
    }
}

/// Task is our unit of execution and holds a future are waiting on
pub struct Task {
    /// SAFETY: We won't poll a future until its reference count is one.
    pub future: UnsafeCell<Pin<Box<dyn Future<Output = ()> + Send + 'static>>>,
    /// SAFETY: It's a constant.
    pub nice: usize,
    /// SAFETY: You must guarantee that only one waker exist outside the context.
    link: LinkedListLink,
}

/// SAFETY: see [Task].
unsafe impl Sync for Task {}

intrusive_adapter!(pub TaskAdapter = Arc<Task>: Task { link: LinkedListLink });

/// Wake by rescheduling.
impl ArcWake for Task {
    fn wake_by_ref(t: &Arc<Self>) {
        DEFAULT_EXECUTOR.lock().sched(t.clone());
    }
}

impl Task {
    fn poll(self: &Arc<Self>) -> Poll<()> {
        // Task may be in poll.
        while alloc::sync::Arc::<Task>::strong_count(self) != 1 {}

        // Safe since the reference count is 1.
        let future = unsafe { self.future.get().as_mut().unwrap() };

        // Poll our future and give it a waker.
        let w = futures::task::waker(self.clone());
        let context = &mut Context::from_waker(&w);
        future.as_mut().poll(context)
    }
}

impl Executor {
    /// Add a task to the scheduler queue.
    fn sched(&mut self, t: Arc<Task>) {
        self.schedque.push(t.nice, t);
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
    ) -> Result<(), AllocError> {
        let t = Arc::try_new(Task {
            nice,
            future: UnsafeCell::new(Box::into_pin(Box::try_new(future)?)),
            link: LinkedListLink::new(),
        })?;
        self.ntasks += 1;
        self.sched(t);
        Ok(())
    }

    /// Called when one task is terminating.
    fn exit1(&mut self) {
        self.ntasks -= 1;
    }
}

lazy_static! {
    static ref DEFAULT_EXECUTOR: Spinlock<Box<Executor>> = {
        let m = Executor::default();
        Spinlock::new(Box::try_new(m).unwrap())
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
pub fn spawn(
    nice: usize,
    future: impl Future<Output = ()> + 'static + Send,
) -> Result<(), AllocError> {
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
        let t = e.schedque.pop();
        drop(e);
        if let Some((_, t)) = t {
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
