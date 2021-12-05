//! An async executor using the Distributed Weighted Round-Robin (DWRR) scheduling algorithm.

use crate::priority_queue::{PriorityQueue64 as PriorityQueue, PriorityQueueTrait};
use crate::task::{Task, TaskAdapter};
use alloc::sync::Arc;
use core::future::Future;
use core::{
    alloc::AllocError,
    sync::atomic::{AtomicUsize, Ordering},
};
use intrusive_collections::LinkedList;
use spin::Mutex;

pub(crate) static DEFAULT_EXECUTOR: Executor = {
    static DEFAULT_LOCAL_EXECUTORS: [LocalExecutor; 1] = [LocalExecutor::new(&DEFAULT_EXECUTOR, 0)];
    Executor {
        local_executors: &DEFAULT_LOCAL_EXECUTORS,
        real_time_queue: Mutex::new(PriorityQueue::NEW),
        ntasks: AtomicUsize::new(0),
    }
};

/// Priority of a real-time task must be in [0, MAX_PRIORITY).
pub const MAX_PRIORITY: usize = PriorityQueue::MAX_PRIORITY;
/// Quantum of a time-sharing task must in [0, MAX_QUANTUM).
pub const MAX_QUANTUM: usize = usize::MAX - MAX_PRIORITY;

const DEFAULT_QUANTUM: usize = 1;

/// Global executor that is made up of per-cpu local executors.
pub struct Executor {
    /// Local(per-cpu) executors governed by this executor.
    pub local_executors: &'static [LocalExecutor],
    pub(crate) ntasks: AtomicUsize,
    pub(crate) real_time_queue: Mutex<PriorityQueue>,
}

/// Per-cpu executor.
pub struct LocalExecutor {
    inner: Mutex<ExecutorInner>,
    ctx: &'static Executor,
    id: usize,
}

impl LocalExecutor {
    /// Create a new executor.
    pub const fn new(ctx: &'static Executor, id: usize) -> Self {
        Self {
            inner: Mutex::new(ExecutorInner::new()),
            ctx,
            id,
        }
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
    pub fn spawn(
        &self,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<(), AllocError> {
        self.spawn_time_sharing(DEFAULT_QUANTUM, future)
    }

    /// Spawn a time-sharing task to run.
    pub fn spawn_time_sharing(
        &self,
        quantum: usize,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<(), AllocError> {
        self.spawn1(ExecuteWeight::from_quantum(quantum), future)
    }

    /// Spawn a real-time task to run.
    ///
    /// For efficiency, a real-time task can only be scheduled by the executor that spawns it.
    pub fn spawn_real_time(
        &self,
        priority: usize,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<(), AllocError> {
        self.spawn1(ExecuteWeight::from_priority(priority), future)
    }

    fn spawn1(
        &self,
        weight: ExecuteWeight,
        future: impl Future<Output = ()> + 'static + Send,
    ) -> Result<(), AllocError> {
        let task = Task::new(self.ctx, self.id, weight, future)?;
        self.reschedule(task, true);
        Ok(())
    }

    /// Run until all tasks of this executor pool are complete.
    pub fn run(&self) {
        while self.ctx.ntasks.load(Ordering::SeqCst) != 0 {
            if let Some((_priority, task)) = self.ctx.real_time_queue.lock().pop() {
                let _ = task.poll();
            } else {
                let mut inner = self.inner.lock();
                if let Some(task) = inner.this_queue().pop_front() {
                    drop(inner);
                    let _ = task.poll();
                } else {
                    let round = inner.round;
                    drop(inner);
                    self.steal_tasks(round);
                    inner = self.inner.lock();
                    if inner.this_queue().is_empty() && !inner.next_queue().is_empty() {
                        inner.round += 1;
                    }
                }
            }
        }
    }

    /// Steal tasks from other local executors.
    fn steal_tasks(&self, max_round: usize) {
        const BATCH_SIZE: usize = 10;
        const NO_TASK: Option<Arc<Task>> = None;
        let mut tasks = [NO_TASK; BATCH_SIZE];
        let mut task_num = 0;
        for (i, executor) in self.ctx.local_executors.iter().enumerate() {
            if i == self.id {
                continue;
            }
            let mut other = executor.inner.lock();
            if task_num < BATCH_SIZE && other.round <= max_round {
                if let Some(task) = other.this_queue().pop_front() {
                    task.switch_executor(self.id, other.round, max_round);
                    tasks[task_num] = Some(task);
                    task_num += 1;
                }
            }
            if task_num < BATCH_SIZE && other.round < max_round {
                if let Some(task) = other.next_queue().pop_front() {
                    task.switch_executor(self.id, other.round, max_round);
                    tasks[task_num] = Some(task);
                    task_num += 1;
                }
            }
            if task_num == BATCH_SIZE {
                break;
            }
        }
        let mut inner = self.inner.lock();
        for i in 0..task_num {
            inner.this_queue().push_back(tasks[i].take().unwrap());
        }
    }

    pub(crate) fn try_preempt(&self, task: Arc<Task>) -> Result<(), ()> {
        let weight = task.get_weight();
        match weight {
            ExecuteWeight::TimeSharing(_quantum) => {
                if !self.ctx.real_time_queue.lock().is_empty() {
                    let mut inner = self.inner.lock();
                    if task.tick().is_some() {
                        inner.this_queue().push_front(task);
                    } else {
                        task.reload_quantum();
                        inner.next_queue().push_back(task);
                    }
                    Ok(())
                } else if task.tick().is_none() {
                    Ok(())
                } else {
                    Err(())
                }
            }
            ExecuteWeight::RealTime(priority) => {
                let mut ret = Err(());
                let mut rt_queue = self.ctx.real_time_queue.lock();
                if let Some((other_priority, other_task)) = rt_queue.pop() {
                    if priority <= other_priority {
                        rt_queue.push(priority, task);
                        ret = Ok(())
                    }
                    rt_queue.push(other_priority, other_task);
                }
                ret
            }
        }
    }

    pub(crate) fn reschedule(&self, task: Arc<Task>, first_time: bool) {
        let weight = task.get_weight();
        match weight {
            ExecuteWeight::TimeSharing(_quantum) => {
                let mut inner = self.inner.lock();
                task.reload_quantum();
                if first_time {
                    inner.this_queue().push_front(task);
                } else {
                    inner.next_queue().push_back(task);
                }
            }
            ExecuteWeight::RealTime(priority) => {
                let mut rt_queue = self.ctx.real_time_queue.lock();
                rt_queue.push(priority, task);
            }
        }
    }
}

unsafe impl Sync for LocalExecutor {}

type TaskQueue = LinkedList<TaskAdapter>;

struct ExecutorInner {
    queue: [TaskQueue; 2],
    round: usize,
}

impl ExecutorInner {
    const fn new() -> Self {
        const QUEUE: TaskQueue = LinkedList::new(TaskAdapter::NEW);
        Self {
            queue: [QUEUE; 2],
            round: 0,
        }
    }

    pub fn this_queue(&mut self) -> &mut TaskQueue {
        &mut self.queue[self.round & 1]
    }

    pub fn next_queue(&mut self) -> &mut TaskQueue {
        &mut self.queue[(self.round + 1) & 1]
    }
}

#[derive(Clone, Copy)]
pub(crate) enum ExecuteWeight {
    TimeSharing(usize),
    RealTime(usize),
}

impl ExecuteWeight {
    pub fn from_quantum(quantum: usize) -> Self {
        let weight = quantum.min(MAX_QUANTUM - 1);
        ExecuteWeight::TimeSharing(weight)
    }

    pub fn from_priority(priority: usize) -> Self {
        let priority = priority.min(MAX_PRIORITY);
        ExecuteWeight::RealTime(priority)
    }

    pub fn from_raw_weight(raw_weight: usize) -> Self {
        if raw_weight < MAX_QUANTUM {
            Self::TimeSharing(raw_weight)
        } else {
            Self::RealTime(raw_weight - MAX_QUANTUM)
        }
    }

    pub fn into_raw_weight(self) -> usize {
        match self {
            ExecuteWeight::TimeSharing(quantum) => quantum,
            ExecuteWeight::RealTime(priority) => priority + MAX_QUANTUM,
        }
    }
}
