//! Sleep queue implementation that used to build up synchronization primitives.
use alloc::collections::VecDeque;
use core::{alloc::AllocError, mem::swap, task::Waker};
use kcore::error::Error;
use kcore::vecque::Vecque;

/// Sleep queue is simply a deque of waker.
pub struct SleepQueue {
    slpque: Vecque<Waker>,
}

impl SleepQueue {
    /// Create a new sleep queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use ksched::slpque::SleepQueue;
    ///
    /// let que = SleepQueue.new();
    /// ```
    pub const fn new() -> Self {
        Self {
            slpque: Vecque::new(),
        }
    }

    /// Notifies at most one blocked operation.
    pub fn wakeup_one(&mut self) {
        if let Some(w) = self.slpque.pop_front() {
            w.wake();
        }
    }

    /// Notifies all blocked operations.
    pub fn wakeup_all(&mut self) {
        while let Some(w) = self.slpque.pop_front() {
            w.wake();
        }
    }

    /// Sleep a task on this queue.
    pub fn sleep(&mut self, w: Waker) -> Result<(), Error> {
        self.slpque.push_back(w)?;
        Ok(())
    }

    /// Sleep a task on the front of this queue.
    pub fn sleep_front(&mut self, w: Waker) -> Result<(), Error> {
        self.slpque.push_front(w)?;
        Ok(())
    }
}
