//! Sleep queue implementation that used to build up synchronization primitives.
use core::{alloc::AllocError, task::Waker};

use alloc::collections::VecDeque;

/// Sleep queue is simply a deque of waker.
pub struct SleepQueue {
    slpque: VecDeque<Waker>,
}

impl SleepQueue {
    /// Create a new sleep queue.
    pub fn new() -> Self {
        Self {
            slpque: VecDeque::new(),
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
    pub fn sleep(&mut self, w: Waker) -> Result<(), AllocError> {
        self.slpque.try_reserve(1).map_err(|_| AllocError)?;
        self.slpque.push_back(w);
        Ok(())
    }
}
