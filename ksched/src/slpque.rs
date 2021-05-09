//! Sleep queue implementation that used to build up synchronization primitives.
use core::task::Waker;

use kalloc::list::List;

/// Sleep queue is simply a deque of waker.
pub struct SleepQueue<T> {
    /// Queue of waker and tags.
    pub que: List<(T, Waker)>,
}

impl<T: Clone> SleepQueue<T> {
    /// Create a new sleep queue.
    pub const fn new() -> Self {
        Self { que: List::new() }
    }

    /// Notifies at most one blocked operation.
    pub fn wakeup_one(&mut self) -> Option<T> {
        self.que.pop_front().map(|(t, w)| {
            w.wake();
            t
        })
    }

    /// Notifies all blocked operations.
    pub fn wakeup_all(&mut self) {
        while let Some((_, w)) = self.que.pop_front() {
            w.wake();
        }
    }

    /// Sleep a task on this queue.
    ///
    /// FIXME:
    /// Unfortunately, Rust doesn't allow us to get the raw pointer behind [`Waker`].
    /// Otherwise, we can get and push back the Arc<Task> from waker to a linked list.
    pub fn sleep(&mut self, tag: T, waker: Waker) {
        while self.que.push_back((tag.clone(), waker.clone())).is_err() {}
    }

    /// Sleep a task on the front of this queue.
    pub fn sleep_front(&mut self, tag: T, waker: Waker) {
        while self.que.push_front((tag.clone(), waker.clone())).is_err() {}
    }
}
