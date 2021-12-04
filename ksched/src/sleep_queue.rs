//! Sleep queue implementation that used to build up synchronization primitives.

use crate::task::{SleepKind, TaskAdapter};
use core::ops::{Deref, DerefMut};
use intrusive_collections::LinkedList;

pub(crate) struct SleepQueue(LinkedList<TaskAdapter>);

impl SleepQueue {
    pub const fn new() -> Self {
        Self(LinkedList::new(TaskAdapter::NEW))
    }

    pub fn peek_front(&self) -> Option<SleepKind> {
        let task = self.0.front().get()?;
        Some(task.get_sleep_kind())
    }
}

impl Deref for SleepQueue {
    type Target = LinkedList<TaskAdapter>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SleepQueue {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Drop for SleepQueue {
    fn drop(&mut self) {
        assert!(self.0.is_empty(), "sleeping task dropped");
    }
}
