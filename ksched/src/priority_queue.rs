//! Bitmap-based priority queue implementation.

use crate::task::{Task, TaskAdapter};
use alloc::sync::Arc;
use core::marker::PhantomData;
use intrusive_collections::LinkedList;

/// For example, `PRI[0b01110100] = 2`
const PRI: &'static [u8; 256] = &{
    let mut pri = [0u8; 256];
    // pri[0] = 0
    let mut i: usize = 1;
    while i <= u8::MAX as usize {
        let greatest_priority = 7 - (i as u8).leading_zeros();
        pri[i] = greatest_priority as u8;
        i += 1;
    }
    pri
};

pub(crate) trait PriorityQueueTrait<T> {
    /// Priority must be in range [0, MAX_PRIORITY).
    const MAX_PRIORITY: usize;

    /// Create a new priority queue.
    const NEW: Self;

    /// Push back a item with specific priority.
    ///
    /// Default to `MAX_PRIORITY - 1` if the priority value is out of range.
    fn push(&mut self, priority: usize, item: T);

    /// Pop out the item of largest priority.
    ///
    /// Return both task and its priority. Items of same priority will be poped FIFO.
    fn pop(&mut self) -> Option<(usize, T)>;

    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A wrapper struct to recusively construct priority queues.
pub(crate) struct PriorityQueue<T, P: PriorityQueueTrait<T>> {
    queue: [P; 8],
    bitmap: usize,
    len: usize,
    phantom: PhantomData<T>,
}

impl<T, P: PriorityQueueTrait<T>> PriorityQueueTrait<T> for PriorityQueue<T, P> {
    const MAX_PRIORITY: usize = P::MAX_PRIORITY * 8;

    const NEW: Self = {
        Self {
            queue: [P::NEW; 8],
            bitmap: 0,
            len: 0,
            phantom: PhantomData,
        }
    };

    fn push(&mut self, priority: usize, item: T) {
        let priority = priority.min(Self::MAX_PRIORITY - 1);
        let i = priority / P::MAX_PRIORITY;
        let queue = &mut self.queue[i];
        queue.push(priority % P::MAX_PRIORITY, item);
        if queue.len() == 1 {
            self.bitmap |= 1 << i;
        }
        self.len += 1;
    }

    fn pop(&mut self) -> Option<(usize, T)> {
        let i = PRI[self.bitmap as usize] as usize;
        if let Some((priority, task)) = self.queue[i].pop() {
            self.len -= 1;
            if self.queue[i].len() == 0 {
                self.bitmap &= !(1 << i);
            }
            Some((i * P::MAX_PRIORITY + priority, task))
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        self.len
    }
}

pub(crate) struct PriorityQueue0 {
    queue: LinkedList<TaskAdapter>,
    len: usize,
}

impl PriorityQueueTrait<Arc<Task>> for PriorityQueue0 {
    const MAX_PRIORITY: usize = 1;

    const NEW: Self = Self {
        queue: LinkedList::new(TaskAdapter::NEW),
        len: 0,
    };

    fn push(&mut self, _priority: usize, task: Arc<Task>) {
        self.len += 1;
        self.queue.push_back(task);
    }

    fn pop(&mut self) -> Option<(usize, Arc<Task>)> {
        if let Some(task) = self.queue.pop_front() {
            self.len -= 1;
            Some((0, task))
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        self.len
    }
}

/// Priority queue of task with 8 priority levels.
pub(crate) type PriorityQueue8 = PriorityQueue<Arc<Task>, PriorityQueue0>;
/// Priority queue of task with 64 priority levels.
pub(crate) type PriorityQueue64 = PriorityQueue<Arc<Task>, PriorityQueue8>;

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use rand::Rng;

    struct PriorityVec0<T>(Vec<T>);

    impl<T> PriorityQueueTrait<T> for PriorityVec0<T> {
        const MAX_PRIORITY: usize = 1;

        const NEW: Self = Self(Vec::new());

        fn push(&mut self, _priority: usize, item: T) {
            self.0.push(item);
        }

        fn pop(&mut self) -> Option<(usize, T)> {
            if self.len() == 0 {
                None
            } else {
                Some((0, self.0.remove(0)))
            }
        }

        fn len(&self) -> usize {
            self.0.len()
        }
    }

    type PriorityVec8<T> = PriorityQueue<T, PriorityVec0<T>>;
    type PriorityVec64<T> = PriorityQueue<T, PriorityVec8<T>>;
    type PriorityVec512<T> = PriorityQueue<T, PriorityVec64<T>>;

    fn test1<P: PriorityQueueTrait<usize>>() {
        // Small cases.
        for i in 1..P::MAX_PRIORITY {
            test_pushpop1(P::NEW, i);
        }
        // Large case.
        test_pushpop1(P::NEW, 10000);
        test_valid_priority1(P::NEW);
        test_preemption1(P::NEW);
    }

    fn test_pushpop1<P: PriorityQueueTrait<usize>>(mut pq: P, n: usize) {
        let mut items = Vec::new();
        let mut rng = rand::thread_rng();

        for i in 0..n {
            let item = (rng.gen_range(0..P::MAX_PRIORITY), i);
            pq.push(item.0, item.1);
            assert_eq!(pq.len(), i + 1);
            items.push(item);
        }
        items.sort_by(|a, b| {
            if a.0 != b.0 {
                b.0.cmp(&a.0)
            } else {
                a.1.cmp(&b.1)
            }
        });
        let mut pqitems = Vec::new();
        let mut len = pq.len();
        while let Some((pri, t)) = pq.pop() {
            pqitems.push((pri, t));
            len -= 1;
            assert_eq!(pq.len(), len);
        }
        assert_eq!(items, pqitems);
    }

    fn test_valid_priority1<P: PriorityQueueTrait<usize>>(mut pq: P) {
        let m = P::MAX_PRIORITY;
        for i in 0..m {
            pq.push(i, 1);
        }
    }

    fn test_invalid_priority<P: PriorityQueueTrait<usize>>(mut pq: P) {
        let m = P::MAX_PRIORITY;
        for i in 0..10 {
            pq.push(m + i, 1);
        }
        for _i in (0..10).rev() {
            let (priority, _task) = pq.pop().unwrap();
            assert_eq!(priority, P::MAX_PRIORITY - 1);
        }
        assert!(pq.pop().is_none());
    }

    fn test_preemption1<P: PriorityQueueTrait<usize>>(mut pq: P) {
        if P::MAX_PRIORITY <= 1 {
            return;
        }
        let n = 10;
        for i in 0..n {
            pq.push(0, i);
        }
        assert_eq!(pq.pop().unwrap(), (0, 0));
        pq.push(0, n);

        for i in 1..=n {
            pq.push(1, 2 * i);
            assert_eq!(pq.pop().unwrap(), (1, 2 * i));
            assert_eq!(pq.pop().unwrap(), (0, i));
        }
        assert_eq!(pq.pop().is_none(), true);
    }

    #[test]
    fn test_prique8() {
        assert_eq!(PriorityVec8::<usize>::MAX_PRIORITY, 8);
        test1::<PriorityVec8<usize>>();
    }

    #[test]
    fn test_prique64() {
        assert_eq!(PriorityVec64::<usize>::MAX_PRIORITY, 64);
        test1::<PriorityVec64<usize>>();
    }

    #[test]
    fn test_prique512() {
        assert_eq!(PriorityVec512::<usize>::MAX_PRIORITY, 512);
        test1::<PriorityVec512<usize>>();
    }

    #[test]
    fn test_prique8_invalid_priority() {
        test_invalid_priority(PriorityVec8::<usize>::NEW);
    }

    #[test]
    fn test_prique64_invalid_priority() {
        test_invalid_priority(PriorityVec64::<usize>::NEW);
    }

    #[test]
    fn test_prique512_invalid_priority() {
        test_invalid_priority(PriorityVec512::<usize>::NEW);
    }
}
