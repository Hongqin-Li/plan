//! Bitmap-based priority queue implementation.

use crate::task::Task;

use super::task::TaskAdapter;
use alloc::sync::Arc;
use core::marker::PhantomData;
use kalloc::list::List;

use intrusive_collections::LinkedList;

use kalloc::wrapper::Vec;

/// For example, `PRI[0b01110100] = 2`
const PRI: &'static [u8; 256] = &{
    let mut pri = [0u8; 256];
    // pri[0] = 0
    let mut i = 1;
    while i < 256 {
        pri[i] = i.trailing_zeros() as u8;
        assert!(pri[i] < 8);
        i += 1;
    }
    pri
};

/// Priority queue with 8 priority levels.
pub type Prique8<T> = Prique<Prique0<T>, T>;
/// Priority queue with 64 priority levels.
pub type Prique64<T> = Prique<Prique8<T>, T>;
/// Priority queue with 512 priority levels.
pub type Prique512<T> = Prique<Prique64<T>, T>;

/// Priority queue of task with 8 priority levels.
pub type Pritask8 = Prique<Pritask0, Arc<Task>>;
/// Priority queue of task with 64 priority levels.
pub type Pritask64 = Prique<Pritask8, Arc<Task>>;
/// Priority queue of task with 512 priority levels.
pub type Pritask512 = Prique<Pritask64, Arc<Task>>;

/// Priority queue with eight priority levels.
pub trait PriqueTrait<T> {
    /// Max nice value.
    const P: usize;
    /// Return the max nice value.
    fn max_nice() -> usize {
        Self::P
    }
    /// Create a new priority queue.
    /// Panic if oom.
    fn new() -> Self
    where
        Self: Sized;

    /// Push back a item with specific priority.
    ///
    /// Panic if nice value is greater or equal to `P`. Nice 0 is of highest priority.
    fn push(&mut self, nice: usize, t: T);
    /// Pop out the item of largest priority(lowest nice value).
    ///
    /// Items of same priority will be poped in order of FIFO.
    fn pop(&mut self) -> Option<(usize, T)>;
    /// Get the number of elements in queue.
    fn len(&self) -> usize;

    /// Checker funtion for debug.
    #[cfg(any(test, debug_assertions))]
    fn check(&self);
}

/// Naive priority queue with single priority level.
pub struct Prique0<T>(List<T>);

impl<T> PriqueTrait<T> for Prique0<T> {
    const P: usize = 1;
    fn new() -> Self
    where
        Self: Sized,
    {
        Self(List::new())
    }

    fn push(&mut self, nice: usize, t: T) {
        debug_assert!(nice < Self::P);
        self.0.push_back(t).unwrap();
    }

    fn pop(&mut self) -> Option<(usize, T)> {
        self.0.pop_front().map(|t| (0, t))
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    #[cfg(any(test, debug_assertions))]
    fn check(&self) {}
}

/// Priority queue of task that won't oom.
pub struct Pritask0(LinkedList<TaskAdapter>, usize);
impl PriqueTrait<Arc<Task>> for Pritask0 {
    const P: usize = 1;
    fn new() -> Self
    where
        Self: Sized,
    {
        Self(LinkedList::new(TaskAdapter::new()), 0)
    }

    fn push(&mut self, nice: usize, t: Arc<Task>) {
        debug_assert!(nice < Self::P);
        self.1 += 1;
        self.0.push_back(t)
    }

    fn pop(&mut self) -> Option<(usize, Arc<Task>)> {
        let ret = self.0.pop_front().map(|t| (0, t));
        if ret.is_some() {
            self.1 -= 1;
        }
        ret
    }

    fn len(&self) -> usize {
        self.1
    }

    #[cfg(any(test, debug_assertions))]
    fn check(&self) {}
}

/// A wrapper struct to recusively construct priority queues of different max nice values.
pub struct Prique<P: PriqueTrait<T>, T> {
    que: Vec<P>,
    bitmap: usize,
    n: usize,
    phantom: PhantomData<T>,
}

impl<T, S: PriqueTrait<T>> PriqueTrait<T> for Prique<S, T> {
    const P: usize = S::P * 8;
    /// Create a new priority queue.
    /// Panic if oom.
    fn new() -> Self {
        let mut que = Vec::new();
        for _ in 0..8 {
            que.push(S::new());
        }
        Self {
            que,
            bitmap: 0,
            n: 0,
            phantom: PhantomData,
        }
    }

    /// Push back a item with specific priority.
    ///
    /// Nice value should be less than 8. Nice 0 is of highest priority.
    fn push(&mut self, nice: usize, t: T) {
        debug_assert!(nice < Self::P);
        let i = nice / S::P;
        let q = &mut self.que[i];
        q.push(nice % S::P, t);
        if q.len() == 1 {
            self.bitmap |= 1 << i;
        }
        self.n += 1;

        #[cfg(any(test, debug_assertions))]
        self.check();
    }

    /// Pop out the item of largest priority(lowest nice value).
    ///
    /// Items of same priority will be poped in order of FIFO.
    fn pop(&mut self) -> Option<(usize, T)> {
        let i = PRI[self.bitmap as usize] as usize;
        if self.que[i].len() == 1 {
            self.bitmap &= !(1 << i);
        }
        let ret = self.que[i].pop().map(|(pi, t)| {
            self.n -= 1;
            (i * S::P + pi, t)
        });

        #[cfg(any(test, debug_assertions))]
        self.check();

        ret
    }

    fn len(&self) -> usize {
        self.n
    }

    #[cfg(any(test, debug_assertions))]
    fn check(&self) {
        for i in 0..8 {
            if self.bitmap & (1 << i) != 0 {
                assert_ne!(self.que[i].len(), 0);
            } else {
                assert_eq!(self.que[i].len(), 0);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    fn test1<P>()
    where
        P: PriqueTrait<usize>,
    {
        // Small cases.
        for i in 1..P::max_nice() {
            test_pushpop1(P::new(), i);
        }
        // Large case.
        test_pushpop1(P::new(), 10000);
        test_valid_priority1(P::new());
        test_preemption1(P::new());
    }

    fn test_pushpop1<P>(mut pq: P, n: usize)
    where
        P: PriqueTrait<usize>,
    {
        let mut items = Vec::new();
        let mut rng = rand::thread_rng();

        for i in 0..n {
            let item = (rng.gen_range(0..P::max_nice()), i);
            pq.push(item.0, item.1);
            assert_eq!(pq.len(), i + 1);
            items.push(item);
        }
        items.sort();
        let mut pgitems = Vec::new();
        let mut len = pq.len();
        while let Some((pri, t)) = pq.pop() {
            pgitems.push((pri, t));
            len -= 1;
            assert_eq!(pq.len(), len);
        }
        assert_eq!(items, pgitems);
    }

    fn test_valid_priority1<P>(mut pq: P)
    where
        P: PriqueTrait<usize>,
    {
        let m = P::max_nice();
        for i in 0..m {
            pq.push(i, 1);
        }
    }

    fn test_invalid_priority1<P>(mut pq: P)
    where
        P: PriqueTrait<usize>,
    {
        let m = P::max_nice();
        for i in 0..10 {
            pq.push(m + i, 1);
        }
    }

    fn test_preemption1<P>(mut pq: P)
    where
        P: PriqueTrait<usize>,
    {
        if P::max_nice() <= 1 {
            return;
        }
        let n = 10;
        for i in 0..n {
            pq.push(1, i);
        }
        assert_eq!(pq.pop().unwrap(), (1, 0));
        pq.push(1, n);

        for i in 1..=n {
            pq.push(0, 2 * i);
            assert_eq!(pq.pop().unwrap(), (0, 2 * i));
            assert_eq!(pq.pop().unwrap(), (1, i));
        }
        assert_eq!(pq.pop().is_none(), true);
    }
    #[test]
    fn test_prique8() {
        test1::<Prique8<usize>>();
    }
    #[test]
    fn test_prique64() {
        test1::<Prique64<usize>>();
    }
    #[test]
    fn test_prique512() {
        test1::<Prique512<usize>>();
    }

    #[test]
    #[should_panic]
    fn test_prique8_panic() {
        test_invalid_priority1(Prique8::<usize>::new());
    }
    #[test]
    #[should_panic]
    fn test_prique64_panic() {
        test_invalid_priority1(Prique64::<usize>::new());
    }
    #[test]
    #[should_panic]
    fn test_prique512_panic() {
        test_invalid_priority1(Prique512::<usize>::new());
    }
}
