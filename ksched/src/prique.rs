//! Bitmap-based priority queue implementation.

use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::{alloc::AllocError, marker::PhantomData};
use kcore::error::Error;
use kcore::utils::{deque_push_back, vec_push};

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

/// Priority queue with eight priority levels.
pub trait PriqueTrait<T> {
    /// Max nice value.
    const P: usize;
    /// Return the max nice value.
    fn max_nice() -> usize {
        Self::P
    }
    /// Create a new priority queue.
    fn new() -> Result<Self, Error>
    where
        Self: Sized;
    /// Push back a item with specific priority.
    ///
    /// Nice value should be less than `P`. Nice 0 is of highest priority.
    fn push(&mut self, nice: usize, t: T) -> Result<(), Error>;
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
pub struct Prique0<T>(VecDeque<T>);

impl<T> PriqueTrait<T> for Prique0<T> {
    const P: usize = 1;
    fn new() -> Result<Self, Error>
    where
        Self: Sized,
    {
        Ok(Self(VecDeque::new()))
    }

    fn push(&mut self, nice: usize, t: T) -> Result<(), Error> {
        if nice != 0 {
            return Err(Error::BadRequest);
        }
        deque_push_back(&mut self.0, t)?;
        Ok(())
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
    fn new() -> Result<Self, Error> {
        let mut que = Vec::new();
        for _ in 0..8 {
            vec_push(&mut que, S::new()?)?;
        }
        Ok(Self {
            que,
            bitmap: 0,
            n: 0,
            phantom: PhantomData,
        })
    }

    /// Push back a item with specific priority.
    ///
    /// Nice value should be less than 8. Nice 0 is of highest priority.
    fn push(&mut self, nice: usize, t: T) -> Result<(), Error> {
        let i = nice / S::P;
        if let Some(q) = self.que.get_mut(i) {
            q.push(nice % S::P, t)?;
            if q.len() == 1 {
                self.bitmap |= 1 << i;
            }
            self.n += 1;

            #[cfg(any(test, debug_assertions))]
            self.check();

            Ok(())
        } else {
            Err(Error::BadRequest)
        }
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
            test_pushpop1(P::new().unwrap(), i);
        }
        // Large case.
        test_pushpop1(P::new().unwrap(), 10000);
        test_invalid_priority1(P::new().unwrap());
        test_preemption1(P::new().unwrap());
    }

    fn test_pushpop1<P>(mut pq: P, n: usize)
    where
        P: PriqueTrait<usize>,
    {
        let mut items = Vec::new();
        let mut rng = rand::thread_rng();

        for i in 0..n {
            let item = (rng.gen_range(0..P::max_nice()), i);
            pq.push(item.0, item.1).unwrap();
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

    fn test_invalid_priority1<P>(mut pq: P)
    where
        P: PriqueTrait<usize>,
    {
        let m = P::max_nice();
        for i in 0..m {
            assert_eq!(pq.push(i, 1).is_ok(), true);
        }
        for i in 0..10 {
            assert_eq!(pq.push(m + i, 1).is_err(), true);
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
            pq.push(1, i).unwrap();
        }
        assert_eq!(pq.pop().unwrap(), (1, 0));
        pq.push(1, n).unwrap();

        for i in 1..=n {
            pq.push(0, 2 * i).unwrap();
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
}
