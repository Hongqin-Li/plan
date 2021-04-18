//! A double-ended queue implemented with two vector.
//!
//! This queue has *O*(1) amortized inserts to both ends of the
//! container. When operations on the queue only involves removal from **single**
//! end, the removals are amortized *O*(1). It also has *O*(1) indexing like
//! a vector. The contained elements are not required to be copyable, and the
//! queue will be sendable if the contained type is sendable.

use crate::error::Result;
use crate::utils::{vec_push, vec_shrink_to_fit};
use alloc::vec::Vec;
use core::mem::swap;

/// A double-ended queue implemented with two vector.
///
/// The "default" usage of this type as a queue is to use [`push_back`] or [`push_front`] to
/// add to the back or front of the queue, and [`pop_front`] or [`pop_back`] to remove from
/// the front or back of the queue.
///
/// Since `Vecque` is simulated by two vector(stack), its elements are not necessarily
/// contiguous in memory.
///
/// [`push_back`]: Vecque::push_back
/// [`push_front`]: Vecque::push_front
/// [`pop_front`]: Vecque::pop_front
/// [`pop_back`]: Vecque::pop_back
pub struct Vecque<T> {
    back: Vec<T>,
    front: Vec<T>,
}

impl<T> Vecque<T> {
    /// Creates an empty `Vecque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let vector: Vecque<u32> = Vecque::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            back: Vec::new(),
            front: Vec::new(),
        }
    }

    /// Creates an empty `Vecque` with space for at least `capacity` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let vector: Vecque<u32> = Vecque::with_capacity(10).expect("oom");
    /// ```
    pub fn with_capacity(capacity: usize) -> Result<Self> {
        // +1 since the ringbuffer always leaves one space empty
        let mut ret = Self {
            back: Vec::new(),
            front: Vec::new(),
        };
        ret.back.try_reserve(capacity)?;
        ret.front.try_reserve(capacity)?;
        Ok(ret)
    }

    /// Provides a reference to the element at the given index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut buf = Vecque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert_eq!(buf.get(1), Some(&4));
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        let front_len = self.front.len();
        if index < front_len {
            self.front.get(front_len - 1 - index)
        } else {
            self.back.get(index - front_len)
        }
    }

    /// Provides a mutable reference to the element at the given index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut buf = Vecque::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// if let Some(elem) = buf.get_mut(1) {
    ///     *elem = 7;
    /// }
    ///
    /// assert_eq!(buf[1], 7);
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        let front_len = self.front.len();
        if index < front_len {
            self.front.get_mut(front_len - 1 - index)
        } else {
            self.back.get_mut(index - front_len)
        }
    }

    /// Provides a reference to the front element, or `None` if the `Vecque` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut d = Vecque::new();
    /// assert_eq!(d.front(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        self.get(0)
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// `Vecque` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut d = Vecque::new();
    /// assert_eq!(d.front_mut(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.front_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.front(), Some(&9));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.get_mut(0)
    }

    /// Provides a reference to the back element, or `None` if the `Vecque` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut d = Vecque::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.back(), Some(&2));
    /// ```
    pub fn back(&self) -> Option<&T> {
        self.get(self.len().wrapping_sub(1))
    }

    /// Provides a mutable reference to the back element, or `None` if the
    /// `Vecque` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut d = Vecque::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.back_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.back(), Some(&9));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.get_mut(self.len().wrapping_sub(1))
    }

    /// Removes the first element and returns it, or `None` if the `Vecque` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut d = Vecque::new();
    /// d.push_back(1);
    /// d.push_back(2);
    ///
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        if self.front.is_empty() {
            self.back.reverse();
            swap(&mut self.back, &mut self.front);
        }
        self.front.pop()
    }

    /// Removes the last element from the `Vecque` and returns it, or `None` if
    /// it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut buf = Vecque::new();
    /// assert_eq!(buf.pop_back(), None);
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(buf.pop_back(), Some(3));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        if self.back.is_empty() {
            self.front.reverse();
            swap(&mut self.back, &mut self.front);
        }
        self.back.pop()
    }

    /// Prepends an element to the `Vecque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut d = Vecque::new();
    /// d.push_front(1).expect("oom");
    /// d.push_front(2).expect("oom");
    /// assert_eq!(d.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, value: T) -> Result<()> {
        vec_push(&mut self.front, value)
    }

    /// Appends an element to the back of the `Vecque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut buf = Vecque::new();
    /// buf.push_back(1).expect("oom");
    /// buf.push_back(3).expect("oom");
    /// assert_eq!(3, *buf.back().unwrap());
    /// ```
    pub fn push_back(&mut self, value: T) -> Result<()> {
        vec_push(&mut self.back, value)
    }

    /// Returns the number of elements in the `Vecque`.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut v = Vecque::new();
    /// assert_eq!(v.len(), 0);
    /// v.push_back(1);
    /// assert_eq!(v.len(), 1);
    /// ```   
    pub fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }

    /// Returns `true` if the `Vecque` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut v = Vecque::new();
    /// assert!(v.is_empty());
    /// v.push_front(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Shrinks the capacity of the `Vecque` as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// `Vecque` that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use kcore::Vecque;
    ///
    /// let mut buf = Vecque::with_capacity(15);
    /// buf.push_front(1);
    /// assert_eq!(buf.capacity(), 15);
    /// buf.shrink_to_fit().expect("oom");
    /// assert!(buf.capacity() >= 1);
    /// ```
    pub fn shrink_to_fit(&mut self) -> Result<()> {
        vec_shrink_to_fit(&mut self.back)?;
        vec_shrink_to_fit(&mut self.front)
    }
}
