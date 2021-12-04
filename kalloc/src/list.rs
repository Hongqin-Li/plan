//! A doubly-linked list with owned nodes ported from [alloc::collections::List].
//!
//! The `List` allows pushing and popping elements at either end
//! in constant time.
//!
//! NOTE: It is almost always better to use [`Vec`] or [`Vecque`] because
//! array-based containers are generally faster,
//! more memory efficient, and make better use of CPU cache.
//!
//! [`Vec`]: alloc::vec::Vec
//! [`Vecque`]: super::vecque::Vecque

use alloc::boxed::Box;
use core::{
    alloc::AllocError,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    marker::PhantomData,
    mem,
    ptr::NonNull,
};

/// An intermediate trait for specialization of `Extend`.
trait SpecExtend<I: IntoIterator> {
    /// Extends `self` with the contents of the given iterator.
    fn spec_extend(&mut self, iter: I);
}

// #[cfg(test)]
// mod tests;

/// A doubly-linked list with owned nodes.
///
/// The `List` allows pushing and popping elements at either end
/// in constant time.
///
/// NOTE: It is almost always better to use `Vec` or `Vecque` because
/// array-based containers are generally faster,
/// more memory efficient, and make better use of CPU cache.
pub struct List<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Box<Node<T>>>,
}

struct Node<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    /// The data of this node.
    pub element: T,
}

/// An iterator over the elements of a `List`.
///
/// This `struct` is created by [`List::iter()`]. See its
/// documentation for more.
pub struct Iter<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a Node<T>>,
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").field(&self.len).finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter { ..*self }
    }
}

/// A mutable iterator over the elements of a `List`.
///
/// This `struct` is created by [`List::iter_mut()`]. See its
/// documentation for more.
pub struct IterMut<'a, T: 'a> {
    // We do *not* exclusively own the entire list here, references to node's `element`
    // have been handed out by the iterator! So be careful when using this; the methods
    // called must be aware that there can be aliasing pointers to `element`.
    list: &'a mut List<T>,
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
}

impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IterMut")
            .field(&self.list)
            .field(&self.len)
            .finish()
    }
}

/// An owning iterator over the elements of a `List`.
///
/// This `struct` is created by the [`into_iter`] method on [`List`]
/// (provided by the `IntoIterator` trait). See its documentation for more.
///
/// [`into_iter`]: List::into_iter
pub struct IntoIter<T> {
    list: List<T>,
}

impl<T: fmt::Debug> fmt::Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.list).finish()
    }
}

impl<T> Node<T> {
    fn new(element: T) -> Self {
        Node {
            next: None,
            prev: None,
            element,
        }
    }

    fn into_element(self: Box<Self>) -> T {
        self.element
    }
}

// private methods
impl<T> List<T> {
    /// Adds the given node to the front of the list.
    #[inline]
    fn push_front_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = self.head;
            node.prev = None;
            let node = Some(Box::leak(node).into());

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the front of the list.
    #[inline]
    fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Adds the given node to the back of the list.
    #[inline]
    fn push_back_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = None;
            node.prev = self.tail;
            let node = Some(Box::leak(node).into());

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the back of the list.
    #[inline]
    fn pop_back_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.tail.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.tail = node.prev;

            match self.tail {
                None => self.head = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    ///
    /// This method takes care not to create mutable references to `element`, to
    /// maintain validity of aliasing pointers.
    #[inline]
    unsafe fn unlink_node(&mut self, mut node: NonNull<Node<T>>) {
        let node = node.as_mut(); // this one is ours now, we can create an &mut.

        // Not creating new mutable (unique!) references overlapping `element`.
        match node.prev {
            Some(prev) => (*prev.as_ptr()).next = node.next,
            // this node is the head node
            None => self.head = node.next,
        };

        match node.next {
            Some(next) => (*next.as_ptr()).prev = node.prev,
            // this node is the tail node
            None => self.tail = node.prev,
        };

        self.len -= 1;
    }

    /// Splices a series of nodes between two existing nodes.
    ///
    /// Warning: this will not check that the provided node belongs to the two existing lists.
    #[inline]
    unsafe fn splice_nodes(
        &mut self,
        existing_prev: Option<NonNull<Node<T>>>,
        existing_next: Option<NonNull<Node<T>>>,
        mut splice_start: NonNull<Node<T>>,
        mut splice_end: NonNull<Node<T>>,
        splice_length: usize,
    ) {
        // This method takes care not to create multiple mutable references to whole nodes at the same time,
        // to maintain validity of aliasing pointers into `element`.
        if let Some(mut existing_prev) = existing_prev {
            existing_prev.as_mut().next = Some(splice_start);
        } else {
            self.head = Some(splice_start);
        }
        if let Some(mut existing_next) = existing_next {
            existing_next.as_mut().prev = Some(splice_end);
        } else {
            self.tail = Some(splice_end);
        }
        splice_start.as_mut().prev = existing_prev;
        splice_end.as_mut().next = existing_next;

        self.len += splice_length;
    }

    /// Detaches all nodes from a linked list as a series of nodes.
    #[inline]
    fn detach_all_nodes(mut self) -> Option<(NonNull<Node<T>>, NonNull<Node<T>>, usize)> {
        let head = self.head.take();
        let tail = self.tail.take();
        let len = mem::replace(&mut self.len, 0);
        if let Some(head) = head {
            let tail = tail.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
            Some((head, tail, len))
        } else {
            None
        }
    }

    #[inline]
    unsafe fn split_off_before_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self {
        // The split node is the new head node of the second part
        if let Some(mut split_node) = split_node {
            let first_part_head;
            let first_part_tail;
            first_part_tail = split_node.as_mut().prev.take();
            if let Some(mut tail) = first_part_tail {
                tail.as_mut().next = None;
                first_part_head = self.head;
            } else {
                first_part_head = None;
            }

            let first_part = List {
                head: first_part_head,
                tail: first_part_tail,
                len: at,
                marker: PhantomData,
            };

            // Fix the head ptr of the second part
            self.head = Some(split_node);
            self.len = self.len - at;

            first_part
        } else {
            mem::replace(self, List::new())
        }
    }

    #[inline]
    unsafe fn split_off_after_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self {
        // The split node is the new tail node of the first part and owns
        // the head of the second part.
        if let Some(mut split_node) = split_node {
            let second_part_head;
            let second_part_tail;
            second_part_head = split_node.as_mut().next.take();
            if let Some(mut head) = second_part_head {
                head.as_mut().prev = None;
                second_part_tail = self.tail;
            } else {
                second_part_tail = None;
            }

            let second_part = List {
                head: second_part_head,
                tail: second_part_tail,
                len: self.len - at,
                marker: PhantomData,
            };

            // Fix the tail ptr of the first part
            self.tail = Some(split_node);
            self.len = at;

            second_part
        } else {
            mem::replace(self, List::new())
        }
    }
}

impl<T> Default for List<T> {
    /// Creates an empty `List<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> List<T> {
    /// Creates an empty `List`.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let list: List<u32> = List::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        List {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    /// Moves all elements from `other` to the end of the list.
    ///
    /// This reuses all the nodes from `other` and moves them into `self`. After
    /// this operation, `other` becomes empty.
    ///
    /// This operation should compute in *O*(1) time and *O*(1) memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut list1 = List::new();
    /// list1.push_back('a');
    ///
    /// let mut list2 = List::new();
    /// list2.push_back('b');
    /// list2.push_back('c');
    ///
    /// list1.append(&mut list2);
    ///
    /// let mut iter = list1.iter();
    /// assert_eq!(iter.next(), Some(&'a'));
    /// assert_eq!(iter.next(), Some(&'b'));
    /// assert_eq!(iter.next(), Some(&'c'));
    /// assert!(iter.next().is_none());
    ///
    /// assert!(list2.is_empty());
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        match self.tail {
            None => mem::swap(self, other),
            Some(mut tail) => {
                // `as_mut` is okay here because we have exclusive access to the entirety
                // of both lists.
                if let Some(mut other_head) = other.head.take() {
                    unsafe {
                        tail.as_mut().next = Some(other_head);
                        other_head.as_mut().prev = Some(tail);
                    }

                    self.tail = other.tail.take();
                    self.len += mem::replace(&mut other.len, 0);
                }
            }
        }
    }

    /// Moves all elements from `other` to the begin of the list.
    pub fn prepend(&mut self, other: &mut Self) {
        match self.head {
            None => mem::swap(self, other),
            Some(mut head) => {
                // `as_mut` is okay here because we have exclusive access to the entirety
                // of both lists.
                if let Some(mut other_tail) = other.tail.take() {
                    unsafe {
                        head.as_mut().prev = Some(other_tail);
                        other_tail.as_mut().next = Some(head);
                    }

                    self.head = other.head.take();
                    self.len += mem::replace(&mut other.len, 0);
                }
            }
        }
    }

    /// Provides a forward iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut list: List<u32> = List::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    /// Provides a forward iterator with mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut list: List<u32> = List::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// for element in list.iter_mut() {
    ///     *element += 10;
    /// }
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next(), Some(&11));
    /// assert_eq!(iter.next(), Some(&12));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            list: self,
        }
    }

    /// Provides a cursor at the front element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    pub fn cursor_front(&self) -> Cursor<'_, T> {
        Cursor {
            index: 0,
            current: self.head,
            list: self,
        }
    }

    /// Provides a cursor with editing operations at the front element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            index: 0,
            current: self.head,
            list: self,
        }
    }

    /// Provides a cursor at the back element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    pub fn cursor_back(&self) -> Cursor<'_, T> {
        Cursor {
            index: self.len.checked_sub(1).unwrap_or(0),
            current: self.tail,
            list: self,
        }
    }

    /// Provides a cursor with editing operations at the back element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            index: self.len.checked_sub(1).unwrap_or(0),
            current: self.tail,
            list: self,
        }
    }

    /// Returns `true` if the `List` is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    /// assert!(dl.is_empty());
    ///
    /// dl.push_front("foo");
    /// assert!(!dl.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Returns the length of the `List`.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    ///
    /// dl.push_front(2);
    /// assert_eq!(dl.len(), 1);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.len(), 2);
    ///
    /// dl.push_back(3);
    /// assert_eq!(dl.len(), 3);
    /// ```
    #[doc(alias = "length")]
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Removes all elements from the `List`.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    ///
    /// dl.push_front(2);
    /// dl.push_front(1);
    /// assert_eq!(dl.len(), 2);
    /// assert_eq!(dl.front(), Some(&1));
    ///
    /// dl.clear();
    /// assert_eq!(dl.len(), 0);
    /// assert_eq!(dl.front(), None);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Returns `true` if the `List` contains an element equal to the
    /// given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut list: List<u32> = List::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// assert_eq!(list.contains(&0), true);
    /// assert_eq!(list.contains(&10), false);
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == x)
    }

    /// Provides a reference to the front element, or `None` if the list is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    /// assert_eq!(dl.front(), None);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.front(), Some(&1));
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        unsafe { self.head.as_ref().map(|node| &node.as_ref().element) }
    }

    /// Provides a mutable reference to the front element, or `None` if the list
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    /// assert_eq!(dl.front(), None);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.front(), Some(&1));
    ///
    /// match dl.front_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(dl.front(), Some(&5));
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        unsafe { self.head.as_mut().map(|node| &mut node.as_mut().element) }
    }

    /// Provides a reference to the back element, or `None` if the list is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    /// assert_eq!(dl.back(), None);
    ///
    /// dl.push_back(1);
    /// assert_eq!(dl.back(), Some(&1));
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        unsafe { self.tail.as_ref().map(|node| &node.as_ref().element) }
    }

    /// Provides a mutable reference to the back element, or `None` if the list
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    /// assert_eq!(dl.back(), None);
    ///
    /// dl.push_back(1);
    /// assert_eq!(dl.back(), Some(&1));
    ///
    /// match dl.back_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(dl.back(), Some(&5));
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        unsafe { self.tail.as_mut().map(|node| &mut node.as_mut().element) }
    }

    /// Adds an element first in the list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut dl = List::new();
    ///
    /// dl.push_front(2);
    /// assert_eq!(dl.front().unwrap(), &2);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.front().unwrap(), &1);
    /// ```
    pub fn push_front(&mut self, elt: T) -> Result<(), AllocError> {
        Ok(self.push_front_node(Box::try_new(Node::new(elt))?))
    }

    /// Removes the first element and returns it, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut d = List::new();
    /// assert_eq!(d.pop_front(), None);
    ///
    /// d.push_front(1);
    /// d.push_front(3);
    /// assert_eq!(d.pop_front(), Some(3));
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.pop_front_node().map(Node::into_element)
    }

    /// Appends an element to the back of a list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut d = List::new();
    /// d.push_back(1);
    /// d.push_back(3);
    /// assert_eq!(3, *d.back().unwrap());
    /// ```
    pub fn push_back(&mut self, elt: T) -> Result<(), AllocError> {
        Ok(self.push_back_node(Box::try_new(Node::new(elt))?))
    }

    /// Removes the last element from a list and returns it, or `None` if
    /// it is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut d = List::new();
    /// assert_eq!(d.pop_back(), None);
    /// d.push_back(1);
    /// d.push_back(3);
    /// assert_eq!(d.pop_back(), Some(3));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.pop_back_node().map(Node::into_element)
    }

    /// Splits the list into two at the given index. Returns everything after the given index,
    /// including the index.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use kalloc::list::List;
    ///
    /// let mut d = List::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// let mut split = d.split_off(2);
    ///
    /// assert_eq!(split.pop_front(), Some(1));
    /// assert_eq!(split.pop_front(), None);
    /// ```
    pub fn split_off(&mut self, at: usize) -> List<T> {
        let len = self.len();
        assert!(at <= len, "Cannot split off at a nonexistent index");
        if at == 0 {
            return mem::take(self);
        } else if at == len {
            return Self::new();
        }

        // Below, we iterate towards the `i-1`th node, either from the start or the end,
        // depending on which would be faster.
        let split_node = if at - 1 <= len - 1 - (at - 1) {
            let mut iter = self.iter_mut();
            // instead of skipping using .skip() (which creates a new struct),
            // we skip manually so we can access the head field without
            // depending on implementation details of Skip
            for _ in 0..at - 1 {
                iter.next();
            }
            iter.head
        } else {
            // better off starting from the end
            let mut iter = self.iter_mut();
            for _ in 0..len - 1 - (at - 1) {
                iter.next_back();
            }
            iter.tail
        };
        unsafe { self.split_off_after_node(split_node, at) }
    }

    /// Removes the element at the given index and returns it.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Panics
    /// Panics if at >= len
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(linked_list_remove)]
    /// use kalloc::list::List;
    ///
    /// let mut d = List::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// assert_eq!(d.remove(1), 2);
    /// assert_eq!(d.remove(0), 3);
    /// assert_eq!(d.remove(0), 1);
    /// ```
    pub fn remove(&mut self, at: usize) -> T {
        let len = self.len();
        assert!(
            at < len,
            "Cannot remove at an index outside of the list bounds"
        );

        // Below, we iterate towards the node at the given index, either from
        // the start or the end, depending on which would be faster.
        let offset_from_end = len - at - 1;
        if at <= offset_from_end {
            let mut cursor = self.cursor_front_mut();
            for _ in 0..at {
                cursor.move_next();
            }
            cursor.remove_current().unwrap()
        } else {
            let mut cursor = self.cursor_back_mut();
            for _ in 0..offset_from_end {
                cursor.move_prev();
            }
            cursor.remove_current().unwrap()
        }
    }
}

unsafe impl<#[may_dangle] T> Drop for List<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut List<T>);

        impl<'a, T> Drop for DropGuard<'a, T> {
            fn drop(&mut self) {
                // Continue the same loop we do below. This only runs when a destructor has
                // panicked. If another one panics this will abort.
                while self.0.pop_front_node().is_some() {}
            }
        }

        while let Some(node) = self.pop_front_node() {
            let guard = DropGuard(self);
            drop(node);
            mem::forget(guard);
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                &node.element
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a T> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                &node.element
            })
        }
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> FusedIterator for Iter<'_, T> {}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                &mut node.element
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a mut T> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                &mut node.element
            })
        }
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}

impl<T> FusedIterator for IterMut<'_, T> {}

/// A cursor over a `List`.
///
/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth.
///
/// Cursors always rest between two elements in the list, and index in a logically circular way.
/// To accommodate this, there is a "ghost" non-element that yields `None` between the head and
/// tail of the list.
///
/// When created, cursors start at the front of the list, or the "ghost" non-element if the list is empty.
pub struct Cursor<'a, T: 'a> {
    index: usize,
    current: Option<NonNull<Node<T>>>,
    list: &'a List<T>,
}

impl<T> Clone for Cursor<'_, T> {
    fn clone(&self) -> Self {
        let Cursor {
            index,
            current,
            list,
        } = *self;
        Cursor {
            index,
            current,
            list,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Cursor<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Cursor")
            .field(&self.list)
            .field(&self.index())
            .finish()
    }
}

/// A cursor over a `List` with editing operations.
///
/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth, and can
/// safely mutate the list during iteration. This is because the lifetime of its yielded
/// references is tied to its own lifetime, instead of just the underlying list. This means
/// cursors cannot yield multiple elements at once.
///
/// Cursors always rest between two elements in the list, and index in a logically circular way.
/// To accommodate this, there is a "ghost" non-element that yields `None` between the head and
/// tail of the list.
pub struct CursorMut<'a, T: 'a> {
    index: usize,
    current: Option<NonNull<Node<T>>>,
    list: &'a mut List<T>,
}

impl<T: fmt::Debug> fmt::Debug for CursorMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CursorMut")
            .field(&self.list)
            .field(&self.index())
            .finish()
    }
}

impl<'a, T> Cursor<'a, T> {
    /// Returns the cursor position index within the `List`.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    pub fn index(&self) -> Option<usize> {
        let _ = self.current?;
        Some(self.index)
    }

    /// Moves the cursor to the next element of the `List`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the first element of the `List`. If it is pointing to the last
    /// element of the `List` then this will move it to the "ghost" non-element.
    pub fn move_next(&mut self) {
        match self.current.take() {
            // We had no current element; the cursor was sitting at the start position
            // Next element should be the head of the list
            None => {
                self.current = self.list.head;
                self.index = 0;
            }
            // We had a previous element, so let's go to its next
            Some(current) => unsafe {
                self.current = current.as_ref().next;
                self.index += 1;
            },
        }
    }

    /// Moves the cursor to the previous element of the `List`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the last element of the `List`. If it is pointing to the first
    /// element of the `List` then this will move it to the "ghost" non-element.
    pub fn move_prev(&mut self) {
        match self.current.take() {
            // No current. We're at the start of the list. Yield None and jump to the end.
            None => {
                self.current = self.list.tail;
                self.index = self.list.len().checked_sub(1).unwrap_or(0);
            }
            // Have a prev. Yield it and go to the previous element.
            Some(current) => unsafe {
                self.current = current.as_ref().prev;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.list.len());
            },
        }
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    pub fn current(&self) -> Option<&'a T> {
        unsafe { self.current.map(|current| &(*current.as_ptr()).element) }
    }

    /// Returns a reference to the next element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the first element of the `List`. If it is pointing to the last
    /// element of the `List` then this returns `None`.
    pub fn peek_next(&self) -> Option<&'a T> {
        unsafe {
            let next = match self.current {
                None => self.list.head,
                Some(current) => current.as_ref().next,
            };
            next.map(|next| &(*next.as_ptr()).element)
        }
    }

    /// Returns a reference to the previous element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the last element of the `List`. If it is pointing to the first
    /// element of the `List` then this returns `None`.
    pub fn peek_prev(&self) -> Option<&'a T> {
        unsafe {
            let prev = match self.current {
                None => self.list.tail,
                Some(current) => current.as_ref().prev,
            };
            prev.map(|prev| &(*prev.as_ptr()).element)
        }
    }
}

impl<'a, T> CursorMut<'a, T> {
    /// Returns the cursor position index within the `List`.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    pub fn index(&self) -> Option<usize> {
        let _ = self.current?;
        Some(self.index)
    }

    /// Moves the cursor to the next element of the `List`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the first element of the `List`. If it is pointing to the last
    /// element of the `List` then this will move it to the "ghost" non-element.
    pub fn move_next(&mut self) {
        match self.current.take() {
            // We had no current element; the cursor was sitting at the start position
            // Next element should be the head of the list
            None => {
                self.current = self.list.head;
                self.index = 0;
            }
            // We had a previous element, so let's go to its next
            Some(current) => unsafe {
                self.current = current.as_ref().next;
                self.index += 1;
            },
        }
    }

    /// Moves the cursor to the previous element of the `List`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the last element of the `List`. If it is pointing to the first
    /// element of the `List` then this will move it to the "ghost" non-element.
    pub fn move_prev(&mut self) {
        match self.current.take() {
            // No current. We're at the start of the list. Yield None and jump to the end.
            None => {
                self.current = self.list.tail;
                self.index = self.list.len().checked_sub(1).unwrap_or(0);
            }
            // Have a prev. Yield it and go to the previous element.
            Some(current) => unsafe {
                self.current = current.as_ref().prev;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.list.len());
            },
        }
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe { self.current.map(|current| &mut (*current.as_ptr()).element) }
    }

    /// Returns a reference to the next element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the first element of the `List`. If it is pointing to the last
    /// element of the `List` then this returns `None`.
    pub fn peek_next(&mut self) -> Option<&mut T> {
        unsafe {
            let next = match self.current {
                None => self.list.head,
                Some(current) => current.as_ref().next,
            };
            next.map(|next| &mut (*next.as_ptr()).element)
        }
    }

    /// Returns a reference to the previous element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the last element of the `List`. If it is pointing to the first
    /// element of the `List` then this returns `None`.
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        unsafe {
            let prev = match self.current {
                None => self.list.tail,
                Some(current) => current.as_ref().prev,
            };
            prev.map(|prev| &mut (*prev.as_ptr()).element)
        }
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The lifetime of the returned `Cursor` is bound to that of the
    /// `CursorMut`, which means it cannot outlive the `CursorMut` and that the
    /// `CursorMut` is frozen for the lifetime of the `Cursor`.
    pub fn as_cursor(&self) -> Cursor<'_, T> {
        Cursor {
            list: self.list,
            current: self.current,
            index: self.index,
        }
    }
}

// Now the list editing operations

impl<'a, T> CursorMut<'a, T> {
    /// Inserts a new element into the `List` after the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the front of the `List`.
    pub fn insert_after(&mut self, item: T) -> Result<(), AllocError> {
        unsafe {
            let spliced_node = Box::leak(Box::try_new(Node::new(item))?).into();
            let node_next = match self.current {
                None => self.list.head,
                Some(node) => node.as_ref().next,
            };
            self.list
                .splice_nodes(self.current, node_next, spliced_node, spliced_node, 1);
            if self.current.is_none() {
                // The "ghost" non-element's index has changed.
                self.index = self.list.len;
            }
        }
        Ok(())
    }

    /// Inserts a new element into the `List` before the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the end of the `List`.
    pub fn insert_before(&mut self, item: T) -> Result<(), AllocError> {
        unsafe {
            let spliced_node = Box::leak(Box::try_new(Node::new(item))?).into();
            let node_prev = match self.current {
                None => self.list.tail,
                Some(node) => node.as_ref().prev,
            };
            self.list
                .splice_nodes(node_prev, self.current, spliced_node, spliced_node, 1);
            self.index += 1;
        }
        Ok(())
    }

    /// Removes the current element from the `List`.
    ///
    /// The element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `List`.
    ///
    /// If the cursor is currently pointing to the "ghost" non-element then no element
    /// is removed and `None` is returned.
    pub fn remove_current(&mut self) -> Option<T> {
        let unlinked_node = self.current?;
        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);
            let unlinked_node = Box::from_raw(unlinked_node.as_ptr());
            Some(unlinked_node.element)
        }
    }

    /// Removes the current element from the `List` without deallocating the list node.
    ///
    /// The node that was removed is returned as a new `List` containing only this node.
    /// The cursor is moved to point to the next element in the current `List`.
    ///
    /// If the cursor is currently pointing to the "ghost" non-element then no element
    /// is removed and `None` is returned.
    pub fn remove_current_as_list(&mut self) -> Option<List<T>> {
        let mut unlinked_node = self.current?;
        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);

            unlinked_node.as_mut().prev = None;
            unlinked_node.as_mut().next = None;
            Some(List {
                head: Some(unlinked_node),
                tail: Some(unlinked_node),
                len: 1,
                marker: PhantomData,
            })
        }
    }

    /// Inserts the elements from the given `List` after the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new elements are
    /// inserted at the start of the `List`.
    pub fn splice_after(&mut self, list: List<T>) {
        unsafe {
            let (splice_head, splice_tail, splice_len) = match list.detach_all_nodes() {
                Some(parts) => parts,
                _ => return,
            };
            let node_next = match self.current {
                None => self.list.head,
                Some(node) => node.as_ref().next,
            };
            self.list.splice_nodes(
                self.current,
                node_next,
                splice_head,
                splice_tail,
                splice_len,
            );
            if self.current.is_none() {
                // The "ghost" non-element's index has changed.
                self.index = self.list.len;
            }
        }
    }

    /// Inserts the elements from the given `List` before the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new elements are
    /// inserted at the end of the `List`.
    pub fn splice_before(&mut self, list: List<T>) {
        unsafe {
            let (splice_head, splice_tail, splice_len) = match list.detach_all_nodes() {
                Some(parts) => parts,
                _ => return,
            };
            let node_prev = match self.current {
                None => self.list.tail,
                Some(node) => node.as_ref().prev,
            };
            self.list.splice_nodes(
                node_prev,
                self.current,
                splice_head,
                splice_tail,
                splice_len,
            );
            self.index += splice_len;
        }
    }

    /// Splits the list into two after the current element. This will return a
    /// new list consisting of everything after the cursor, with the original
    /// list retaining everything before.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the entire contents
    /// of the `List` are moved.
    pub fn split_after(&mut self) -> List<T> {
        let split_off_idx = if self.index == self.list.len {
            0
        } else {
            self.index + 1
        };
        if self.index == self.list.len {
            // The "ghost" non-element's index has changed to 0.
            self.index = 0;
        }
        unsafe { self.list.split_off_after_node(self.current, split_off_idx) }
    }

    /// Splits the list into two before the current element. This will return a
    /// new list consisting of everything before the cursor, with the original
    /// list retaining everything after.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the entire contents
    /// of the `List` are moved.
    pub fn split_before(&mut self) -> List<T> {
        let split_off_idx = self.index;
        self.index = 0;
        unsafe { self.list.split_off_before_node(self.current, split_off_idx) }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.list.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.list.pop_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Consumes the list into an iterator yielding elements by value.
    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { list: self }
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut List<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.iter().ne(other)
    }
}

impl<T: Eq> Eq for List<T> {}

impl<T: PartialOrd> PartialOrd for List<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for List<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: Hash> Hash for List<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for elt in self {
            elt.hash(state);
        }
    }
}

// Ensure that `List` and its read-only iterators are covariant in their type parameters.
#[allow(dead_code)]
fn assert_covariance() {
    fn a<'a>(x: List<&'static str>) -> List<&'a str> {
        x
    }
    fn b<'i, 'a>(x: Iter<'i, &'static str>) -> Iter<'i, &'a str> {
        x
    }
    fn c<'a>(x: IntoIter<&'static str>) -> IntoIter<&'a str> {
        x
    }
}

unsafe impl<T: Send> Send for List<T> {}

unsafe impl<T: Sync> Sync for List<T> {}

unsafe impl<T: Sync> Send for Iter<'_, T> {}

unsafe impl<T: Sync> Sync for Iter<'_, T> {}

unsafe impl<T: Send> Send for IterMut<'_, T> {}

unsafe impl<T: Sync> Sync for IterMut<'_, T> {}

unsafe impl<T: Sync> Send for Cursor<'_, T> {}

unsafe impl<T: Sync> Sync for Cursor<'_, T> {}

unsafe impl<T: Send> Send for CursorMut<'_, T> {}

unsafe impl<T: Sync> Sync for CursorMut<'_, T> {}
