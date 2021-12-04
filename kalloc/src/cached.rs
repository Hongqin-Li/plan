//! Cached multi buddy system
//!
//! It simply caches the pages used by the underlying buddy system. Assuming `to_order` is
//! O(1), the allocation is amortized O(logN), worst-case O(N) and O(1) in most cases,
//! which is much faster than O(logN). Deallocation is always O(1) since pages are cached
//! in a freelist instead of returning to the buddy system.
//!
//! ## When to use
//!
//! If the system requires strict bound on running time (e.g. real-time system),
//! use the buddy allocator. Otherwise, use this cached one to achieve faster
//! performance in most scenarios.

use crate::{buddy::MultiBuddySystem, to_order};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
};
use spin::Mutex;
use typenum::{PowerOfTwo, Unsigned};

struct Freelist {
    next: *mut Freelist,
}

impl Freelist {
    pub const fn new() -> Self {
        Self { next: null_mut() }
    }
}

/// Allocator with cached pages.
pub struct Cached<T> {
    inner: T,
    freelist: [Freelist; 32],
}

impl<P: Unsigned + PowerOfTwo + 'static> Cached<MultiBuddySystem<P>> {
    pub(crate) const fn new() -> Self {
        const LS: Freelist = Freelist::new();
        Self {
            inner: MultiBuddySystem::new(),
            freelist: [LS; 32],
        }
    }

    pub(crate) unsafe fn add_zone(&mut self, begin: usize, end: usize) {
        self.inner.add_zone(begin, end);
    }

    /// Allocate memory according to layout.
    ///
    /// Due to the cache layer, this operation is amotized O(logN) and maybe O(N)
    /// in worst case. But it's usually O(1) and much faster than O(logN).
    pub unsafe fn alloc(&mut self, layout: core::alloc::Layout) -> *mut u8 {
        let order = to_order(P::to_usize(), &layout);
        if let Some(head) = self.freelist.get_mut(order) {
            let p = head.next;
            if !p.is_null() {
                head.next = (*p).next;
                return p as *mut u8;
            }
        }
        // Not cached.
        let p = self.inner.alloc1(order);
        if !p.is_null() {
            return p;
        }
        // Need to free cached pages.
        for (d, head) in self.freelist.iter_mut().enumerate().rev() {
            let mut p = head.next;
            while !p.is_null() {
                head.next = (*p).next;
                if self.inner.free(p as *mut u8, d) >= order {
                    return self.inner.alloc1(order);
                }
                p = head.next;
            }
        }
        p
    }

    /// Free the memory pointed by ptr with specified layout.
    ///
    /// This operation is O(1).
    pub unsafe fn dealloc(&mut self, ptr: *mut u8, layout: core::alloc::Layout) {
        let order = to_order(P::to_usize(), &layout);
        if let Some(head) = self.freelist.get_mut(order) {
            let ptr = ptr as *mut Freelist;
            (*ptr).next = head.next;
            head.next = ptr;
        } else {
            self.inner.free(ptr, order);
        }
    }
}

/// A thread-safe allocator with multiple buddy systems.
pub struct Allocator<P> {
    inner: Mutex<Cached<MultiBuddySystem<P>>>,
}

impl<P: Unsigned + PowerOfTwo + 'static> Allocator<P> {
    /// Create a allocator with empty memory.
    pub const fn new() -> Self {
        Self {
            inner: Mutex::new(Cached::<MultiBuddySystem<P>>::new()),
        }
    }

    /// Add free memory [begin, end) to this allocator.
    pub unsafe fn add_zone(&mut self, begin: usize, end: usize) {
        self.inner.lock().add_zone(begin, end);
    }
}

unsafe impl<P: Unsigned + PowerOfTwo + 'static> GlobalAlloc for Allocator<P> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.inner.lock().alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.inner.lock().dealloc(ptr, layout);
    }
}

#[cfg(test)]
mod tests {
    use super::super::buddy::tests::{test1, PGSIZE};
    use super::*;
    use rand::Rng;
    use std::vec::Vec;
    use typenum::Unsigned;

    #[test]
    fn test_allocator() {
        let n: usize = PGSIZE::to_usize() * 1000;
        let mut v: Vec<u8> = Vec::new();
        v.reserve(n);
        let mut rng = rand::thread_rng();
        for _ in 0..n {
            v.push(rng.gen_range(0..0xFF));
        }
        let ptr = v.as_mut_ptr() as usize;
        unsafe {
            let mut a: Allocator<PGSIZE> = Allocator::new();
            a.add_zone(ptr, ptr + n);
            test1(&a);
        }
    }
}
