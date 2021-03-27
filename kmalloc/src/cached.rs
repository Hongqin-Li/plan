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
use core::{
    alloc::{GlobalAlloc, Layout},
    ops::Mul,
    ptr::{self, null, null_mut},
};

use mcs::{Mutex, Slot};
use typenum::{PowerOfTwo, Unsigned};

use crate::{buddy::MultiBuddySystem, list::Freelist, to_order};

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
        let d = to_order(P::to_usize(), &layout);
        if let Some(head) = self.freelist.get_mut(d) {
            let p = head.next;
            if p.is_null() {
                let p = self.inner.alloc(layout);
                if p.is_null() {
                    // TODO: Try to free by pages.
                    p
                } else {
                    p
                }
            } else {
                head.next = (*p).next;
                p as *mut u8
            }
        } else {
            // No cached.
            self.inner.alloc(layout)
        }
    }

    /// Free the memory pointed by ptr with specified layout.
    ///
    /// This operation is O(1).
    pub unsafe fn dealloc(&mut self, ptr: *mut u8, layout: core::alloc::Layout) {
        let d = to_order(P::to_usize(), &layout);
        if let Some(head) = self.freelist.get_mut(d) {
            let ptr = ptr as *mut Freelist;
            (*ptr).next = head.next;
            head.next = ptr;
        } else {
            self.inner.dealloc(ptr, layout);
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
        let mut slot = Slot::new();
        {
            self.inner.lock(&mut slot).add_zone(begin, end);
        }
    }
}

unsafe impl<P: Unsigned + PowerOfTwo + 'static> GlobalAlloc for Allocator<P> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut slot = Slot::new();
        let p = { self.inner.lock(&mut slot).alloc(layout) };
        p
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut slot = Slot::new();
        {
            self.inner.lock(&mut slot).dealloc(ptr, layout);
        }
    }
}
