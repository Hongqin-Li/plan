//! # Buddy system allocator
//!
//! Buddy system is a memory allocation algorithm, designed to reduce
//! external fragmentation but can still achieve high performance.
//! It has been widely used in modern operating systems such as Linux for
//! dynamic allocation and deallocation of memory chunks.
//!
//! ## Complexity
//!
//! Allocation and deallocation are both guaranteed to finish within O(log n),
//! where n is the size of memory handled by this buddy system.
//!
use core::{
    alloc::GlobalAlloc,
    cmp::{max, min},
    mem::size_of,
    ptr::null_mut,
};
use core::{alloc::Layout, mem, ptr};

use synctools::mcs::MCSLock;

use crate::list::List;

/// Round down to the nearest multiple of n.
#[inline]
fn round_down(x: usize, n: usize) -> usize {
    x - (x % n)
}
/// Round up to the nearest multiple of n.
#[inline]
fn round_up(x: usize, n: usize) -> usize {
    round_down(x + n - 1, n)
}
#[inline]
fn left(i: usize) -> usize {
    i * 2
}
#[inline]
fn right(i: usize) -> usize {
    left(i) + 1
}
#[inline]
fn father(i: usize) -> usize {
    i / 2
}
#[inline]
fn buddy_idx(i: usize) -> usize {
    i ^ 1
}

/// Buddy System Allocator Structure.
pub struct BuddySystem {
    /// Should be power of 2.
    page_size: usize,

    /// Should be less than 32.
    max_order: usize,

    /// Should be equal to 2^max_order.
    npages: usize,

    bitmap_begin: usize,

    page_begin: usize,

    page_end: usize,
    /// Maximum order is 31, only support area of 2^31 pages.
    freelist: [List; 32],

    /// Pointer to next buddy system, used by MultiBuddySystem.
    next: *mut BuddySystem,
}

impl BuddySystem {
    #[inline]
    unsafe fn set_bit(&mut self, i: usize) {
        let p = self.bitmap_begin + i / 8;
        debug_assert!(self.bitmap_begin <= p && p < self.page_begin);
        *(p as *mut u8) |= 1 << (i % 8);
    }

    #[inline]
    unsafe fn unset_bit(&mut self, i: usize) {
        let p = self.bitmap_begin + i / 8;
        debug_assert!(self.bitmap_begin <= p && p < self.page_begin);
        *(p as *mut u8) &= !(1 << (i % 8));
    }

    #[inline]
    unsafe fn get_bit(&self, i: usize) -> bool {
        let p = self.bitmap_begin + i / 8;
        debug_assert!(self.bitmap_begin <= p && p < self.page_begin);
        let b = *(p as *mut u8);
        if ((b >> (i % 8)) & 1) == 0 {
            false
        } else {
            true
        }
    }

    #[inline]
    fn to_order(&self, layout: &Layout) -> usize {
        debug_assert!(self.page_size.is_power_of_two());
        debug_assert!(layout.align().is_power_of_two());
        let sz = max(layout.size().next_power_of_two(), layout.align()) / self.page_size;
        sz.trailing_zeros() as usize
    }

    #[inline]
    fn bitmap_idx(&self, p: usize, order: usize) -> usize {
        (1 << (self.max_order - order)) + (((p - self.page_begin) / self.page_size) >> order)
    }

    /// Construct a buddy system allocator at memory [begin, end) with specific page size.
    ///
    /// Notice that it guarantees safety only if the access to [begin, end) is safe
    /// and `self` is a static variable.
    pub unsafe fn build(
        page_size: usize,
        mut begin: usize,
        end: usize,
    ) -> Result<&'static mut Self, ()> {
        assert_eq!(page_size.is_power_of_two(), true);
        assert!(page_size >= mem::size_of::<List>());
        let b = &mut (*(begin as *mut Self));
        begin += size_of::<Self>();
        if begin >= end {
            return Err(());
        }
        b.max_order = b.freelist.len();
        b.page_size = page_size;
        b.bitmap_begin = begin;
        b.next = ptr::null_mut();

        for i in 0..b.freelist.len() {
            let n: usize = 1 << i;
            let bitmap_end = begin + round_up(2 * n, 8) / 8;
            let page_begin = round_up(bitmap_end, page_size);
            let page_end = page_begin + n * page_size;
            if page_end <= end {
                b.max_order = i;
                b.npages = n;
                b.page_begin = page_begin;
                b.page_end = page_end;
            } else {
                break;
            }
        }
        if b.max_order >= b.freelist.len() {
            return Err(());
        }
        for head in b.freelist.iter_mut() {
            List::init(head);
        }
        List::push_front(&mut b.freelist[b.max_order], b.page_begin as *mut List);
        ptr::write_bytes(begin as *mut u8, 0, round_up(2 * b.npages, 8) / 8);
        Ok(b)
    }

    /// Allocate a range of memory specified by `layout`.
    pub unsafe fn alloc(&mut self, layout: Layout) -> *mut u8 {
        let order = self.to_order(&layout);
        let mut d = order;
        let mut p = ptr::null_mut();
        while d <= self.max_order {
            let head = &mut self.freelist[d] as *mut List;
            if !List::is_empty(head) {
                p = List::pop_front(head) as *mut u8;
                let mut i = self.bitmap_idx(p as usize, d);
                self.set_bit(i);
                while d > order {
                    d -= 1;
                    List::push_front(
                        &mut self.freelist[d],
                        (p as usize + (1 << d) * self.page_size) as *mut List,
                    );
                    i = left(i);
                    self.set_bit(i);
                }
                break;
            }
            d += 1;
        }
        p
    }

    /// Free the block of memory starting from `ptr` with specific `layout`.
    pub unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        debug_assert_eq!(ptr.is_null(), false);

        let mut order = self.to_order(&layout);
        let mut i = self.bitmap_idx(ptr as usize, order);
        let mut p = ptr as usize;
        while i != 1 && self.get_bit(buddy_idx(i)) == false {
            let bp = if i < buddy_idx(i) {
                p + (1 << order) * self.page_size
            } else {
                p - (1 << order) * self.page_size
            };
            List::drop(bp as *mut List);
            self.unset_bit(i);

            order += 1;
            i = father(i);
            p = min(p, bp);
        }
        self.unset_bit(i);
        List::push_front(&mut self.freelist[order], p as *mut List);
    }

    #[cfg(test)]
    pub unsafe fn check(&self) -> std::vec::Vec<(usize, usize)> {
        let mut allocated = vec![];
        let mut nalloc = 0;
        let mut nfree = 0;

        // BFS starting from root node 1.
        let mut que = std::collections::LinkedList::new();
        que.push_back((1, self.max_order, self.get_bit(1)));
        while let Some((u, d, tag)) = que.pop_front() {
            let l = left(u);
            let r = right(u);

            let npages = 1 << d;
            let addr =
                self.page_begin + npages * self.page_size * (u - (1 << (self.max_order - d)));

            // 1-nodes that don't have any 1-node child are allocated chunks.
            if tag == true && (d == 0 || (self.get_bit(l) == false && self.get_bit(r) == false)) {
                allocated.push((addr, npages * self.page_size));
                nalloc += npages;
            }

            // Root 0-nodes and 0-nodes whose father is 1-node and buddy is 1-node are free chunks.
            if tag == false
                && (u == 1
                    || (self.get_bit(father(u)) == true) && self.get_bit(buddy_idx(u)) == true)
            {
                let mut found = false;
                let head = &self.freelist[d] as *const List;
                let mut p = self.freelist[d].next as *const List;
                while p != head {
                    if p as usize == addr {
                        found = true;
                        break;
                    }
                    p = (*p).next;
                }
                assert_eq!(found, true);
                nfree += npages;
            }

            // Children of any 0-node must be also 0-nodes.
            if d != 0 && tag == false {
                assert_eq!(self.get_bit(l), false);
                assert_eq!(self.get_bit(r), false);
            }

            // BFS routine.
            if d != 0 {
                que.push_back((l, d - 1, self.get_bit(l)));
                que.push_back((r, d - 1, self.get_bit(r)));
            }
        }

        let mut nfreelist = 0;
        for i in 0..=self.max_order {
            let head = &self.freelist[i] as *const List;
            let mut p = self.freelist[i].next as *const List;
            let mut free_ptrs = vec![];
            while p != head {
                nfreelist += 1 << i;
                free_ptrs.push(self.bitmap_idx(p as usize, i));
                p = (*p).next;
            }
            // println!("freelist[{}] = {:?}", i, free_ptrs);
        }
        assert_eq!(nfree, nfreelist);
        assert_eq!(nalloc + nfree, self.npages);
        allocated
    }
}

struct MultiBuddySystem {
    head: *mut BuddySystem,
}

impl MultiBuddySystem {
    pub const fn new() -> Self {
        Self {
            head: ptr::null_mut(),
        }
    }
    pub unsafe fn add_zone(&mut self, page_size: usize, mut begin: usize, end: usize) {
        while let Ok(p) = BuddySystem::build(page_size, begin, end) {
            p.next = self.head;
            self.head = p;
            begin = p.page_end;
        }
    }
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut b = self.head;
        let mut p: *mut u8 = ptr::null_mut();
        while !b.is_null() && p.is_null() {
            p = (*b).alloc(layout);
            b = (*b).next;
        }
        p
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut b = self.head;
        while !b.is_null() {
            if (*b).page_begin <= ptr as usize && (ptr as usize) < (*b).page_end {
                (*b).dealloc(ptr, layout);
                break;
            }
            b = (*b).next;
        }
    }
}

/// A thread safe buddy system allocator.
pub struct Allocator {
    inner: MCSLock<MultiBuddySystem>,
}

impl Allocator {
    /// Create a allocator with empty memory.
    pub const fn new() -> Self {
        Self {
            inner: MCSLock::new(MultiBuddySystem::new()),
        }
    }

    /// Add free memory [begin, end) to this allocator.
    pub unsafe fn add_zone(&mut self, page_size: usize, begin: usize, end: usize) {
        self.inner.lock().add_zone(page_size, begin, end);
    }
}

unsafe impl GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.inner.lock().alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.inner.lock().dealloc(ptr, layout);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NBUF: usize = 4 * 1024;
    const PGSIZE: usize = 64; // Should be large enough to store the List structure.

    #[test]
    fn test_utils() {
        assert_eq!(left(1), 2);
        assert_eq!(left(2), 4);
        assert_eq!(left(3), 6);

        assert_eq!(right(1), 3);
        assert_eq!(right(2), 5);
        assert_eq!(right(3), 7);
    }

    #[test]
    fn test_buddy() {
        let buf: [u8; NBUF] = [0; NBUF];
        let mem_begin = buf.as_ptr() as usize;
        let mem_end = buf.as_ptr() as usize + NBUF;

        unsafe {
            let b = BuddySystem::build(PGSIZE, mem_begin, mem_end).unwrap();
            assert!(mem_begin < b.page_end && b.page_end <= mem_end);
            assert_eq!(b.check(), vec![]);
            let layouts = [
                Layout::from_size_align(4, PGSIZE).unwrap(),
                Layout::from_size_align(5, PGSIZE).unwrap(),
                Layout::from_size_align(2 * PGSIZE, PGSIZE).unwrap(),
                Layout::from_size_align(PGSIZE, PGSIZE).unwrap(),
            ];

            let mut to_dealloc = vec![];
            for x in layouts.iter() {
                let ptr = b.alloc(x.clone());
                assert_ne!(ptr, ptr::null_mut());
                ptr::write_bytes(ptr, 0xFF, x.size());

                to_dealloc.push((ptr, x.clone()));
                b.check();
            }

            loop {
                let ly = Layout::from_size_align(PGSIZE, PGSIZE).unwrap();
                let ptr = b.alloc(ly.clone());
                if ptr.is_null() {
                    break;
                }
                ptr::write_bytes(ptr, 0xFF, ly.size());
                to_dealloc.push((ptr, ly.clone()));
                b.check();
            }

            for (ptr, layout) in to_dealloc {
                b.dealloc(ptr, layout);
                b.check();
            }
        }
    }

    #[test]
    fn test_multi_buddy() {
        let buf: [u8; NBUF] = [0; NBUF];
        let mem_begin = buf.as_ptr() as usize;
        let mem_end = buf.as_ptr() as usize + NBUF;
        let mut b = MultiBuddySystem::new();

        unsafe {
            b.add_zone(PGSIZE, mem_begin, mem_end);

            let layouts = [
                Layout::from_size_align(4, PGSIZE).unwrap(),
                Layout::from_size_align(5, PGSIZE).unwrap(),
                Layout::from_size_align(2 * PGSIZE, PGSIZE).unwrap(),
                Layout::from_size_align(PGSIZE, PGSIZE).unwrap(),
            ];

            let mut to_dealloc = vec![];
            for x in layouts.iter() {
                let ptr = b.alloc(x.clone());
                assert_ne!(ptr, ptr::null_mut());
                ptr::write_bytes(ptr, 0xFF, x.size());
                to_dealloc.push((ptr, x.clone()));
            }

            loop {
                let ly = Layout::from_size_align(PGSIZE, PGSIZE).unwrap();
                let ptr = b.alloc(ly.clone());
                if ptr.is_null() {
                    break;
                }
                ptr::write_bytes(ptr, 0xFF, ly.size());
                to_dealloc.push((ptr, ly.clone()));
            }

            for (ptr, layout) in to_dealloc {
                b.dealloc(ptr, layout);
            }
        }
    }
}
