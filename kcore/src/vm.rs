//! Virtual memory tools.

use ::alloc::{alloc, sync::Arc, vec::Vec};
use core::ptr;
use core::ptr::NonNull;
use core::{alloc::Layout, marker::PhantomData, ops::Range};

use crate::utils::{arc_new, vec_push, Error};

/// Page table.
pub trait PageTable: Sized {
    /// Layout used to alloc and dealloc physical pages from global allocator.
    const PG_LAYOUT: Layout;

    /// Create a new page table.
    fn new() -> Result<Self, Error>;

    /// Map virtual address [va, va + len) to physical address [pa, pa + len).
    ///
    /// It is required to be atomic, i.e., undo the mapping if failed.
    /// Caller guarantees that pages in [va, va+len) are unmapped.
    fn map(&mut self, va: usize, pg: &Page<Self>, len: usize) -> Result<(), Error>;

    /// Unmap [va, va+len) in this page table.
    ///
    /// Caller guarantees that [va, va+len) has been mapped before unmapping them.
    fn unmap(&mut self, va: usize, len: usize);
}

/// Physical page.
pub struct Page<P: PageTable> {
    ptr: NonNull<u8>,
    phantom: PhantomData<P>,
}

impl<P: PageTable> Page<P> {
    fn new() -> Result<Self, Error> {
        let p = unsafe { alloc::alloc(P::PG_LAYOUT) };
        if let Some(ptr) = NonNull::new(p) {
            Ok(Self {
                ptr,
                phantom: PhantomData,
            })
        } else {
            Err(Error::OutOfMemory)
        }
    }
    /// Get virtual address of the page.
    pub fn va(&self) -> usize {
        self.ptr.as_ptr() as usize
    }
}

impl<P: PageTable> Drop for Page<P> {
    fn drop(&mut self) {
        unsafe { alloc::dealloc(self.ptr.as_ptr() as *mut u8, P::PG_LAYOUT) }
    }
}

/// Inner data of a segment.
pub struct SegmentInner<P: PageTable> {
    /// Virtual address range of this segment.
    range: Range<usize>,
    /// Corresponding va of the pages should be contiguous and non-decreasing.
    pages: Vec<Arc<Page<P>>>,
}

/// Segment.
pub enum Segment<P: PageTable> {
    /// Local segment can be mutable.
    Local(SegmentInner<P>),
    /// Shared segment should be immutable, which is guaranteed by ``Arc`.
    Shared(Arc<SegmentInner<P>>),
}

/// Address space manager.
///
/// It manages the address space by a page table and segments. The page table describes the
/// information of mapping from virtual address to physical address, while each segment describe
/// one contiguous virtual memory with corresponding physical pages.
///
/// Memory management within the manageer is also divided into two parts. Page table handles pages
/// used to build the table, while segments handles the allocation and deallocation of the mapped
/// physical pages.
///
/// It's necessary to divide the function of address space into these two parts when implementing
/// shared memory. For example, when the page table is freed, some shared physical pages should
/// not be freed, thus, such information should be maintained outside the page table.
pub struct AddressSpace<P: PageTable> {
    /// Page table that contains mapping information.
    pgdir: P,
    /// Physical memory segments.
    ///
    /// We don't use B-tree to guarantee O(logN) searching since the number of segments
    /// per-process is small and the insertion/deletion of segments is infrequent.
    seg: Vec<Segment<P>>,
}

impl<P: PageTable> AddressSpace<P> {
    // const PGSIZE: usize = P::PG_LAYOUT.size();

    const fn pgsize() -> usize {
        P::PG_LAYOUT.size()
    }
    /// Create a new address space.
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            pgdir: PageTable::new().map_err(|_| Error::OutOfMemory)?,
            seg: Vec::new(),
        })
    }

    /// Check if range [va.start, va.end) is overlap with any segments.
    ///
    /// Returns the index of the overlap segment.
    fn overlap(&self, rg: &Range<usize>) -> Option<usize> {
        let intersect = |a: &Range<usize>, b: &Range<usize>| a.start < b.end && a.end > b.start;
        for (i, s) in self.seg.iter().enumerate() {
            match s {
                Segment::Local(s) => {
                    if intersect(rg, &s.range) {
                        return Some(i);
                    }
                }
                Segment::Shared(s) => {
                    if intersect(rg, &s.range) {
                        return Some(i);
                    }
                }
            }
        }
        None
    }

    /// Add a new memory segment.
    ///
    /// Segments are not allowed to be overlap with each other. But can optionaly overwrite old
    /// segments.
    ///
    /// Returns true if added.
    pub fn attach(
        &mut self,
        range: Range<usize>,
        shared: bool,
        overwrite: bool,
    ) -> Result<bool, Error> {
        debug_assert_eq!(range.start & (Self::pgsize() - 1), 0);
        debug_assert_eq!(range.end & (Self::pgsize() - 1), 0);
        let mut map_len = 0;
        let mut f = || {
            let mut replace = None;
            if let Some(i) = self.overlap(&range) {
                if !overwrite {
                    return Ok(false);
                }
                replace = Some(i);
            }

            let mut pages = Vec::new();
            for va in range.clone().step_by(Self::pgsize()) {
                let p = Page::new()?;
                self.pgdir.map(va, &p, Self::pgsize())?;
                map_len += Self::pgsize();
                vec_push(&mut pages, arc_new(p)?)?;
            }

            let inner = SegmentInner {
                range: range.clone(),
                pages,
            };
            let new_seg = if shared {
                Segment::Shared(arc_new(inner)?)
            } else {
                Segment::Local(inner)
            };

            if let Some(i) = replace {
                self.seg[i] = new_seg;
            } else {
                vec_push(&mut self.seg, new_seg)?;
            }
            return Ok(true);
        };
        match f() {
            Ok(x) => Ok(x),
            Err(e) => {
                self.pgdir.unmap(range.start, map_len);
                Err(e)
            }
        }
    }

    /// Remove a segment.
    ///
    /// Returns true if removed.
    pub fn detach(&mut self, saddr: usize) -> Result<bool, Error> {
        if let Some(i) = self.overlap(&(saddr..(saddr + 1))) {
            let rg = match self.seg.remove(i) {
                Segment::Local(inner) => inner.range,
                Segment::Shared(inner) => inner.range.clone(),
            };
            self.pgdir.unmap(rg.start, rg.len());
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Mark the segment as shared.
    ///
    /// The target segment to be shared is any segment that contains `saddr`. Since segments do
    /// not overlap, it is unique.
    ///
    /// Return false if no such segment. Otherwise, return true.
    pub fn share(&mut self, saddr: usize) -> Result<bool, Error> {
        if let Some(i) = self.overlap(&(saddr..(saddr + 1))) {
            if let Some(inner) = {
                if let Segment::Local(inner) = &mut self.seg[i] {
                    // FIXME: Move instead of clone a new one?
                    let mut pages = Vec::new();
                    for p in inner.pages.iter() {
                        vec_push(&mut pages, p.clone())?;
                    }
                    Some(SegmentInner {
                        range: inner.range.clone(),
                        pages,
                    })
                } else {
                    // Segment already shared.
                    None
                }
            } {
                self.seg[i] = Segment::Shared(arc_new(inner)?);
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Change the segment from [old_start, old_end) to [old_start, addr).
    ///
    /// `addr` is required to be page-aligned. If addr > old_end, add new mappings and physical
    /// pages, else remove unnecessary mappings and physical pages. Shared segments cannot be
    /// changed.
    ///
    /// Return true if changed. Otherwise return false.
    pub fn segbrk(&mut self, saddr: usize, addr: usize) -> Result<bool, Error> {
        debug_assert_eq!(addr & (Self::pgsize() - 1), 0);
        if let Some(i) = self.overlap(&(saddr..(saddr + 1))) {
            let rg = match &self.seg[i] {
                Segment::Local(inner) => inner.range.clone(),
                Segment::Shared(_) => {
                    // Shared segments are immutable.
                    return Ok(false);
                }
            };
            if addr < rg.start {
                return Ok(false);
            }
            if addr > rg.end && self.overlap(&(rg.end..addr)).is_some() {
                return Ok(false);
            }

            let inner = match &mut self.seg[i] {
                Segment::Local(ref mut inner) => inner,
                Segment::Shared(_) => unreachable!(),
            };

            // Grow and maintain the consistency between page table mapping and physical pages.
            if inner.range.end < addr {
                let old_npages = inner.pages.len();
                let mut map_len = 0;
                let mut f = |inner: &mut SegmentInner<P>, pgdir: &mut P| -> Result<bool, Error> {
                    for va in (inner.range.end..addr).step_by(Self::pgsize()) {
                        let pg = Page::new()?;
                        pgdir.map(va, &pg, Self::pgsize())?;
                        map_len += Self::pgsize();
                        vec_push(&mut inner.pages, arc_new(pg)?)?;
                    }
                    Ok(true)
                };
                match f(inner, &mut self.pgdir) {
                    Ok(x) => Ok(x),
                    Err(e) => {
                        // Undo
                        self.pgdir.unmap(inner.range.end, map_len);
                        while inner.pages.len() > old_npages {
                            inner.pages.pop();
                        }
                        Err(e)
                    }
                }
            } else {
                self.pgdir.unmap(addr, inner.range.end - addr);
                for _ in (addr..inner.range.end).step_by(Self::pgsize()) {
                    inner.pages.pop().unwrap();
                }
                Ok(true)
            }
        } else {
            Ok(false)
        }
    }

    /// Mark as free, do noting currently.
    // pub fn free_seg(&self) -> Result<(), Error> {
    //     Ok(())
    // }

    /// Fork address space and allocate new physical pages only for local segments.
    pub fn fork(&self) -> Result<Self, Error> {
        let mut new_pgdir: P = PageTable::new().map_err(|_| Error::OutOfMemory)?;
        let mut new_segs = Vec::new();
        for s in self.seg.iter() {
            let (new_range, pages, shared) = match s {
                Segment::Local(s) => (s.range.clone(), &s.pages, false),
                Segment::Shared(s) => (s.range.clone(), &s.pages, true),
            };
            let mut va = new_range.start;
            let mut new_pages = Vec::new();
            for p in pages.iter() {
                let pa = if shared {
                    new_pgdir.map(va, &p, Self::pgsize())?;
                    vec_push(&mut new_pages, p.clone())?;
                } else {
                    let pg = Page::new()?;
                    new_pgdir.map(va, &p, Self::pgsize())?;
                    let pg_va = pg.ptr.as_ptr() as *mut u8;

                    vec_push(&mut new_pages, arc_new(pg)?)?;
                    unsafe { ptr::copy(p.ptr.as_ptr() as *const u8, pg_va, Self::pgsize()) };
                };
                va += Self::pgsize();
            }
            let inner = SegmentInner {
                range: new_range,
                pages: new_pages,
            };
            vec_push(
                &mut new_segs,
                if shared {
                    Segment::Shared(arc_new(inner)?)
                } else {
                    Segment::Local(inner)
                },
            )?;
        }
        Ok(AddressSpace {
            pgdir: new_pgdir,
            seg: new_segs,
        })
    }
}
