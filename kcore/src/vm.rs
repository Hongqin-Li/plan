//! Virtual memory management.
//!
//! The virtual memory of a process is represented by a [VmSpace], which uses [VmSegment] to describe
//! each non-overlapping contiguous virtual memory area. These segments are ordered by their begin
//! address in a red-black tree owned by the [VmSpace]. It also contains `pgdir`, a user-specific
//! interface to manipulate physical MMU.
//!
//! # Hardware layer
//!
//! The hardware-dependent mapping from virtual address to physical address is usually done by MMU.
//! It describes the permission of all virtual address in the unit of pages. Each page can only be
//! in one of the following states.
//!
//! - Empty: Reference to this page is forbidden.
//! - Read-only: Read is allowed but write is not.
//! - Read-write: Both read and write are allowed.
//!
//! # Memory mapping
//!
//! Each segment has a backing chan, to which pages of governed by this segment will be flushed
//! after removing the segment. It seems like we have mapped some part of the chan into the memory
//! as a segment, that's why it's called memory mapping. There only two kinds of segments, private
//! or shared. Private mapped segments won't allow any modifications of pages to affect the backing
//! chan, while shared mapped segments will.
//!
//! Each segment has a backing chan. The backing chan is used to store pages when paging out.
//! For a private mapped segment, it also has a reference chan, from which it fetches pages and
//! then move to the backing store. For example, when the first time we fault in a private page,
//! we may check the page in reference chan and map it as read-only.
//!
//! # Demand paging
//!
//! # Page out
//!
//! # Fault tolarence
//!
//! Disk read and write must not fail due to memory shortage.
//!

use crate::{
    chan::Chan,
    error::{Error, Result},
    pager::{Page, PageBufGuard, PageMapEntry, PageOwner, PageOwnerKind, Pager, PAGE_LIST},
    utils::{round_down, round_up},
};
use ::alloc::{alloc, boxed::Box, sync::Arc, vec::Vec};
use core::{
    alloc::{Allocator, Layout},
    cell::UnsafeCell,
    cmp::{max, min},
    fmt::Debug,
    intrinsics::copy_nonoverlapping,
    ops::{Deref, Range, RangeInclusive},
    ptr::{slice_from_raw_parts, slice_from_raw_parts_mut},
    usize,
};
use intrusive_collections::{intrusive_adapter, Bound, KeyAdapter, RBTree, RBTreeLink, UnsafeRef};
use kalloc::guard::AllocGuard;
use ksched::{
    sync::{Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard, Spinlock},
    task::yield_now,
};

pub const PAGE_SIZE: usize = 4096;
pub const PAGE_LAYOUT: Layout = unsafe { Layout::from_size_align_unchecked(PAGE_SIZE, PAGE_SIZE) };
pub const USERTOP: usize = usize::MAX / 2;

/// Page table trait.
pub trait PhysicalMap {
    /// Create a new page table.
    fn new() -> Result<Box<Self>>
    where
        Self: Sized + 'static;

    /// Switch to this page table.
    ///
    /// SAFETY: All pages mapped before switching should be accessiable after that.
    ///
    /// That means the implementation can batch the map and unmap requests.
    fn switch(&self);

    /// Map virtual address `[va, va+PAGE_SIZE)` to physical page at `vpa` with write permission.
    ///
    /// It's guaranteed that `va` is page-aligned. Overwrite the old mapping if exists.
    /// The implementation is required to be atomic, i.e., undo the mapping if failed.
    fn map(&mut self, va: usize, vpa: usize, read_only: bool) -> Result<()>;

    /// Unmap the pages in `[va, va+PAGE_SIZE)` in this page table.
    ///
    /// Returns false if there is no such page. It's guaranteed that `va` is page-aligned.
    fn unmap(&mut self, va: usize) -> bool;

    /// Protect the page in `[va, va+PAGE_SIZE)` as read-only or read-write.
    ///
    /// It's guaranteed that `va` is page-aligned.
    fn protect(&mut self, va: usize, read_only: bool);
}

type PageTable = Box<dyn PhysicalMap + 'static>;

#[derive(Debug)]
enum VmFaultKind {
    ReadFault,
    WriteFault,
}

#[derive(Debug, Clone, Copy)]
struct VmAddrRange {
    start_va: usize,
    npages: usize,
}

impl VmAddrRange {
    fn new(va_range: RangeInclusive<usize>) -> Self {
        let end_pgid = *va_range.end() / PAGE_SIZE + 1;
        let start_va = round_down(*va_range.start(), PAGE_SIZE);
        let npages = end_pgid - start_va / PAGE_SIZE;
        Self { start_va, npages }
    }

    fn inclusive_end(&self) -> usize {
        self.start_va + (self.npages * PAGE_SIZE - 1)
    }

    fn va_range(&self) -> RangeInclusive<usize> {
        self.start_va..=self.inclusive_end()
    }
}

#[derive(Debug)]
pub(crate) struct VmSegmentInner {
    /// Range of virtual address that mapped by this segment.
    addr_range: VmAddrRange,
    /// Offset in number of pages in the back chan.
    back_pgoff: usize,
    /// Offset in number of pages in the ref chan(if any).
    ref_pgoff: usize,
}

#[derive(Debug)]
pub(crate) struct VmSegment {
    /// The [VmSpace] that this segment belongs to.
    pub vmspace: UnsafeRef<VmSpaceInner>,
    pub back_chan: Chan,
    pub ref_chan: Option<Chan>,
    pub inner: RwLock<VmSegmentInner>,
    link: RBTreeLink,
}

intrusive_adapter!(VmSegmentAdapter = Box<VmSegment>: VmSegment { link: RBTreeLink } );

impl<'a> KeyAdapter<'a> for VmSegmentAdapter {
    type Key = usize;
    fn get_key(&self, seg: &'a VmSegment) -> Self::Key {
        let inner = seg.inner.try_read().unwrap();
        inner.addr_range.start_va
    }
}

impl VmSegment {
    fn new(
        vmspace: UnsafeRef<VmSpaceInner>,
        addr_range: VmAddrRange,
        back_chan: Chan,
        ref_chan: Option<Chan>,
        back_pgoff: usize,
        ref_pgoff: usize,
    ) -> Self {
        let inner = VmSegmentInner {
            addr_range,
            back_pgoff,
            ref_pgoff,
        };
        Self {
            vmspace,
            inner: RwLock::new(inner),
            back_chan,
            ref_chan,
            link: RBTreeLink::new(),
        }
    }

    pub fn is_shared(&self) -> bool {
        self.ref_chan.is_none()
    }

    /// Get page offset in ref chan of the page with specific virtual address.
    fn ref_pgoff(&self, va: usize) -> usize {
        let inner = self.inner.try_read().unwrap();
        debug_assert!(va > inner.addr_range.start_va);
        debug_assert_eq!(va % PAGE_SIZE, 0);
        let seg_pgoff = (va - inner.addr_range.start_va) / PAGE_SIZE;
        inner.ref_pgoff + seg_pgoff
    }

    /// Get page offset in back chan of the page with specific virtual address.
    fn back_pgoff(&self, va: usize) -> usize {
        let inner = self.inner.try_read().unwrap();
        debug_assert!(va > inner.addr_range.start_va);
        debug_assert_eq!(va % PAGE_SIZE, 0);
        let seg_pgoff = (va - inner.addr_range.start_va) / PAGE_SIZE;
        inner.back_pgoff + seg_pgoff
    }

    fn npages(&self) -> usize {
        self.inner.try_read().unwrap().addr_range.npages
    }

    pub fn va_range(&self) -> RangeInclusive<usize> {
        self.inner.try_read().unwrap().addr_range.va_range()
    }

    pub async fn fork_ref(&self, new_seg: &VmSegment) -> Result<()> {
        debug_assert!(!self.is_shared());
        let chan = self.ref_chan.as_ref().unwrap();
        let pgdir = &self.vmspace.pgdir;
        let pgid_start = self.ref_pgoff(*self.va_range().start());
        let pgid_end = pgid_start + self.npages();
        let pgmap = chan.pgmap.lock().await;
        let mut cur = pgmap.lower_bound(Bound::Included(&pgid_start));
        while let Some(page_entry) = cur.get() {
            if page_entry.pgid >= pgid_end {
                break;
            }
            let mut owners = page_entry.owners.lock().await;
            if let Some(this_owner) = owners.owned_by(&self) {
                debug_assert_eq!(this_owner.kind, PageOwnerKind::ReadOnlyPrivateRef);
                owners.add_owner(new_seg, PageOwnerKind::ReadOnlyPrivateRef)?;
            }
            cur.move_next();
        }
        Ok(())
    }

    pub async fn fork_back(&self, new_seg: &VmSegment) -> Result<()> {
        debug_assert!(!self.is_shared());
        let chan = &self.back_chan;
        let pgdir = &self.vmspace.pgdir;
        let pgid_start = self.back_pgoff(*self.va_range().start());
        let pgid_end = pgid_start + self.npages();
        let pgmap = chan.pgmap.lock().await;
        let mut cur = pgmap.lower_bound(Bound::Included(&pgid_start));
        while let Some(page_entry) = cur.get() {
            if page_entry.pgid >= pgid_end {
                break;
            }
            let mut owners = page_entry.owners.lock().await;
            if let Some(this_owner) = owners.owned_by(self) {
                let new_kind = PageOwnerKind::ReadOnlyPrivateBack;
                if this_owner.kind != new_kind {
                    debug_assert_eq!(owners.len(), 1);
                    debug_assert_eq!(this_owner.kind, PageOwnerKind::ReadWritePrivateBack);
                    if let Some(va) = this_owner.va {
                        pgdir.write().await.unmap(va);
                    }
                    this_owner.kind = new_kind;
                }
                owners.add_owner(new_seg, new_kind)?;
            }
            cur.move_next();
        }
        Ok(())
    }

    /// Split the segment of [start, end) into [start, va) and [va, end).
    ///
    /// Caller must hold segments' write lock. This function is atomic. Return the new
    /// segment of [va, end).
    pub async fn split_from(&self, va: usize) -> Result<Box<Self>> {
        let va_range = self.va_range();
        debug_assert_eq!(va & PAGE_SIZE, 0);
        debug_assert!(va_range.start() < &va && &va < va_range.end());

        let old_npages = (va - va_range.start()) / PAGE_SIZE;
        let npages = (va_range.end() - va + 1) / PAGE_SIZE;
        let back_chan = self.back_chan.dup();
        let back_pgoff = self.back_pgoff(va);
        let back_pgids = back_pgoff..back_pgoff + npages;
        let mut ref_chan = None;
        let mut ref_pgoff = 0;
        let mut ref_pgids = 0..0;
        if let Some(chan) = &self.ref_chan {
            ref_chan = Some(chan.dup());
            ref_pgoff = self.ref_pgoff(va);
            ref_pgids = ref_pgoff..ref_pgoff + npages;
        }

        let seg = Box::try_new(VmSegment::new(
            self.vmspace.clone(),
            VmAddrRange::new(va..=*va_range.end()),
            back_chan,
            ref_chan,
            back_pgoff,
            ref_pgoff,
        ))?;
        let pgmap = self.back_chan.pgmap.lock().await;
        pgmap.change_owner(back_pgids, self, seg.as_ref()).await;
        drop(pgmap);
        if let Some(chan) = &self.ref_chan {
            let pgmap = chan.pgmap.lock().await;
            pgmap.change_owner(ref_pgids, self, seg.as_ref()).await;
        }
        let mut inner = self.inner.try_write().unwrap();
        inner.addr_range.npages = old_npages;
        Ok(seg)
    }

    /// Shrink the segment by unmapping pages from one end.
    ///
    /// The target range must be
    /// 1. a strict sub set of va range interval of this segment
    /// 2. its left endpoint is equal to the left endpoint of va range of this segment, or
    ///    its right endpoint is equal to the right endpoint of va range of this segment.
    ///
    /// Caller must hold segments' write lock. This function won't fail.
    pub async fn unmap_edge(&self, target: VmAddrRange) {
        self.unmap_pages(target).await;
        self.shrink_addr_range(target);
    }

    /// Unmap pages of a region in this segemnt.
    async fn unmap_pages(&self, target: VmAddrRange) {
        let chanoff = &self.back_chan;
        let pgid_start = self.back_pgoff(target.start_va);
        let pgid_end = pgid_start + target.npages;
        let mut pgmap = self.back_chan.pgmap.lock().await;
        pgmap.remove_owner(pgid_start..pgid_end, self);
        if let Some(chan) = &self.ref_chan {
            let pgid_start = self.ref_pgoff(target.start_va);
            let pgid_end = pgid_start + target.npages;
            let mut pgmap = chan.pgmap.lock().await;
            pgmap.remove_owner(pgid_start..pgid_end, self);
        }
    }

    fn shrink_addr_range(&self, target: VmAddrRange) {
        let va_range = self.va_range();
        let mut inner = self.inner.try_write().unwrap();
        inner.addr_range.npages -= target.npages;
        if target.start_va == *va_range.start() {
            let target_end = target.inclusive_end();
            debug_assert!(target_end < *va_range.end());
            // Note that order won't be changed since all segments are already non-overlapping.
            inner.addr_range.start_va = target_end + 1;
            inner.back_pgoff += target.npages;
            inner.ref_pgoff += target.npages;
        } else {
            debug_assert!(target.start_va > *va_range.start());
            debug_assert_eq!(target.inclusive_end(), *va_range.end());
        }
    }

    /// Lock the page entry in a shared segment.
    ///
    /// 1. Lock the page map of back chan.
    /// 2. Find the target page entry or create a new one.
    /// 3. Lock the page entry and unlock page map.
    /// 4. Adjust the owner kind of the page entry.
    /// 5. Return the locked page entry so that this segment won't change its owner kind on it.
    ///
    /// Caller must hold segments' read lock. The locked page entry can then be used to access
    /// its physical page.
    ///
    /// The locked page entry can
    ///
    /// 1. fetch or flush underlying page from or to backing chan.
    /// 2. map or unmap the fetched page in physical map.
    async fn lock_shared_page_entry(&self, va: usize) -> Result<PageEntryGuard> {
        todo!()
    }

    /// Similar to [lock_shared_page_entry] but for private segment.
    async fn lock_private_page_entry(&self, va: usize) -> Result<PageEntryGuard> {
        todo!()
    }

    /// Fetch a page for reading in shared segment.
    ///
    /// After that, the fetched page will then be read-only or read-write.
    async fn read_shared(&self, va: usize) -> Result<PageBufGuard> {
        debug_assert_eq!(self.is_shared(), true);
        debug_assert_eq!(va & PAGE_SIZE, 0);
        let mut readonly = true;
        let pgid = self.back_pgoff(va);
        let mut pgmap = self.back_chan.pgmap.lock().await;
        let page = if let Some(page_entry) = pgmap.find(&pgid).get() {
            let mut owners = page_entry.owners.lock().await;
            if let Some(this_owner) = owners.owned_by(self) {
                readonly = this_owner.kind == PageOwnerKind::ReadOnlySharedBack;
            } else {
                let my_kind = match owners[0].kind {
                    PageOwnerKind::ReadWritePrivateBack => {
                        debug_assert_eq!(owners.len(), 1);
                        return Err(Error::Conflict("cannot read others private backing page"));
                    }
                    PageOwnerKind::ReadOnlyPrivateRef
                    | PageOwnerKind::ReadOnlyPrivateBack
                    | PageOwnerKind::ReadOnlySharedBack => PageOwnerKind::ReadOnlySharedBack,
                    PageOwnerKind::ReadWriteSharedBack => {
                        readonly = false;
                        PageOwnerKind::ReadWriteSharedBack
                    }
                };
                owners.add_owner(self, my_kind)?;
            }
            page_entry.page.upgrade().unwrap()
        } else {
            let my_kind = PageOwnerKind::ReadOnlySharedBack;
            pgmap.new_page(pgid, self, my_kind).await?
        };
        let page_buf = PageBufGuard::lock(page, pgmap).await?;
        // FIXME: only need to map when page fault.
        let mut pgdir = self.vmspace.pgdir.write().await;
        pgdir.map(va, page_buf.as_ptr() as usize, readonly)?;
        Ok(page_buf)
    }

    async fn read_private(&self, va: usize) -> Result<PageBufGuard> {
        debug_assert_eq!(self.is_shared(), false);
        debug_assert_eq!(va & PAGE_SIZE, 0);
        let mut readonly = true;
        let ref_chanoff = self.ref_chan.as_ref().unwrap();
        let back_pgid = self.back_pgoff(va);
        let ref_pgid = self.ref_pgoff(va);
        let (mut back_pgmap, mut ref_pgmap) = loop {
            let ref_pgmap = self.ref_chan.as_ref().unwrap().pgmap.lock().await;
            if let Some(back_pgmap) = self.back_chan.pgmap.try_lock() {
                break (back_pgmap, ref_pgmap);
            }
            yield_now().await;
        };
        let page = if let Some(page) = back_pgmap.find(&back_pgid).get() {
            if let Some(this_owner) = page.owners.lock().await.owned_by(self) {
                debug_assert!(
                    this_owner.kind == PageOwnerKind::ReadWritePrivateBack
                        || this_owner.kind == PageOwnerKind::ReadOnlyPrivateBack
                );
                readonly = this_owner.kind == PageOwnerKind;
            } else {
                return Err(Error::Conflict("private backing page is not mine"));
            }
            page
        } else if let Some(page) = ref_pgmap.find(&ref_pgid).clone_pointer() {
            let mut pagei = page.lock().await;
            if let Some(kind) = pagei.owned_by(self) {
                debug_assert_eq!(kind, PageOwnerKind::ReadOnlyPrivate);
                readonly = true;
            } else {
                let first_kind = pagei.owners[0].kind;
                if first_kind == PageOwnerKind::ReadWritePrivate
                    || first_kind == PageOwnerKind::ReadWriteShared
                {
                    drop(ref_pgmap);

                    let new_page = Page::new(&self.back_chan.chan, back_pgid)?;
                    let guard = AllocGuard::new(PAGE_LAYOUT)?;
                    let ptr = guard.ptr();
                    let buf = unsafe { &mut *slice_from_raw_parts_mut(ptr.as_ptr(), PAGE_SIZE) };

                    if let Some(ref_ptr) = pagei.ptr {
                        let ref_buf = unsafe {
                            &*slice_from_raw_parts(ref_ptr.as_ptr() as *const _, PAGE_SIZE)
                        };
                        buf.copy_from_slice(ref_buf)
                    } else {
                        let chan = Chan::from_weak(&page.chan);
                        if chan.read(buf, page.pgid * PAGE_SIZE).await? != PAGE_SIZE {
                            return Err(Error::InternalError("failed to page in"));
                        }
                        chan.close().await;
                    };
                    drop(pagei);

                    let mut new_pagei = new_page.try_lock().unwrap();
                    new_pagei.add_owner(self, PageOwnerKind::ReadWritePrivate)?;
                    back_pgmap.insert(new_page.clone());
                    new_pagei.ptr = Some(ptr);
                    guard.consume();
                    PAGE_LIST.lock().await.push_back(new_page.clone());
                    drop(new_pagei);

                    let page_buf = PageBufGuard::lock(new_page, [back_pgmap]).await?;
                    let mut pgdir = self.vmspace.pgdir.write().await;
                    pgdir.map(va, page_buf.as_ptr() as usize, false)?;
                    return Ok(page_buf);
                } else {
                    pagei.add_owner(self, PageOwnerKind::ReadOnlyPrivate)?;
                }
            }
            drop(pagei);
            page
        } else {
            let page = Page::new(&ref_chanoff.chan, ref_pgid)?;
            page.try_lock()
                .unwrap()
                .add_owner(self, PageOwnerKind::ReadOnlyPrivate)?;
            ref_pgmap.insert(page.clone());
            page
        };
        let page_buf = PageBufGuard::lock(page, [back_pgmap, ref_pgmap]).await?;
        let mut pgdir = self.vmspace.pgdir.write().await;
        pgdir.map(va, page_buf.as_ptr() as usize, readonly)?;
        Ok(page_buf)
    }

    async fn write_shared(&self, va: usize) -> Result<PageBufGuard<'_>> {
        debug_assert_eq!(self.is_shared(), true);
        debug_assert_eq!(va & PAGE_SIZE, 0);
        let pgid = self.back_chan.pgoff + (va - self.start) / PAGE_SIZE;
        let mut pgmap = self.back_chan.chan.pgmap.lock().await;
        let page = if let Some(page) = pgmap.find(&pgid).clone_pointer() {
            let mut pagei = page.lock().await;
            let my_kind = match pagei.owners[0].kind {
                PageOwnerKind::ReadWritePrivate => {
                    debug_assert_eq!(pagei.owners.len(), 1);
                    return Err(Error::Conflict("cannot read others private backing page"));
                }
                PageOwnerKind::ReadOnlyPrivate | PageOwnerKind::ReadOnlyShared => {
                    if pagei.owners.len() != 1 || pagei.owned_by(self).is_none() {
                        return Err(Error::Conflict("cannot upgrade to rw page"));
                    }
                    pagei.owners[0].kind = PageOwnerKind::ReadWriteShared;
                }
                PageOwnerKind::ReadWriteShared => {
                    if pagei.owned_by(self).is_none() {
                        pagei.add_owner(self, PageOwnerKind::ReadWriteShared)?;
                    }
                }
            };
            drop(pagei);
            page
        } else {
            let page = Page::new(&self.back_chan.chan, pgid)?;
            page.try_lock()
                .unwrap()
                .add_owner(self, PageOwnerKind::ReadWriteShared)?;
            pgmap.insert(page.clone());
            page
        };
        let page_buf = PageBufGuard::lock(page, pgmap).await?;
        let mut pgdir = self.vmspace.pgdir.write().await;
        pgdir.map(va, page_buf.as_ptr() as usize, false)?;
        Ok(page_buf)
    }

    async fn write_private(&self, va: usize) -> Result<PageBufGuard<'_>> {
        debug_assert!(!self.is_shared());
        debug_assert_eq!(va & PAGE_SIZE, 0);
        let ref_chanoff = self.ref_chan.as_ref().unwrap();
        let seg_pgoff = (va - self.start) / PAGE_SIZE;
        let back_pgid = self.back_chan.pgoff + seg_pgoff;
        let ref_pgid = ref_chanoff.pgoff + seg_pgoff;
        let (mut back_pgmap, mut ref_pgmap) = loop {
            let back_pgmap = self.back_chan.chan.pgmap.lock().await;
            if let Some(ref_pgmap) = ref_chanoff.chan.pgmap.try_lock() {
                break (back_pgmap, ref_pgmap);
            }
            yield_now().await;
        };
        let page = if let Some(page) = back_pgmap.find(&back_pgid).clone_pointer() {
            if let Some(kind) = page.lock().await.owned_by(self) {
                debug_assert_eq!(kind, PageOwnerKind::ReadWritePrivate);
            } else {
                return Err(Error::Conflict("private backing page is not mine"));
            }
            page
        } else {
            let new_page = Page::new(&self.back_chan.chan, back_pgid)?;
            let guard = AllocGuard::new(PAGE_LAYOUT)?;
            let ptr = guard.ptr();
            let buf = unsafe { &mut *slice_from_raw_parts_mut(ptr.as_ptr(), PAGE_SIZE) };

            let mut ref_buf = None;
            let mut cur = ref_pgmap.find_mut(&ref_pgid);
            if let Some(page) = cur.get() {
                let pagei = page.lock().await;
                if let Some(ptr) = pagei.ptr {
                    ref_buf = Some(unsafe {
                        &*slice_from_raw_parts(ptr.as_ptr() as *const u8, PAGE_SIZE)
                    });
                }
            }
            if let Some(ref_buf) = ref_buf {
                buf.copy_from_slice(ref_buf);
            } else {
                if ref_chanoff.chan.read(buf, ref_pgid * PAGE_SIZE).await? != PAGE_SIZE {
                    return Err(Error::InternalError("failed to page in"));
                }
            }

            let mut new_pagei = new_page.try_lock().unwrap();
            new_pagei.add_owner(self, PageOwnerKind::ReadWritePrivate)?;
            new_pagei.ptr = Some(ptr);
            guard.consume();
            drop(new_pagei);
            back_pgmap.insert(new_page.clone());
            PAGE_LIST.lock().await.push_back(new_page.clone());

            // Clean up old page in ref chan.
            let mut remove = None;
            if let Some(page) = cur.get() {
                let mut pagei = page.lock().await;
                if let Some(num_owners) = pagei.remove_owner(self) {
                    if num_owners == 0 {
                        remove = Some(pagei.ptr.is_some());
                    }
                }
            }
            if let Some(remove_pglist) = remove {
                let page = cur.remove().unwrap();
                if remove_pglist {
                    let mut pglist = PAGE_LIST.lock().await;
                    let mut cur = unsafe { pglist.cursor_mut_from_ptr(page.as_ref()) };
                    cur.remove();
                }
            }

            new_page
        };
        let page_buf = PageBufGuard::lock(page, [back_pgmap, ref_pgmap]).await?;
        let mut pgdir = self.vmspace.pgdir.write().await;
        pgdir.map(va, page_buf.as_ptr() as usize, false)?;
        Ok(page_buf)
    }

    async fn fetch_for_read(&self, va: usize) -> Result<PageBufGuard<'_>> {
        Ok(if self.is_shared() {
            self.read_shared(va).await?
        } else {
            self.read_private(va).await?
        })
    }

    async fn fetch_for_write(&self, va: usize) -> Result<PageBufGuard<'_>> {
        Ok(if self.is_shared() {
            self.write_shared(va).await?
        } else {
            self.write_private(va).await?
        })
    }
}

struct VmSpaceInner {
    pgdir: RwLock<PageTable>,
    /// The read-write lock guards towards the number of segments and the va range of the segments.
    segments: RwLock<RBTree<VmSegmentAdapter>>,
    refcnt: Spinlock<usize>,
}

impl Drop for VmSpaceInner {
    fn drop(&mut self) {
        let refcnt = self.refcnt.lock();
        debug_assert_eq!(*refcnt, 0);
    }
}

impl Debug for VmSpaceInner {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("VmSpaceInner")
            .field("refcnt", &self.refcnt)
            .field("segments", &self.segments)
            .finish()
    }
}

#[derive(Debug)]
pub struct VmSpace {
    inner: UnsafeRef<VmSpaceInner>,
    dropped: bool,
}

impl Deref for VmSpace {
    type Target = UnsafeRef<VmSpaceInner>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl Drop for VmSpace {
    fn drop(&mut self) {
        debug_assert!(self.dropped, "forgot to free: {:?}", self);
    }
}

impl VmSpace {
    /// Create a new address space.
    pub fn new<P: PhysicalMap + 'static>() -> Result<Self> {
        Ok(Self {
            inner: UnsafeRef::from_box(Box::try_new(VmSpaceInner {
                refcnt: Spinlock::new(1),
                pgdir: RwLock::new(P::new()?),
                segments: RwLock::new(RBTree::new(VmSegmentAdapter::new())),
            })?),
            dropped: false,
        })
    }

    /// Duplicate a new address space with the same physical map.
    ///
    /// May be called when spawning a thread.
    pub fn dup(&self) -> Self {
        self.refcnt_inc();
        Self {
            inner: self.inner.clone(),
            dropped: false,
        }
    }

    /// Fork an address space.
    ///
    /// May be called when forking a process.
    pub async fn fork<P: PhysicalMap + 'static>(&mut self) -> Result<VmSpace> {
        let mut new_vm = Self::new::<P>()?;
        if let Err(e) = self.fork1(&mut new_vm).await {
            new_vm.free().await;
            Err(e)
        } else {
            Ok(new_vm)
        }
    }

    async fn fork1(&self, new_vm: &mut VmSpace) -> Result<()> {
        let segments = self.segments.read().await;
        for seg in segments.iter() {
            let new_seg = Box::try_new(VmSegment::new(
                new_vm.clone(),
                seg.inner.try_read().unwrap().addr_range.clone(),
                self.new_back_chan().await?,
                seg.ref_chan.as_ref().map(|chan| chan.dup()),
                seg.back_pgoff(),
                seg.ref_pgoff(),
            ))?;
            if !seg.is_shared() {
                seg.fork_back(&new_seg).await?;
                seg.fork_ref(&new_seg).await?;
            }
            let mut new_segments = new_vm.segments.try_write().unwrap();
            new_segments.insert(new_seg);
        }
        Ok(())
    }

    /// Unmap all segments and drop this address space.
    ///
    /// Note that this dosen't gurantee all dirty pages are successfully flushed
    /// to their backing object.
    pub async fn free(mut self) {
        self.dropped = true;
        if self.refcnt_dec() == 0 {
            self.munmap(0, USERTOP).await.unwrap();
            unsafe { UnsafeRef::into_box(self.inner.clone()) };
        }
    }

    /// Create a memory segment mapping.
    ///
    /// Accessing virtual address [addr, addr + len) is equivalent to accessing ontents starting
    /// at `offset` of given chan. offset, addr and len must be a multiple of page size.
    ///
    /// An anonymous mapping won't carry any modification to the underlying chan. It's unspecified
    /// when the underlying chan is then modified by others after creating the anonymous mapping,
    /// since we may or may not view the modified value in the mapping.
    pub async fn mmap(
        &self,
        addr: usize,
        len: usize,
        chan: &Chan,
        offset: usize,
        anonymous: bool,
    ) -> Result<()> {
        if addr % PAGE_SIZE != 0 || len % PAGE_SIZE != 0 || offset % PAGE_SIZE != 0 {
            return Err(Error::BadRequest("mmap va misaligned"));
        } else if len == 0 || addr.checked_add(len).is_none() {
            return Err(Error::BadRequest("mmap invalid va range"));
        }
        let addr_range = VmAddrRange::new(addr..=(addr + len - 1));
        let pgoff = offset / PAGE_SIZE;
        let (back_chan, ref_chan, back_pgoff, ref_pgoff) = if anonymous {
            (self.new_back_chan().await?, Some(chan.dup()), 0, pgoff)
        } else {
            (chan.dup(), None, pgoff, 0)
        };
        let result = self
            .mmap1(addr_range, &back_chan, &ref_chan, back_pgoff, ref_pgoff)
            .await;
        back_chan.close().await;
        result
    }

    async fn mmap1(
        &self,
        addr_range: VmAddrRange,
        back_chan: &Chan,
        ref_chan: &Option<Chan>,
        back_pgoff: usize,
        ref_pgoff: usize,
    ) -> Result<()> {
        let mut segments = self.segments.write().await;
        let new_seg = VmSegment::new(
            self.inner.clone(),
            addr_range,
            back_chan.dup(),
            ref_chan.as_ref().map(|chan| chan.dup()),
            back_pgoff,
            ref_pgoff,
        );
        Self::check_overlap(&segments, &new_seg)?;
        segments.insert(Box::try_new(new_seg)?);
        Ok(())
    }

    /// Unmap a continugous chunk of memory.
    ///
    /// All pages containing a part of the indicated range [addr, addr + len) are unmapped.
    ///
    /// Note that when the chunk of memory to unmap is included by exactly one segment, we need to
    /// split it and add a new segment. In other cases, we can just reuse the old segments by
    /// adjusting their structures.
    ///
    /// This is atomic. Return error if failed. Otherwise, all mappings are guaranteed to
    /// be unmapped and the return value indicates whether there are any error when flushing
    /// to the backing chans. See also [`VmSegment::unmap`].
    pub async fn munmap(&mut self, addr: usize, len: usize) -> Result<bool> {
        if addr.checked_add(len).is_none() {
            return Err(Error::BadRequest("mmap invalid va range"));
        } else if len == 0 {
            return Ok(false);
        }
        let target = VmAddrRange::new(addr..=(addr + len - 1));
        let mut segments = self.segments.write().await;
        let mut cur = segments.upper_bound_mut(Bound::Included(&target.start_va));
        if let Some(seg) = cur.get() {
            if *seg.va_range().end() < target.start_va {
                cur.move_next();
            }
        }
        if let Some(seg) = cur.get() {
            let va_range = seg.va_range();
            if *va_range.start() < target.start_va && target.va_range().end() < va_range.end() {
                let new_seg = seg.split_from(target.va_range().end() + 1).await?;
                let bad = seg.unmap_edge(target).await;
                segments.insert(new_seg);
                return Ok(bad);
            }
        }

        let mut bad = false;
        while let Some(seg) = cur.get() {
            let va_range = seg.va_range();
            if va_range.start() < target.va_range().end() {
                break;
            }
            let l = max(*va_range.start(), *target.va_range().start());
            let r = min(*va_range.end(), *target.va_range().end());
            let cur_range = l..=r;
            bad |= seg.unmap_edge(VmAddrRange::new(cur_range.clone())).await;
            if cur_range == va_range {
                let seg = cur.remove().unwrap();
                seg.back_chan.close().await;
                if let Some(chan) = seg.ref_chan {
                    chan.close().await;
                }
            } else {
                cur.move_next();
            }
        }
        Ok(bad)
    }

    /// Page fault handler.
    ///
    /// If it returns ok, the address space will have read/write permission to the page containing
    /// virtual address `va`. That means the kernel can safely read or write to the page (after
    /// switching to it) without page fault.
    pub async fn fault(&self, va: usize, kind: VmFaultKind) -> Result<()> {
        let va = round_down(va, PAGE_SIZE);
        let segments = self.segments.read().await;
        if let Some(seg) = segments.upper_bound(Bound::Included(&va)).get() {
            let end = seg.end.try_read().unwrap();
            if va < *end {
                match kind {
                    VmFaultKind::ReadFault => seg.fetch_for_read(&self.pgdir, va).await?,
                    VmFaultKind::WriteFault => seg.fetch_for_write(&self.pgdir, va).await?,
                };
                return Ok(());
            }
        }
        Err(Error::SegmentFault)
    }

    /// Read data in memory area [offset, offset + buf.len) from this address space.
    pub async fn read(&mut self, mut buf: &mut [u8], mut offset: usize) -> Result<()> {
        if offset.checked_add(buf.len()).is_none() {
            return Err(Error::BadRequest("vm read"));
        }
        let segments = self.segments.read().await;
        let mut cur = segments.upper_bound(Bound::Included(&offset));
        let end = offset + buf.len();
        while let Some(seg) = cur.get() {
            if offset < seg.start || buf.is_empty() {
                break;
            }
            let l = round_down(offset, PAGE_SIZE);
            let r = min(end, *seg.end.try_read().unwrap());
            for va in (l..r).step_by(PAGE_SIZE) {
                let page_buf = seg.fetch(&mut self.pgdir, va).await?;
                let page_off = offset - va;
                let cnt = min(end, va + PAGE_SIZE) - max(offset, va);
                buf[..cnt].copy_from_slice(&page_buf[page_off..page_off + cnt]);
                buf = &mut buf[cnt..];
                offset += cnt;
            }
            cur.move_next();
        }
        if !buf.is_empty() {
            Err(Error::Forbidden("vm read"))
        } else {
            Ok(())
        }
    }

    /// Write data from buffer to memory area [offset, offset + buf.len) of this address space.
    pub async fn write(&mut self, mut buf: &[u8], mut offset: usize) -> Result<()> {
        if offset.checked_add(buf.len()).is_none() {
            return Err(Error::BadRequest("vm write"));
        }
        let mut cur = self.segments.upper_bound(Bound::Included(&offset));
        let end = offset + buf.len();
        while let Some(seg) = cur.get() {
            let segi = unsafe { &*seg.inner.get() };
            if offset < segi.va.start || buf.is_empty() {
                break;
            }
            let l = round_down(offset, PAGE_SIZE);
            let r = min(end, segi.va.end);
            for va in (l..r).step_by(PAGE_SIZE) {
                let page_buf = seg.fetch(&mut self.pgdir, va).await?;
                let page_off = offset - va;
                let cnt = min(end, va + PAGE_SIZE) - max(offset, va);
                page_buf[page_off..page_off + cnt].copy_from_slice(&buf[..cnt]);
                buf = &buf[cnt..];
                offset += cnt;
            }
            cur.move_next();
        }
        if !buf.is_empty() {
            Err(Error::Forbidden("vm write"))
        } else {
            Ok(())
        }
    }

    /// Entering user space.
    ///
    /// The lock of physical map ensures that the mapping won't change when executing user
    /// programs. It must be called before entering user space.
    async fn enter_user(&self) -> RwLockReadGuard<'_, PageTable> {
        let pgdir = self.pgdir.read().await;
        pgdir.switch();
        pgdir
    }

    /// Check if segments are still non-overlapping after adding the new segment.
    fn check_overlap(segments: &RBTree<VmSegmentAdapter>, new_seg: &VmSegment) -> Result<()> {
        let new_va_range = new_seg.va_range();
        let cur = segments.lower_bound(Bound::Excluded(new_va_range.start()));
        let mut overlap = false;
        if let Some(seg) = cur.get() {
            let va_range = seg.va_range();
            if va_range.start() <= new_va_range.end() {
                overlap = true;
            }
        };
        if let Some(seg) = cur.peek_prev().get() {
            let va_range = seg.va_range();
            if va_range.end() >= new_va_range.start() {
                overlap = true;
            }
        }
        if overlap {
            Err(Error::Conflict("mmap segment overlap"))
        } else {
            Ok(())
        }
    }

    async fn new_back_chan(&self) -> Result<Chan> {
        todo!()
    }
}

impl VmSpace {
    fn refcnt_inc(&self) -> usize {
        let refcnt = self.refcnt.lock();
        *refcnt += 1;
        *refcnt
    }

    fn refcnt_dec(&self) -> usize {
        let refcnt = self.refcnt.lock();
        *refcnt -= 1;
        *refcnt
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lower_upper_bound() {
        struct Entry {
            key: usize,
            link: RBTreeLink,
        }
        intrusive_adapter!(Adapter = Box<Entry>: Entry { link: RBTreeLink });
        impl<'a> KeyAdapter<'a> for Adapter {
            type Key = usize;
            fn get_key(&self, ent: &'a Entry) -> Self::Key {
                ent.key
            }
        }

        let mut tree = RBTree::new(Adapter::new());
        let mut insert = |key| {
            tree.insert(Box::new(Entry {
                key,
                link: RBTreeLink::new(),
            }));
        };

        insert(1);
        insert(2);
        insert(3);
        insert(10);

        assert_eq!(tree.lower_bound(Bound::Included(&0)).get().unwrap().key, 1);
        assert_eq!(tree.lower_bound(Bound::Included(&1)).get().unwrap().key, 1);
        assert_eq!(tree.lower_bound(Bound::Included(&2)).get().unwrap().key, 2);
        assert_eq!(tree.lower_bound(Bound::Included(&3)).get().unwrap().key, 3);
        assert_eq!(tree.lower_bound(Bound::Included(&4)).get().unwrap().key, 10);
        assert_eq!(tree.lower_bound(Bound::Included(&11)).get().is_none(), true);

        assert_eq!(tree.lower_bound(Bound::Excluded(&0)).get().unwrap().key, 1);
        assert_eq!(tree.lower_bound(Bound::Excluded(&1)).get().unwrap().key, 2);
        assert_eq!(tree.lower_bound(Bound::Excluded(&2)).get().unwrap().key, 3);
        assert_eq!(tree.lower_bound(Bound::Excluded(&3)).get().unwrap().key, 10);
        assert_eq!(tree.lower_bound(Bound::Excluded(&4)).get().unwrap().key, 10);
        assert_eq!(tree.lower_bound(Bound::Excluded(&9)).get().unwrap().key, 10);
        assert_eq!(tree.lower_bound(Bound::Excluded(&10)).get().is_none(), true);

        assert_eq!(tree.upper_bound(Bound::Included(&0)).get().is_none(), true);
        assert_eq!(tree.upper_bound(Bound::Included(&1)).get().unwrap().key, 1);
        assert_eq!(tree.upper_bound(Bound::Included(&2)).get().unwrap().key, 2);
        assert_eq!(tree.upper_bound(Bound::Included(&3)).get().unwrap().key, 3);
        assert_eq!(tree.upper_bound(Bound::Included(&4)).get().unwrap().key, 3);
        assert_eq!(tree.upper_bound(Bound::Included(&9)).get().unwrap().key, 3);
        assert_eq!(
            tree.upper_bound(Bound::Included(&10)).get().unwrap().key,
            10
        );

        assert_eq!(tree.upper_bound(Bound::Excluded(&0)).get().is_none(), true);
        assert_eq!(tree.upper_bound(Bound::Excluded(&1)).get().is_none(), true);
        assert_eq!(tree.upper_bound(Bound::Excluded(&2)).get().unwrap().key, 1);
        assert_eq!(tree.upper_bound(Bound::Excluded(&3)).get().unwrap().key, 2);
        assert_eq!(tree.upper_bound(Bound::Excluded(&4)).get().unwrap().key, 3);
        assert_eq!(tree.upper_bound(Bound::Excluded(&9)).get().unwrap().key, 3);
        assert_eq!(tree.upper_bound(Bound::Excluded(&10)).get().unwrap().key, 3);
        assert_eq!(
            tree.upper_bound(Bound::Excluded(&11)).get().unwrap().key,
            10
        );
    }
}
