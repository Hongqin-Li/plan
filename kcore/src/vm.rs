//! FIXME: You must specify only ONE PageTable when using this crate.
#![allow(missing_docs)]

use crate::{
    chan::Chan,
    error::{Error, Result},
    utils::{round_down, round_up},
};
use ::alloc::{alloc, boxed::Box, sync::Arc, vec::Vec};
use core::{
    alloc::Layout,
    cell::UnsafeCell,
    cmp::{max, min},
    intrinsics::copy_nonoverlapping,
    ops::Range,
    ptr::{slice_from_raw_parts_mut, NonNull},
};
use intrusive_collections::{intrusive_adapter, Bound, KeyAdapter, RBTree, RBTreeLink, UnsafeRef};
use kalloc::guard::AllocGuard;
use ksched::sync::{Mutex, Spinlock, SpinlockGuard};

/// Page table.
pub trait PageTable: Sized {
    /// Request map to the page table will be always lower than USERTOP.
    /// This must be page aligned.
    const USERTOP: usize;

    /// Layout used to alloc and dealloc physical pages from global allocator.
    const PAGE_LAYOUT: Layout;

    /// Page size derived from [PAGE_LAYOUT]. Donot overwrite this.
    const PAGE_SIZE: usize = Self::PAGE_LAYOUT.size();

    /// Create a new page table.
    fn new() -> Result<Self>;

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
    fn map(&mut self, va: usize, vpa: usize) -> Result<()>;

    /// Unmap the pages in `[va, va+PAGE_SIZE)` in this page table.
    ///
    /// Returns false if there is no such page. It's guaranteed that `va` is page-aligned.
    fn unmap(&mut self, va: usize) -> bool;

    /// Protect the page in `[va, va+PAGE_SIZE)` as read-only or read-write.
    ///
    /// It's guaranteed that `va` is page-aligned.
    fn protect(&mut self, va: usize, read_only: bool);
}

#[derive(Debug)]
struct Page {
    /// Pointer to the physical page.
    ptr: NonNull<u8>,
    /// Array of distinct segments that map this page.
    ///
    /// The length of the array represents the refcnt. In `anon` if refcnt is greater than 1,
    /// all corresponding mappings must be marked as read-only.
    ///
    /// Why not array of address space? Because different segments of an address space
    /// may map to the same pages.
    owner: Spinlock<Vec<UnsafeRef<VmSegment>>>,
}

impl Page {
    /// Return true iff
    /// - `from` is one of the owners.
    /// - `to` is not one of the owners or is equal to `from`.
    ///
    /// Note that calling `change_owner` with `from` equal to `to` can be used to verify an owner.
    fn change_owner(&self, from: &VmSegment, to: &VmSegment) -> bool {
        let mut owner = self.owner.lock();
        let (mut some_from_idx, mut some_to_idx) = (None, None);
        for (i, seg) in owner.iter().enumerate() {
            let seg_ptr = seg.as_ref() as *const _;
            if seg_ptr == from {
                some_from_idx = Some(i);
            }
            if seg_ptr == to {
                some_to_idx = Some(i);
            }
        }
        if let Some(i) = some_from_idx {
            if some_to_idx.is_none() {
                owner[i] = unsafe { UnsafeRef::from_raw(to) };
                true
            } else {
                to as *const _ == from
            }
        } else {
            false
        }
    }

    fn owned_by(&self, target: &VmSegment) -> bool {
        self.change_owner(target, target)
    }

    /// Caller must guarantee that target is not the owner.
    fn add_owner(&self, target: &VmSegment) -> Result<usize> {
        let mut owner = self.owner.lock();
        debug_assert_eq!(
            owner
                .iter()
                .find(|seg| seg.as_ref() as *const _ == target)
                .is_some(),
            false
        );

        owner.try_reserve(1)?;
        owner.push(unsafe { UnsafeRef::from_raw(target) });
        Ok(owner.len())
    }

    /// Remove target owner and return the new number of owners.
    fn remove_owner(&self, target: &VmSegment) -> Option<usize> {
        let mut owner = self.owner.lock();
        Self::remove_owner_guarded(&mut owner, target)
    }

    fn remove_owner_guarded(
        owner: &mut SpinlockGuard<Vec<UnsafeRef<VmSegment>>>,
        target: &VmSegment,
    ) -> Option<usize> {
        let some_idx = owner.iter().enumerate().find_map(|(i, seg)| {
            if seg.as_ref() as *const _ == target {
                Some(i)
            } else {
                None
            }
        });
        some_idx.map(|i| {
            owner.swap_remove(i);
            owner.len()
        })
    }
}

unsafe impl Sync for Page {}
unsafe impl Send for Page {}

#[derive(Debug)]
pub struct VmObjectEntry {
    /// Key, the offset (in number of pages) in this object.
    pgid: usize,
    /// Value.
    page: Page,
    link: RBTreeLink,
}

intrusive_adapter!(pub VmObjectEntryAdapter = Box<VmObjectEntry>: VmObjectEntry { link: RBTreeLink });

impl<'a> KeyAdapter<'a> for VmObjectEntryAdapter {
    type Key = usize;
    fn get_key(&self, ent: &'a VmObjectEntry) -> Self::Key {
        ent.pgid
    }
}

#[derive(Debug, Default)]
pub(crate) struct VmObject {
    /// Maps from page index (key) to resident page (value). See [VmObjectEntry].
    pgmap: Mutex<RBTree<VmObjectEntryAdapter>>,
}

impl VmObject {
    pub(crate) fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
struct VmSegment {
    /// Inner mutable data.
    inner: UnsafeCell<VmSegmentInner>,
    /// Pointer to backing object.
    chan: Arc<Chan>,
    /// Segments are linked by a RB-tree in their [`VmSpace`].
    link: RBTreeLink,
}

unsafe impl Send for VmSegment {}
unsafe impl Sync for VmSegment {}

intrusive_adapter!(VmSegmentAdapter= Box<VmSegment>: VmSegment { link: RBTreeLink } );

impl<'a> KeyAdapter<'a> for VmSegmentAdapter {
    type Key = usize;
    fn get_key(&self, seg: &'a VmSegment) -> Self::Key {
        unsafe { &*seg.inner.get() }.va.start
    }
}

#[derive(Debug)]
struct VmSegmentInner {
    /// Range of virtual memory of this segment.
    va: Range<usize>,
    /// Offset (in pages) in the backing file.
    pgoff: usize,
    /// Array of anonymous page entries.
    ///
    /// If empty, the segment is a copy-on-write mapping and all changes made to data
    /// in the mapping should be done in anonymous memory. Otherwise, the segment is a shared
    /// mapping and all changes should be made directly to the underlying object.
    anon: Vec<Option<UnsafeRef<Page>>>,
}

impl VmSegment {
    fn new(
        va: Range<usize>,
        pgoff: usize,
        anon: Vec<Option<UnsafeRef<Page>>>,
        chan: Arc<Chan>,
    ) -> Self {
        Self {
            inner: UnsafeCell::new(VmSegmentInner { va, pgoff, anon }),
            chan,
            link: RBTreeLink::new(),
        }
    }

    fn is_shared(&self) -> bool {
        unsafe { &*self.inner.get() }.anon.is_empty()
    }

    /// Split the segment of [start, end) into [start, va) and [va, end).
    ///
    /// This function is atomic. Return the new segment of [va, end).
    async fn split_from<P: PageTable>(&self, va: usize) -> Result<Box<Self>> {
        let old_seg = unsafe { &mut *self.inner.get() };
        let old_va = &mut old_seg.va;

        debug_assert_eq!(va & P::PAGE_SIZE, 0);
        debug_assert!(old_va.start < va && va < old_va.end);

        let old_npages = (va - old_va.start) / P::PAGE_SIZE;
        let new_npages = (old_va.end - va) / P::PAGE_SIZE;
        let new_pgoff = old_seg.pgoff + old_npages;
        let new_seg_box = Box::try_new(VmSegment::new(
            va..old_va.end,
            new_pgoff,
            Vec::new(),
            self.chan.dup(),
        ))?;
        if self.is_shared() {
            let pgmap = self.chan.vmobj.pgmap.lock().await;
            let cur = pgmap.lower_bound(Bound::Included(&new_pgoff));
            while let Some(ent) = cur.get() {
                if ent.pgid >= new_pgoff + new_npages {
                    break;
                }
                ent.page.change_owner(self, &new_seg_box);
            }
        } else {
            let old_anon = &mut old_seg.anon;
            let new_anon = &mut unsafe { &mut *new_seg_box.inner.get() }.anon;
            new_anon.try_reserve(new_npages)?;
            debug_assert_eq!(new_npages + old_npages, old_anon.len());
            for some_page in &mut old_anon[old_npages..] {
                new_anon.push(some_page.take().map(|page| {
                    page.change_owner(self, &new_seg_box);
                    page
                }))
            }
            old_anon.truncate(old_npages);
            old_va.end = va;
        }
        Ok(new_seg_box)
    }

    /// Unmap the region of target_va in this segemnt.
    ///
    /// For shared segment, pages will be flushed back to the backing object.
    /// Return true if some of the pages are failed to flushed back.
    ///
    /// For private segment, pages are dropped and cannot be retrieved after that.
    /// Always return false.
    ///
    /// Note that the `va` and `anon` are not maintained. For example, you still need to
    /// truncate the size and redistribute the anon slots.
    async fn unmap1<P: PageTable>(&self, pgdir: &mut P, target_va: Range<usize>) -> bool {
        let seg = unsafe { &mut *self.inner.get() };
        debug_assert!(seg.va.start <= target_va.start && target_va.end <= seg.va.end);
        let mut bad = false;
        if self.is_shared() {
            for va in target_va.step_by(P::PAGE_SIZE) {
                if !pgdir.unmap(va) {
                    continue;
                }
                let chan_pgid = seg.pgoff + (va - seg.va.start) / P::PAGE_SIZE;
                let mut pgmap = self.chan.vmobj.pgmap.lock().await;
                let mut cur = pgmap.find_mut(&chan_pgid);
                let ent = cur.get().unwrap();
                let left_owners = ent.page.remove_owner(self).unwrap();
                if left_owners == 0 {
                    // Flush page to the backing object.
                    let page_ptr = ent.page.ptr.as_ptr();
                    let page_buf = unsafe { &*slice_from_raw_parts_mut(page_ptr, P::PAGE_SIZE) };
                    let err = match self.chan.write(page_buf, chan_pgid * P::PAGE_SIZE).await {
                        Ok(cnt) => cnt != page_buf.len(),
                        Err(_) => true,
                    };
                    bad |= err;
                    cur.remove();
                    unsafe { alloc::dealloc(page_ptr, P::PAGE_LAYOUT) }
                }
            }
        } else {
            for va in target_va.step_by(P::PAGE_SIZE) {
                if !pgdir.unmap(va) {
                    continue;
                }
                let seg_pgidx = (va - seg.va.start) / P::PAGE_SIZE;
                // SAFETY: Since pgdir.unmap returns true.
                unsafe {
                    let page_ref = seg.anon[seg_pgidx].take().unwrap_unchecked();
                    let left_owners = page_ref.remove_owner(self).unwrap_unchecked();
                    if left_owners == 0 {
                        alloc::dealloc(page_ref.ptr.as_ptr(), P::PAGE_LAYOUT);
                        UnsafeRef::into_box(page_ref);
                    }
                }
            }
        }
        bad
    }

    async fn unmap_inner<P: PageTable>(
        &self,
        pgdir: &mut P,
        target_va: Range<usize>,
    ) -> Result<(Box<VmSegment>, bool)> {
        let seg = unsafe { &mut *self.inner.get() };
        debug_assert!(seg.va.start < target_va.start && target_va.end < seg.va.end);
        let new_seg = self.split_from::<P>(target_va.end).await?;
        let bad = self.unmap_edge(pgdir, target_va).await;
        Ok((new_seg, bad))
    }

    async fn unmap_edge<P: PageTable>(&self, pgdir: &mut P, target_va: Range<usize>) -> bool {
        let seg = unsafe { &mut *self.inner.get() };
        let bad = self.unmap1(pgdir, target_va.clone()).await;
        if target_va.start > seg.va.start {
            debug_assert!(target_va.end == seg.va.end);
            seg.va.end = target_va.end;
            if !self.is_shared() {
                debug_assert_eq!(seg.anon.len(), seg.va.len() / P::PAGE_SIZE);
                seg.anon
                    .truncate((target_va.start - seg.va.start) / P::PAGE_SIZE);
            }
        } else {
            debug_assert!(target_va.end < seg.va.end);
            let pgoff_diff = (target_va.end - seg.va.start) / P::PAGE_SIZE;
            // SAFETY: Order won't be changed since all segments are
            // non-overlapping and r is in [va.start, va.end).
            seg.va.start = target_va.end;
            seg.pgoff += pgoff_diff;
            if !self.is_shared() {
                let npages = seg.va.len() / P::PAGE_SIZE;
                for i in 0..npages {
                    seg.anon[i] = seg.anon[i + pgoff_diff].take();
                }
                seg.anon.truncate(npages);
            }
        }
        bad
    }

    async fn fetch<P: PageTable>(&self, pgdir: &mut P, va: usize) -> Result<&mut [u8]> {
        debug_assert_eq!(va % P::PAGE_SIZE, 0);
        let segi = unsafe { &mut *self.inner.get() };
        let seg_pgid = (va - segi.va.start) / P::PAGE_SIZE;
        let buf = if self.is_shared() {
            // Fault at a shared page in chan.
            let mut pgmap = self.chan.vmobj.pgmap.lock().await;
            let chan_pgid = segi.pgoff + seg_pgid;
            if let Some(ent) = pgmap.find(&chan_pgid).get() {
                if ent.page.owned_by(self) {
                    pgdir.protect(va, false);
                } else {
                    ent.page.add_owner(self)?;
                    pgdir.map(va, ent.page.ptr.as_ptr() as usize).map_err(|e| {
                        ent.page.remove_owner(self).unwrap();
                        e
                    })?;
                }
                unsafe { &mut *slice_from_raw_parts_mut(ent.page.ptr.as_ptr(), P::PAGE_SIZE) }
            } else {
                let guard = AllocGuard::new(P::PAGE_LAYOUT)?;
                let ent = Box::try_new(VmObjectEntry {
                    pgid: chan_pgid,
                    page: Page {
                        ptr: guard.ptr(),
                        owner: Spinlock::new(Vec::new()),
                    },
                    link: RBTreeLink::new(),
                })?;
                let page_buf =
                    unsafe { &mut *slice_from_raw_parts_mut(guard.ptr().as_ptr(), P::PAGE_SIZE) };
                let cnt = self.chan.read(page_buf, segi.pgoff * P::PAGE_SIZE).await?;
                if cnt != P::PAGE_SIZE {
                    return Err(Error::InternalError("read page from chan failed"));
                }
                ent.page.add_owner(self)?;
                pgdir.map(va, guard.ptr().as_ptr() as usize)?;
                // Since it's a new page, no need to remove the owner when failed.
                pgmap.insert(ent);
                guard.consume();
                page_buf
            }
        } else {
            debug_assert!(seg_pgid < segi.anon.len());
            let some_page = if let Some(page) = &mut segi.anon[seg_pgid] {
                // Fault at a copy-on-write page.
                debug_assert!(page.owned_by(self));
                let mut owner = page.owner.lock();
                if owner.len() == 1 {
                    pgdir.protect(va, false);
                    None
                } else {
                    let guard = AllocGuard::new(P::PAGE_LAYOUT)?;
                    let new_page = Box::try_new(Page {
                        ptr: guard.ptr(),
                        owner: Spinlock::new(Vec::new()),
                    })?;
                    new_page.add_owner(self)?;
                    pgdir.map(va, guard.ptr().as_ptr() as usize)?;
                    Page::remove_owner_guarded(&mut owner, self);
                    unsafe {
                        copy_nonoverlapping(
                            new_page.ptr.as_ptr(),
                            guard.ptr().as_mut(),
                            P::PAGE_SIZE,
                        )
                    }
                    guard.consume();
                    Some(UnsafeRef::from_box(new_page))
                }
            } else {
                // Fault at a unfetched private page.
                let guard = AllocGuard::new(P::PAGE_LAYOUT)?;
                let page = Box::try_new(Page {
                    ptr: guard.ptr(),
                    owner: Spinlock::new(Vec::new()),
                })?;
                page.add_owner(self)?;
                let page_buf =
                    unsafe { &mut *slice_from_raw_parts_mut(guard.ptr().as_ptr(), P::PAGE_SIZE) };
                let cnt = self.chan.read(page_buf, segi.pgoff * P::PAGE_SIZE).await?;
                if cnt != P::PAGE_SIZE {
                    return Err(Error::InternalError("read page from chan failed"));
                }
                pgdir.map(va, guard.ptr().as_ptr() as usize)?;
                guard.consume();
                Some(UnsafeRef::from_box(page))
            };
            if let Some(page) = some_page {
                segi.anon[seg_pgid] = Some(page);
            }
            unsafe {
                &mut *slice_from_raw_parts_mut(
                    segi.anon[seg_pgid].as_ref().unwrap().ptr.as_ptr(),
                    P::PAGE_SIZE,
                )
            }
        };
        Ok(buf)
    }
}

/// Virtual memory address space.
pub struct VmSpace<P: PageTable> {
    pgdir: P,
    segments: RBTree<VmSegmentAdapter>,
}

/// Type of fault in the address space.
pub enum VmFaultKind {
    /// A read from then memory causes the fault.
    ReadFault,
    /// A write to the memory causes the fault.
    WriteFault,
}

impl<P: PageTable> VmSpace<P> {
    /// Create a new address space.
    pub fn new() -> Result<Self> {
        Ok(Self {
            pgdir: P::new()?,
            segments: RBTree::new(VmSegmentAdapter::new()),
        })
    }

    // Check if segments are still non-overlapping after adding the new segment with range `va`.
    pub fn check_overlap(&self, va: Range<usize>) -> Result<()> {
        let cur = self.segments.lower_bound(Bound::Excluded(&va.start));
        let mut overlap = false;
        if let Some(seg) = cur.get() {
            let seg = unsafe { &*seg.inner.get() };
            if va.end > seg.va.start {
                overlap = true;
            }
        };
        if let Some(seg) = cur.peek_prev().get() {
            let seg = unsafe { &*seg.inner.get() };
            if seg.va.end > va.start {
                overlap = true;
            }
        }
        if overlap {
            Err(Error::Conflict("mmap segment overlap"))
        } else {
            Ok(())
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
        &mut self,
        addr: usize,
        len: usize,
        chan: &Arc<Chan>,
        offset: usize,
        anonymous: bool,
    ) -> Result<()> {
        if len == 0 || addr.checked_add(len).is_none() || addr + len >= P::USERTOP {
            return Err(Error::BadRequest("mmap invalid va range"));
        } else if addr % P::PAGE_SIZE != 0 || len % P::PAGE_SIZE != 0 || offset % P::PAGE_SIZE != 0
        {
            return Err(Error::BadRequest("mmap va misaligned"));
        }
        let va = addr..addr + len;
        self.check_overlap(va.clone())?;
        let mut anon = Vec::new();
        if anonymous {
            let npages = len / P::PAGE_SIZE;
            anon.try_reserve(npages)?;
            anon.resize(npages, None);
        }
        self.segments.insert(Box::try_new(VmSegment::new(
            va,
            offset / P::PAGE_SIZE,
            anon,
            chan.clone(),
        ))?);
        Ok(())
    }

    /// Unmap a continugous chunk of memory.
    ///
    /// All pages containing a part of the indicated range [addr, addr + len) are unmapped.
    ///
    /// Note that when the chunk of memory to unmap is included by exactly one segment,
    /// we need to split it and add a new segment. In other cases, we can just reuse the old
    /// segments by modifying their keys and anon.
    ///
    /// This is atomic. Return error if unmap failed. Otherwise, all mappings are guaranteed to
    /// be unmapped and the return value indicates whether there are any error when flushing
    /// to the backing objects. See also [`VmSegment::unmap`].
    pub async fn munmap(&mut self, addr: usize, len: usize) -> Result<bool> {
        if addr.checked_add(len).is_none() || addr + len >= P::USERTOP {
            return Err(Error::BadRequest("mmap invalid va range"));
        }
        let target_va = round_down(addr, P::PAGE_SIZE)..round_up(addr + len, P::PAGE_SIZE);
        let mut cur = self
            .segments
            .upper_bound_mut(Bound::Included(&target_va.start));

        if let Some(seg) = cur.get() {
            let seg_va = &unsafe { &*seg.inner.get() }.va;
            if seg_va.end <= target_va.start {
                cur.move_next();
            }
        } else {
            cur.move_next();
        }

        if let Some(seg) = cur.get() {
            let seg_va = &unsafe { &*seg.inner.get() }.va;
            if seg_va.start < target_va.start && target_va.end < seg_va.end {
                let (new_seg, bad) = seg.unmap_inner(&mut self.pgdir, target_va).await?;
                self.segments.insert(new_seg);
                return Ok(bad);
            }
        }

        let mut bad = false;
        while let Some(seg) = cur.get() {
            let segi = unsafe { &mut *seg.inner.get() };
            if segi.va.start <= target_va.end {
                break;
            }
            let l = max(segi.va.start, target_va.start);
            let r = min(segi.va.end, target_va.end);
            bad |= seg.unmap_edge(&mut self.pgdir, l..r).await;
            if (l..r) == segi.va {
                // SAFETY: By loop condition.
                let seg = unsafe { cur.remove().unwrap_unchecked() };
                seg.chan.close().await;
            } else {
                cur.move_next();
            }
        }
        Ok(bad)
    }

    async fn fork1(&mut self, new_vm: &mut VmSpace<P>) -> Result<()> {
        for seg in self.segments.iter() {
            let segi = unsafe { &mut *seg.inner.get() };
            let new_seg = Box::try_new(VmSegment::new(
                segi.va.clone(),
                segi.pgoff,
                Vec::new(),
                seg.chan.dup(),
            ))?;
            let new_seg_ref = unsafe { UnsafeRef::from_raw(new_seg.as_ref() as *const _) };
            new_vm.segments.insert(new_seg);
            if !seg.is_shared() {
                let new_anon = unsafe { &mut (*seg.inner.get()).anon };
                new_anon.try_reserve(segi.anon.len())?;
                let mut va = segi.va.start;
                for some_page in segi.anon.iter() {
                    if let Some(page) = some_page {
                        let new_owners = page.add_owner(&new_seg_ref)?;
                        if let Err(e) = new_vm.pgdir.map(va, page.ptr.as_ptr() as usize) {
                            page.remove_owner(&new_seg_ref).unwrap();
                            return Err(e);
                        }
                        new_vm.pgdir.protect(va, true);
                        if new_owners == 2 {
                            self.pgdir.protect(va, true);
                        }
                        new_anon.push(Some(page.clone()));
                    } else {
                        new_anon.push(None);
                    }
                    va += P::PAGE_SIZE;
                }
            }
        }
        Ok(())
    }

    /// Fork an address space.
    ///
    /// For example, it may be called when forking a process.
    pub async fn fork(&mut self) -> Result<VmSpace<P>> {
        let mut new_vm = Self::new()?;
        if let Err(e) = self.fork1(&mut new_vm).await {
            new_vm.free().await;
            Err(e)
        } else {
            Ok(new_vm)
        }
    }

    /// Page fault handler at virtual address `va`.
    ///
    /// Faults can be divided into following cases:
    /// 1. Fault at a shared page in chan.
    ///    It may happen when the page is newly mapped shared but not yet referred.
    /// 2. Fault at a copy-on-write private page.
    ///    When the private page is forked, corresponding page table entries will be marked as
    ///    read-only. Thus, for example, this kind of fault will happend when the child process
    ///    is trying to modify this page.
    /// 3. Fault at a unfetched private page.
    ///    It may happen when the page is newly mapped private but not yet referred.
    ///
    /// If it returns ok, the address space will have read/write permission to the page containing
    /// virtual address `va`. That means the kernel can safely read or write to the page (after
    /// switching to it) without page fault.
    pub async fn fault(&mut self, va: usize) -> Result<()> {
        let va = round_down(va, P::PAGE_SIZE);
        let cur = self.segments.upper_bound_mut(Bound::Included(&va));
        if let Some(seg) = cur.get() {
            let segi = unsafe { &*seg.inner.get() };
            if va < segi.va.end {
                return seg.fetch(&mut self.pgdir, va).await.map(|_| {});
            }
        }
        Err(Error::SegmentFault)
    }

    /// Unmap all segments and drop this address space.
    ///
    /// Note that this dosen't gurantee all dirty pages are successfully flushed
    /// to their backing object.
    pub async fn free(mut self) {
        self.munmap(0, P::USERTOP).await.unwrap();
    }

    /// Read data in memory area [offset, offset + buf.len) from this address space.
    pub async fn read(&mut self, mut buf: &mut [u8], mut offset: usize) -> Result<()> {
        if offset.checked_add(buf.len()).is_none() || offset + buf.len() >= P::USERTOP {
            return Err(Error::BadRequest("vm read"));
        }
        let mut cur = self.segments.upper_bound(Bound::Included(&offset));
        let end = offset + buf.len();
        while let Some(seg) = cur.get() {
            let segi = unsafe { &*seg.inner.get() };
            if offset < segi.va.start || buf.is_empty() {
                break;
            }
            let l = round_down(offset, P::PAGE_SIZE);
            let r = min(end, segi.va.end);
            for va in (l..r).step_by(P::PAGE_SIZE) {
                let page_buf = seg.fetch(&mut self.pgdir, va).await?;
                let page_off = offset - va;
                let cnt = min(end, va + P::PAGE_SIZE) - max(offset, va);
                buf[..cnt].copy_from_slice(&page_buf[page_off..page_off + cnt]);
                buf = &mut buf[cnt..];
                offset += cnt;
            }
            cur.move_next();
        }
        if buf.is_empty() {
            Ok(())
        } else {
            Err(Error::Forbidden("vm read"))
        }
    }

    /// Write data from buffer to memory area [offset, offset + buf.len) of this address space.
    pub async fn write(&mut self, mut buf: &[u8], mut offset: usize) -> Result<()> {
        if offset.checked_add(buf.len()).is_none() || offset + buf.len() >= P::USERTOP {
            return Err(Error::BadRequest("vm write"));
        }
        let mut cur = self.segments.upper_bound(Bound::Included(&offset));
        let end = offset + buf.len();
        while let Some(seg) = cur.get() {
            let segi = unsafe { &*seg.inner.get() };
            if offset < segi.va.start || buf.is_empty() {
                break;
            }
            let l = round_down(offset, P::PAGE_SIZE);
            let r = min(end, segi.va.end);
            for va in (l..r).step_by(P::PAGE_SIZE) {
                let page_buf = seg.fetch(&mut self.pgdir, va).await?;
                let page_off = offset - va;
                let cnt = min(end, va + P::PAGE_SIZE) - max(offset, va);
                page_buf[page_off..page_off + cnt].copy_from_slice(&buf[..cnt]);
                buf = &buf[cnt..];
                offset += cnt;
            }
            cur.move_next();
        }
        if buf.is_empty() {
            Ok(())
        } else {
            Err(Error::Forbidden("vm write"))
        }
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
