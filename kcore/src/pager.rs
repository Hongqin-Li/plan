//! Pager
//!
//! Each in-memory page must have at least one owner. Note that the existence of a page doesn't
//! mean the physical page it owns exists. In fact, Depending on whether its pointer is null or
//! not, it can be either stored in the underlying chan or paged in. Page won't be mapped in any
//! page table if its pointer is null. If its pointer is non-null, the page may or may not be
//! mapped in some page table.
//!
//! To keep track of all pages that can be swapped out, we maintain a global page lists. For any
//! page, it exists in the list iff its pointer is non-null, i.e., paged in.
use crate::{
    chan::{Chan, ChanWeak},
    error::{Error, Result},
    utils::{round_down, round_up},
    vm::{VmSegment, PAGE_LAYOUT, PAGE_SIZE},
};
use ::alloc::{
    alloc::{self, Global},
    boxed::Box,
    sync::{Arc, Weak},
    vec::Vec,
};
use core::{
    alloc::{Allocator, GlobalAlloc},
    cell::UnsafeCell,
    mem,
    ops::{Deref, DerefMut, Range},
    ptr::{self, null_mut, slice_from_raw_parts, slice_from_raw_parts_mut, NonNull},
    usize,
};
use intrusive_collections::{
    intrusive_adapter, Bound, KeyAdapter, LinkedList, LinkedListLink, RBTree, RBTreeLink, UnsafeRef,
};
use kalloc::{guard::AllocGuard, wrapper::vec_push};
use ksched::sync::{Condvar, Mutex, MutexGuard, RwLock, RwLockWriteGuard, Spinlock, SpinlockGuard};

intrusive_adapter!(PageListAdapter = Arc<Page>: Page { link_pglist: LinkedListLink });

pub(crate) static PAGE_LIST: Mutex<LinkedList<PageListAdapter>> =
    Mutex::new(LinkedList::new(PageListAdapter::new()));

async fn page_out(npages: &mut usize) {
    let mut page_list = PAGE_LIST.lock().await;
    let mut cur = page_list.front_mut();
    while *npages != 0 {
        let mut dropped = false;
        if let Some(page) = cur.get() {
            dropped = page.page_out().await.is_ok();
        } else {
            break;
        }
        if dropped {
            *npages -= 1;
            cur.remove();
        } else {
            cur.move_next();
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PageOwnerKind {
    ReadOnlyPrivateRef,
    ReadOnlyPrivateBack,
    ReadWritePrivateBack,
    ReadWriteSharedBack,
    ReadOnlySharedBack,
}

#[derive(Debug)]
pub struct PageOwnerInner {
    pub kind: PageOwnerKind,
    pub seg: UnsafeRef<VmSegment>,
    /// If is some, it indicates the virtual address mapped in the owner's address space.
    pub va: Option<usize>,
}

#[derive(Debug)]
pub struct PageOwner {
    /// If is none, it means locked by its owner. That's, the segment owner won't change its kind
    /// on this page.
    pub inner: Option<PageOwnerInner>,
    pub cvar: Condvar,
}

impl PageOwner {
    fn backing_chan(&self) -> &'_ Chan {
        match self.kind {
            PageOwnerKind::ReadOnlyPrivateRef => self.seg.ref_chan.as_ref().unwrap(),
            PageOwnerKind::ReadOnlyPrivateBack
            | PageOwnerKind::ReadWritePrivateBack
            | PageOwnerKind::ReadWriteSharedBack
            | PageOwnerKind::ReadOnlySharedBack => &self.seg.back_chan,
        }
    }

    fn try_unmap_page(&mut self) -> Result<()> {
        if let Some(va) = self.va {
            let locked = self.seg.vmspace.pgdir.try_write();
            let pgdir = locked.ok_or(Error::Conflict("lock"))?;
            pgdir.unmap(va);
            self.va = None;
        }
        Ok(())
    }

    fn need_flush_when_removed(&self) -> bool {
        self.kind == PageOwnerKind::ReadWriteSharedBack
            || self.kind == PageOwnerKind::ReadOnlySharedBack
    }

    async fn remove_from(self, page_entry: &PageMapEntry) -> bool {}
}

#[derive(Debug)]
/// Must be one of the following cases:
/// FIXME: seperate private and shared?
///
/// 1. Some ReadWriteSharedBack
/// 2. Some ReadOnlyPrivateRef/ReadOnlyPrivateBack/ReadOnlySharedBack
/// 3. One ReadWritePrivateBack
struct PageOwners(Vec<PageOwner>);

impl Deref for PageOwners {
    type Target = Vec<PageOwner>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for PageOwners {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl PageOwners {
    /// Return true iff
    /// - `from` is one of the owners.
    /// - `to` is not one of the owners or is equal to `from`.
    pub fn change_owner(&mut self, from: *const VmSegment, to: *const VmSegment) -> bool {
        let mut owners = self;
        let (mut some_from_idx, mut some_to_idx) = (None, None);
        for (i, owner) in owners.iter().enumerate() {
            let seg_ptr: *const VmSegment = owner.seg.as_ref();
            if seg_ptr == from {
                some_from_idx = Some(i);
            }
            if seg_ptr == to {
                some_to_idx = Some(i);
            }
        }
        if let Some(i) = some_from_idx {
            if some_to_idx.is_none() {
                owners[i].seg = unsafe { UnsafeRef::from_raw(to) };
                true
            } else {
                to as *const _ == from
            }
        } else {
            false
        }
    }

    pub fn owned_by(&self, seg: &VmSegment) -> Option<&'_ mut PageOwner> {
        let owners = self;
        for owner in owners.iter_mut() {
            if owner.seg.as_ref() as *const _ == seg {
                return Some(owner);
            }
        }
        None
    }

    /// Caller must guarantee that newly added segment is not the owner.
    pub fn add_owner(&mut self, seg: &VmSegment, kind: PageOwnerKind) -> Result<usize> {
        debug_assert_eq!(self.owned_by(seg).is_none(), true);
        let owners = self;
        let seg = unsafe { UnsafeRef::from_raw(seg) };
        let va = None;
        let new_owner = PageOwner { seg, kind, va };
        vec_push(&mut owners, new_owner)?;
        Ok(owners.len())
    }

    /// Remove target owner and return the new number of owners.
    pub fn remove_owner(&mut self, target: &VmSegment) -> Option<PageOwner> {
        let mut owners = self;
        let some_idx = owners.iter().enumerate().find_map(|(i, owner)| {
            if owner.seg.as_ref() as *const _ == target {
                Some(i)
            } else {
                None
            }
        });
        some_idx.map(|i| owners.swap_remove(i))
    }
}

#[derive(Debug)]
pub(crate) struct PageMapEntry {
    pub pgid: usize,
    pub page: Weak<Page>,
    pub owners: Spinlock<PageOwners>,
    pub link_pgmap: RBTreeLink,
    pub link_pggroup: LinkedListLink,
}

intrusive_adapter!(PageGroupAdapter = Arc<PageMapEntry>: PageMapEntry { link_pggroup: LinkedListLink });

intrusive_adapter!(PageMapAdapter = Arc<PageMapEntry>: PageMapEntry { link_pgmap: RBTreeLink });

impl<'a> KeyAdapter<'a> for PageMapAdapter {
    type Key = usize;
    fn get_key(&self, ent: &'a PageMapEntry) -> Self::Key {
        ent.pgid
    }
}

impl PageMapEntry {
    /// Return whether this page entry needs to be removed.
    async fn remove_owner(&self, seg: &VmSegment) -> bool {
        let mut remove_me = false;
        let mut owners = self.owners.lock().await;
        if let Some(this_owner) = owners.remove_owner(seg) {
            if let Some(va) = this_owner.va {
                let mut pgdir = this_owner.seg.vmspace.pgdir.write().await;
                pgdir.unmap(va);
            }
            if owners.is_empty() {
                let page = self.page.upgrade().unwrap();
                let mut page = page.lock().await;
                let fetched = page.ptr.is_some();
                let mut cur = unsafe { page.entries.cursor_mut_from_ptr(self) };
                let need_transfer =
                    !fetched && cur.peek_prev().get().is_none() && cur.peek_next().get().is_some();
                let need_flush = fetched && this_owner.need_flush_when_removed();
                cur.remove();
                let chan = this_owner.backing_chan();
                if need_transfer {
                    if page.page_in_by(chan, self.pgid).await.is_err() {
                        page.pincnt = -1;
                    }
                } else if need_flush {
                    // Ignore error.
                    page.flush_to(chan, self.pgid).await;
                }
                remove_me = true;
            }
        }
        remove_me
    }

    pub async fn free(&self) -> bool {
        todo!()
    }
}

#[derive(Debug, Default)]
pub(crate) struct PageMap(RBTree<PageMapAdapter>);

impl Deref for PageMap {
    type Target = RBTree<PageMapAdapter>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for PageMap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl PageMap {
    pub async fn new_page(
        &mut self,
        pgid: usize,
        seg: &VmSegment,
        kind: PageOwnerKind,
    ) -> Result<Arc<Page>> {
        let mut owners = PageOwners(Vec::new());
        owners.add_owner(seg, kind)?;
        let page = Arc::try_new(Page::default())?;
        let page_entry = Arc::try_new(PageMapEntry {
            pgid,
            page: Arc::downgrade(&page),
            owners: Mutex::new(owners),
            link_pgmap: RBTreeLink::new(),
            link_pggroup: LinkedListLink::new(),
        })?;
        self.insert(page_entry);
        Ok(page)
    }

    pub async fn change_owner(&self, pgids: Range<usize>, from: &VmSegment, to: &VmSegment) {
        let mut cur = self.lower_bound(Bound::Included(&pgids.start));
        while let Some(page_entry) = cur.get() {
            if page_entry.pgid >= pgids.end {
                break;
            }
            let mut owners = page_entry.owners.lock().await;
            owners.change_owner(from, to);
            cur.move_next();
        }
    }

    pub async fn remove_owner(&mut self, pgids: Range<usize>, seg: &VmSegment) {
        let mut cur = self.lower_bound_mut(Bound::Included(&pgids.start));
        while let Some(page_entry) = cur.get() {
            if page_entry.pgid >= pgids.end {
                break;
            }
            let remove_me = page_entry.remove_owner(seg).await;
            if remove_me {
                cur.remove();
            } else {
                cur.move_next();
            }
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct PageInner {
    /// Pointer to the physical page. None means that the page hasn't been fetched from the pager.
    pub ptr: Option<NonNull<u8>>,
    /// Number of owners that want this page not to be flushed. -1 means a bad page that cannot
    /// fetched from backing chan any more.
    pub pincnt: isize,
    pub chan: Option<Chan>,
    pub entries: LinkedList<PageGroupAdapter>,
}

unsafe impl Sync for PageInner {}
unsafe impl Send for PageInner {}

impl PageInner {
    /// Return whether we need to add it into the page list.
    pub async fn page_in(&mut self) -> Result<bool> {
        let first_entry = self.entries.front().clone_pointer().unwrap();
        let owners = first_entry.owners.lock().await;
        let chan = owners[0].backing_chan();
        self.page_in_by(chan, first_entry.pgid).await
    }

    pub async fn page_in_by(&mut self, chan: &Chan, pgid: usize) -> Result<bool> {
        if self.pincnt < 0 {
            return Err(Error::Gone("bad page"));
        }
        let mut add_to_pglist = false;
        if self.ptr.is_none() {
            let guard = AllocGuard::new(PAGE_LAYOUT)?;
            let cnt = chan.read(guard.as_mut_slice(), pgid * PAGE_SIZE).await?;
            if cnt != PAGE_SIZE {
                return Err(Error::InternalError("failed to page in"));
            }
            self.ptr = Some(guard.ptr());
            guard.consume();
            add_to_pglist = true;
        }
        Ok(add_to_pglist)
    }

    pub async fn flush_to(&self, chan: &Chan, pgid: usize) -> Result<()> {
        let cnt = chan.write(self.page_buf(), pgid * PAGE_SIZE).await?;
        if cnt != PAGE_SIZE {
            return Err(Error::InternalError("failed to flush page"));
        }
        Ok(())
    }

    pub fn free_page(&mut self) {
        unsafe { Global.deallocate(self.ptr.take().unwrap(), PAGE_LAYOUT) }
    }

    /// Return the backing chan page.
    fn try_unmap_from_owners(&mut self) -> Result<(Chan, usize)> {
        let mut backing_chan = None;
        let mut backing_pgid = 0;
        for page_entry in self.entries.iter() {
            let locked = page_entry.owners.try_lock();
            let mut owners = locked.ok_or(Error::Conflict("lock"))?;
            for owner in owners.iter_mut() {
                owner.try_unmap_page()?;
                if backing_chan.is_none() {
                    backing_chan = Some(owner.backing_chan().dup());
                    backing_pgid = page_entry.pgid;
                }
            }
        }
        Ok((backing_chan.unwrap(), backing_pgid))
    }

    /// FIXME: this is unsafecell.
    pub fn page_buf(&self) -> &[u8] {
        let ptr = self.ptr.unwrap().as_ptr();
        unsafe { &*slice_from_raw_parts(ptr as *const _, PAGE_SIZE) }
    }

    /// FIXME: this is unsafecell.
    pub fn page_buf_mut(&self) -> &mut [u8] {
        let ptr = self.ptr.unwrap().as_ptr();
        unsafe { &mut *slice_from_raw_parts_mut(ptr, PAGE_SIZE) }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Page {
    pub inner: Mutex<PageInner>,
    pub link_pglist: LinkedListLink,
}

impl Page {
    /// Flush the page to disk and unmap it from its owners' virtual memory.
    ///
    /// Return ok if paged out.
    pub async fn try_page_out(&self) -> Result<()> {
        let mut page = self.try_lock().ok_or(Error::Conflict("lock"))?;
        debug_assert!(page.ptr.is_some());

        let (backing_chan, backing_pgid) = page.try_unmap_from_owners()?;
        let buf = page.page_buf();
        let cnt = backing_chan.write(buf, backing_pgid * PAGE_SIZE).await?;
        if cnt != PAGE_SIZE {
            return Err(Error::InternalError("page out"));
        }
        page.free_page();
        Ok(())
    }
}

impl Deref for Page {
    type Target = Mutex<PageInner>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl Drop for Page {
    fn drop(&mut self) {
        if let Some(ptr) = self.inner.get_mut().ptr {
            unsafe { Global.deallocate(ptr, PAGE_LAYOUT) }
        }
    }
}

pub(crate) struct PageBufGuard(Arc<Page>, NonNull<u8>);

impl PageBufGuard {
    pub async fn lock<T>(page: Arc<Page>, guard_to_release: T) -> Result<PageBufGuard> {
        let mut pagei = page.lock().await;
        drop(guard_to_release);

        let add_to_pglist = pagei.page_in().await?;
        if add_to_pglist {
            PAGE_LIST.lock().await.push_back(page.clone());
        }

        let ptr = pagei.ptr.unwrap();
        mem::forget(pagei);
        Ok(Self(page, ptr))
    }
}

impl Deref for PageBufGuard {
    type Target = NonNull<u8>;
    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl Drop for PageBufGuard {
    fn drop(&mut self) {
        self.0.release();
    }
}
