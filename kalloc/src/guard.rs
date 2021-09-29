//! Smart pointer guard.
use alloc::alloc;
use core::{
    alloc::{AllocError, Layout},
    mem,
    ptr::{slice_from_raw_parts, slice_from_raw_parts_mut, NonNull},
};

/// Smart pointer guard.
pub struct AllocGuard {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl AllocGuard {
    /// Create a new smart pointer.
    pub fn new(layout: Layout) -> Result<Self, AllocError> {
        unsafe {
            NonNull::new(alloc::alloc(layout))
                .map_or(Err(AllocError), |ptr| Ok(Self::from_ptr(ptr, layout)))
        }
    }

    /// Get the pointer inside.
    pub fn ptr(&self) -> NonNull<u8> {
        self.ptr.clone()
    }

    /// Extract the slice.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { &*slice_from_raw_parts(self.ptr.as_ptr() as *const _, self.layout.size()) }
    }

    /// Extract the mutable slice.
    pub fn as_mut_slice(&self) -> &mut [u8] {
        unsafe { &mut *slice_from_raw_parts_mut(self.ptr.as_ptr(), self.layout.size()) }
    }

    /// Drop and don't deallocate the pointer.
    ///
    /// Often called when the ownership of the pointer is transfered.
    pub fn consume(self) {
        mem::forget(self)
    }

    /// Create a new smart pointer from raw pointer.
    ///
    /// SAFETY: You must guarantee that
    /// - `ptr` and `layout `are valid.
    /// - [consume] is called before anyone uses `ptr`.
    pub unsafe fn from_ptr(ptr: NonNull<u8>, layout: Layout) -> Self {
        Self { ptr, layout }
    }
}

impl Drop for AllocGuard {
    fn drop(&mut self) {
        unsafe { alloc::dealloc(self.ptr.as_ptr(), self.layout) }
    }
}

unsafe impl Sync for AllocGuard {}
unsafe impl Send for AllocGuard {}
