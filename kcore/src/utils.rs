//! Simple util funtions.

use alloc::{sync::Arc, vec::Vec};

/// Round down to the nearest multiple of n.
#[inline]
pub fn round_down(x: usize, n: usize) -> usize {
    x - (x % n)
}

/// Round up to the nearest multiple of n.
#[inline]
pub fn round_up(x: usize, n: usize) -> usize {
    round_down(x + n - 1, n)
}

/// Wrapper to push back an element into a vector.
pub fn vec_push<T>(v: &mut Vec<T>, x: T) -> Result<(), Error> {
    v.try_reserve(1).map_err(|_| Error::OutOfMemory)?;
    v.push(x);
    Ok(())
}

/// Wrapper to try creating an `Arc`.
pub fn arc_new<T>(x: T) -> Result<Arc<T>, Error> {
    Arc::try_new(x).map_err(|_| Error::OutOfMemory)
}

/// Kernel errors.
pub enum Error {
    /// When global allocator returns zero.
    OutOfMemory,
    /// When something not found.
    NotFound,
}
