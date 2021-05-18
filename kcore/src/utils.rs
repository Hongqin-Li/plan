//! Simple util funtions.

use core::{alloc::AllocError, hash::Hash, mem::swap, ops::Range};

use crate::error::{Error, Result};
use alloc::{
    collections::{TryReserveError, VecDeque},
    sync::Arc,
    vec::Vec,
};

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

/// Check if two ranges are intersect with each other.
#[inline]
pub fn intersect<T: Ord>(a: &Range<T>, b: &Range<T>) -> bool {
    a.start < b.end && a.end > b.start
}

/// Convert slice to uint.
#[macro_export]
macro_rules! from_bytes {
    ($type:ty, $slice:expr) => {
        <$type>::from_le_bytes($slice.try_into().unwrap())
    };
}
