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
pub fn intersect(a: &Range<usize>, b: &Range<usize>) -> bool {
    a.start < b.end && a.end > b.start
}
