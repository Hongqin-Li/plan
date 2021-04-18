//! Simple util funtions.

use core::{alloc::AllocError, hash::Hash, mem::swap, ops::Range};

use crate::error::{Error, Result};
use alloc::{
    collections::{TryReserveError, VecDeque},
    sync::Arc,
    vec::Vec,
};
use hashbrown::HashMap;

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

/// OOM Wrapper to push back an element into a vector. Amortized O(1).
pub fn vec_push<T>(v: &mut Vec<T>, x: T) -> Result<()> {
    v.try_reserve(1)?;
    v.push(x);
    Ok(())
}

/// OOM Wrapper to shrink a vector. O(N).
pub fn vec_shrink_to_fit<T>(v: &mut Vec<T>) -> Result<()> {
    let mut nv = Vec::new();
    nv.try_reserve(v.len())?;
    while let Some(x) = v.pop() {
        nv.push(x);
    }
    nv.reverse();
    swap(v, &mut nv);
    Ok(())
}

/// OOM Wrapper to try creating an `Arc`.
pub fn arc_new<T>(x: T) -> Result<Arc<T>> {
    Arc::try_new(x).map_err(|_| Error::OutOfMemory)
}

/// OOM Wrapper to push front an element to a deque.
pub fn deque_push_front<T>(v: &mut VecDeque<T>, x: T) -> Result<()> {
    v.try_reserve(1)?;
    v.push_front(x);
    Ok(())
}

/// OOM Wrapper to push back an element to a deque.
pub fn deque_push_back<T>(v: &mut VecDeque<T>, x: T) -> Result<()> {
    v.try_reserve(1)?;
    v.push_back(x);
    Ok(())
}

/// OOM Wrapper to insert key-valud pair to a hash map.
pub fn map_insert<K: Eq + Hash, V>(m: &mut HashMap<K, V>, k: K, v: V) -> Result<Option<V>> {
    m.try_reserve(1)?;
    Ok(m.insert(k, v))
}
