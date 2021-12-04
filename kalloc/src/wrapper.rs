//! OOM wrapper functions.

use core::hash::Hash;
use core::mem::swap;

pub use alloc::{
    alloc::AllocError,
    collections::{TryReserveError, VecDeque},
    string::String,
    vec::Vec,
};
pub use hashbrown::HashMap;

/// Map [TryReserveError] to [AllocError] for consistency.
pub fn r2a<T>(r: Result<T, TryReserveError>) -> Result<T, AllocError> {
    r.map_err(|_| AllocError)
}

/// OOM Wrapper to push back an element into a vector. Amortized O(1).
pub fn str_push<T>(s: &mut String, x: char) -> Result<(), AllocError> {
    r2a(s.try_reserve(1))?;
    s.push(x);
    Ok(())
}

/// OOM Wrapper to push back an element into a vector. Amortized O(1).
pub fn vec_push<T>(v: &mut Vec<T>, x: T) -> Result<(), AllocError> {
    r2a(v.try_reserve(1))?;
    v.push(x);
    Ok(())
}

/// OOM Wrapper to shrink a vector. O(N).
pub fn vec_shrink_to_fit<T>(v: &mut Vec<T>) -> Result<(), AllocError> {
    let mut nv = Vec::new();
    r2a(nv.try_reserve(v.len()))?;
    while let Some(x) = v.pop() {
        nv.push(x);
    }
    nv.reverse();
    swap(v, &mut nv);
    Ok(())
}

/// OOM Wrapper to push front an element to a deque.
pub fn deque_push_front<T>(v: &mut VecDeque<T>, x: T) -> Result<(), AllocError> {
    r2a(v.try_reserve(1))?;
    v.push_front(x);
    Ok(())
}

/// OOM Wrapper to push back an element to a deque.
pub fn deque_push_back<T>(v: &mut VecDeque<T>, x: T) -> Result<(), AllocError> {
    r2a(v.try_reserve(1))?;
    v.push_back(x);
    Ok(())
}

/// OOM Wrapper to insert key-valud pair to a hash map.
pub fn map_insert<K: Eq + Hash, V>(
    m: &mut HashMap<K, V>,
    k: K,
    v: V,
) -> Result<Option<V>, AllocError> {
    m.try_reserve(1).map_err(|_| AllocError)?;
    Ok(m.insert(k, v))
}
