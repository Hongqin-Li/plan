//! Asynchronous executor for kernel development.
#![no_std]
#![deny(missing_docs)]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(box_into_pin)]
#![feature(const_panic)]
#![feature(const_generics)]
#![feature(const_fn)]
#![feature(associated_type_bounds)]
#![feature(shrink_to)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

extern crate alloc;

pub mod condvar;
pub mod mutex;
pub mod prique;
pub mod rwlock;
pub mod slpque;
pub mod task;

/// Synchronization primitives.
pub mod sync {
    pub use super::condvar::Condvar;
    pub use super::mutex::{Mutex, MutexGuard};
    pub use super::rwlock::{RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard};
}
