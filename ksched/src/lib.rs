#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

extern crate alloc;

pub mod condvar;
pub mod mutex;
pub mod slpque;
pub mod task;

pub mod sync {
    pub use super::condvar::Condvar;
    pub use super::mutex::{Mutex, MutexGuard};
}
