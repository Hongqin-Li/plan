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
pub mod sched;
pub mod slpque;
pub mod yield_now;

pub mod sync {
    pub use super::condvar::Condvar;
    pub use super::mutex::{Mutex, MutexGuard};
}

pub mod task {
    pub use super::sched::{run, run_all, spawn};
    pub use super::yield_now::yield_now;
}
