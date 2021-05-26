//! Asynchronous executor for kernel development.
#![no_std]
#![deny(missing_docs)]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(box_into_pin)]
#![feature(const_panic)]
#![feature(const_generics)]
#![feature(associated_type_bounds)]
#![feature(shrink_to)]
#![feature(const_fn_trait_bound)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

extern crate alloc;

pub mod mpsc;
pub mod prique;
pub mod task;
pub mod time;

mod condvar;
mod mutex;
mod rwlock;
mod slpque;
mod spinlock;

/// Synchronization primitives.
pub mod sync {
    pub use super::condvar::Condvar;
    pub use super::mpsc;
    pub use super::mutex::{Mutex, MutexGuard};
    pub use super::rwlock::{RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard};
    pub use super::spinlock::{Spinlock, SpinlockGuard};
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn run_multi(ncpu: usize) {
        let mut threads = vec![];
        for _ in 0..ncpu {
            let t = std::thread::spawn(move || {
                task::run_all();
            });
            threads.push(t);
        }
        for thread in threads {
            thread.join().unwrap();
        }
    }
}
