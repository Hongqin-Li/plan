//! Asynchronous executor for kernel development.

#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(box_into_pin)]
#![feature(const_panic)]
#![feature(associated_type_bounds)]
#![feature(shrink_to)]
#![feature(const_fn_trait_bound)]
#![feature(new_uninit)]
#![feature(maybe_uninit_extra)]

#[cfg(test)]
#[macro_use]
extern crate std;

extern crate alloc;

mod condvar;
mod mutex;
mod priority_queue;
mod rwlock;
mod sleep_queue;

pub mod executor;
pub mod mpsc;
pub mod task;
pub mod time;

/// Synchronization primitives.
pub mod sync {
    pub use super::condvar::Condvar;
    pub use super::mpsc;
    pub use super::mutex::{Mutex, MutexGuard};
    pub use super::rwlock::{RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard};
    pub use spin::lock_api::{Mutex as Spinlock, MutexGuard as SpinlockGuard};
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn run_multi(ncpu: usize) {
        let mut threads = vec![];
        for _ in 0..ncpu {
            let t = std::thread::spawn(move || {
                task::run();
            });
            threads.push(t);
        }
        for thread in threads {
            thread.join().unwrap();
        }
    }
}
