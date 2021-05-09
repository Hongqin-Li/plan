//! Kernel building blocks.

#![deny(missing_docs)]
#![no_std]
#![feature(test)]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(const_fn)]
#![feature(box_into_pin)]
#![feature(generators, generator_trait)]
#![feature(dropck_eyepatch)]
#![feature(drain_filter)]
#![feature(async_closure)]
#![feature(type_alias_impl_trait)]
#![feature(generic_associated_types)]
#![feature(associated_type_defaults)]

extern crate alloc;

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
extern crate test;

pub mod chan;
pub mod dev;
pub mod error;
pub mod mnt;
pub mod utils;
pub mod vm;
pub use async_trait::async_trait_try;
pub use ksched;

#[cfg(test)]
mod tests {
    use ksched::task;

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
