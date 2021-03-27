#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

extern crate alloc;


pub mod mutex;
pub mod sched;
pub mod yield_now;
