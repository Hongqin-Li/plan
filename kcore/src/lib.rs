//! Kernel building blocks.

#![deny(missing_docs)]
#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(const_fn)]

extern crate alloc;

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

mod utils;
pub mod vm;
