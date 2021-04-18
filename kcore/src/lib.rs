//! Kernel building blocks.

#![deny(missing_docs)]
#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(const_fn)]
#![feature(box_into_pin)]
#![feature(generators, generator_trait)]

extern crate alloc;

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

pub mod chan;
pub mod dev;
pub mod error;
pub mod mnt;
pub mod utils;
pub mod vecque;
pub mod vm;
pub use async_trait::async_trait_try;
