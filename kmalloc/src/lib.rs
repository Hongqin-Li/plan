//! # Bare-metal memory allocator for kernel development.
#![deny(missing_docs)]
#![no_std]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

mod buddy;
mod list;

pub use buddy::Allocator;
