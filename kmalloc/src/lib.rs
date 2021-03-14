//! # Bare-metal memory allocator for kernel development.
#![deny(missing_docs)]
#![no_std]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

pub mod buddy;
mod freelist;
mod list;
