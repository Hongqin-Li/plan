//! # Bare-metal memory allocator for kernel development.
#![deny(missing_docs)]
#![no_std]
#![feature(const_fn)]
#![feature(associated_type_defaults)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

pub mod buddy;
pub mod cached;
mod list;

use core::{alloc::Layout, cmp::max};

pub use buddy::Allocator;
pub use typenum::consts;

#[inline]
fn to_order(pgsize: usize, layout: &Layout) -> usize {
    debug_assert!(pgsize.is_power_of_two());
    debug_assert!(layout.align().is_power_of_two());
    let npage = (max(layout.size().next_power_of_two(), layout.align()) + pgsize - 1) / pgsize;
    npage.trailing_zeros() as usize
}
