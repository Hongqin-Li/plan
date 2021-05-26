//! # Bare-metal memory allocator for kernel development.
#![deny(missing_docs)]
#![no_std]
#![feature(associated_type_defaults)]
#![feature(allocator_api)]
#![feature(dropck_eyepatch)]
#![feature(try_reserve)]
#![feature(const_fn_trait_bound)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

extern crate alloc;

mod rawlist;

pub mod buddy;
pub mod cached;
pub mod list;
pub mod vecque;
pub mod wrapper;

pub use cached::Allocator;
pub use typenum::consts;

use core::{alloc::Layout, cmp::max};

#[inline]
fn to_order(pgsize: usize, layout: &Layout) -> usize {
    debug_assert!(pgsize.is_power_of_two());
    debug_assert!(layout.align().is_power_of_two());
    let npage = (max(layout.size().next_power_of_two(), layout.align()) + pgsize - 1) / pgsize;
    npage.trailing_zeros() as usize
}
