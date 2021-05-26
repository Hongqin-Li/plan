//! Device driver model and file systems.

#![deny(missing_docs)]
#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(box_into_pin)]
#![feature(generators, generator_trait)]
#![feature(generic_associated_types)]
#![feature(type_alias_impl_trait)]
#![feature(concat_idents)]
#![feature(new_uninit)]
#![feature(const_fn_trait_bound)]
#![feature(min_type_alias_impl_trait)]

extern crate alloc;

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

pub mod cache;
pub mod log;

pub mod block;
pub mod fat;
pub mod root;

mod utils;
