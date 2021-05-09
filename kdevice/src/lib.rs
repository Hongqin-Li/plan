//! Device driver model and file systems.

#![deny(missing_docs)]
#![no_std]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(const_fn)]
#![feature(box_into_pin)]
#![feature(generators, generator_trait)]
#![feature(generic_associated_types)]
#![feature(assoc_char_funcs)]
#![feature(type_alias_impl_trait)]
#![feature(concat_idents)]
#![feature(option_unwrap_none)]

extern crate alloc;

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

pub mod cache;
pub mod fat;
pub mod log;
mod utils;
