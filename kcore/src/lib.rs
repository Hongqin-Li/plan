//! Kernel building blocks.
#![no_std]
#![feature(test)]
#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(box_into_pin)]
#![feature(generators, generator_trait)]
#![feature(dropck_eyepatch)]
#![feature(drain_filter)]
#![feature(async_closure)]
#![feature(type_alias_impl_trait)]
#![feature(generic_associated_types)]
#![feature(associated_type_defaults)]
#![feature(get_mut_unchecked)]
#![feature(new_uninit)]
#![feature(const_fn_fn_ptr_basics)]
#![feature(const_mut_refs)]
#![feature(const_fn_trait_bound)]
#![feature(bool_to_option)]
#![feature(option_result_unwrap_unchecked)]
#![feature(const_evaluatable_checked)]
#![feature(const_generics)]
#![feature(slice_ptr_get)]

// So that we can use std when testing.
#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
extern crate test;

extern crate alloc;

pub mod chan;
pub mod dev;
pub mod error;
// pub mod pager;
pub mod utils;
// pub mod vm;
pub use async_trait;
pub use ksched;

#[cfg(test)]
pub mod tests {
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
