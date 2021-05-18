#![feature(allocator_api)]
#![feature(try_reserve)]
#![feature(box_into_pin)]
#![feature(generators, generator_trait)]
#![feature(generic_associated_types)]
#![feature(type_alias_impl_trait)]
#![feature(concat_idents)]

extern crate alloc;

use core::ops::Range;

use ksched::task;
use rand::distributions::Alphanumeric;
use rand::{thread_rng, Rng};

pub mod fs;

pub fn rand_str(len: usize) -> String {
    thread_rng()
        .sample_iter(&Alphanumeric)
        .take(len)
        .map(char::from)
        .collect()
}

pub fn rand_int(range: Range<usize>) -> usize {
    let mut rng = rand::thread_rng();
    rng.gen_range(range)
}

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
