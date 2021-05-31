#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use ::criterion::{black_box, Criterion};
use criterion_macro::criterion;

use core::{
    cmp::{max, min},
    ops::Range,
};
use std::sync::Arc;

use kcore::chan::Chan;
use kdevice::fat::FAT;
use ksched::task;
use ktest::*;

use tempfile::TempDir;

fn prepare_crud(
    ntask: usize,
    name_len: Range<usize>,
    data_len: Range<usize>,
    off: Range<usize>,
) -> TempDir {
    let (dir, img_path) = fs::gen_fat32img();

    let req = (0..ntask)
        .map(|i| {
            let name = format!("{}-{}", i, rand_str(rand_int(name_len.clone())));
            let data = rand_str(rand_int(data_len.clone()));
            let off = rand_int(off.clone());
            (name, data, off)
        })
        .collect();

    task::spawn(0, async move {
        let disk = Arc::new(fs::FileDisk::new(img_path));
        let disk_root = Chan::attach(disk, b"").await.unwrap();
        let fs = FAT::new(ntask + 10, 100, &disk_root).await.unwrap();
        disk_root.close().await;

        println!("{:?}", fs);
        ktest::fs::crud(fs, req).await;
    })
    .unwrap();

    dir
}

#[criterion(Criterion::default().sample_size(10))]
fn bench_crud_10mb(c: &mut Criterion) {
    c.bench_function("crud 10mb", |b| {
        let sz = black_box(10 * 1024 * 1024);
        let dir = prepare_crud(1, 2..5, sz..sz + 1, 0..1);
        b.iter(|| {
            task::run_all();
        });
        drop(dir);
    });
}
