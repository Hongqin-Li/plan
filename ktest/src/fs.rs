use crate::{rand_int, rand_str, run_multi};
use alloc::{sync::Arc, vec::Vec};
use core::{convert::TryInto, fmt, ops::Range};
use kcore::{
    chan::{Chan, ChanId, ChanKind},
    dev::Device,
    error::Result,
};
use ksched::{sync::Spinlock, task};
use std::{
    fs::{File, OpenOptions},
    io::SeekFrom,
    path::Path,
};
use std::{
    io::{Read, Seek, Write},
    path::PathBuf,
    process::Command,
};
use tempfile::{tempdir, TempDir};

use task::yield_now;

pub struct FileDisk {
    file: Spinlock<File>,
}
impl FileDisk {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            file: Spinlock::new(
                OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(path)
                    .unwrap(),
            ),
        }
    }
}

#[async_trait::async_trait_try]
impl Device for FileDisk {
    async fn shutdown(self)
    where
        Self: Sized,
    {
        todo!()
    }

    async fn attach(&self, aname: &[u8]) -> Result<ChanId>
    where
        Self: Sized,
    {
        Ok(ChanId {
            path: 0,
            version: 0,
            kind: ChanKind::File,
        })
    }

    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> kcore::error::Result<Option<ChanId>> {
        todo!()
    }

    async fn close(&self, c: ChanId) {
        println!("disk close");
    }

    async fn remove(&self, c: &ChanId) -> kcore::error::Result<bool> {
        todo!()
    }

    async fn stat(&self, c: &ChanId) -> kcore::error::Result<kcore::chan::Dirent> {
        todo!()
    }

    async fn wstat(&self, c: &ChanId, dirent: &kcore::chan::Dirent) -> kcore::error::Result<()> {
        todo!()
    }

    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> kcore::error::Result<usize> {
        //println!("read: sz {}, off {}", buf.len(), off);

        let mut g = self.file.lock();
        g.seek(SeekFrom::Start(off as u64)).unwrap();
        Ok(g.read(buf).unwrap())
    }

    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> kcore::error::Result<usize> {
        //println!("write: sz {}, off {}", buf.len(), off);
        let mut g = self.file.lock();
        g.seek(SeekFrom::Start(off as u64)).unwrap();
        Ok(g.write(buf).unwrap())
    }
    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        todo!()
    }
}

pub struct MemDisk {
    file: Spinlock<Vec<u8>>,
}
impl MemDisk {
    pub fn new(size: usize) -> Self {
        Self {
            file: Spinlock::new(vec![0; size]),
        }
    }
}

#[async_trait::async_trait_try]
impl Device for MemDisk {
    async fn shutdown(self)
    where
        Self: Sized,
    {
        todo!()
    }

    async fn attach(&self, aname: &[u8]) -> Result<ChanId>
    where
        Self: Sized,
    {
        Ok(ChanId {
            path: 0,
            version: 0,
            kind: ChanKind::File,
        })
    }

    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> kcore::error::Result<Option<ChanId>> {
        todo!()
    }

    async fn close(&self, c: ChanId) {
        println!("disk close");
    }

    async fn remove(&self, c: &ChanId) -> kcore::error::Result<bool> {
        todo!()
    }

    async fn stat(&self, c: &ChanId) -> kcore::error::Result<kcore::chan::Dirent> {
        todo!()
    }

    async fn wstat(&self, c: &ChanId, dirent: &kcore::chan::Dirent) -> kcore::error::Result<()> {
        todo!()
    }

    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> kcore::error::Result<usize> {
        let g = self.file.lock();
        buf.copy_from_slice(g[off..off + buf.len()].try_into().unwrap());
        Ok(buf.len())
    }

    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> kcore::error::Result<usize> {
        let mut g = self.file.lock();
        g[off..off + buf.len()].copy_from_slice(buf);
        Ok(buf.len())
    }

    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        todo!()
    }
}

pub fn gen_fat32img() -> (TempDir, PathBuf) {
    let dir = tempdir().unwrap();
    println!("path: {:?}", dir.path());
    let out = Command::new("pwd").output().unwrap();
    println!("stdout: {:?}", out);
    let img_path = dir.path().join("test.img");

    Command::new("touch")
        .arg("test.img")
        .current_dir(dir.path())
        .output()
        .unwrap();

    Command::new("dd")
        .arg("if=/dev/zero")
        .arg("of=test.img")
        .arg("seek=100000")
        .arg("bs=512")
        .arg("count=1")
        .current_dir(dir.path())
        .output()
        .unwrap();

    Command::new("mkfs.vfat")
        .arg("-F 32")
        .arg("test.img")
        .current_dir(dir.path())
        .output()
        .unwrap();

    Command::new("mcopy")
        .arg("-i")
        .arg(img_path.to_str().unwrap())
        .arg("src")
        .arg("::src")
        .output()
        .unwrap();

    (dir, img_path)
}

pub async fn crud<T: Device + fmt::Debug + Send + Sync + 'static>(
    fs: T,
    req: Vec<(String, String, usize)>,
) {
    let fs = Arc::new(fs);

    for (name, data, off) in req {
        let fs = fs.clone();
        task::spawn(async move {
            println!("file '{}' start", name);

            let root = loop {
                if let Ok(r) = Chan::attach(fs.clone(), b"").await {
                    break r;
                }
                yield_now().await;
            };
            println!("file '{}' attached", name);

            // Create a file with random name.
            let file = root
                .open(name.as_bytes(), Some(false))
                .await
                .unwrap()
                .unwrap();

            file.close().await;
            println!("file '{}' created", name);

            let file = root.open(name.as_bytes(), None).await.unwrap().unwrap();

            // Write random data to the file starting from random offset.
            let sz = file.write(data.as_bytes(), off).await.unwrap();
            assert_eq!(sz, data.as_bytes().len());
            println!("file '{}' written", name);

            yield_now().await;

            // Read back the data.
            let mut buf = Vec::new();
            buf.resize(data.as_bytes().len(), 0);
            let sz = file.read(&mut buf, off).await.unwrap();
            assert_eq!(sz, buf.len());
            assert_eq!(String::from_utf8(buf).unwrap(), data);
            println!("file '{}' read", name);

            // Remove the file.
            let rm = file.remove().await.unwrap();
            assert_eq!(rm, true, "file '{}' not removed", name);
            println!("file '{}' can removed", name);

            file.close().await;
            println!("file '{}' removed after close", name);

            debug_assert!(root.open(name.as_bytes(), None).await.unwrap().is_none());

            root.close().await;
        })
        .unwrap();
    }

    let fs = loop {
        if Arc::strong_count(&fs) == 1 {
            break Arc::try_unwrap(fs).unwrap();
        }
        yield_now().await;
    };
    fs.shutdown().unwrap().await;
}

pub async fn create_dir<T: Device + fmt::Debug + Send + Sync + 'static>(
    fs: T,
    req: Vec<(String, String, usize)>,
) {
    let fs = Arc::new(fs);

    for (name, data, off) in req {
        let fs = fs.clone();
        task::spawn(async move {
            println!("dir '{}' start", name);

            let root = loop {
                if let Ok(r) = Chan::attach(fs.clone(), b"").await {
                    break r;
                }
                yield_now().await;
            };
            println!("dir '{}' attached", name);

            // Create a directory with random name.
            let dir = root
                .open(name.as_bytes(), Some(true))
                .await
                .unwrap()
                .unwrap();

            dir.close().await;
            println!("dir '{}' created", name);

            let dir = root.open(name.as_bytes(), None).await.unwrap().unwrap();

            // Cannot write to directory
            assert!(dir.write(data.as_bytes(), off).await.is_err());

            // . and .. cannot be created, but this will dup itself since the processed
            // path is empty.
            assert!(dir.open(b".", Some(false)).await.unwrap().is_some());
            assert!(dir.open(b"..", Some(false)).await.unwrap().is_some());

            // Cannot remove non-empty directory;
            let file = dir.open(b"tmp", Some(false)).await.unwrap().unwrap();
            assert_eq!(dir.remove().await.unwrap(), false);

            assert_eq!(file.remove().await.unwrap(), true);
            file.close().await;

            assert_eq!(dir.remove().await.unwrap(), true);
            dir.close().await;
            println!("dir '{}' removed", name);

            debug_assert!(root.open(name.as_bytes(), None).await.unwrap().is_none());

            root.close().await;
        })
        .unwrap();
    }

    let fs = loop {
        if Arc::strong_count(&fs) == 1 {
            break Arc::try_unwrap(fs).unwrap();
        }
        yield_now().await;
    };
    fs.shutdown().unwrap().await;
}
