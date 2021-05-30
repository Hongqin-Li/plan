//! Transaction-safe FAT32 file system by RCU FAT list.
//!
//! Only support FAT32 with block size 512.
//! I-number here is the same as cluster number in FAT's terminology.
use core::{
    cmp::{max, min},
    convert::{TryFrom, TryInto},
    usize,
};

use crate::{
    block::BSIZE,
    cache::Cache,
    log::{Log, MAXEXOPBLOCKS, MAXOPBLOCKS},
};

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use kcore::{
    chan::{Chan, ChanId, ChanType, Dirent},
    dev::Device,
    error::{Error, Result},
};
use ksched::{sync::Spinlock, task::yield_now};

use super::inode::{Inode, FAT};
use super::{
    fname::{utf8_to_utf16, ATTR_DIRECTORY},
    inode::InodeKey,
};

#[async_trait::async_trait_try]
impl Device for FAT {
    async fn shutdown(self)
    where
        Self: Sized,
    {
        self.log.close().await;
    }

    async fn attach(&self, aname: &[u8]) -> Result<ChanId>
    where
        Self: Sized,
    {
        let root_key = InodeKey {
            cno: self.meta.root as u32,
            doff: 0,
            attr: ATTR_DIRECTORY,
        };
        let ip = self
            .iget(root_key)
            .await
            .ok_or(Error::OutOfMemory("attach fat"))?;
        let path = self.to_path(ip);
        Ok(ChanId {
            path,
            version: 0,
            ctype: ChanType::Dir,
        })
    }

    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<ChanId>> {
        let dp = self.to_inode(dir.path);
        if name.is_empty() {
            self.iget(dp.key()).await.unwrap();
            return Ok(Some(dir.clone()));
        }
        if !dp.key().is_dir() {
            if create_dir.is_some() {
                return Err(Error::BadRequest("fat create in file"));
            }
            return Ok(None);
        }

        self.log.begin_op().await?;
        let mut g = dp.lock().await.unwrap();

        let mut new_dir = false;
        let mut some_ip = None;
        let mut result: Result<Option<InodeKey>> = async {
            Ok(if let Some(dir) = create_dir {
                let result = self.dirlink(&mut g, &name, None, dir).await?;
                if result.is_some() && dir {
                    new_dir = true;
                }
                result
            } else {
                self.dirlookup(&g, &name).await?
            })
        }
        .await;

        if let Ok(Some(key)) = result {
            if let Some(ip) = self.iget(key).await {
                if new_dir {
                    // Create "." and ".." for new dir.
                    let (ip_cno, dp_cno) = (ip.key().cno, dp.key().cno);
                    let mut g = ip.lock().await.unwrap();
                    result = self.dirlink(&mut g, b".", Some(ip_cno), true).await;
                    if result.is_ok() {
                        result = self.dirlink(&mut g, b"..", Some(dp_cno), true).await;
                    }
                    // For simplicity, just reset the inode as if we didn't get it.
                    g.addr = Vec::new();
                    g.unlock(true).await.unwrap();
                }
                if result.is_ok() {
                    some_ip = Some(ip);
                }
            } else {
                result = Err(Error::OutOfMemory("inode cache used out"));
            }
        }
        g.addr.clear();
        g.unlock(false).await.unwrap();

        if let Some(ip) = some_ip {
            let op = self.log.end_op(result.is_err(), true).await;
            if !op.committed {
                self.iput(ip);
                drop(op);
                return Err(Error::InternalError("rollback"));
            }
            let ctype = if ip.key().is_dir() {
                ChanType::Dir
            } else {
                ChanType::File
            };
            Ok(Some(ChanId {
                path: self.to_path(ip),
                version: 0,
                ctype,
            }))
        } else {
            let committed = self.log.end_op(result.is_err(), false).await.committed;
            if !committed {
                return Err(Error::InternalError("rollback"));
            }
            return Ok(None);
        }
    }

    async fn close(&self, c: ChanId) {
        let ip = self.to_inode(c.path);
        let step = (self.meta.bps * self.meta.spc * (MAXEXOPBLOCKS - 5)) as u32;

        let op = loop {
            if self.log.begin_exop().await.is_err() {
                // FIXME:
                yield_now().await;
            }

            if ip.nref() != 1 {
                break self.log.end_exop(false, true).await;
            }

            let mut g = ip.lock().await.unwrap();
            if g.nlink != 0 {
                debug_assert_eq!(g.nlink, 1);
                g.addr = Vec::new();
                g.unlock(true).await.unwrap();
                break self.log.end_exop(false, true).await;
            }

            let rm: Result<Option<bool>> = async {
                if ip.key().is_dir() && !self.dirempty(&g).await? {
                    return Ok(Some(false));
                }
                let new = self.resize(&mut g, |old| old - min(old, step)).await?;
                if new == 0 {
                    self.removei(&g).await?;
                    return Ok(Some(true));
                }
                Ok(None)
            }
            .await;

            g.unlock(true).await.unwrap();

            let done = match rm {
                Ok(None) => false,
                _ => true,
            };

            // Since the addr is just truncated when removing, no need to restore previous value.
            let op = self.log.end_exop(rm.is_err(), false).await;
            if !op.committed || done {
                // After removed, someone may create a file with the same inode key,
                // whose nlink must be 1. Thus, even if we have removed the file,
                // we still need to restore nlink to 1 here.
                let mut g = ip.lock().await.unwrap();
                g.nlink = 1;
                g.addr = Vec::new();
                g.unlock(true).await.unwrap();

                break op;
            }
        };
        self.iput(self.to_inode(c.path));
        drop(op);
    }

    /// Return false the link is already zero or it is an non-empty directory.
    async fn remove(&self, c: &ChanId) -> Result<bool> {
        let ip = self.to_inode(c.path);
        let mut can_remove = Ok(false);

        self.log.begin_exop().await?;
        let mut g = ip.lock().await.unwrap();

        if ip.key().is_dir() {
            match self.dirempty(&g).await {
                Ok(true) => can_remove = Ok(g.nlink > 0),
                Err(e) => can_remove = Err(e),
                _ => {}
            }
        } else {
            can_remove = Ok(g.nlink > 0);
        }

        if let Ok(true) = can_remove {
            g.nlink -= 1;
        }

        g.unlock(false).await.unwrap();
        // Since diremtpy is read-only, no need to rollback.
        self.log.end_exop(false, false).await;
        can_remove
    }

    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        let ip = self.to_inode(c.path);

        if ip.key().is_dir() {
            return Err(Error::BadRequest("resize dir"));
        }

        // Each resize of step will modify at most resv blocks (1 SFN + 2 FAT).
        // let resv = 1 + 5 + 1;
        let step = (self.meta.bps * self.meta.spc * (MAXOPBLOCKS - 2)) as u32;
        let size: u32 = size.try_into().unwrap_or(u32::MAX);
        loop {
            self.log.begin_op().await?;
            let mut g = ip.lock().await.unwrap();

            let result = self
                .resize(&mut g, |old| {
                    if old <= size {
                        old
                    } else {
                        max(old.checked_sub(step).unwrap_or(size), size)
                    }
                })
                .await;
            if result.is_err() {
                g.addr.clear();
            }

            g.unlock(false).await.unwrap();
            let op = self.log.end_op(result.is_err(), true).await;

            if !op.committed {
                // Won't block since we have acquired log's lock in op.
                let mut g = ip.lock().await.unwrap();
                g.addr.clear();
                g.unlock(false).await.unwrap();
                drop(op);
                return Err(Error::InternalError("rollback"));
            }

            let newsz = result?;
            if newsz <= size {
                return Ok(newsz as usize);
            }
        }
    }

    async fn stat(&self, c: &ChanId) -> Result<Dirent> {
        let ip = self.to_inode(c.path);
        let g = ip.lock().await?;
        let ret = self.stati(&g).await;
        g.unlock(false).await.unwrap();
        ret
    }

    async fn wstat(&self, c: &ChanId, dirent: &Dirent) -> Result<()> {
        todo!()
    }

    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> Result<usize> {
        let ip = self.to_inode(c.path);

        if ip.key().is_dir() {
            todo!()
        }

        u32::try_from(off + buf.len()).or(Err(Error::BadRequest("read buf len overflow")))?;

        self.log.begin_op().await?;
        let mut g = ip.lock().await.unwrap();
        let result = self.readi(&mut g, buf, off).await;
        g.unlock(false).await.unwrap();
        let committed = self.log.end_op(false, false).await.committed;

        if committed {
            result
        } else {
            Err(Error::InternalError("rollback"))
        }
    }

    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> Result<usize> {
        let ip = self.to_inode(c.path);

        if ip.key().is_dir() {
            return Err(Error::BadRequest("write dir"));
        }

        let end =
            u32::try_from(off + buf.len()).or(Err(Error::BadRequest("write buf len overflow")))?;

        // Each resize of step will modify at most resv blocks (1 SFN + 2 FAT).
        // let resv = 1 + 5 + 1;
        let step = (self.meta.bps * self.meta.spc * (MAXOPBLOCKS - 2)) as u32;
        loop {
            self.log.begin_op().await?;
            let mut g = ip.lock().await.unwrap();

            let result = self
                .resize(&mut g, |old| {
                    if old < end {
                        min(old.checked_add(step).unwrap_or(u32::MAX), end)
                    } else {
                        old
                    }
                })
                .await;
            if result.is_err() {
                g.addr.clear();
            }

            g.unlock(false).await.unwrap();
            let op = self.log.end_op(result.is_err(), true).await;

            if !op.committed {
                // Won't block since we have acquired log's lock in op.
                let mut g = ip.lock().await.unwrap();
                g.addr.clear();
                g.unlock(false).await.unwrap();
                drop(op);
                return Err(Error::InternalError("rollback"));
            }

            if result? >= end {
                break;
            }
        }

        let step = (self.meta.bps * (MAXOPBLOCKS - 1)) as u32;
        let mut n = 0;
        for i in (0..buf.len()).step_by(step as usize) {
            if self.log.begin_op().await.is_err() {
                break;
            }
            let cur_step = min(step as usize, buf.len() - i);
            let mut g = ip.lock().await.unwrap();
            let result = self.writei(&mut g, &buf[i..i + cur_step], off + i).await;
            g.unlock(false).await.unwrap();
            self.log.end_op(result.is_err(), false).await;
            match result {
                Err(e) => break,
                Ok(cnt) => {
                    n += cnt;
                    if cnt != cur_step {
                        break;
                    }
                }
            }
        }
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use ktest::{
        fs::{gen_fat32img, FileDisk},
        rand_int, rand_str, run_multi,
    };

    use super::*;
    use alloc::sync::Arc;
    use core::ops::Range;
    use kcore::dev::Device;
    use ksched::task;
    use task::yield_now;

    #[test]
    fn test_build_log() {
        let (dir, img_path) = gen_fat32img();
        let disk = Arc::new(FileDisk::new(img_path));

        task::spawn(0, async move {
            let disk_root = Chan::attach(disk, b"").await.unwrap();

            let fs = Arc::new(FAT::new(50, 100, &disk_root).await.unwrap());
            println!("fs: {:?}", fs);

            let root = Chan::attach(fs.clone(), b"").await.unwrap();
            let src_dir = root.open(b"src", None).await.unwrap().unwrap();
            src_dir.close().await;

            root.close().await;
            disk_root.close().await;

            let fs = Arc::try_unwrap(fs).unwrap();
            fs.shutdown().unwrap().await;
        })
        .unwrap();
        task::run_all();
        drop(dir);
    }

    #[test]
    fn test_create_dir() {
        let (dir, img_path) = gen_fat32img();
        let disk = Arc::new(FileDisk::new(img_path));
        let ntask = 100;
        let ncpu = 10;
        let (name_len, data_len) = (1..20, 0..1);

        let req = (0..ntask)
            .map(|i| {
                let name = format!("{}-{}", i, rand_str(rand_int(name_len.clone())));
                let data = rand_str(rand_int(data_len.clone()));
                let off = rand_int(0..max(1, data.len()));
                (name, data, off)
            })
            .collect();

        task::spawn(0, async move {
            let disk_root = Chan::attach(disk, b"").await.unwrap();

            let fs = FAT::new(2 * ntask + 10, 100, &disk_root).await.unwrap();
            disk_root.close().await;
            println!("{:?}", fs);
            ktest::fs::create_dir(fs, req).await;
        })
        .unwrap();
        run_multi(ncpu);

        drop(dir);
    }

    fn multi_crud(ncpu: usize, ntask: usize, name_len: Range<usize>, data_len: Range<usize>) {
        let (dir, img_path) = gen_fat32img();
        let disk = Arc::new(FileDisk::new(img_path));

        let req = (0..ntask)
            .map(|i| {
                let name = format!("{}-{}", i, rand_str(rand_int(name_len.clone())));
                let data = rand_str(rand_int(data_len.clone()));
                let off = rand_int(0..max(1, data.len()));
                (name, data, off)
            })
            .collect();

        task::spawn(0, async move {
            let disk_root = Chan::attach(disk, b"").await.unwrap();
            let fs = FAT::new(ntask + 10, 100, &disk_root).await.unwrap();
            disk_root.close().await;
            println!("{:?}", fs);
            ktest::fs::crud(fs, req).await;
        })
        .unwrap();
        run_multi(ncpu);

        drop(dir);
    }

    #[test]
    fn test_crud1() {
        multi_crud(1, 200, 1..20, 0..BSIZE * 2);
        multi_crud(1, 100, 20..100, 0..BSIZE * 2);
        multi_crud(1, 100, 1..20, 0..BSIZE * 10);
    }

    #[test]
    fn test_crud() {
        // Short name.
        multi_crud(10, 200, 1..20, 0..BSIZE * 2);
        // Long name.
        multi_crud(10, 100, 20..100, 0..BSIZE * 2);
        // Large data.
        multi_crud(10, 50, 1..20, 0..BSIZE * 10);
    }

    #[test]
    fn test_create_rm() {
        let ntask = 100;
        let ncpu = 10;
        let name_len = 1..20;

        let (dir, img_path) = gen_fat32img();
        let disk = Arc::new(FileDisk::new(img_path));
        let names = Arc::new(Spinlock::new(Vec::new()));

        // Create some files.
        {
            let disk = disk.clone();
            let names = names.clone();
            let name_len = name_len.clone();
            task::spawn(0, async move {
                let disk_root = Chan::attach(disk, b"").await.unwrap();
                let fs = Arc::new(FAT::new(ntask + 10, 100, &disk_root).await.unwrap());
                disk_root.close().await;
                for i in 0..ntask {
                    let fs = fs.clone();
                    let name_len = name_len.clone();
                    let names = names.clone();

                    task::spawn(0, async move {
                        let root = Chan::attach(fs.clone(), b"").await.unwrap();

                        // Create a file with random name.
                        let name = format!("old-{}-{}", i, rand_str(rand_int(name_len)));
                        names.lock().push(name.clone());
                        let file = root
                            .open(name.as_bytes(), Some(false))
                            .await
                            .unwrap()
                            .unwrap();

                        file.close().await;

                        let file = root
                            .open(name.as_bytes(), None)
                            .await
                            .unwrap()
                            .or_else(|| {
                                panic!("file '{}' not found", name);
                            })
                            .unwrap();

                        file.close().await;
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
            })
            .unwrap();
        }
        run_multi(ncpu);

        task::spawn(0, async move {
            let disk_root = Chan::attach(disk, b"").await.unwrap();
            let fs = Arc::new(FAT::new(ntask + 10, 100, &disk_root).await.unwrap());
            disk_root.close().await;
            for i in 0..ntask {
                let fs = fs.clone();
                let name_len = name_len.clone();
                let names = names.clone();

                task::spawn(0, async move {
                    let root = Chan::attach(fs.clone(), b"").await.unwrap();

                    let mut g = names.lock();
                    let rm = rand_int(0..2) == 0 && !g.is_empty();
                    let name = if rm {
                        g.pop().unwrap()
                    } else {
                        format!("new-{}-{}", i, rand_str(rand_int(name_len)))
                    };
                    drop(g);

                    // Create a new file or remove an old one.
                    if rm {
                        let file = root.open(name.as_bytes(), None).await.unwrap().unwrap();

                        // Remove the old file.
                        assert_eq!(file.remove().await.unwrap(), true);
                        file.close().await;

                        assert_eq!(
                            root.open(name.as_bytes(), None).await.unwrap().is_none(),
                            true
                        );
                        println!("file '{}' removed", name);
                    } else {
                        let file = root
                            .open(name.as_bytes(), Some(false))
                            .await
                            .unwrap()
                            .unwrap();

                        assert_eq!(file.remove().await.unwrap(), true);
                        file.close().await;

                        assert_eq!(
                            root.open(name.as_bytes(), None).await.unwrap().is_none(),
                            true
                        );
                        println!("file '{}' removed", name);
                    }

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
        })
        .unwrap();
        run_multi(ncpu);

        drop(dir);
    }

    #[test]
    fn test_random_err() {
        // TODO:
    }
}
