//! The root file system.
use core::usize;

use alloc::boxed::Box;

use kcore::{
    chan::{ChanId, ChanKind, Dirent},
    dev::Device,
    error::{Error, Result},
};

/// The root file system.
#[derive(Default)]
pub struct Root {}

const ROOT_DIRS: &[&str] = &["boot", "root", "proc", "env", "dev"];

#[async_trait::async_trait_try]
impl Device for Root {
    async fn shutdown(self)
    where
        Self: Sized,
    {
    }

    async fn attach(&self, aname: &[u8]) -> Result<ChanId>
    where
        Self: Sized,
    {
        Ok(ChanId {
            path: 0,
            version: b'/' as u32,
            kind: ChanKind::Dir,
        })
    }

    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<ChanId>> {
        if name.is_empty() {
            Ok(Some(dir.clone()))
        } else if create_dir.is_some() {
            // FIXME:
            Ok(None)
            // Err(Error::BadRequest("create in devroot"))
        } else if dir.path != 0 {
            Ok(None)
        } else {
            debug_assert_eq!(dir.kind, ChanKind::Dir);
            debug_assert_eq!(dir.path, 0);
            Ok(ROOT_DIRS
                .iter()
                .enumerate()
                .find(|(i, s)| s.as_bytes() == name)
                .map(|(i, s)| ChanId {
                    path: i as u64 + 1,
                    version: 0,
                    kind: ChanKind::Dir,
                }))
        }
    }

    async fn close(&self, c: ChanId) {}

    /// Return false the link is already zero or it is an non-empty directory.
    async fn remove(&self, c: &ChanId) -> Result<bool> {
        Err(Error::BadRequest("remove file of devroot"))
    }

    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        unimplemented!()
    }

    async fn stat(&self, c: &ChanId) -> Result<Dirent> {
        todo!()
    }

    async fn wstat(&self, c: &ChanId, dirent: &Dirent) -> Result<()> {
        todo!()
    }

    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> Result<usize> {
        unimplemented!()
    }

    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> Result<usize> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fat::FAT;
    use alloc::sync::Arc;
    use kcore::chan::Chan;
    use ksched::task;
    use ktest::fs::{gen_fat32img, FileDisk};

    #[test]
    fn test_mount() {
        let (dir, img_path) = gen_fat32img();
        let disk = Arc::new(FileDisk::new(img_path));

        task::spawn(async move {
            let devroot = Arc::new(Root::default());
            let root = Chan::attach(devroot, b"").await.unwrap();
            assert_eq!(root.path().await.unwrap(), b"/");

            // Cannot create directories.
            assert!(root.open(b"dev", Some(true)).await.unwrap().is_none());
            assert!(root.open(b"dev", Some(false)).await.unwrap().is_none());
            assert!(root.open(b"x", Some(true)).await.unwrap().is_none());
            assert!(root.open(b"x", Some(false)).await.unwrap().is_none());

            // Can open itself.
            let root2 = root.open(b"", None).await.unwrap().unwrap();
            root2.close().await;

            let root_dev = root.open(b"dev", None).await.unwrap().unwrap();
            assert_eq!(root_dev.path().await.unwrap(), b"/dev");

            let disk_root = Chan::attach(disk, b"").await.unwrap();
            let fs = Arc::new(FAT::new(50, 100, &disk_root).await.unwrap());
            disk_root.close().await;

            // Mount fs to root.
            let fs_root = Chan::attach(fs.clone(), b"").await.unwrap();
            root.mount(&fs_root).await.unwrap();
            // Cannot bind to directory.
            assert_eq!(root.bind(&fs_root).await.is_err(), true);
            fs_root.close().await;

            // Can open file in mounted fs.
            let src_dir = root.open(b"src", None).await.unwrap().unwrap();
            assert_eq!(src_dir.path().await.unwrap(), b"/src");
            src_dir.close().await;

            root.close().await;
            root_dev.close().await;

            let fs = Arc::try_unwrap(fs).unwrap();
            fs.shutdown().unwrap().await;
        })
        .unwrap();
        task::run();
        drop(dir);
    }
}
