//! Device driver.
//!
//! The design should be applicable for such use cases:
//! - Env server
//! - Tempdir and tempfile: env,
//! - Two-way pipe: stdin/stdout, network
//! - Event listener on file: Epoll
//! - how to retrieve directory that posesses this file and then call its wstat.
//! - Donot support atomic renaming due to portable reason, use special ctrl file instead.
//! - Donot support link/unlink, use bind and mount instead. Since they provide more abstraction
//!   and behave more generally and more user-friendly.
//! - Donot deal with access control, just r/w permission information.
//!
//! ## Permission in file system?
//!
//! Use namespace instead?

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use bitflags::bitflags;

use crate::{
    chan::{Chan, Dirent, Perm},
    error::{Error, Result},
};

use crate::chan::Qid;

/// Common trait of a device driver.
#[async_trait::async_trait_try]
pub trait Device {
    /// Type determine which driver to used for this channel, analogous to UNIX's major number.
    fn typeid(&self) -> usize;

    /// The async destructor of the device.
    async fn shutdown(self)
    where
        Self: Sized;

    /// Return the root channel. `aname` is a user-specified hint.
    async fn attach(self: &Arc<Self>, aname: &[u8]) -> Result<Chan>
    where
        Self: Sized;

    /// Open a file by looking for the file name in the directory represented by a channel.
    ///
    /// If `create_dir` is [None], this operation is a normal open. Return [None] if not found.
    ///
    /// Otherwise, it means creating a file. The boolean indicates type of the file to be
    /// created is a directory or not. Return [None] if the file already exist.
    async fn open(&self, dir: &Chan, name: &[u8], create_dir: Option<bool>)
        -> Result<Option<Chan>>;
    /// Close a file. The drop of channel is done by [Chan::close](`super::chan::Chan::close`)
    ///
    /// This functioni must always succeed.
    async fn close(&self, c: &Chan);

    /// Remove a file by hint such that the server won't remove the file until
    /// all clients have closed it. Can only remove normal file or empty directory.
    /// May not atomic since having to truncate the file first.
    ///
    /// Return true if removed, else false.
    async fn remove(&self, c: &Chan) -> Result<bool>;

    /// Inquires about the file attribute identified by a channel.
    async fn stat(&self, c: &Chan) -> Result<Dirent>;
    /// Change the file attribute identified by a channel. Should be atomic.
    async fn wstat(&self, c: &Chan, dirent: &Dirent) -> Result<()>;

    /// Read data from a channel by offset and store to buffer.
    ///
    /// For plain files, it returns the number of bytes read.
    ///
    /// For directories, read returns an integral number of directory entries exactly
    /// as in stat, one for each member of the directory.
    /// The offset and buffer len must be zero modulo DIRLEN.
    async fn read(&self, c: &Chan, buf: &mut [u8], off: usize) -> Result<usize>;

    /// Write the data in buffer to a channel starting by specific offset.
    /// Directories are not allowed to be written.
    ///
    /// Return the number of bytes writed.
    async fn write(&self, c: &Chan, buf: &[u8], off: usize) -> Result<usize>;
}

#[cfg(test)]
mod tests {
    use ksched::task;

    use super::*;

    use crate::chan::{CFlag, QType};

    struct A<T>(T);

    #[async_trait::async_trait_try]
    impl<T: Send + 'static + Sync> Device for A<T> {
        fn typeid(&self) -> usize {
            todo!();
        }
        async fn shutdown(self)
        where
            Self: Sized,
        {
            todo!()
        }
        async fn attach(self: &Arc<Self>, aname: &[u8]) -> Result<Chan>
        where
            Self: Sized,
        {
            todo!()
        }
        async fn open(
            &self,
            dir: &Chan,
            name: &[u8],
            create_dir: Option<bool>,
        ) -> Result<Option<Chan>> {
            todo!()
        }
        async fn close(&self, c: &Chan) {}
        async fn remove(&self, c: &Chan) -> Result<bool> {
            todo!()
        }

        async fn stat(&self, c: &Chan) -> Result<Dirent> {
            todo!()
        }

        async fn wstat(&self, c: &Chan, dirent: &Dirent) -> Result<()> {
            todo!()
        }

        async fn read(&self, c: &Chan, buf: &mut [u8], off: usize) -> Result<usize> {
            buf[0] = 10;
            Ok(0)
        }

        async fn write(&self, c: &Chan, buf: &[u8], off: usize) -> Result<usize> {
            todo!()
        }
    }

    // // May corrupt other testing threads.
    // #[test]
    // #[should_panic]
    // fn forget_close() {
    //     task::spawn(0, async move {
    //         let a = Arc::new(A(1u8));
    //         let c = Chan {
    //             dev: a.clone(),
    //             devid: 0,
    //             qid: Qid {
    //                 path: 0,
    //                 version: 0,
    //                 qtype: QType::FILE,
    //             },
    //             flag: CFlag::OPEN,
    //             name: Vec::new(),
    //             dropped: false,
    //         };
    //         let mut buf = [0u8; 10];
    //         a.read(&c, &mut buf, 0).unwrap().await.unwrap();
    //         assert_eq!(buf[0], 10);
    //     })
    //     .unwrap();
    //     task::run_all();
    // }

    #[test]
    fn it_compiles() {
        task::spawn(0, async move {
            let a = Arc::new(A(1u8));
            let c = Chan {
                dev: a.clone(),
                devid: 0,
                qid: Qid {
                    path: 0,
                    version: 0,
                    qtype: QType::FILE,
                },
                flag: CFlag::OPEN,
                name: Vec::new(),
                dropped: false,
            };
            let mut buf = [0u8; 10];
            a.read(&c, &mut buf, 0).unwrap().await.unwrap();
            assert_eq!(buf[0], 10);
            c.close().await;
        })
        .unwrap();
        task::run_all();
    }
}
