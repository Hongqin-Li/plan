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

#![allow(missing_docs)]

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use bitflags::bitflags;
use core::ops::Deref;

use crate::{
    chan::{Chan, ChanId, ChanKey, ChanType, Dirent, Perm},
    error::{Error, Result},
};

/// Common trait of a device driver.
///
/// # Why not use GAT to get async trait?
///
/// Since that may cause loop when our FS is dependent on a Chan, and the compiler cannot
/// determine the future size at compile time. Think of the case when we have FS on a file,
/// which resides on another FS, and the length of such chain cannot be known at compile time.
#[allow(missing_docs)]
#[async_trait::async_trait_try]
pub trait Device {
    /// The async destructor of the device.
    ///
    /// This may be called when some device in the global device table Vec<Arc<Dev>> has
    /// no reference(i.e. no opened file).
    async fn shutdown(self)
    where
        Self: Sized;

    /// Return the root channel. `aname` is a user-specified hint.
    async fn attach(&self, aname: &[u8]) -> Result<ChanId>;

    /// Open a file in the directory or reopen a file.
    ///
    /// If `name` is empty, ignore other parameters and reopen the file itself(same as dup).
    /// The reopen operation returns either an error or some chan id(but not [None]).
    ///
    /// `dir` is guaranteed to be a directory if `name` is not empty.
    ///
    /// If `create_dir` is [None], this operation is a normal open. Return [None] if not found.
    ///
    /// Otherwise, it means creating a file. The boolean indicates type of the file to be
    /// created is a directory or not. Return [None] if the file already exist.
    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<ChanId>>;
    /// Close a file. The drop of channel is done by [Chan::close](`super::chan::Chan::close`)
    ///
    /// This function must always succeed.
    async fn close(&self, c: ChanId);

    /// Remove a file by hint such that the server won't remove the file until
    /// all clients have closed it. Can only remove normal file or empty directory.
    /// May not atomic since having to truncate the file first.
    ///
    /// Return true if removed, else false.
    async fn remove(&self, c: &ChanId) -> Result<bool>;

    /// Inquires about the file attribute identified by a channel.
    async fn stat(&self, c: &ChanId) -> Result<Dirent>;
    /// Change the file attribute identified by a channel. Should be atomic.
    async fn wstat(&self, c: &ChanId, dirent: &Dirent) -> Result<()>;

    /// Read data from a channel by offset and store to buffer.
    ///
    /// For plain files, it returns the number of bytes read.
    ///
    /// For directories, read returns an integral number of directory entries exactly
    /// as in stat, one for each member of the directory.
    /// The offset and buffer len must be zero modulo DIRLEN.
    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> Result<usize>;

    /// Write the data in buffer to a channel starting by specific offset.
    /// Directories are not allowed to be written.
    ///
    /// Return the number of bytes writed.
    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> Result<usize>;
    /// Reduce the size of a file.
    ///
    /// If the file previously was larger than or equal to this size, the extra data is lost.
    /// Otherwise, do nothing.
    ///
    /// Return the new size, which may or may not be equal to the expected size.
    ///
    /// NOTE: truncate with infinite size can be used to retrieve the size of the file.
    /// Why not resize? Since resize by write can better handle initial bytes.
    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize>;
}

#[cfg(test)]
mod tests {
    use ksched::task;

    use super::*;

    use crate::chan::ChanInner;
    use crate::chan::ChanType;
    use alloc::sync::Weak;
    use ksched::sync::Mutex;

    struct A<T>(T);

    #[async_trait::async_trait_try]
    impl<T: Send + 'static + Sync> Device for A<T> {
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
            todo!()
        }
        async fn open(
            &self,
            dir: &ChanId,
            name: &[u8],
            create_dir: Option<bool>,
        ) -> Result<Option<ChanId>> {
            todo!()
        }
        async fn close(&self, c: ChanId) {}
        async fn remove(&self, c: &ChanId) -> Result<bool> {
            todo!()
        }
        async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
            todo!();
        }

        async fn stat(&self, c: &ChanId) -> Result<Dirent> {
            todo!()
        }

        async fn wstat(&self, c: &ChanId, dirent: &Dirent) -> Result<()> {
            todo!()
        }

        async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> Result<usize> {
            println!("c {:?}", c);
            buf[0] = 10;
            Ok(0)
        }

        async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> Result<usize> {
            todo!()
        }
    }

    #[test]
    fn it_compiles() {
        // task::spawn(0, async move {
        //     let a = Arc::new(Dev::FAT(A(1u8)));
        //     let key = ChanKey::new(
        //         a.clone(),
        //         0,
        //         Qid {
        //             path: 0,
        //             version: 0,
        //             qtype: QType::File,
        //         },
        //     );
        //     let mut buf = [0u8; 10];
        //     // Test NewDevice.
        //     let newa = A(1u8);
        //     newa.read(&newa, &key, &mut buf, 0).await.unwrap();

        //     let file = Arc::new(Chan {
        //         key,
        //         name: Vec::new(),
        //         parent: Weak::new(),
        //         inner: Mutex::new(ChanInner::default()),
        //     });

        //     file.read(&mut buf, 0).await.unwrap();
        //     assert_eq!(buf[0], 10);
        //     file.close().await;
        // })
        // .unwrap();
        // task::run_all();
    }
}
