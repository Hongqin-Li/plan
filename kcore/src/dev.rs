//! Device driver.
//!
//! The design should be applicable for such use cases:
//! - Env server
//! - Tempdir and tempfile: env,
//! - Two-way pipe: stdin/stdout, network
//! - Event listener on file: Epoll

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;

use crate::{chan::Chan, error::Error};

use crate::chan::Qid;

/// Machine-independent directory entry.
///
/// A directory entry represents information of a file(or directory file).
/// Timestamps are measured in seconds since the epoch(Jan 1 00:00 1970 GMT).
pub struct Dirent {
    /// Name string.
    pub name: Vec<u8>,
    /// Length of file in bytes.
    pub len: u64,
    /// Timestamp of last change of the content.
    ///
    /// For a plain file, mtime is the time of the most recent create, open with truncation, or
    /// write; for a directory it is the time of the most recent remove, create, or wstat of a
    /// file in the directory.
    pub mtime: u32,
    /// Timestamp of last read of the content.
    ///
    /// It's also set whenever mtime is set. In addition, for a directory, it is set by an attach,
    /// walk, or create, all whether successful or not.
    pub atime: u32,
}

/// Common trait of a device driver.
#[async_trait::async_trait_try]
pub trait Device {
    /// Unique character representing this device, such as #s.
    // const CHAR: u8;

    /// Unique name of the device.
    // const NAME: &'static str;

    /// Type determine which driver to used for this channel, analogous to UNIX's major number.
    fn typeid(&self) -> usize;

    ///
    fn reset(&mut self);
    ///
    fn init(&mut self);
    ///
    fn shutdown(&mut self);
    ///
    fn power(&mut self, on: bool);

    ///
    async fn attach(&mut self, name: &[u8]) -> Result<Arc<Chan>, Error>;

    /// Looks for the file name in the directory represented by a channel.
    /// FIXME: why different from plan9.
    async fn walk(&mut self, c: &Chan, name: &[u8]) -> Result<Option<Chan>, Error>;

    /// Inquires about the file attribute identified by a channel.
    async fn stat(&mut self, c: &Chan) -> Result<Dirent, Error>;

    /// Change the file attribute identified by a channel.
    async fn wstat(&mut self, c: &Chan, dirent: Dirent) -> Result<bool, Error>;

    /// Open a file for reading or writing.
    async fn open(&mut self, c: &Chan, omode: u32) -> Result<Chan, Error>;
    /// Create a file for reading or writing.
    async fn create(&mut self, c: &Chan, name: &[u8], omode: u32, perm: u32) -> Result<(), Error>;
    /// Remove a file.
    async fn remove(&mut self, c: &Chan) -> Result<bool, Error>;
    /// Close a file.
    async fn close(&mut self, c: &Chan) -> Result<bool, Error>;

    /// Read data from a channel by offset and store to buffer.
    /// Return the number of bytes read.
    async fn read(&mut self, c: &Chan, buf: &mut [u8], off: usize) -> Result<usize, Error>;

    /// Write the data in buffer to a channel starting by specific offset.
    /// Return the number of bytes writed.
    async fn write(&mut self, c: &Chan, buf: &[u8], off: usize) -> Result<usize, Error>;
}
