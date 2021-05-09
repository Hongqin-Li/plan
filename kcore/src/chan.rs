//! Channel.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::pin::Pin;
use core::{
    alloc::AllocError,
    convert::TryFrom,
    hash::{Hash, Hasher},
};
use core::{
    mem,
    ops::{Generator, GeneratorState},
};
use ksched::task::yield_now;

use alloc::sync::Arc;
use bitflags::bitflags;

use crate::{
    dev::Device,
    error::{Error, Result},
};

bitflags! {
    /// Bits for type of a file.
    #[derive(Default)]
    pub struct QType: u8 {
        /// Directories.
        const DIR = 0x80;
        /// Append-only files.
        const APPEND = 0x40;
        /// Exclusive use files.
        const EXCL = 0x20;
        /// Mounted channel.
        const MOUNT = 0x10;
        /// Authentication file.
        const AUTH = 0x08;
        /// Plain file.
        const FILE = 0x00;
    }
}

bitflags! {
    /// Channel flags.
    pub struct CFlag: u32 {
        /// For I/O.
        const OPEN = 0x0001;
        /// The message channel for a mount.
        const MSG = 0x0002;
        /// Close on exec.
        const CEXEC = 0x0008;
        /// Not in use.
        const FREE = 0x0010;
        /// Remove on close.
        const RCLOSE = 0x0020;
        /// Client cache.
        const CACHE = 0x0080;
    }
}

/// Access types in namec.
pub enum AMode {
    /// As in stat, wstat.
    Access,
    /// For left-hand-side of bind.
    Bind,
    /// As in chdir.
    Todir,
    /// For I/O.
    Open,
    /// To be mounted or mounted upon.
    Mount,
    /// Is to be created
    Create,
    /// Will be removed by caller.
    Remove,
}

bitflags! {
    /// Bits for open mode.
    pub struct OMode: u16 {
        /// Open for read.
        const READ = 0x0000;
        /// Open for write.
        const WRITE = 0x0001;
        /// Open for read and write.
        const RDWR = 0x0002;
        /// Execute, == read but check execute permission.
        const EXEC = 0x0003;
        /// Or'ed in (except for exec), truncate file first.
        const TRUNC = 0x0010;
        /// Or'ed in, close on exec.
        const CEXEC = 0x0020;
        /// Or'ed in, remove on close.
        const RCLOSE = 0x0040;
        /// Or'ed in, exclusive create.
        const EXCL = 0x1000;
    }
}

/// Permission control on a file.
pub enum Perm {
    /// Execute, == read but check execute permission.
    EXEC,
    /// Read-only.
    READ,
    /// Write-only.
    WRITE,
    /// Read and write.
    RDWR,
}

/// Machine-independent directory entry.
///
/// A directory entry represents information of a file(or directory file).
/// Timestamps are measured in seconds since the epoch(Jan 1 00:00 1970 GMT).
pub struct Dirent {
    /// File name, must be "/" if the file is the root directory of the server.
    ///
    /// It an be changed by anyone with write permission in the parent directory.
    /// It is an error to change the name to that of an existing file.
    pub name: Vec<u8>,
    /// Owner name. Cannot changed by a wstat.
    pub uid: Vec<u8>,
    /// Group name.
    ///
    /// The gid can be changed: by the owner if also a member of the new group; or by the
    /// group leader of the file's current group if also leader of the new group.
    pub gid: Vec<u8>,
    /// Unique id from server. Cannot changed by a wstat.
    pub qid: Qid,
    /// Permission flags.
    ///
    /// The mode can be changed by the owner of the file or the group leader of the file's current
    /// group. The directory bit cannot be changed by a wstat; the other defined permission and mode
    /// bits can.
    pub mode: u32,
    /// Length of file in bytes. Cannot changed by a wstat.
    pub len: u64,
    /// Timestamp of last change of the content.
    ///
    /// For a plain file, mtime is the time of the most recent create, open with truncation, or
    /// write; for a directory it is the time of the most recent remove, create, or wstat of a
    /// file in the directory.
    ///
    /// It can be changed by the owner of the file or the group leader of the file's current group.
    pub mtime: u32,
    /// Timestamp of last read of the content. Cannot changed by a wstat.
    ///
    /// It's also set whenever mtime is set. In addition, for a directory, it is set by an attach,
    /// walk, or create, all whether successful or not.
    pub atime: u32,
}

#[derive(Copy, Clone, Debug)]
/// Qid identifies the file within a device, analogous to the i-number.
pub struct Qid {
    /// The path is a unique file number assigned by a device driver or file server when
    /// a file is created.
    pub path: u64,
    /// The version number is updated whenever the file is modified, which can be used­ ­
    /// to maintain cache coherency between clients and servers.
    pub version: u32,
    /// Type of the file.
    pub qtype: QType,
}

/// Channel represents a virtual file from kernel's perspective.
/// TODO: dev, devid, qid::path, qid::qtype are immutable.
pub struct Chan {
    /// Type determine which driver to used for this channel, analogous to UNIX's major number.
    pub dev: Arc<dyn Device + Send + Sync>,
    /// Device id indicates which instance of the driver it is, analogous to UNIX's minor number.
    pub devid: usize,
    /// Qid is the file server's unique identification of the file, similar to UNIX's inode number.
    pub qid: Qid,
    /// To check if we have close the channel.
    pub dropped: bool,

    /// Flags indicating previous settings of this file by client.
    /// Reserved for user of this library.
    pub flag: CFlag,
    /// File name.
    /// Reserved for user of this library.
    pub name: Vec<u8>,
}

impl core::fmt::Debug for Chan {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Chan")
            .field("devid", &self.devid)
            .field("qid", &self.qid)
            .field("dropped", &self.dropped)
            .field("flag", &self.flag)
            .field("name", &self.name)
            .finish()
    }
}

impl Chan {
    /// Close a file. Async version of [`drop`].
    pub async fn close(mut self) {
        loop {
            if let Ok(f) = self.dev.clone().close(&self) {
                f.await;
                break;
            }
            yield_now().await;
        }
        self.dropped = true;
        drop(self);
    }

    /// Duplicate a file.
    // pub fn dup(&self) -> Result<Self> {
    //     let mut name = Vec::new();
    //     name.try_reserve(self.name.len())?;
    //     name.extend_from_slice(&self.name);
    //     Ok(Self {
    //         dev: self.dev.clone(),
    //         devid: self.devid,
    //         qid: self.qid,
    //         flag: self.flag,
    //         name
    //     })
    // }

    /// Open wrapper.
    pub async fn open(&self, name: &[u8], create_dir: Option<bool>) -> Result<Option<Chan>> {
        self.dev.open(self, name, create_dir)?.await
    }
    /// Remove wrapper.
    pub async fn remove(&self) -> Result<bool> {
        self.dev.remove(self)?.await
    }
    /// Stat wrapper.
    pub async fn stat(&self) -> Result<Dirent> {
        self.dev.stat(self)?.await
    }
    /// Wstat wrapper.
    pub async fn wstat(&self, dirent: &Dirent) -> Result<()> {
        self.dev.wstat(self, dirent)?.await
    }
    /// Read wrapper.
    pub async fn read(&self, buf: &mut [u8], off: usize) -> Result<usize> {
        off.checked_add(buf.len()).ok_or(Error::BadRequest)?;
        self.dev.read(self, buf, off)?.await
    }
    /// Write wrapper.
    pub async fn write(&self, buf: &[u8], off: usize) -> Result<usize> {
        off.checked_add(buf.len()).ok_or(Error::BadRequest)?;
        self.dev.write(self, buf, off)?.await
    }
}

impl Drop for Chan {
    /// Use [`Self::close`] instead, since Rust doesn't support async drop.
    ///
    /// TODO: How to statically assert some function is unreachable?
    fn drop(&mut self) {
        assert!(self.dropped, "forgot to close");
    }
}

impl PartialEq for Chan {
    fn eq(&self, other: &Self) -> bool {
        self.dev.typeid() == other.dev.typeid()
            && self.devid == other.devid
            && self.qid.path == other.qid.path
    }
}

impl Eq for Chan {}

impl Hash for Chan {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.dev.typeid().hash(state);
        self.devid.hash(state);
        self.qid.path.hash(state);
    }
}
