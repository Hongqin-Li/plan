//! Channel.

use alloc::boxed::Box;
use core::ops::{Generator, GeneratorState};
use core::pin::Pin;
use core::{
    alloc::AllocError,
    convert::TryFrom,
    hash::{Hash, Hasher},
};

use alloc::sync::Arc;
use bitflags::bitflags;

use crate::{dev::Device, error::Error};

// bitflags! {
//     struct QType: u8 {
//         /// Type bit for directories.
//         const DIR = 0x80;
//         ///Type bit for append only files.
//         const APPEND = 0x40;
//         /// Type bit for exclusive use files.
//         const EXCL = 0x20;
//         /// Type bit for mounted channel.
//         const MOUNT	= 0x10;
//         /// Type bit for authentication file.
//         const AUTH = 0x08;
//         /// Plain file.
//         const FILE = 0x00;
//     }
// }

/// Type of a file.
pub enum QType {
    /// Directories.
    Dir,
    /// Plain files.
    File,
}

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
pub struct Chan {
    /// Type determine which driver to used for this channel, analogous to UNIX's major number.
    pub dev: Arc<dyn Device + Send + Sync>,
    /// Device id indicates which instance of the driver it is, analogous to UNIX's minor number.
    pub devid: usize,
    /// Qid is the file server's unique identification of the file, similar to UNIX's inode number.
    pub qid: Qid,
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
