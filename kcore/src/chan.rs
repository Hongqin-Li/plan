//! Channel and mount space.

use alloc::sync::Weak;
use alloc::vec::Vec;
use core::hint::unreachable_unchecked;
use core::{cmp::min, convert::TryFrom, fmt::Debug, iter, mem::MaybeUninit, str};
use kalloc::wrapper::vec_push;
use ksched::{
    sync::{Mutex, RwLock},
    task::yield_now,
};

use alloc::sync::Arc;

use crate::{
    dev::Device,
    error::{Error, Result},
};

/// File type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChanKind {
    /// Directory.
    Dir,
    /// Plain file.
    File,
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
/// File identification within a device, analogous to the i-number.
pub struct ChanId {
    /// The path is a unique file number assigned by a device driver or file server when
    /// a file is created.
    /// This can also used to determine whether a PnP device has been removed.
    pub path: u64,
    /// The version number is updated whenever the file is modified, which can be used­ ­
    /// to maintain cache coherency between clients and servers.
    pub version: u32,
    /// Type of the file.
    pub kind: ChanKind,
}

/// A key representing one client handle of the file.
/// Basically, it's used to check if we have forgotten to close a file.
pub struct ChanKey {
    /// Which driver to used for this channel, analogous to UNIX's major number.
    dev: Arc<dyn Device + Send + Sync>,
    id: ChanId,

    /// To check if we have close the channel.
    /// FIXME: Once we have async drop in Rust, it can be removed.
    dropped: bool,
}

impl ChanKey {
    /// Create a new chan key.
    pub fn new(dev: Arc<dyn Device + Send + Sync>, devid: usize, id: ChanId) -> Self {
        Self {
            dev,
            id,
            dropped: false,
        }
    }

    async fn dup(&self) -> Result<ChanKey> {
        self.dev.open(&self.id, b"", None)?.await?.map_or(
            Err(Error::Gone("failed to rekey")),
            |id| {
                Ok(ChanKey {
                    dev: self.dev.clone(),
                    id,
                    dropped: false,
                })
            },
        )
    }

    /// FIXME: pre-allocate the future on creation.
    async fn close(mut self) {
        self.dropped = true;
        loop {
            if let Ok(f) = self.dev.close(self.id) {
                f.await;
                break;
            }
            yield_now().await;
        }
    }
}

impl Debug for ChanKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ChanKey")
            .field("id", &self.id)
            .field("dropped", &self.dropped)
            .finish()
    }
}

impl Drop for ChanKey {
    /// Use [`Self::close`] instead, since Rust doesn't support async drop.
    ///
    /// FIXME: How to statically assert some function is unreachable?
    fn drop(&mut self) {
        assert!(self.dropped, "forgot to close: {:?}", self);
    }
}

/// Channel represents a virtual file from kernel's perspective.
#[derive(Debug)]
pub struct Chan {
    key: ChanKey,
    parent: Option<Arc<Chan>>,
    name: Vec<u8>,

    /// Union mount point that derives Chan.
    /// Use ChanKey instead of Chan to avoid cycle in the graph.
    umnt: RwLock<Vec<ChanKey>>,
    /// The weak pointer must be able to upgrade.
    child: Mutex<Vec<Weak<Chan>>>,
}

impl Chan {
    /// Create a new mount space from the root of a device.
    pub async fn attach(dev: Arc<dyn Device + Send + Sync>, aname: &[u8]) -> Result<Arc<Self>> {
        let mut name = Vec::new();
        name.try_reserve(aname.len())?;
        for x in aname {
            name.push(*x);
        }
        let a = Arc::<Chan>::try_new_uninit()?;
        let id = dev.clone().attach(aname)?.await?;
        let key = ChanKey {
            dev,
            id,
            dropped: false,
        };
        Ok(unsafe { Self::from_key(key, a) })
    }

    /// Get the absolute path string of this chan.
    pub async fn path(self: &Arc<Chan>) -> Result<Vec<u8>> {
        let name1 = |u: &Arc<Chan>| -> Result<Vec<u8>> {
            let mut buf = Vec::new();
            for b in &u.name {
                vec_push(&mut buf, *b)?;
            }
            Ok(buf)
        };
        let mut u = self.clone();
        let mut ret = Vec::new();
        while let Some(fa) = &u.parent {
            let name = name1(&u)?;
            for b in name.iter().rev() {
                vec_push(&mut ret, *b)?;
            }
            u = fa.clone();
        }
        vec_push(&mut ret, b'/')?;
        ret.reverse();
        Ok(ret)
    }

    /// Create a new mount space rooted at a chan.
    pub async fn new(chan: &Arc<Chan>) -> Result<Arc<Self>> {
        let a = Arc::<Chan>::try_new_uninit()?;
        let key = chan.key.dup().await?;
        Ok(unsafe { Self::from_key(key, a) })
    }

    unsafe fn from_key(key: ChanKey, mut a: Arc<MaybeUninit<Chan>>) -> Arc<Self> {
        Arc::get_mut_unchecked(&mut a).as_mut_ptr().write(Self {
            parent: None,
            umnt: RwLock::new(Vec::new()),
            child: Mutex::new(Vec::new()),
            key,
            name: Vec::new(),
        });
        a.assume_init()
    }

    /// Mount directory to this chan.
    ///
    /// This will mount all union directories from old to this chan.
    pub async fn mount(&self, old: &Arc<Self>) -> Result<()> {
        if !(self.is_dir() && old.is_dir()) {
            return Err(Error::BadRequest("cannot mount file"));
        }

        let mut umnt = Vec::new();
        let result = async {
            let g = old.umnt.read().await;
            umnt.try_reserve(g.len() + 1)?;
            for key in iter::once(&old.key).chain(g.iter()) {
                umnt.push(key.dup().await?);
            }
            drop(g);

            let mut g = self.umnt.write().await;
            g.try_reserve(umnt.len())?;
            umnt.reverse();
            while let Some(k) = umnt.pop() {
                g.push(k);
            }
            Ok(())
        }
        .await;

        while let Some(key) = umnt.pop() {
            key.close().await;
        }
        result
    }

    /// Bind file to this chan.
    ///
    /// Drop any previously bound chan.
    pub async fn bind(&self, old: &Arc<Self>) -> Result<()> {
        if self.is_dir() || old.is_dir() {
            return Err(Error::BadRequest("cannot bind dir"));
        }
        let mut g = self.umnt.write().await;
        if g.is_empty() {
            g.try_reserve(1)?;
        }
        let key = old.key.dup().await?;
        if let Some(key) = g.pop() {
            key.close().await;
        }
        g.push(key);
        debug_assert_eq!(g.len(), 1);
        Ok(())
    }

    /// Remove all mount point of this chan.
    pub async fn clear_mount(&self) {
        let mut g = self.umnt.write().await;
        while let Some(key) = g.pop() {
            key.close().await;
        }
    }

    /// Caller should guarantee `name` is non-empty.
    async fn open1(
        self: &Arc<Self>,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<Arc<Chan>>> {
        debug_assert_eq!(name.is_empty(), false);
        if !self.is_dir() {
            return Ok(None);
        }

        let mut child = self.child.lock().await;
        for u in child.iter() {
            let u = u.upgrade().unwrap();
            if u.name == name {
                return Ok(Some(u.clone()));
            }
        }

        // Pre allocation.
        let mut names = Vec::new();
        for x in name {
            vec_push(&mut names, *x)?;
        }
        child.try_reserve(1)?;
        let mut a = Arc::<Self>::try_new_uninit()?;

        let mut some_chan = None;
        let g = self.umnt.read().await;
        for key in iter::once(&self.key).chain(g.iter()) {
            debug_assert_eq!(key.id.kind, ChanKind::Dir);
            if let Some(id) = key.dev.open(&key.id, name, create_dir)?.await? {
                let u = unsafe {
                    Arc::get_mut_unchecked(&mut a).as_mut_ptr().write(Self {
                        parent: Some(self.clone()),
                        umnt: RwLock::new(Vec::new()),
                        child: Mutex::new(Vec::new()),
                        key: ChanKey {
                            dev: key.dev.clone(),
                            id,
                            dropped: false,
                        },
                        name: names,
                    });
                    a.assume_init()
                };
                some_chan = Some(u);
                break;
            }
        }
        Ok(some_chan.map(|c| {
            child.push(Arc::<Self>::downgrade(&c));
            c
        }))
    }

    /// Open a file located at path starting from this chan.
    ///
    /// Return [NotFound](Error::NotFound) if failed to find any directory components within the path.
    /// Otherwise it can find the parent directory.
    pub async fn open(
        self: &Arc<Self>,
        path: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<Arc<Self>>> {
        let path = Path::try_from(path)?;
        let mut cur = self.clone();
        for _ in 0..path.dotdots {
            if let Some(fa) = &cur.parent {
                cur = fa.clone();
            }
        }

        for (i, name) in path.names.iter().enumerate() {
            let last = i == path.names.len() - 1;
            match cur
                .open1(name.as_bytes(), if last { create_dir } else { None })
                .await
            {
                Ok(Some(u)) => {
                    // Since u is the child of cur and chan that has children won't be close.
                    // just drop cur.
                    cur = u;
                }
                Ok(None) => {
                    cur.close().await;
                    return if last {
                        Ok(None)
                    } else {
                        Err(Error::NotFound("failed to find intermediate directory"))
                    };
                }
                Err(e) => {
                    cur.close().await;
                    return Err(e);
                }
            }
        }

        Ok(Some(cur))
    }

    async fn close1(u: Arc<Self>) -> Option<Arc<Self>> {
        let fa = &u.parent;

        let ug = u.child.lock().await;
        let mut fg = if let Some(fa) = fa {
            Some(fa.child.lock().await)
        } else {
            None
        };
        // Once we have locked this node and its parent, the reference count won't
        // decrease(but may be increased by dup) since every close operation also need to
        // enter this function. And if we are the last one, the reference count won't change.
        let last = Arc::<Self>::strong_count(&u) == 1;

        if last {
            assert_eq!(ug.len(), 0);
            while let Some(ck) = u.umnt.try_write().unwrap().pop() {
                ck.close().await;
            }

            if let Some(mut fg) = fg.take() {
                let w = Arc::<Self>::downgrade(&u);
                let i = fg.iter().position(|x| Weak::<Self>::ptr_eq(&w, x)).unwrap();
                fg.swap_remove(i);
            }
            drop(fg);
            drop(ug);

            let c = Arc::<Self>::try_unwrap(u).unwrap();
            c.key.close().await;
            c.parent
        } else {
            None
        }
    }

    /// Close a file. The async destructor.
    pub async fn close(self: Arc<Self>) {
        let mut cur = self;
        while let Some(fa) = Self::close1(cur).await {
            cur = fa;
        }
    }

    /// Duplicate a handle of file.
    pub fn dup(self: &Arc<Self>) -> Arc<Self> {
        self.clone()
    }

    /// Check if this chan is directory.
    /// Chans in umnt are of same type of itself.
    pub fn is_dir(&self) -> bool {
        self.key.id.kind == ChanKind::Dir
    }

    /// Remove wrapper.
    pub async fn remove(&self) -> Result<bool> {
        self.key.dev.remove(&self.key.id)?.await
    }

    /// Stat wrapper.
    pub async fn stat(&self) -> Result<Dirent> {
        todo!()
    }

    /// Wstat wrapper.
    pub async fn wstat(&self, dirent: &Dirent) -> Result<()> {
        todo!()
    }

    /// Read wrapper.
    pub async fn read(&self, buf: &mut [u8], off: usize) -> Result<usize> {
        if self.is_dir() {
            return Err(Error::BadRequest("read dir"));
        }
        off.checked_add(buf.len())
            .ok_or(Error::BadRequest("read buffer len overflow"))?;

        let umnt = self.umnt.read().await;
        let key = umnt.first().unwrap_or(&self.key);
        let ret = key.dev.read(&key.id, buf, off)?.await;
        drop(umnt);
        ret
    }
    /// Write wrapper.
    pub async fn write(&self, buf: &[u8], off: usize) -> Result<usize> {
        if self.is_dir() {
            return Err(Error::BadRequest("write dir"));
        }
        off.checked_add(buf.len())
            .ok_or(Error::BadRequest("write buffer len overflow"))?;

        let umnt = self.umnt.read().await;
        let key = umnt.first().unwrap_or(&self.key);
        let ret = key.dev.write(&key.id, buf, off)?.await;
        drop(umnt);
        ret
    }

    /// Truncate wrapper.
    pub async fn truncate(&self, size: usize) -> Result<usize> {
        if self.is_dir() {
            return Err(Error::BadRequest("truncate dir"));
        }
        let umnt = self.umnt.read().await;
        let key = umnt.first().unwrap_or(&self.key);
        let ret = key.dev.truncate(&key.id, size)?.await;
        drop(umnt);
        ret
    }
}

struct Path<'a> {
    dotdots: usize,
    names: Vec<&'a str>,
}

impl<'a> TryFrom<&'a [u8]> for Path<'a> {
    type Error = Error;

    fn try_from(value: &'a [u8]) -> Result<Self> {
        let path: &str =
            str::from_utf8(value).map_err(|_| Error::BadRequest("path is not valid utf-8"))?;
        let mut dotdots = 0;
        let mut names = Vec::new();

        let mut eat = |name: &'a str| -> Result<()> {
            if name == ".." {
                if names.pop().is_none() {
                    dotdots += 1;
                }
            } else if !name.is_empty() && name != "." {
                vec_push(&mut names, name)?;
            }
            Ok(())
        };

        let mut l = 0;
        for (i, c) in path.char_indices() {
            if c == b'/' as char {
                eat(&path[l..i])?;
                l = i + 1;
            }
        }
        eat(&path[l..path.len()])?;
        Ok(Self { dotdots, names })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path() {
        let p = Path::try_from("".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 0);
        assert_eq!(p.names.is_empty(), true);

        let p = Path::try_from("a/b/c".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 0);
        assert_eq!(p.names, &["a", "b", "c"]);

        let p = Path::try_from("a/b/c/".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 0);
        assert_eq!(p.names, &["a", "b", "c"]);

        let p = Path::try_from("a/b/c////d".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 0);
        assert_eq!(p.names, &["a", "b", "c", "d"]);

        let p = Path::try_from("a/./b/c".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 0);
        assert_eq!(p.names, &["a", "b", "c"]);

        let p = Path::try_from("a/b/../c".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 0);
        assert_eq!(p.names, &["a", "c"]);

        let p = Path::try_from("../a../b/c".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 1);
        assert_eq!(p.names, &["a..", "b", "c"]);

        let p = Path::try_from("../a/b/c".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 1);
        assert_eq!(p.names, &["a", "b", "c"]);

        let p = Path::try_from("../a/b/../../c".as_bytes()).unwrap();
        assert_eq!(p.dotdots, 1);
        assert_eq!(p.names, &["c"]);
    }
}
