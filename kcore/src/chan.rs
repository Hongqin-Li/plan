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
pub enum ChanType {
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
    pub ctype: ChanType,
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

    /// SAFETY: Your need to guarantee that the original key won't dropped
    /// when borrowed.
    unsafe fn borrow(&self) -> Self {
        Self {
            dev: self.dev.clone(),
            id: self.id,
            dropped: true,
        }
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

/// Mutable part of [Chan].
#[derive(Debug, Default)]
pub struct ChanInner {
    /// Union mount point that derives Chan.
    /// Use qid instead of Chan to avoid cycle in the graph.
    umnt: Vec<ChanKey>,
    /// The weak pointer must be able to upgrade.
    child: Vec<Weak<Chan>>,
}

/// Channel represents a virtual file from kernel's perspective.
#[derive(Debug)]
pub struct Chan {
    key: ChanKey,
    parent: Option<Arc<Chan>>,
    name: Vec<u8>,

    /// Inner mutable data.
    inner: RwLock<ChanInner>,
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
            // if u.is_dir() {
            //     vec_push(&mut buf, b'/')?;
            // }
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
        let key = Self::rekey(&chan).await?;
        Ok(unsafe { Self::from_key(key, a) })
    }

    unsafe fn from_key(key: ChanKey, mut a: Arc<MaybeUninit<Chan>>) -> Arc<Self> {
        Arc::get_mut_unchecked(&mut a).as_mut_ptr().write(Self {
            parent: None,
            inner: RwLock::new(ChanInner::default()),
            key,
            name: Vec::new(),
        });
        a.assume_init()
    }

    /// Retrieve key by reopening this chan.
    /// May failed(e.g. a removed disk chan).
    async fn rekey(self: &Arc<Self>) -> Result<ChanKey> {
        self.key.dev.open(&self.key.id, b"", None)?.await?.map_or(
            Err(Error::Gone("failed to rekey")),
            |id| {
                Ok(ChanKey {
                    dev: self.key.dev.clone(),
                    id,
                    dropped: false,
                })
            },
        )
    }

    /// Mount directory to this chan.
    pub async fn mount(&self, old: &Arc<Self>) -> Result<()> {
        if !(self.is_dir() && old.is_dir()) {
            return Err(Error::BadRequest("cannot mount file"));
        }
        let mut g = self.inner.write().await;
        g.umnt.try_reserve(1)?;
        let key = old.rekey().await?;
        Ok(g.umnt.push(key))
    }

    /// Bind file to this chan.
    pub async fn bind(&self, old: &Arc<Self>) -> Result<()> {
        if self.is_dir() || old.is_dir() {
            return Err(Error::BadRequest("cannot bind dir"));
        }
        let mut g = self.inner.write().await;
        if g.umnt.is_empty() {
            g.umnt.try_reserve(1)?;
        }
        let key = old.rekey().await?;
        if let Some(key) = g.umnt.pop() {
            key.close().await;
        }
        g.umnt.push(key);
        Ok(())
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

        let mut g = self.inner.write().await;
        for u in g.child.iter() {
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
        g.child.try_reserve(1)?;
        let mut a = Arc::<Self>::try_new_uninit()?;

        let mut some_chan = None;
        for key in iter::once(&self.key).chain(g.umnt.iter()) {
            debug_assert_eq!(key.id.ctype, ChanType::Dir);
            if let Some(id) = key.dev.open(&key.id, name, create_dir)?.await? {
                let u = unsafe {
                    Arc::get_mut_unchecked(&mut a).as_mut_ptr().write(Self {
                        parent: Some(self.clone()),
                        inner: RwLock::new(ChanInner::default()),
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
            g.child.push(Arc::<Self>::downgrade(&c));
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

        let mut ug = u.inner.write().await;
        let mut fg = if let Some(fa) = fa {
            Some(fa.inner.write().await)
        } else {
            None
        };
        // Once we have locked this node and its parent, the reference count won't
        // decrease(but may be increased by dup) since every close operation also need to
        // enter this function. And if we are the last one, the reference count won' change.
        let last = Arc::<Self>::strong_count(&u) == 1;

        if last {
            assert_eq!(ug.child.len(), 0);
            while let Some(ck) = ug.umnt.pop() {
                ck.close().await;
            }

            if let Some(mut fg) = fg.take() {
                let w = Arc::<Self>::downgrade(&u);
                let i = fg
                    .child
                    .iter()
                    .position(|x| Weak::<Self>::ptr_eq(&w, x))
                    .unwrap();
                fg.child.swap_remove(i);
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
        self.key.id.ctype == ChanType::Dir
    }

    /// Remove wrapper.
    pub async fn remove(&self) -> Result<bool> {
        self.key.dev.remove(&self.key.id)?.await
    }

    /// Stat wrapper.
    pub async fn stat(&self) -> Result<Dirent> {
        self.key.dev.stat(&self.key.id)?.await
    }

    /// Wstat wrapper.
    pub async fn wstat(&self, dirent: &Dirent) -> Result<()> {
        todo!();
        // self.key.dev.wstat(&self.key.id, dirent)?.await
    }

    /// Read wrapper.
    pub async fn read(&self, buf: &mut [u8], off: usize) -> Result<usize> {
        if self.is_dir() {
            return Err(Error::BadRequest("read dir"));
        }
        off.checked_add(buf.len())
            .ok_or(Error::BadRequest("read buffer len overflow"))?;

        let g = self.inner.read().await;
        let key = g.umnt.first().unwrap_or(&self.key);
        let ret = key.dev.read(&key.id, buf, off)?.await;
        drop(g);
        ret
    }
    /// Write wrapper.
    pub async fn write(&self, buf: &[u8], off: usize) -> Result<usize> {
        if self.is_dir() {
            return Err(Error::BadRequest("write dir"));
        }
        off.checked_add(buf.len())
            .ok_or(Error::BadRequest("write buffer len overflow"))?;

        let g = self.inner.read().await;
        let key = g.umnt.first().unwrap_or(&self.key);
        let ret = key.dev.write(&key.id, buf, off)?.await;
        drop(g);
        ret
    }

    /// Truncate wrapper.
    pub async fn truncate(&self, size: usize) -> Result<usize> {
        if self.is_dir() {
            return Err(Error::BadRequest("truncate dir"));
        }
        let g = self.inner.read().await;
        let key = g.umnt.first().unwrap_or(&self.key);
        let ret = key.dev.truncate(&key.id, size)?.await;
        drop(g);
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
