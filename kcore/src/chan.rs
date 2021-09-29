//! Channel and mount space.

use crate::{
    dev::Device,
    error::{Error, Result},
};
use alloc::{
    string::String,
    sync::{Arc, Weak},
    vec::Vec,
};
use core::{convert::TryFrom, fmt::Debug, iter, mem::MaybeUninit, ops::Deref, str};
use kalloc::wrapper::vec_push;
use ksched::{
    sync::{Mutex, RwLock},
    task::yield_now,
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
    pub fn new(dev: Arc<dyn Device + Send + Sync>, id: ChanId) -> Self {
        let dropped = false;
        Self { dev, id, dropped }
    }

    async fn dup(&self) -> Result<ChanKey> {
        match self.dev.open(&self.id, b"", None)?.await? {
            None => Err(Error::Gone("unexpected return value from reopen")),
            Some(id) => Ok(ChanKey::new(self.dev.clone(), id)),
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

impl Drop for ChanKey {
    /// Use [`Self::close`] instead, since Rust doesn't support async drop.
    ///
    /// FIXME: How to statically assert some function is unreachable?
    fn drop(&mut self) {
        debug_assert!(self.dropped, "forgot to close: {:?}", self);
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

/// Channel represents a virtual file from kernel's perspective.
#[derive(Debug)]
pub struct ChanInner {
    key: ChanKey,
    parent: Option<Chan>,
    name: String,

    /// Union mount point that derives Chan.
    /// Use ChanKey instead of Chan to avoid cycle in the graph.
    umnt: RwLock<Vec<ChanKey>>,
    /// The weak pointer must always be able to upgrade.
    child: Mutex<Vec<ChanWeak>>,
    // Managing all memory mapped pages from this chan.
    // pub(crate) pgmap: Spinlock<PageMap>,
}

impl ChanInner {
    fn new(key: ChanKey, parent: Option<Chan>, name: String) -> Self {
        Self {
            key,
            parent,
            name,
            umnt: RwLock::new(Vec::new()),
            child: Mutex::new(Vec::new()),
            // pgmap: Mutex::new(PageMap::default()),
        }
    }
}

pub(crate) type ChanWeak = Weak<ChanInner>;

#[derive(Debug)]
pub struct Chan(Arc<ChanInner>);

impl Deref for Chan {
    type Target = Arc<ChanInner>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Chan {
    /// Create a new mount space from the root of a device.
    pub async fn attach(dev: Arc<dyn Device + Send + Sync>, aname: &[u8]) -> Result<Self> {
        let uninit_chan = Arc::try_new_uninit()?;
        let chan_id = dev.clone().attach(aname)?.await?;
        let chan_key = ChanKey::new(dev, chan_id);
        let name_str = str::from_utf8(aname)?;
        let mut name = String::new();
        name.try_reserve(name_str.len())?;
        name.push_str(name_str);
        Ok(unsafe { Self::from_uninit(uninit_chan, chan_key, None, name) })
    }

    /// Create a new mount space rooted at a chan.
    pub async fn new(chan: &Self) -> Result<Self> {
        let uninit = Arc::try_new_uninit()?;
        let key = chan.key.dup().await?;
        Ok(unsafe { Self::from_uninit(uninit, key, None, String::new()) })
    }

    unsafe fn from_uninit(
        mut uninit: Arc<MaybeUninit<ChanInner>>,
        key: ChanKey,
        parent: Option<Self>,
        name: String,
    ) -> Self {
        Arc::get_mut_unchecked(&mut uninit)
            .as_mut_ptr()
            .write(ChanInner::new(key, parent, name));
        Chan(uninit.assume_init())
    }

    /// Mount all union directories from another chan to this chan.
    pub async fn mount(&self, from: &Self) -> Result<()> {
        if !self.is_dir() || !from.is_dir() {
            return Err(Error::BadRequest("cannot mount file"));
        }

        let mut keys = Vec::new();
        let result = async {
            let from_umnt = from.umnt.read().await;
            keys.try_reserve(from_umnt.len() + 1)?;
            for key in iter::once(&from.key).chain(from_umnt.iter()) {
                keys.push(key.dup().await?);
            }
            drop(from_umnt);

            let mut umnt = self.umnt.write().await;
            umnt.try_reserve(keys.len())?;
            keys.reverse();
            while let Some(key) = keys.pop() {
                umnt.push(key);
            }
            Ok(())
        }
        .await;
        while let Some(key) = keys.pop() {
            key.close().await;
        }
        result
    }

    /// Bind another chan to this chan and drop any previously bound chan.
    pub async fn bind(&self, chan: &Self) -> Result<()> {
        if self.is_dir() || chan.is_dir() {
            return Err(Error::BadRequest("cannot bind dir"));
        }

        let mut umnt = self.umnt.write().await;
        if umnt.is_empty() {
            umnt.try_reserve(1)?;
        }

        let new_key = chan.key.dup().await?;
        if let Some(key) = umnt.pop() {
            key.close().await;
        }
        umnt.push(new_key);
        Ok(())
    }

    /// Remove all mount point of this chan.
    pub async fn clear_mount(&self) {
        let mut g = self.umnt.write().await;
        while let Some(key) = g.pop() {
            key.close().await;
        }
    }

    /// Get the absolute path string of this chan.
    pub async fn path(&self) -> Result<String> {
        let mut path = Vec::new();
        let mut cur = self;
        while let Some(fa) = &cur.parent {
            for b in cur.name.as_bytes().iter().rev() {
                vec_push(&mut path, *b)?;
            }
            vec_push(&mut path, b'/')?;
            cur = fa;
        }
        if path.is_empty() {
            vec_push(&mut path, b'/')?;
        }
        path.reverse();
        Ok(unsafe { String::from_utf8_unchecked(path) })
    }

    /// Caller should guarantee `name` is non-empty.
    async fn open1(&self, name_str: &str, create_dir: Option<bool>) -> Result<Option<Self>> {
        debug_assert_eq!(name_str.is_empty(), false);
        if !self.is_dir() {
            return Ok(None);
        }

        let mut child = self.child.lock().await;
        for u in child.iter() {
            let chan = Chan::from_weak(u);
            if chan.name == name_str {
                return Ok(Some(chan));
            }
        }

        let uninit = Arc::try_new_uninit()?;
        let name_bytes = name_str.as_bytes();
        let mut name = String::new();
        name.try_reserve(name_str.len())?;
        name.push_str(name_str);
        child.try_reserve(1)?;

        let mut some_chan = None;
        let umnt = self.umnt.read().await;
        for key in iter::once(&self.key).chain(umnt.iter()) {
            debug_assert_eq!(key.id.kind, ChanKind::Dir);
            if let Some(id) = key.dev.open(&key.id, name_bytes, create_dir)?.await? {
                let new_key = ChanKey::new(key.dev.clone(), id);
                let parent = Some(self.dup());
                let chan = unsafe { Self::from_uninit(uninit, new_key, parent, name) };
                some_chan = Some(chan);
                break;
            }
        }
        Ok(some_chan.map(|chan| {
            child.push(Arc::downgrade(&chan));
            chan
        }))
    }

    /// Open a file located at path starting from this chan.
    ///
    /// Return [NotFound](Error::NotFound) if failed to find any directory components within the path.
    /// Otherwise it can find the parent directory.
    pub async fn open(&self, path: &[u8], create_dir: Option<bool>) -> Result<Option<Self>> {
        let path = Path::try_from(path)?;
        let mut cur = self.dup();
        for _ in 0..path.dotdots {
            if let Some(fa) = &cur.parent {
                // Do not need to close cur since cur is the ancestor of self
                // and self exists across this function and won't be closed.
                cur = fa.dup();
            }
        }
        for (i, name) in path.names.iter().enumerate() {
            let last = i == path.names.len() - 1;
            let to_create_dir = if last { create_dir } else { None };
            match cur.open1(name, to_create_dir).await {
                Err(e) => {
                    cur.close().await;
                    return Err(e);
                }
                Ok(None) => {
                    cur.close().await;
                    return if last {
                        Ok(None)
                    } else {
                        Err(Error::NotFound("failed to open intermediate directory"))
                    };
                }
                // Do not need to close cur since u is already the child of cur
                // and thus won't be closed.
                Ok(Some(u)) => cur = u,
            }
        }
        Ok(Some(cur))
    }

    async fn close1(self) -> Option<Self> {
        let parent = &self.parent;
        let self_child = self.child.lock().await;
        let mut parent_child = if let Some(parent) = parent {
            Some(parent.child.lock().await)
        } else {
            None
        };
        // Once we have locked this node and its parent, the reference count won't
        // decrease(but may be increased by dup) since every close operation also need to
        // enter this function. And if we are the last one, the reference count won't change.
        if Arc::strong_count(&self) == 1 {
            assert_eq!(self_child.len(), 0);
            while let Some(key) = self.umnt.try_write().unwrap().pop() {
                key.close().await;
            }
            if let Some(mut child) = parent_child.take() {
                let me = Arc::downgrade(&self);
                let i = child.iter().position(|x| Weak::ptr_eq(&me, x)).unwrap();
                child.swap_remove(i);
            }
            drop(parent_child);
            drop(self_child);

            let inner = self.into_inner();
            inner.key.close().await;
            inner.parent
        } else {
            None
        }
    }

    /// Close a file. The async destructor.
    pub async fn close(mut self) {
        while let Some(fa) = Self::close1(self).await {
            self = fa;
        }
    }

    /// Duplicate a handle of chan.
    pub fn dup(&self) -> Self {
        Chan(self.0.clone())
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

    fn into_inner(self) -> ChanInner {
        Arc::<ChanInner>::try_unwrap(self.0).unwrap()
    }

    pub(crate) fn from_weak(weak_chan: &ChanWeak) -> Self {
        Chan(weak_chan.upgrade().unwrap())
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
