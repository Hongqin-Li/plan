//! Channel and mount space.

use alloc::sync::Weak;
use alloc::vec::Vec;
use core::{cmp::min, convert::TryFrom, fmt::Debug, iter, mem::MaybeUninit, str};
use kalloc::wrapper::vec_push;
use ksched::{sync::Mutex, task::yield_now};

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
    inner: Mutex<ChanInner>,
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

    /// Create a new mount space rooted at a chan.
    pub async fn new(chan: &Arc<Chan>) -> Result<Arc<Self>> {
        let a = Arc::<Chan>::try_new_uninit()?;
        let key = Self::rekey(&chan).await?;
        Ok(unsafe { Self::from_key(key, a) })
    }

    unsafe fn from_key(key: ChanKey, mut a: Arc<MaybeUninit<Chan>>) -> Arc<Self> {
        Arc::get_mut_unchecked(&mut a).as_mut_ptr().write(Self {
            parent: None,
            inner: Mutex::new(ChanInner::default()),
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

    /// Mount file `old` to this chan.
    pub async fn mount(&self, old: &Arc<Self>) -> Result<()> {
        let mut g = self.inner.lock().await;
        if let Err(e) = g.umnt.try_reserve(1) {
            return Err(e.into());
        }
        let key = old.rekey().await?;
        Ok(g.umnt.push(key))
    }

    /// Caller should guarantee `name` is non-empty.
    async fn open1(
        self: &Arc<Self>,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<Arc<Chan>>> {
        debug_assert_eq!(name.is_empty(), false);

        let mut g = self.inner.lock().await;
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
        for ck in iter::once(&self.key).chain(g.umnt.iter()) {
            if let Some(id) = ck.dev.open(&ck.id, name, create_dir)?.await? {
                let u = unsafe {
                    Arc::get_mut_unchecked(&mut a).as_mut_ptr().write(Self {
                        parent: Some(self.clone()),
                        inner: Mutex::new(ChanInner::default()),
                        key: ChanKey {
                            dev: ck.dev.clone(),
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

        let mut ug = u.inner.lock().await;
        let mut fg = if let Some(fa) = fa {
            Some(fa.inner.lock().await)
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
        self.key.dev.wstat(&self.key.id, dirent)?.await
    }
    /// Read wrapper.
    pub async fn read(&self, buf: &mut [u8], off: usize) -> Result<usize> {
        off.checked_add(buf.len())
            .ok_or(Error::BadRequest("read buffer len overflow"))?;
        self.key.dev.read(&self.key.id, buf, off)?.await
    }
    /// Write wrapper.
    pub async fn write(&self, buf: &[u8], off: usize) -> Result<usize> {
        off.checked_add(buf.len())
            .ok_or(Error::BadRequest("write buffer len overflow"))?;
        self.key.dev.write(&self.key.id, buf, off)?.await
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
