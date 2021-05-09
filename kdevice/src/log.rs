//! Log layer supporting transaction operations on blocks.
//!
//! The isolation level is Read Committed.
use crate::{
    cache::{CGuard, Cache, CacheData},
    cache_impl, from_bytes,
};
use intrusive_collections::intrusive_adapter;
use intrusive_collections::{LinkedList, LinkedListLink};

use alloc::sync::Arc;
use kcore::chan::Chan;
use kcore::error::{Error, Result};
use ksched::sync::{Condvar, Spinlock, SpinlockGuard};

use core::{cell::UnsafeCell, convert::TryInto, mem::swap};

use alloc::boxed::Box;
use static_assertions::const_assert_eq;

/// Block size. The block device hardware should guarantee that write to a block is always atomic.
/// That's, either all data in a single block is updated or not.
pub const BSIZE: usize = 512;

/// Maximum number of blocks to be trace by log.
/// Note that the log layer use additional one block to store log header. Thus, the total number of
/// blocks used by log is `LOGSIZE + 1`, which is exactly `BSIZE`.
pub const LOGSIZE: usize = 63;

/// Maximum number of blocks per transactional operation.
/// The caller should guarantee this between each pair of `begin_op` and `end_op`.
pub const MAXOPBLOCKS: usize = 20;

/// Maximum number of blocks per exclusive transactional operation.
pub const MAXEXOPBLOCKS: usize = LOGSIZE - (LOGSIZE % MAXOPBLOCKS);

/// Number of in-memory buffer.
/// Theoretically, `LOGSIZE + 2`(one for log header and one for `install_trans`) is enough.
pub const NBUF: usize = 100;

/// Magic value in the header.
pub const LOGMAGIC: u32 = 0xACAC;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LogState {
    Active,
    Commit,
    Redo,
    Redoing,
    Undo,
}

#[derive(Debug)]
struct LogHeader {
    magic: u32,
    n: u32,
    block: [u64; LOGSIZE],
}

#[derive(Debug)]
struct Node {
    link: LinkedListLink,
    committed: UnsafeCell<bool>,
}

unsafe impl Sync for Node {}

intrusive_adapter!(NodeAdapter = Arc<Node>: Node { link: LinkedListLink });

#[derive(Debug)]
struct LogInner {
    /// Block start is for log header, block [start+1, start+LOGSIZE] are for log blocks.
    start: usize,
    /// In-memory copy of log header.
    lh: LogHeader,
    /// How many operations are executing, i.e, after `begin_op` and not yet `end_op`.
    outstanding: usize,
    /// How many operations are ending.
    ending: usize,

    state: LogState,

    /// Waiters in `end_op`, to check if current transaction is committed
    /// or not.
    ender: LinkedList<NodeAdapter>,
}

/// Generic log layer with buffer cache.
#[derive(Debug)]
pub struct Log {
    disk: Chan,
    begin_cvar: Condvar,
    end_cvar: Condvar,
    bio: Spinlock<CacheData<usize, Box<[u8; BSIZE]>>>,
    log: Spinlock<LogInner>,
}

/// The bio cache.
impl Cache for Log {
    cache_impl!(usize, Box<[u8; BSIZE]>, bio);

    fn disk_read<'a>(&'a self, key: &'a Self::Key, val: &'a mut Self::Value) -> Self::ReadFut<'a> {
        async move {
            self.disk.read(val.as_mut(), key * BSIZE).await?;
            Ok(())
        }
    }

    fn disk_write<'a>(&'a self, key: &'a Self::Key, val: &'a Self::Value) -> Self::WriteFut<'a> {
        async move {
            self.disk.write(val.as_ref(), key * BSIZE).await?;
            Ok(())
        }
    }
}

impl Log {
    /// Create a buffer cache with maximum `nbuf` in-memory buffers.
    ///
    /// Close the disk on error.
    pub async fn new(nbuf: usize, start: usize, disk: Chan) -> Result<Self> {
        const_assert_eq!(LOGSIZE * 8 + 8, BSIZE);
        assert!(nbuf >= NBUF);
        match async {
            let mut buf = [0u8; BSIZE];
            disk.read(&mut buf, start * BSIZE).await?;

            let log = LogInner {
                start,
                outstanding: 0,
                ending: 0,
                ender: LinkedList::new(NodeAdapter::new()),
                state: LogState::Redo,
                lh: Self::read_head(&buf)?,
            };
            let bio = Self::new_cache(nbuf, || Ok(Box::try_new([0u8; BSIZE])?))?;
            Ok((log, bio))
        }
        .await
        {
            Err(e) => {
                disk.close().await;
                Err(e)
            }
            Ok((log, bio)) => Ok(Self {
                disk,
                bio,
                log: Spinlock::new(log),
                begin_cvar: Condvar::new(),
                end_cvar: Condvar::new(),
            }),
        }
    }

    /// Close the underlying disk file. Async destructor.
    pub async fn close(self) {
        self.disk.close().await;
    }

    /// Read and parse the log header from a disk block.
    fn read_head(buf: &[u8; BSIZE]) -> Result<LogHeader> {
        let magic = from_bytes!(u32, buf[0..4]);
        let n = from_bytes!(u32, buf[4..8]);
        let mut block = [0u64; LOGSIZE];

        if magic != LOGMAGIC || n > LOGSIZE as u32 {
            return Err(Error::InternalError);
        }

        for i in (8..64).step_by(8) {
            block[i / 8 - 1] = u64::from_le_bytes(buf[i..i + 8].try_into().unwrap());
        }
        Ok(LogHeader { magic, n, block })
    }

    /// Write the in-memory log header to disk.
    /// If failed, the log on disk won't be updated.
    async fn write_head(&self, log: &LogInner) -> Result<()> {
        let b = self.cache_get(log.start, false).await?.unwrap();
        let mut g = b.lock().await?;

        debug_assert_eq!(from_bytes!(u32, g[0..4]), LOGMAGIC);
        g[0..4].copy_from_slice(&LOGMAGIC.to_le_bytes());
        g[4..8].copy_from_slice(&log.lh.n.to_le_bytes());

        for i in 0..log.lh.n as usize {
            let left = (i + 1) * 8;
            g[left..left + 8].copy_from_slice(&log.lh.block[i].to_le_bytes());
        }

        g.unlock(true).await
    }

    /// Copy modified blocks from cache to log or install from log to disk.
    async fn install_trans(&self, log: &LogInner, to_log: bool) -> Result<()> {
        for i in 0..log.lh.n as usize {
            let (mut from, mut to) = (log.start + 1 + i, log.lh.block[i] as usize);
            if to_log {
                swap(&mut from, &mut to);
            };

            let from_buf = self.cache_get(from, false).await?.unwrap();
            let to_buf = self.cache_get(to, false).await?.unwrap();

            let from_guard = from_buf.lock().await?;
            let mut to_guard = match to_buf.lock().await {
                Ok(g) => g,
                Err(e) => {
                    from_guard.unlock(false).await.unwrap();
                    return Err(e);
                }
            };

            if to_log {
                debug_assert_eq!(from_guard.is_dirty(), true);
            }

            to_guard.clone_from_slice(from_guard.as_ref());
            debug_assert_eq!(to_guard[0..BSIZE], from_guard[0..BSIZE]);

            from_guard.unlock(false).await.unwrap();
            to_guard.unlock(true).await?;

            drop(from_buf);
            drop(to_buf);
        }
        Ok(())
    }

    /// Redo the log by copying committed blocks to destination.
    /// If failed, both in-memory and on-disk log won't be updated.
    async fn redo(&self, log: &mut LogInner) -> Result<()> {
        #[cfg(all(test, debug_assertions))]
        println!("redo begin: {:?}", log);

        if log.lh.n > 0 {
            self.install_trans(log, false).await?;
            let pre = log.lh.n;
            log.lh.n = 0;
            self.write_head(log).await.map_err(|e| {
                log.lh.n = pre;
                e
            })?
        }

        #[cfg(all(test, debug_assertions))]
        println!("redo end: {:?}", log);

        #[cfg(all(test, debug_assertions))]
        assert_eq!(
            super::cache::cache_stat(self),
            (0, 0),
            "cache not clean after redo"
        );

        Ok(())
    }

    fn undo(&self, log: &mut LogInner) {
        log.lh.n = 0;
        self.cache_invalidate();

        #[cfg(all(test, debug_assertions))]
        assert_eq!(super::cache::cache_stat(self), (0, 0));
    }

    async fn commit(&self, log: &LogInner) -> Result<()> {
        if log.lh.n > 0 {
            self.install_trans(log, true).await?;
            self.write_head(log).await?;
        }
        Ok(())
    }

    /// Called at the start of each transaction.
    pub async fn begin_opx(&self, reserved: usize) -> Result<()> {
        let (redo, mut log) = loop {
            let log = self.log.lock();
            if log.state == LogState::Active {
                if log.lh.n as usize + (log.outstanding + reserved) * MAXOPBLOCKS <= LOGSIZE {
                    break (false, log);
                }
            } else if log.state == LogState::Redo {
                break (true, log);
            }
            self.begin_cvar.spin_await_notify(log).await;
        };

        if redo {
            log.state = LogState::Redoing;
            drop(log);

            let log1 = unsafe { self.log.get_mut() };
            let failed = self.redo(log1).await.is_err();
            let mut g = self.log.lock();
            g.state = if failed {
                LogState::Redo
            } else {
                LogState::Active
            };
            self.begin_cvar.notify_all();

            if failed {
                drop(g);
                return Err(Error::InternalError);
            }
            log = g;
        }
        log.outstanding += reserved;
        #[cfg(all(test, debug_assertions))]
        println!("transaction begin_op: resv {}, {:?}", reserved, log);
        drop(log);
        Ok(())
    }
    async fn end_opx<'a>(&'a self, bad: bool, wait: bool, reserved: usize) -> OpGuard<'a> {
        let mut log = self.log.lock();
        if bad {
            log.state = LogState::Undo;
        }
        log.outstanding -= reserved;
        if log.outstanding != 0 {
            if log.state == LogState::Undo && !wait {
                return OpGuard {
                    log: self,
                    guard: None,
                    committed: false,
                };
            }

            let u = loop {
                // FIXME: pre-allocate and reuse them?
                if let Ok(u) = Arc::try_new(Node {
                    committed: UnsafeCell::new(true),
                    link: LinkedListLink::new(),
                }) {
                    break u;
                }
            };
            log.ender.push_back(u.clone());

            // begin_op() may be waiting for log space,
            // and decrementing log.outstanding has decreased
            // the amount of reserved space.
            self.begin_cvar.notify_all();

            let guard = if wait {
                log.ending += 1;
                Some(self.end_cvar.spin_wait(log).await)
            } else {
                self.end_cvar.spin_await_notify(log).await;
                None
            };
            let committed = unsafe { *u.committed.get() };
            return OpGuard {
                log: self,
                guard,
                committed,
            };
        }
        if log.state == LogState::Active {
            log.state = LogState::Commit;
        } else {
            assert_eq!(log.state, LogState::Undo);
        }
        drop(log);

        // Call commit without holding locks, since not allowed
        // to sleep with locks.
        //
        // SAFETY:
        //
        // Guarded by `log.state == Commit || Undo`, no one can access `log` until
        // committing becomes false later. After that, `drop(log)` will
        // synchronize all memory writes before it, including the
        // modification of `log` in `commit`. Thus, no need for memory
        // fence here.
        let log = unsafe { self.log.get_mut() };
        let committed = if log.state == LogState::Undo || self.commit(log).await.is_err() {
            self.undo(log);
            // Notify that this transaction failed.
            while let Some(tx) = log.ender.pop_front() {
                unsafe { *tx.committed.get() = false };
            }
            false
        } else {
            log.ender.clear();
            true
        };

        let mut g = self.log.lock();
        g.ending += 1;

        self.end_cvar.notify_all();

        OpGuard {
            log: self,
            guard: Some(g),
            committed,
        }
    }

    /// Start an exclusive operation.
    ///
    /// At any time, only one exclusive operation or some normal operations are allowed to be
    /// active.
    pub async fn begin_exop(&self) -> Result<()> {
        self.begin_opx(MAXEXOPBLOCKS / MAXOPBLOCKS).await
    }

    /// End an exlusive operation.
    pub async fn end_exop<'a>(&'a self, bad: bool, wait: bool) -> OpGuard<'a> {
        self.end_opx(bad, wait, MAXEXOPBLOCKS / MAXOPBLOCKS).await
    }

    /// Called at the start of each transaction.
    pub async fn begin_op(&self) -> Result<()> {
        self.begin_opx(1).await
    }

    /// Called at the end of each operation.
    ///
    /// Try to commit if this was the last outstanding operation. Otherwise wait until transaction
    /// completes.
    ///
    /// If mark as bad, every operation in this transaction won't execute.
    ///
    /// If wait is true, new transactions won't enter `begin_op` until all waiters of current
    /// transaction have dropped their guards. This is useful when you want to block new operations
    /// and clean something when the current transaction is bad.
    ///
    /// Return whether the whole transaction is actually committed or not.
    pub async fn end_op<'a>(&'a self, bad: bool, wait: bool) -> OpGuard<'a> {
        self.end_opx(bad, wait, 1).await
    }

    /// Keep track of a buffer in log.
    ///
    /// Return the number of newly traced blocks (0 or 1).
    ///
    /// NOTE:
    /// 1. Must use `cache_get` without flush to avoid emitting dirty blocks,
    ///    which is handled by log.
    /// 2. Must use this function instead of `unlock`.
    pub async fn trace<'a>(&'a self, buf: CGuard<'a, Self>) -> usize {
        let mut new = 0;
        if buf.is_dirty() {
            let key = buf.key().try_into().unwrap();

            let mut found = false;
            let mut inner = self.log.lock();
            let n = inner.lh.n as usize;
            for i in 0..n {
                if inner.lh.block[i] == key {
                    found = true;
                    break;
                }
            }
            if !found {
                inner.lh.block[n] = key;
                inner.lh.n += 1;
                new = 1;

                #[cfg(all(test, debug_assertions))]
                {
                    let mut bnos = alloc::vec::Vec::new();
                    for x in inner.lh.block[..inner.lh.n as usize].iter() {
                        bnos.push(x);
                    }
                    println!(
                        "log trace new dirty block: bno {}, n {}, blocks {:?}",
                        key, inner.lh.n, bnos
                    );
                }

                assert!(inner.lh.n <= LOGSIZE as u32);
            }
        }
        buf.unlock(false).await.unwrap();
        new
    }
}

/// Returned by `end_op`.
pub struct OpGuard<'a> {
    log: &'a Log,
    guard: Option<SpinlockGuard<'a, LogInner>>,
    /// If this operation is committed or not finally.
    pub committed: bool,
}

impl<'a> Drop for OpGuard<'a> {
    fn drop(&mut self) {
        if let Some(mut g) = self.guard.take() {
            debug_assert!(g.state == LogState::Commit || g.state == LogState::Undo);
            g.ending -= 1;
            if g.ending == 0 {
                g.state = if self.committed {
                    LogState::Redo
                } else {
                    LogState::Active
                };
                self.log.begin_cvar.notify_all();
                #[cfg(all(test, debug_assertions))]
                println!(
                    "transaction end{}",
                    if self.committed { "" } else { ": bad!" }
                );
            }
            drop(g);
        }
    }
}

#[cfg(test)]
mod tests {
    use kcore::dev::Device;
    use ksched::task::yield_now;

    use super::*;
    use ktest::{fs::MemDisk, rand_int, run_multi};

    #[test]
    fn test_all() {
        let ntask = 100;
        let ncpu = 10;
        let log_start = 1000;
        ksched::task::spawn(0, async move {
            let disk = Arc::new(MemDisk::new(1100 * BSIZE));
            let disk_chan = disk.attach(b"").unwrap().await.unwrap();

            // Install magic.
            disk_chan
                .write(&LOGMAGIC.to_le_bytes(), log_start * BSIZE)
                .await
                .unwrap();

            let log = Arc::new(Log::new(100, log_start, disk_chan).await.unwrap());
            for _ in 0..ntask {
                let log = log.clone();
                ksched::task::spawn(0, async move {
                    log.begin_op().await.unwrap();
                    for _ in 0..MAXOPBLOCKS {
                        let buf = log
                            .cache_get(rand_int(0..1000), false)
                            .await
                            .unwrap()
                            .unwrap();
                        let mut g = buf.lock().await.unwrap();
                        for i in 0..BSIZE {
                            g[i] = rand_int(0..0xFF) as u8;
                        }
                        log.trace(g).await;
                    }
                    let wait = rand_int(0..2) == 1;
                    log.end_op(false, wait).await;
                })
                .unwrap();
            }

            while Arc::strong_count(&log) != 1 {
                yield_now().await;
            }
            Arc::try_unwrap(log).unwrap().close().await;
        })
        .unwrap();
        run_multi(ncpu);
    }
}
