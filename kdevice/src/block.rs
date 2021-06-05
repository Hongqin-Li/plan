//! Block device driver.

use crate::from_bytes;
use alloc::boxed::Box;
use core::{convert::TryInto, ops::Range};

use kcore::{
    async_trait,
    chan::{ChanId, ChanKind, Dirent},
    dev::Device,
    error::{Error, Result},
    utils::intersect,
};
use ksched::sync::{Mutex, MutexGuard};

/// Block size. The block device hardware should guarantee that write to a block is always atomic.
/// That's, either all data in a single block is updated or not.
pub const BSIZE: usize = 512;

fn path_slot(path: u64) -> usize {
    ((path >> 32) & 0xFFFF_FFFF) as usize
}
fn path_part(path: u64) -> Option<usize> {
    let x = ((path >> 16) & 0xFFFF) as u16;
    if x == u16::MAX {
        None
    } else {
        Some(x as usize)
    }
}
fn path_type(path: u64) -> usize {
    (path & 0xFFFF) as usize
}

fn to_path(slot: usize, part: Option<usize>, ptype: usize) -> u64 {
    let (slot, ptype) = (slot as u64, ptype as u64);
    let part = part.unwrap_or(u16::MAX as usize) as u64;
    (slot << 32) | ((part & 0xFFFF) << 16) | (ptype & 0xFFFF)
}

/// Block device trait that you need to implement for each slot.
///
/// For each instance, all three methods are guaranteed to becalled exlusively.
pub trait BlockBus {
    /// Return Ok if the bus is active.
    fn probe(&mut self) -> Result<()>;
    /// Read a block from the block device.
    fn read(&mut self, bno: usize, buf: &mut [u8]) -> Result<()>;
    /// Write a block to the block device.
    fn write(&mut self, bno: usize, buf: &[u8]) -> Result<()>;
}

/// A partion in a block device.
struct BlockPart {
    /// Whether this partition is being used.
    ///
    /// When open the whole block device as a file, (e.g. file of name "emmc"), all partition
    /// must not in used in order to avoid data races.
    used: bool,
    /// Range in block number of this  partition.
    range: Range<usize>,
}
struct BlockSlotInner {
    version: u32,
    bus: Box<dyn BlockBus + Send + Sync>,

    /// None means it has been removed.
    /// Only support MBR with four partitions now.
    part: Option<[BlockPart; 4]>,
}

/// Representing a physical device slot.
pub struct BlockSlot {
    name: &'static str,
    inner: Mutex<BlockSlotInner>,
}

impl BlockSlot {
    /// Create a slot with name and bus driver.
    pub fn new(name: &'static str, bus: Box<dyn BlockBus + Send + Sync>) -> Self {
        Self {
            name,
            inner: Mutex::new(BlockSlotInner {
                version: 0,
                bus,
                part: None,
            }),
        }
    }
}

/// Block device driver.
pub struct Blocks<const N: usize>([BlockSlot; N]);

impl<const N: usize> Blocks<N> {
    /// Create a new block driver that handles several physical slots.
    pub fn new(slots: [BlockSlot; N]) -> Self {
        Self(slots)
    }

    /// If ok, `inner.part` is guaranteed to be non empty.
    /// Return error iff the chan id is deprecated, i.e. the block has been removed.
    async fn get_slot(&self, c: &ChanId) -> Result<MutexGuard<'_, BlockSlotInner>> {
        let g = self.0[path_slot(c.path)].inner.lock().await;
        if c.version != g.version || g.part.is_none() {
            return Err(Error::Gone("failed to get removed slot"));
        }
        Ok(g)
    }

    fn probe(&self, inner: &mut MutexGuard<'_, BlockSlotInner>) -> Result<()> {
        inner.bus.probe()?;

        // Parse MBR.
        let mut buf = [0u8; BSIZE];
        inner.bus.read(0, &mut buf)?;

        // FIXME:
        debug_assert_eq!(buf[510], 0x55);
        debug_assert_eq!(buf[511], 0xAA);

        const R: BlockPart = BlockPart {
            used: false,
            range: 0..0,
        };
        let mut part = [R; 4];

        for i in 0..4 {
            let off = 446 + i * 16;
            let ent = &buf[off..off + 16];
            let start_bno = from_bytes!(u32, ent[8..12]);
            let part_size = from_bytes!(u32, ent[12..16]);
            let end_bno = start_bno
                .checked_add(part_size)
                .ok_or(Error::InternalError("partition size overflow"))?;
            part[i].range = (start_bno as usize)..(end_bno as usize);
        }

        // Check intersection.
        for i in 0..4 {
            for j in (i + 1)..4 {
                if intersect(&part[i].range, &part[j].range) {
                    return Err(Error::InternalError("partition intersect"));
                }
            }
        }

        inner.version += 1;
        inner.part = Some(part);
        Ok(())
    }
}

#[async_trait::async_trait_try]
impl<const N: usize> Device for Blocks<N> {
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
        Ok(ChanId {
            path: 0,
            version: b'b' as u32,
            kind: ChanKind::Dir,
        })
    }
    async fn open(
        &self,
        dir: &ChanId,
        name: &[u8],
        create_dir: Option<bool>,
    ) -> Result<Option<ChanId>> {
        if name.is_empty() {
            if dir.kind == ChanKind::Dir {
                return Ok(Some(dir.clone()));
            } else {
                // Since devices and their partitions are opened exclusively.
                return Err(Error::Conflict("dup of block file"));
            }
        }
        debug_assert_eq!(dir.kind, ChanKind::Dir);
        if let Some(create_dir) = create_dir {
            if !create_dir {
                // Create a block device file by probing.
                for (i, slot) in self.0.iter().enumerate() {
                    if slot.name.as_bytes() == name {
                        let mut g = slot.inner.lock().await;
                        if g.part.is_some() {
                            return Ok(None);
                        }
                        self.probe(&mut g)?;
                        // Disk file is open as exclusive mode.
                        for p in g.part.as_mut().unwrap().iter_mut() {
                            p.used = true;
                        }
                        return Ok(Some(ChanId {
                            path: to_path(i, None, 0),
                            version: g.version,
                            kind: ChanKind::File,
                        }));
                    }
                }
            }
            return Err(Error::BadRequest("create unregistered block file"));
        }

        for (i, slot) in self.0.iter().enumerate() {
            if name.starts_with(slot.name.as_bytes()) {
                let mut g = slot.inner.lock().await;
                let kind = ChanKind::File;
                let version = g.version as u32;
                if let Some(part) = &mut g.part {
                    if name.len() == slot.name.len() {
                        if part.iter().find(|p| p.used).is_some() {
                            return Err(Error::Conflict("disk occupied"));
                        }

                        // Disk file is open as exclusive mode.
                        for p in part.iter_mut() {
                            p.used = true;
                        }
                        return Ok(Some(ChanId {
                            path: to_path(i, None, 0),
                            version,
                            kind,
                        }));
                    } else if name.len() == slot.name.len() + 1 {
                        if let Some(pi) = name.last().unwrap().checked_sub(b'1') {
                            if let Some(BlockPart { used, range }) = part.get_mut(pi as usize) {
                                if range.len() == 0 {
                                    return Ok(None);
                                } else if *used {
                                    return Err(Error::Conflict("partition occupied"));
                                }
                                *used = true;
                                return Ok(Some(ChanId {
                                    path: to_path(i, Some(pi as usize), 0),
                                    version,
                                    kind,
                                }));
                            }
                        }
                    }
                }
            }
        }
        Ok(None)
    }
    async fn close(&self, c: ChanId) {
        if c.kind == ChanKind::Dir {
            return;
        }

        let mut g = match self.get_slot(&c).await {
            Ok(x) => x,
            _ => return,
        };
        let part = g.part.as_mut().unwrap();
        if let Some(pi) = path_part(c.path) {
            debug_assert_eq!(part[pi].used, true);
            part[pi].used = false;
        } else {
            for BlockPart { used, range } in part.iter_mut() {
                debug_assert_eq!(*used, true);
                *used = false;
            }
        }
    }
    /// Remove a block device.
    /// Active partition within device are not allowed to be removed.
    async fn remove(&self, c: &ChanId) -> Result<bool> {
        if c.kind == ChanKind::Dir {
            return Err(Error::BadRequest("remove block root dir"));
        }
        let mut g = match self.get_slot(&c).await {
            Ok(g) => g,
            _ => return Ok(true),
        };
        if path_part(c.path).is_some() {
            return Err(Error::BadRequest("remove partition file"));
        }
        g.part = None;
        Ok(true)
    }

    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        debug_assert_eq!(c.kind, ChanKind::File);
        let g = self.0[path_slot(c.path)].inner.lock().await;
        if c.version != g.version || g.part.is_none() {
            return Err(Error::Gone("truncate removed slot"));
        }
        let part = g.part.as_ref().unwrap();
        let oldsz = if let Some(pi) = path_part(c.path) {
            part[pi].range.len()
        } else {
            0
        };
        if size >= oldsz {
            Ok(oldsz)
        } else {
            Err(Error::BadRequest("resize file of devblock"))
        }
    }

    async fn stat(&self, c: &ChanId) -> Result<Dirent> {
        todo!()
    }

    async fn wstat(&self, c: &ChanId, dirent: &Dirent) -> Result<()> {
        todo!()
    }

    async fn read(&self, c: &ChanId, buf: &mut [u8], off: usize) -> Result<usize> {
        debug_assert_eq!(c.kind, ChanKind::File);

        // TODO: Allow any block address.
        if off % BSIZE != 0 || buf.len() % BSIZE != 0 {
            todo!();
        }
        let end = buf.len() + off;

        let mut g = self.0[path_slot(c.path)].inner.lock().await;
        if c.version != g.version || g.part.is_none() {
            return Err(Error::Gone("read removed slot"));
        }
        let part = g.part.as_ref().unwrap();
        let bno_off = if let Some(pi) = path_part(c.path) {
            part[pi].range.start
        } else {
            0
        };

        let mut cnt = 0;
        for addr in (off..end).step_by(BSIZE) {
            let bno = match bno_off.checked_add(addr / BSIZE) {
                Some(x) => x,
                None => return Ok(cnt),
            };
            if g.bus
                .read(bno, &mut buf[addr - off..addr - off + BSIZE])
                .is_err()
            {
                return Ok(cnt);
            }
            cnt += BSIZE;
        }
        Ok(cnt)
    }

    async fn write(&self, c: &ChanId, buf: &[u8], off: usize) -> Result<usize> {
        debug_assert_eq!(c.kind, ChanKind::File);

        // TODO: Allow any block address.
        if off % BSIZE != 0 || buf.len() % BSIZE != 0 {
            todo!();
        }
        let end = buf.len() + off;

        let mut g = self.0[path_slot(c.path)].inner.lock().await;
        if c.version != g.version || g.part.is_none() {
            return Err(Error::Gone("write removed slot"));
        }
        let part = g.part.as_ref().unwrap();
        let bno_off = if let Some(pi) = path_part(c.path) {
            part[pi].range.start
        } else {
            0
        };

        let mut cnt = 0;
        for addr in (off..end).step_by(BSIZE) {
            let bno = match bno_off.checked_add(addr / BSIZE) {
                Some(x) => x,
                None => return Ok(cnt),
            };
            if g.bus
                .write(bno, &buf[addr - off..addr - off + BSIZE])
                .is_err()
            {
                return Ok(cnt);
            }
            cnt += BSIZE;
        }
        Ok(cnt)
    }
}
