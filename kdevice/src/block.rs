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
use ksched::sync::{Mutex, MutexGuard, Spinlock, SpinlockGuard};

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
    part: Option<[Spinlock<BlockPart>; 4]>,
}

impl BlockSlotInner {
    fn use_all(&self) -> Result<()> {
        let part = self.part.as_ref().unwrap();
        let mut i = 0;
        for part in part.iter() {
            let mut part = part.lock();
            if part.used {
                break;
            }
            part.used = true;
            i += 1;
        }
        if i != part.len() {
            for part in part[0..i].iter() {
                let mut part = part.lock();
                debug_assert!(part.used);
                part.used = false;
            }
            Err(Error::Conflict("disk occupied"))
        } else {
            Ok(())
        }
    }

    fn probe(&mut self) -> Result<()> {
        self.bus.probe()?;

        // Parse MBR.
        let mut buf = [0u8; BSIZE];
        self.bus.read(0, &mut buf)?;

        // FIXME:
        debug_assert_eq!(buf[510], 0x55);
        debug_assert_eq!(buf[511], 0xAA);

        const R: Spinlock<BlockPart> = Spinlock::new(BlockPart {
            used: false,
            range: 0..0,
        });
        let part = [R; 4];

        for i in 0..4 {
            let off = 446 + i * 16;
            let ent = &buf[off..off + 16];
            let start_bno = from_bytes!(u32, ent[8..12]);
            let part_size = from_bytes!(u32, ent[12..16]);
            let end_bno = start_bno
                .checked_add(part_size)
                .ok_or(Error::InternalError("partition size overflow"))?;
            part[i].lock().range = (start_bno as usize)..(end_bno as usize);
        }

        // Check intersection.
        for i in 0..4 {
            for j in (i + 1)..4 {
                if intersect(&part[i].lock().range, &part[j].lock().range) {
                    return Err(Error::InternalError("partition intersect"));
                }
            }
        }

        self.version += 1;
        self.part = Some(part);
        Ok(())
    }
}

/// Representing a physical device slot.
pub struct BlockSlot {
    name: &'static str,
    inner: Spinlock<BlockSlotInner>,
}

impl BlockSlot {
    /// Create a slot with name and bus driver.
    pub fn new(name: &'static str, bus: Box<dyn BlockBus + Send + Sync>) -> Self {
        Self {
            name,
            inner: Spinlock::new(BlockSlotInner {
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
    fn get_slot(&self, c: &ChanId) -> Result<SpinlockGuard<'_, BlockSlotInner>> {
        let g = self.0[path_slot(c.path)].inner.lock();
        if c.version != g.version || g.part.is_none() {
            return Err(Error::Gone("failed to get removed slot"));
        }
        Ok(g)
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
                        let mut sloti = slot.inner.lock();
                        if sloti.part.is_some() {
                            return Ok(None);
                        }
                        sloti.probe()?;
                        // Disk file is open as exclusive mode.
                        sloti.use_all()?;
                        return Ok(Some(ChanId {
                            path: to_path(i, None, 0),
                            version: sloti.version,
                            kind: ChanKind::File,
                        }));
                    }
                }
            }
            return Err(Error::BadRequest("create unregistered block file"));
        }

        for (i, slot) in self.0.iter().enumerate() {
            if name.starts_with(slot.name.as_bytes()) {
                let mut sloti = slot.inner.lock();
                let kind = ChanKind::File;
                let version = sloti.version as u32;
                if let Some(part) = &mut sloti.part {
                    if name.len() == slot.name.len() {
                        // Disk file is open as exclusive mode.
                        sloti.use_all()?;
                        return Ok(Some(ChanId {
                            path: to_path(i, None, 0),
                            version,
                            kind,
                        }));
                    } else if name.len() == slot.name.len() + 1 {
                        if let Some(pi) = name.last().unwrap().checked_sub(b'1') {
                            if let Some(part) = part.get(pi as usize) {
                                let mut part = part.lock();
                                if part.range.len() == 0 {
                                    return Ok(None);
                                } else if part.used {
                                    return Err(Error::Conflict("partition occupied"));
                                }
                                part.used = true;
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

        let sloti = match self.get_slot(&c) {
            Ok(sloti) => sloti,
            _ => return,
        };
        if let Some(part) = &sloti.part {
            if let Some(pi) = path_part(c.path) {
                let mut part = part[pi].lock();
                debug_assert_eq!(part.used, true);
                part.used = false;
            } else {
                for part in part.iter() {
                    let mut part = part.lock();
                    debug_assert_eq!(part.used, true);
                    part.used = false;
                }
            }
        } else {
            // Slot removed.
            debug_assert!(path_part(c.path).is_none());
        }
    }

    /// Remove a block device.
    /// Active partition within device are not allowed to be removed.
    async fn remove(&self, c: &ChanId) -> Result<bool> {
        if c.kind == ChanKind::Dir {
            return Err(Error::BadRequest("remove block root dir"));
        }
        let mut sloti = match self.get_slot(&c) {
            Ok(sloti) => sloti,
            _ => return Ok(true),
        };
        if path_part(c.path).is_some() {
            return Err(Error::BadRequest("remove partition file"));
        }
        sloti.part = None;
        Ok(true)
    }

    async fn truncate(&self, c: &ChanId, size: usize) -> Result<usize> {
        debug_assert_eq!(c.kind, ChanKind::File);
        let sloti = self.0[path_slot(c.path)].inner.lock();
        if c.version != sloti.version || sloti.part.is_none() {
            return Err(Error::Gone("truncate removed slot"));
        }
        let part = sloti.part.as_ref().unwrap();
        let oldsz = if let Some(pi) = path_part(c.path) {
            part[pi].lock().range.len()
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

        let mut sloti = self.0[path_slot(c.path)].inner.lock();
        if c.version != sloti.version || sloti.part.is_none() {
            return Err(Error::Gone("read removed slot"));
        }
        let part = sloti.part.as_ref().unwrap();
        let bno_off = if let Some(pi) = path_part(c.path) {
            part[pi].lock().range.start
        } else {
            0
        };

        let mut cnt = 0;
        for addr in (off..end).step_by(BSIZE) {
            let bno = match bno_off.checked_add(addr / BSIZE) {
                Some(x) => x,
                None => return Ok(cnt),
            };
            if sloti
                .bus
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

        let mut slot = self.0[path_slot(c.path)].inner.lock();
        if c.version != slot.version || slot.part.is_none() {
            return Err(Error::Gone("write removed slot"));
        }
        let part = slot.part.as_ref().unwrap();
        let bno_off = if let Some(pi) = path_part(c.path) {
            part[pi].lock().range.start
        } else {
            0
        };

        let mut cnt = 0;
        for addr in (off..end).step_by(BSIZE) {
            let bno = match bno_off.checked_add(addr / BSIZE) {
                Some(x) => x,
                None => return Ok(cnt),
            };
            if slot
                .bus
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
