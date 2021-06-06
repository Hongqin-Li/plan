//! Simulated i-node layer of FAT32 file system.
use alloc::boxed::Box;
use core::{
    cmp::{max, min},
    convert::{TryFrom, TryInto},
    fmt::Debug,
    hash::Hash,
    mem::ManuallyDrop,
    ops::Range,
    usize,
};

use super::fname::{
    lfn_init, lfn_name, lfn_set_name, sfn_attr, sfn_cno, sfn_name, sfn_set_attr, sfn_set_cno,
    sfn_set_name, sfn_set_size, sfn_size, Filename, ATTR_ARCHIVE, ATTR_DIRECTORY, ATTR_LONG_NAME,
    ATTR_LONG_NAME_MASK, DIRENTSZ, LAST_LONG_ENTRY, MAX_NUMERIC_TAIL,
};
use crate::{
    block::BSIZE,
    cache::{CEntry, CGuard, CNodePtr, Cache, CacheData},
    cache_impl,
    fat::fname::checksum,
    from_bytes,
    log::{Log, LOGMAGIC, LOGSIZE},
};

use alloc::{sync::Arc, vec::Vec};
use kalloc::wrapper::vec_push;
use kcore::{
    chan::{Chan, Dirent},
    error::{Error, Result},
};
use ksched::sync::Spinlock;

const FAT_MASK: u32 = 0x0FFF_FFFF;
const FAT_END: u32 = 0x0FFF_FFF8;
const FAT_BAD: u32 = 0x0FFF_FFF7;
const FAT_EMPTY: u32 = 0;
/// Maximum directory size stated in FAT32 spec.
const MAX_DIRSZ: u32 = 65536 * DIRENTSZ as u32;

/// Common routine of readi and writei.
macro_rules! rwinode {
    ($sel:ident, $ip:ident, $buf:ident, $off:ident, $fn:ident) => {{
        let (bps, spc) = ($sel.meta.bps, $sel.meta.spc);
        let bpc = bps * spc;

        let mut ret = 0;

        // Read size info.
        let sz = $sel.resize($ip, |x| x).await? as usize;
        let end = min($off + $buf.len(), sz);
        if end <= $off {
            return Ok(ret);
        }

        let mut i = $off;
        while i < end {
            let ci = i / bpc;
            let (si, soff) = (ci % spc, i % bps);
            let n = min(bps - soff, end - i);

            let cno = $ip.addr.get(ci).ok_or(Error::InternalError("fatrw"))?;
            let disk_si = $sel.meta.data_off + (*cno as usize - 2) * spc + si;

            let b: CEntry<'a, Log> = $sel.log.cache_get(disk_si, false).await?.unwrap();
            let mut g = b.lock().await?;
            $fn($buf, &mut g, i - $off, soff, n);
            $sel.log.trace(g).await;

            i += n;
            ret += n;
        }
        debug_assert!(ret <= $buf.len());
        Ok(ret)
    }};
}

/// TFAT32
#[derive(Debug)]
pub struct FAT {
    pub(crate) meta: FATMeta,
    pub(crate) log: Log,
    pub(crate) icache: Spinlock<CacheData<InodeKey, Inode>>,
}

#[derive(Debug, Clone)]
pub struct FATMeta {
    /// Number of bytes per sector.
    pub bps: usize,
    /// Number of sector per cluster.
    pub spc: usize,
    /// Offset in sectors from beginning of the disk to the first data cluster(i.e. cluster 2).
    data_off: usize,
    /// The count of data clusters starting at cluster 2.
    data_clust: usize,
    /// Offset in sectors from the beginnig of the disk to the first fat.
    fat_off: usize,
    /// Number of sectors per FAT.
    fat_sect: usize,

    ///	Number of File Allocation Tables (FAT's) on the storage media. Often this value is 2.
    nfat: usize,

    /// The cluster number of the root directory. Often this field is set to 2.
    pub root: u32,

    /// Log cluster numbers.
    log_area: Range<usize>,
}

/// The actual key is just inum. The whole struct is passed as key when looking up into the icache.
/// This struct is assumed to be immutable as long as the file exists.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InodeKey {
    /// Cluster number. Guarded by icache's spinlock.
    pub cno: u32,
    /// Disk offset in bytes to the SFN of its directory entry.
    pub doff: usize,
    /// File attribute.
    pub attr: u8,
}

/// Inode with it's cluster numbers.
#[derive(Debug, Default)]
pub struct Inode {
    /// Hard links. For FAT, the possible values are 0 or 1.
    pub nlink: usize,
    /// Cluster numbers of the clusters of this file.
    pub addr: Vec<u32>,
}

impl InodeKey {
    /// If this inode is a directory.
    pub fn is_dir(&self) -> bool {
        self.attr & ATTR_DIRECTORY != 0
    }
}

type InodePtr<'a, T> = ManuallyDrop<CEntry<'a, T>>;

/// The inode cache.
impl Cache for FAT {
    cache_impl!(InodeKey, Inode, icache);

    fn disk_read<'a>(
        &'a self,
        _key: &'a Self::Key,
        inode: &'a mut Self::Value,
    ) -> Self::ReadFut<'a> {
        async move {
            inode.addr = Vec::new();
            inode.nlink = 1;
            Ok(())
        }
    }

    fn disk_write<'a>(&'a self, _key: &'a Self::Key, _ip: &'a Self::Value) -> Self::WriteFut<'a> {
        async move { Ok(()) }
    }
}

impl FAT {
    /// Initialize a new FAT from a virtual disk.
    ///
    /// `ninodes` is the maximum active inode, `nbuf` is the number of cached buffer.
    pub async fn new(ninodes: usize, nbuf: usize, disk: &Arc<Chan>) -> Result<Self> {
        let mut buf = unsafe { Box::<[u8; BSIZE]>::try_new_uninit()?.assume_init() };
        disk.read(buf.as_mut(), 0).await?;

        let bps = from_bytes!(u16, buf[11..13]) as usize;
        let spc = from_bytes!(u8, buf[13..14]) as usize;
        let reserved_sect = from_bytes!(u16, buf[14..16]) as u32;
        let nfat = from_bytes!(u8, buf[16..17]) as u32;
        let totsect = from_bytes!(u32, buf[32..36]);
        let fat_sect = from_bytes!(u32, buf[36..40]);
        let root = from_bytes!(u32, buf[44..48]) as u32;

        if !([512, 1024, 2048, 4096].contains(&bps)
            && [1, 2, 4, 8, 16, 32, 64, 128].contains(&spc)
            && reserved_sect != 0
            && nfat == 2
            && totsect != 0
            && &buf[82..90] == b"FAT32   ")
        {
            return Err(Error::NotImplemented("FAT meta"));
        }

        // NOTE: Customized, not in FAT32.
        let mut log_cno = from_bytes!(u32, buf[52..56]) as usize;

        let fat_off = reserved_sect;
        let data_off = reserved_sect
            .checked_add(
                nfat.checked_mul(fat_sect)
                    .ok_or(Error::NotImplemented("data offset too large"))?,
            )
            .ok_or(Error::NotImplemented("data offset too large"))?;

        let data_sect = totsect
            .checked_sub(data_off)
            .ok_or(Error::NotImplemented("data sect too large"))?;
        // The count of data clusters starting at cluster 2.
        let data_clust = data_sect / spc as u32;

        if root != 2 || bps != BSIZE {
            return Err(Error::NotImplemented("FAT meta"));
        }

        let log_clust = (LOGSIZE + 1 + spc - 1) / spc;

        // Build log if none.
        if log_cno == 0 {
            let fps = bps / 4 as usize;

            let last_cno = (data_clust + 2) as usize;

            let mut buf2 = Vec::new();
            buf2.try_reserve(bps)?;
            buf2.resize(bps, 0);

            let mut bi = fat_off as usize;
            disk.read(&mut buf2, bi * bps).await?;

            let mut nempty: usize = 0;

            for i in 2..=last_cno {
                if i % fps == 0 {
                    bi += 1;
                    disk.read(&mut buf2, bi * bps).await?;
                }
                let off = i % fps;
                let fat_value = from_bytes!(u32, buf2[off..off + 4]);
                if fat_value == FAT_EMPTY {
                    nempty += 1;
                } else {
                    nempty = 0;
                }
                if nempty == log_clust {
                    log_cno = i - nempty + 1;
                    break;
                }
            }
            if log_cno == 0 {
                return Err(Error::InsufficientStorage("reverse space for log"));
            }
            buf[52..56].copy_from_slice(&(log_cno as u32).to_le_bytes());
            disk.write(buf.as_ref(), 0).await?;
            // Install empty log with magic value.
            let log_bno = data_off as usize + (log_cno - 2) * spc;
            // buf2.truncate(8);
            buf2[0..4].copy_from_slice(&LOGMAGIC.to_le_bytes());
            buf2[4..8].copy_from_slice(&0u32.to_le_bytes());
            disk.write(&buf2, log_bno * BSIZE).await?;
        }

        let meta = FATMeta {
            bps,
            spc,
            data_off: data_off as usize,
            data_clust: data_clust as usize,
            fat_sect: fat_sect as usize,
            fat_off: fat_off as usize,
            nfat: nfat as usize,
            root,
            log_area: log_cno..(log_cno + log_clust),
        };
        let log_bno = data_off as usize + (log_cno - 2) * spc;

        Ok(Self {
            meta,
            log: Log::new(nbuf, log_bno, disk.dup()).await?,
            icache: Self::new_cache(ninodes, || Ok(Inode::default()))?,
        })
    }

    /// Convert qid to inode pointer.
    pub fn to_inode<'a>(&'a self, path: u64) -> InodePtr<'a, Self> {
        let addr: usize = path.try_into().unwrap();
        let ent = unsafe { CEntry::from_ptr(self, CNodePtr::from_addr(addr)) };
        ManuallyDrop::new(ent)
    }
    /// Convert inode pointer to unique path id.
    pub fn to_path<'a>(&'a self, ip: InodePtr<'a, Self>) -> u64 {
        let ent = ManuallyDrop::into_inner(ip);
        ent.leak().to_addr() as u64
    }

    /// Open and increase the reference of a file.
    pub async fn iget<'a>(&'a self, key: InodeKey) -> Option<InodePtr<'a, Self>> {
        self.cache_get(key, false)
            .await
            .unwrap()
            .map(|ent| ManuallyDrop::new(ent))
    }

    /// Close and decrease the reference counter of a file.
    pub fn iput<'a>(&'a self, ip: InodePtr<'a, Self>) {
        let ent = ManuallyDrop::into_inner(ip);
        drop(ent);
    }

    /// Cluster number validator.
    fn valid_cno(&self, cno: u32) -> Result<u32> {
        if !((2..(self.meta.data_clust + 2) as u32).contains(&cno)
            && !self.meta.log_area.contains(&(cno as usize)))
        {
            return Err(Error::InternalError("invalid cno"));
        }
        Ok(cno)
    }

    /// FAT entry validator.
    fn valid_fat(&self, ent: u32) -> Result<u32> {
        let ent = ent & FAT_MASK;
        if !(ent == FAT_EMPTY
            || ent >= FAT_END
            || (2..(self.meta.data_clust + 2) as u32).contains(&ent))
        {
            return Err(Error::InternalError("invalid fat entry"));
        }
        Ok(ent)
    }

    /// Read or modify a FAT entry. Return the old value.
    ///
    /// If f is [None], read the fat value. Otherwise apply f on the value of FAT entry.
    /// If failed the FAT entry won't be updated in both bio cache and log.
    ///
    /// Return the old entry value.
    pub async fn fatrw<'a>(&'a self, cno: u32, f: impl FnOnce(u32) -> u32) -> Result<u32> {
        let cno = self.valid_cno(cno)?;
        let offb_fat = cno as usize * 4;
        let offs_disk = self.meta.fat_off + offb_fat / self.meta.bps;
        let offb_insect = offb_fat % self.meta.bps;
        let buf: CEntry<'a, Log> = self.log.cache_get(offs_disk, false).await?.unwrap();
        let mut g = buf.lock().await?;
        // FIXME: validate?
        let old = from_bytes!(u32, g[offb_insect..(offb_insect + 4)]) & FAT_MASK;
        let new = f(old) & FAT_MASK;
        if new != old {
            g[offb_insect..(offb_insect + 4)].copy_from_slice(&new.to_le_bytes());
        }
        self.log.trace(g).await;
        Ok(old)
    }

    /// Allocate a chain of cluster of len n.
    ///
    /// Return validated head cluster number.
    pub async fn calloc<'a>(&'a self, mut n: usize) -> Result<u32> {
        debug_assert_ne!(n, 0);
        let (mut i, mut j) = (0, self.meta.fat_off);
        let mut head: u32 = FAT_END;
        while i < self.meta.data_clust + 2 {
            let buf: CEntry<'a, Log> = self.log.cache_get(j, false).await?.unwrap();
            let mut g = buf.lock().await?;
            for bi in (0..self.meta.bps).step_by(4) {
                let ent = from_bytes!(u32, g[bi..(bi + 4)]);
                // Avoid log clusters.
                if i >= 2 && ent == FAT_EMPTY && !self.meta.log_area.contains(&i) {
                    g[bi..(bi + 4)].copy_from_slice(&head.to_le_bytes());
                    head = i as u32;

                    n -= 1;
                    if n == 0 {
                        self.log.trace(g).await;
                        return Ok(self.valid_cno(head)?);
                    }
                }
                i += 1;
                if i >= self.meta.data_clust + 2 {
                    break;
                }
            }
            self.log.trace(g).await;
            j += 1;
        }
        Err(Error::InsufficientStorage("calloc"))
    }

    /// This should only be called when
    /// 1. No other transactions.
    /// 2. The size of file is within one cluster.
    /// 3. A plain file or empty directory.
    ///
    /// Modify at most 2 blocks.
    pub async fn removei<'a>(&'a self, ip: &'a CGuard<'a, Self>) -> Result<()> {
        // First, mark SFN as unused.
        let buf = self
            .log
            .cache_get(ip.key().doff / self.meta.bps, false)
            .await?
            .unwrap();
        let mut g = buf.lock().await?;
        let off = ip.key().doff % self.meta.bps;
        g[off..off + 1].copy_from_slice(&[0xE5u8; 1]);
        debug_assert_eq!(sfn_cno(&g[off..off + 32].try_into().unwrap()), ip.key().cno);
        self.log.trace(g).await;

        // Then, mark the whole FAT chain as empty.
        self.fatrw(ip.key().cno, |_| FAT_EMPTY).await?;
        Ok(())
    }

    /// Get the meta information of this file.
    pub async fn stati<'a>(&'a self, ip: &'a CGuard<'a, Self>) -> Result<Dirent> {
        if ip.key().doff == 0 {
            return Ok(Dirent {
                len: 0,
                mtime: 0,
                atime: 0,
            });
        }
        let buf = self
            .log
            .cache_get(ip.key().doff / self.meta.bps, false)
            .await?
            .unwrap();
        let g = buf.lock().await?;
        let off = ip.key().doff % self.meta.bps;
        debug_assert_eq!(sfn_cno(&g[off..off + 32].try_into().unwrap()), ip.key().cno);
        let len = sfn_size(&g[off..off + 32].try_into().unwrap());
        self.log.trace(g).await;
        Ok(Dirent {
            len: len as u64,
            mtime: 0,
            atime: 0,
        })
    }

    /// Extend the addr pointers.
    pub async fn extend<'a>(&'a self, ip: &mut CGuard<'a, Self>) -> Result<()> {
        let bpc = self.meta.bps * self.meta.spc;
        let mut cno = ip.key().cno;
        if let Some(x) = ip.addr.last() {
            cno = *x;
        } else {
            vec_push(&mut ip.addr, cno)?;
        }
        loop {
            let ent = self.valid_fat(self.fatrw(cno, |x| x).await?)?;
            if ent >= FAT_END {
                break Ok(());
            }
            cno = self.valid_cno(ent)?;
            vec_push(&mut ip.addr, cno)?;

            if (ip.addr.len() - 1) * bpc >= u32::MAX as usize {
                return Err(Error::InternalError("FAT extend too large"));
            }
        }
    }

    /// Modify the size of this file and update its cluster pointers.
    ///
    /// Return the new size. For directory, the old size is always a multiple of byte-per-cluster.
    pub async fn resize<'a>(
        &'a self,
        ip: &mut CGuard<'a, Self>,
        f: impl FnOnce(u32) -> u32,
    ) -> Result<u32> {
        let bps = self.meta.bps;
        let bpc = bps * self.meta.spc;

        let boff = ip.key().doff % bps;

        self.extend(ip).await?;

        let (old, new) = if ip.key().is_dir() {
            // Directories are sized by simply following their cluster chains to the end.
            if ip.addr.len() > MAX_DIRSZ as usize / bpc {
                return Err(Error::InternalError("FAT directory too large"));
            }
            let old: u32 = (ip.addr.len() * bpc) as u32;
            (old, f(old))
        } else {
            let b: CEntry<'a, Log> = self
                .log
                .cache_get(ip.key().doff / bps, false)
                .await?
                .unwrap();

            let mut g = b.lock().await?;
            let old = sfn_size(&g[boff..(boff + 32)].try_into().unwrap());
            let new = f(old);
            if new != old {
                let buf: &mut [u8; 32] = (&mut g[boff..(boff + 32)]).try_into().unwrap();
                sfn_set_size(buf, new);
            }
            self.log.trace(g).await;
            (old, new)
        };

        // Each file has at least one cluster.
        let old_ci = max(1, (old as usize + bpc - 1) / bpc);
        let new_ci = max(1, (new as usize + bpc - 1) / bpc);

        // Allocate or deallocate cluster.
        if new_ci > old_ci {
            let new_cno = self.calloc(new_ci - old_ci).await?;
            self.fatrw(*ip.addr.last().unwrap(), |_| new_cno).await?;
            self.extend(ip).await?;
        } else if new_ci < old_ci {
            ip.addr.truncate(new_ci);
            let mut nxt = self.fatrw(ip.addr[new_ci - 1], |_| FAT_END).await?;
            while nxt < FAT_END {
                nxt = self.fatrw(nxt, |_| FAT_EMPTY).await?;
            }
        }
        Ok(new)
    }

    /// Read data from inode.
    pub async fn readi<'a>(
        &'a self,
        ip: &mut CGuard<'a, Self>,
        buf: &mut [u8],
        off: usize,
    ) -> Result<usize> {
        #[inline]
        fn trans(to: &mut [u8], from: &CGuard<'_, Log>, to_off: usize, from_off: usize, n: usize) {
            to[to_off..(to_off + n)].copy_from_slice(&from[from_off..(from_off + n)]);
        }
        rwinode!(self, ip, buf, off, trans)
    }

    /// Write data to inode.
    pub async fn writei<'a>(
        &'a self,
        ip: &mut CGuard<'a, Self>,
        buf: &[u8],
        off: usize,
    ) -> Result<usize> {
        #[inline]
        fn trans(from: &[u8], to: &mut CGuard<'_, Log>, from_off: usize, to_off: usize, n: usize) {
            to[to_off..(to_off + n)].copy_from_slice(&from[from_off..(from_off + n)]);
        }
        rwinode!(self, ip, buf, off, trans)
    }

    /// Look up a file in directory.
    /// Return a referenced inode.
    pub async fn dirlookup<'a>(
        &'a self,
        dp: &CGuard<'a, Self>,
        name: &[u8],
    ) -> Result<Option<InodeKey>> {
        let fname = Filename::try_from(name)?;

        let mut iter = DirIter::new(self, dp).await?;
        while let Some(ent) = iter.next(0).await? {
            debug_assert_eq!(ent.is_empty, false);
            // . and .. are hidden, which are handled by mount space.
            if ent.name == [b'.' as u16] || ent.name == [b'.' as u16, b'.' as u16] {
                continue;
            }

            let mut matched = true;
            if ent.nent == 1 {
                // SFN is case-insensitive.
                if ent.name.len() != fname.data.len() {
                    matched = false;
                } else {
                    for i in 0..ent.name.len() {
                        debug_assert_eq!(ent.name[i] & 0xFF, ent.name[i]);
                        let enti = ent.name[i] as u8;
                        debug_assert_eq!(enti.to_ascii_lowercase(), enti);
                        if enti != (fname.data[i] as u8).to_ascii_lowercase() {
                            matched = false;
                            break;
                        }
                    }
                }
            } else {
                // LFN is case-sensitive.
                matched = ent.name == fname.data
            };

            if matched {
                let key = InodeKey {
                    cno: self.valid_cno(ent.cno)?,
                    doff: ent.doff,
                    attr: ent.attr,
                };
                return Ok(Some(key));
            }
        }
        Ok(None)
    }

    /// Create a directory entry with specific inum.
    ///
    /// Caller should guarantee then name doesn't exist in this dir.
    /// Return inode if the link succeed. Return None if entry with the same name already exist.
    pub async fn dirlink<'a>(
        &'a self,
        dp: &mut CGuard<'a, Self>,
        name: &[u8],
        cno: Option<u32>,
        dir: bool,
    ) -> Result<Option<InodeKey>> {
        // debug_assert_eq!(dp.key().is_dir(), true);
        debug_assert_eq!(
            dp.key().is_dir(),
            true,
            "name: {:?}, dp: {:?}, dir: {}",
            name,
            dp,
            dir,
        );

        let fname = Filename::try_from(name)?;
        let empty_ent = max(2, fname.nent());
        let mut resize = true;

        let mut iter = DirIter::new(self, dp).await?;
        while let Some(ent) = iter.next(empty_ent).await? {
            if ent.is_empty {
                resize = false;
            } else if ent.name == fname.data {
                return Ok(None);
            }
        }
        drop(iter);

        if resize {
            let bpc = self.meta.bps * self.meta.spc;
            let mut grow = false;
            // Allocate a new cluster.
            let new = self
                .resize(dp, |x| {
                    if x < MAX_DIRSZ {
                        grow = true;
                        x + bpc as u32
                    } else {
                        x
                    }
                })
                .await? as usize;
            if !grow {
                return Err(Error::InsufficientStorage("dirlink grow dir"));
            }
            debug_assert_eq!(new % bpc, 0);
            // Zero filled.
            let mut buf: Vec<u8> = Vec::new();
            buf.try_reserve(bpc)?;
            buf.resize(bpc, 0);
            if self.writei(dp, &buf, new - bpc).await? != bpc {
                return Err(Error::InternalError("dirlink grow dir"));
            }
        }

        // Generate unique SFN for LFN
        let fake_sfn = if fname.is_sfn {
            None
        } else {
            let mut i = 0;
            Some(loop {
                i += 1;
                if i >= MAX_NUMERIC_TAIL {
                    return Err(Error::InternalError("max numeric tail"));
                }
                let new_sfn = fname.gen_sfn(i)?;
                if new_sfn.data == fname.data {
                    continue;
                }
                let mut dup = false;
                let mut iter = DirIter::new(self, dp).await?;
                while let Some(ent) = iter.next(0).await? {
                    if ent.name == new_sfn.data {
                        dup = true;
                        break;
                    }
                }
                if !dup {
                    break new_sfn;
                }
            })
        };

        // Insert the entry.
        let mut iter = DirIter::new(self, dp).await?;
        let mut some_empty = None;
        while let Some(ent) = iter.next(empty_ent).await? {
            if ent.is_empty {
                some_empty = Some(ent);
                break;
            }
        }
        drop(iter);

        if let Some(ent) = some_empty {
            debug_assert!(ent.nent >= 2);
            let mut name_buf = [0u8; 11];
            if let Some(ref sfn) = fake_sfn {
                sfn.dump_sfn(&mut name_buf);
            } else {
                fname.dump_sfn(&mut name_buf);
            }

            let cno = if let Some(cno) = cno {
                cno
            } else {
                // Allocate a cluster.
                let cno = self.calloc(1).await?;
                if dir {
                    let bps = self.meta.bps;
                    // Zero filled.
                    let mut buf0: Vec<u8> = Vec::new();
                    buf0.try_reserve(bps)?;
                    buf0.resize(bps, 0);
                    let mut iter = SectIter::new(self, cno);
                    while let Some(item) = iter.next().await? {
                        let mut g = item.buf.lock().await?;
                        g[0..bps].copy_from_slice(&buf0);
                        self.log.trace(g).await;
                    }
                }
                cno
            };

            let mut buf = [0u8; DIRENTSZ];
            let attr = if dir { ATTR_DIRECTORY } else { ATTR_ARCHIVE };
            sfn_set_attr(&mut buf, attr);
            sfn_set_name(&mut buf, &name_buf);
            sfn_set_cno(&mut buf, cno);
            sfn_set_size(&mut buf, 0);
            self.writei(dp, &buf, ent.ioff).await?;

            if let Some(sfn) = fake_sfn {
                let chksum = checksum(&buf[0..11]);
                lfn_init(&mut buf, chksum);
                for i in 1..ent.nent {
                    let ord = if i == ent.nent - 1 { i | 0x40 } else { i } as u8;
                    buf[0] = ord;
                    lfn_set_name(
                        &mut buf,
                        &fname.data[((i - 1) * 13)..min(i * 13, fname.data.len())],
                    );
                    self.writei(dp, &buf, ent.ioff - i * DIRENTSZ).await?;
                }
            } else {
                // Entry prior to each non-free single SFN must be a SFN.
                // This is required by the algorithm of [`DirIter`].
                // Otherwise, we cannot determine if this is indeed a single SFN
                // or just a SFN generated by LFN.
                sfn_set_attr(&mut buf, 0);
                buf[0] = 0xE5;
                self.writei(dp, &buf, ent.ioff - DIRENTSZ).await?;
            }

            let key = InodeKey {
                cno,
                doff: ent.doff,
                attr,
            };
            return Ok(Some(key));
        }
        panic!("failed to find empty entry");
    }

    /// Check if directory is empty.
    pub async fn dirempty<'a>(&'a self, dp: &'a CGuard<'a, Self>) -> Result<bool> {
        let mut iter = DirIter::new(self, dp).await?;
        // Skip the first two '.' and '..'.
        while let Some(ent) = iter.next(0).await? {
            if ent.name != [b'.' as u16] && ent.name != [b'.' as u16, b'.' as u16] {
                return Ok(false);
            }
        }
        Ok(true)
    }

    #[cfg(test)]
    pub async fn dirstat<'a>(&'a self, dp: &'a CGuard<'a, Self>, print: bool) -> Vec<Vec<u16>> {
        let mut names = Vec::new();

        let mut iter = DirIter::new(self, &dp).await.unwrap();
        while let Some(ent) = iter.next(0).await.unwrap() {
            debug_assert_eq!(ent.is_empty, false);
            if print {
                println!("ent: {:?}", ent);
            }

            names.push(ent.name);
        }
        names
    }
}

struct SectItem<'a> {
    buf: CEntry<'a, Log>,

    file_secti: usize,
    /// Disk offset in sectors.
    disk_secti: usize,
}

struct SectIter<'a> {
    fs: &'a FAT,
    cno: u32,
    clusi: usize,
    secti: usize,
}

impl<'a> SectIter<'a> {
    fn new(fs: &'a FAT, cno: u32) -> Self {
        Self {
            fs,
            cno,
            clusi: 0,
            secti: 0,
        }
    }

    async fn next(&mut self) -> Result<Option<SectItem<'a>>> {
        if self.fs.valid_cno(self.cno).is_err() {
            return Ok(None);
        }
        let disk_secti =
            self.fs.meta.data_off + (self.cno as usize - 2) * self.fs.meta.spc + self.secti;
        let item = SectItem {
            buf: self.fs.log.cache_get(disk_secti, false).await?.unwrap(),
            file_secti: self.clusi * self.fs.meta.spc + self.secti,
            disk_secti,
        };
        self.secti += 1;
        if self.secti == self.fs.meta.spc {
            self.cno = self.fs.fatrw(self.cno, |x| x).await?;
            self.clusi += 1;
            self.secti = 0;
        }
        Ok(Some(item))
    }
}

struct DirItem {
    /// Offset in bytes from the beginning of directory to its SFN.
    pub ioff: usize,
    /// Offset in bytes from the beginning of disk to its SFN.
    pub doff: usize,
    pub nent: usize,
    pub name: Vec<u16>,
    pub cno: u32,
    pub attr: u8,
    pub is_empty: bool,
}

impl Debug for DirItem {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let name = alloc::string::String::from_utf16_lossy(&self.name);
        let is_dir = self.attr & ATTR_DIRECTORY != 0;
        f.debug_struct("DirItem")
            .field("name", &name)
            .field("is_dir", &is_dir)
            .field("ioff", &self.ioff)
            .field("doff", &self.doff)
            .field("nent", &self.nent)
            .field("cno", &self.cno)
            .field("attr", &self.attr)
            .field("is_empty", &self.is_empty)
            .finish()
    }
}

struct DirIter<'a> {
    siter: SectIter<'a>,
    sitem: SectItem<'a>,
    /// The order(start by 0) of last-seen entry in current sector.
    entid: usize,
    stall: bool,
    /// Number of entries per sector.
    eps: usize,
    prev_doff: usize,
}

impl<'a> DirIter<'a> {
    async fn new(fs: &'a FAT, dp: &'a CGuard<'a, FAT>) -> Result<DirIter<'a>> {
        let mut siter = SectIter::new(fs, dp.key().cno);
        let sitem = siter
            .next()
            .await?
            .ok_or(Error::InternalError("diriter new"))?;
        let eps = fs.meta.bps / DIRENTSZ;
        Ok(Self {
            siter,
            sitem,
            entid: 0,
            stall: true,
            eps,
            prev_doff: 0,
        })
    }

    /// If empty_ent is zero, skip all empty entries.
    /// Otherwise, it is allowed to return an empty entry consisting of exactly
    /// `empty_ent` sequencial directory entries.
    ///
    /// If failed, the iterator will be corrupted, don't call `next` after that.
    async fn next(&mut self, empty_ent: usize) -> Result<Option<DirItem>> {
        let mut cno = 0;
        let mut attr;

        let mut names = Vec::new();
        let mut maybe_empty = 0;

        #[derive(Debug)]
        enum Token {
            /// Last or not.
            LFN(bool),
            /// Free or not.
            SFN(bool),
            Ignore,
        }

        let prev = loop {
            if self.stall {
                self.stall = false;
            } else {
                self.prev_doff = self.sitem.disk_secti + self.entid * DIRENTSZ;
                self.entid += 1;
                if self.entid == self.eps {
                    self.sitem = if let Some(item) = self.siter.next().await? {
                        item
                    } else {
                        return Ok(None);
                    };
                    self.entid = 0;
                }
            }

            let buf = self.sitem.buf.lock().await?;
            let ebuf: &[u8; DIRENTSZ] = &buf[self.entid * DIRENTSZ..(self.entid + 1) * DIRENTSZ]
                .try_into()
                .unwrap();

            let ord = ebuf[0];
            attr = sfn_attr(&ebuf);

            let token = if attr & ATTR_LONG_NAME_MASK == ATTR_LONG_NAME && ord != 0xE5 {
                Token::LFN(ord & LAST_LONG_ENTRY != 0)
            } else if attr & ATTR_LONG_NAME_MASK != ATTR_LONG_NAME {
                Token::SFN(ord == 0xE5 || ord == 0)
            } else {
                Token::Ignore
            };

            let brk: Result<Option<bool>> = (|| {
                match token {
                    Token::LFN(true) => {
                        names.clear();
                        if empty_ent != 0 && maybe_empty >= empty_ent {
                            // Emit previous empty entries.
                            return Ok(Some(true));
                        }
                        maybe_empty += 1;
                        vec_push(&mut names, lfn_name(&ebuf)?)?;
                    }
                    Token::LFN(false) => {
                        maybe_empty += 1;

                        if !names.is_empty() {
                            vec_push(&mut names, lfn_name(&ebuf)?)?;
                        } else if empty_ent != 0 && maybe_empty >= empty_ent {
                            return Ok(Some(false));
                        }
                    }
                    Token::SFN(false) => {
                        // Ignore SFN if previous LFN exists.
                        if names.is_empty() {
                            vec_push(&mut names, sfn_name(&ebuf)?)?;
                        } else {
                            vec_push(&mut names, Vec::new())?;
                        }
                        cno = sfn_cno(&ebuf);
                        return Ok(Some(false));
                    }
                    Token::SFN(true) => {
                        names.clear();
                        maybe_empty += 1;
                        if empty_ent != 0 && maybe_empty >= empty_ent {
                            return Ok(Some(false));
                        }
                    }
                    Token::Ignore => {
                        names.clear();
                        if empty_ent != 0 && maybe_empty >= empty_ent {
                            // Emit previous empty entries.
                            return Ok(Some(true));
                        }
                        maybe_empty = 0;
                    }
                }
                Ok(None)
            })();
            buf.unlock(false).await.unwrap();

            if let Some(prev) = brk? {
                break prev;
            }
        };

        let mut name = Vec::new();
        for bs in names.iter().rev() {
            for b in bs {
                vec_push(&mut name, b.clone())?;
            }
        }

        let is_empty = names.is_empty();
        let nent = if is_empty { empty_ent } else { names.len() };

        let mut doff = self.sitem.disk_secti * self.siter.fs.meta.bps + self.entid * DIRENTSZ;
        let mut ioff = (self.sitem.file_secti * self.eps + self.entid) * DIRENTSZ;
        if prev {
            debug_assert_ne!(self.prev_doff, 0);
            debug_assert_ne!(self.prev_doff, doff);

            debug_assert_eq!(is_empty, true);
            self.stall = true;
            doff = self.prev_doff;
            ioff -= DIRENTSZ;
        }

        if empty_ent == 0 {
            debug_assert_eq!(is_empty, false);
        } else if is_empty {
            debug_assert!(maybe_empty >= empty_ent);
        }

        Ok(Some(DirItem {
            doff,
            ioff,
            nent,
            name,
            cno,
            attr,
            is_empty,
        }))
    }
}
