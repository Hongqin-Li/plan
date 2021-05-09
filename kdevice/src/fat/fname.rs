//! Directory entry parser of FAT32.

use crate::from_bytes;
use core::{
    cmp,
    convert::{TryFrom, TryInto},
    num, str,
};

use alloc::vec::Vec;
use kalloc::wrapper::vec_push;
use kcore::error::{Error, Result};

const SPACE: u8 = 0x20;

pub const ATTR_READ_ONLY: u8 = 0x01;
pub const ATTR_HIDDEN: u8 = 0x02;
pub const ATTR_SYSTEM: u8 = 0x04;
pub const ATTR_VOLUME_ID: u8 = 0x08;
pub const ATTR_LONG_NAME: u8 = ATTR_READ_ONLY | ATTR_HIDDEN | ATTR_SYSTEM | ATTR_VOLUME_ID;

pub const ATTR_DIRECTORY: u8 = 0x10;
/// Normal file. See https://en.wikipedia.org/wiki/Archive_bit
pub const ATTR_ARCHIVE: u8 = 0x20;
pub const ATTR_LONG_NAME_MASK: u8 = ATTR_LONG_NAME | ATTR_DIRECTORY | ATTR_ARCHIVE;

pub const LAST_LONG_ENTRY: u8 = 0x40;
pub const MAX_LONG_ENTRY: u8 = LAST_LONG_ENTRY - 1;

/// Maximum number x of the numeric tail ~x.
pub const MAX_NUMERIC_TAIL: usize = 999999;
/// Each directory entry in FAT32 is of 32 bytes.
pub const DIRENTSZ: usize = 32;

/// Get the 8.3-style file name.
pub fn sfn_name(buf: &[u8; DIRENTSZ]) -> Result<Vec<u16>> {
    let mut name = Vec::new();
    let mut has_dot = false;
    for i in (0..8).take_while(|i| buf[i.clone()] != SPACE) {
        vec_push(&mut name, buf[i] as u16)?;
    }
    for i in (8..11).take_while(|i| buf[i.clone()] != SPACE) {
        if !has_dot {
            vec_push(&mut name, b'.' as u16)?;
            has_dot = true;
        }
        vec_push(&mut name, buf[i] as u16)?;
    }
    Ok(name)
}

pub fn sfn_set_name(buf: &mut [u8; DIRENTSZ], name: &[u8; 11]) {
    buf[0..11].copy_from_slice(name);
}

/// Get the file size in bytes.
pub fn sfn_size(buf: &[u8; DIRENTSZ]) -> u32 {
    from_bytes!(u32, buf[28..32])
}
/// Alter the file size field of a sfn entry.
pub fn sfn_set_size(buf: &mut [u8; DIRENTSZ], sz: u32) {
    buf[28..32].copy_from_slice(&sz.to_le_bytes());
}

/// Get the cluster number of the file.
pub fn sfn_cno(buf: &[u8; DIRENTSZ]) -> u32 {
    let hi = from_bytes!(u16, buf[20..22]) as u32;
    let lo = from_bytes!(u16, buf[26..28]) as u32;
    (hi << 16) | lo
}

/// Set the cluster number of the file.
pub fn sfn_set_cno(buf: &mut [u8; DIRENTSZ], cno: u32) {
    let hi = (cno >> 16) as u16;
    let lo = (cno & 0xFFFF) as u16;
    buf[20..22].copy_from_slice(&hi.to_le_bytes());
    buf[26..28].copy_from_slice(&lo.to_le_bytes());
}

/// Get File attribute.
pub fn sfn_attr(buf: &[u8; DIRENTSZ]) -> u8 {
    buf[11]
}

/// Set File attribute.
pub fn sfn_set_attr(buf: &mut [u8; DIRENTSZ], attr: u8) {
    buf[11] = attr
}

/// Get name from a LFN entry.
pub fn lfn_name(buf: &[u8; DIRENTSZ]) -> Result<Vec<u16>> {
    let mut name = Vec::new();
    let range = [(1..11), (14..26), (28..32)];
    for rg in range.iter() {
        for i in rg.clone().step_by(2) {
            if buf[i] == 0 && buf[i + 1] == 0 {
                return Ok(name);
            }
            vec_push(&mut name, from_bytes!(u16, buf[i..i + 2]))?;
        }
    }
    Ok(name)
}

/// Initialize the LFN entry by setting some default values.
pub fn lfn_init(buf: &mut [u8; DIRENTSZ], chksum: u8) {
    buf[11] = ATTR_LONG_NAME;
    buf[13] = chksum;

    // If zero, indicates a directory entry that is a sub-component of along name.
    // NOTE: Other values reserved for future extensions. Non-zero implies other dirent types.
    buf[12] = 0;

    // Must be ZERO. This is an artifact of the FAT "first cluster" and must be zero for
    // compatibility with existing disk utilities.
    // It's meaningless in the context of a long dir entry.
    buf[26] = 0;
    buf[27] = 0;
}

pub fn lfn_set_name(buf: &mut [u8; DIRENTSZ], name: &[u16]) {
    let len = name.len();
    let rng = [(1..11), (14..26), (28..32)];
    let mut end = false;
    let mut i = 0;
    for rg in rng.iter() {
        for bi in rg.clone().step_by(2) {
            if end {
                buf[bi..(bi + 2)].copy_from_slice(&(0xFFFF as u16).to_le_bytes());
            } else {
                let x = if let Some(x) = name.get(i) {
                    *x
                } else {
                    end = true;
                    0
                };
                buf[bi..(bi + 2)].copy_from_slice(&x.to_le_bytes());
                i += 1;
            }
        }
    }
}

/// Convert utf-8 bytes to utf-16.
pub fn utf8_to_utf16(bytes: &[u8]) -> Result<Vec<u16>> {
    let mut ret = Vec::new();
    let str = str::from_utf8(bytes).map_err(|_| Error::BadRequest)?;
    for c in str.chars() {
        let mut buf = [0u16; 2];
        let buf = c.encode_utf16(&mut buf);
        for x in buf {
            vec_push(&mut ret, *x)?;
        }
    }
    Ok(ret)
}

fn valid_sfn_char(c: &char) -> bool {
    match c {
        '\u{80}'..='\u{FF}' => true,
        'a'..='z' | 'A'..='Z' | '0'..='9' => true,
        '$' | '%' | '\'' | '-' | '_' | '@' | '~' | '`' | '!' | '(' | ')' | '{' | '}' | '^'
        | '#' | '&' => true,
        '.' => true,
        _ => false,
    }
}

/// Valid file name.
#[derive(Debug)]
pub struct Filename {
    pub base_len: usize,
    pub ext_len: usize,
    pub has_period: bool,
    /// Is it a SFN or LFN?
    pub is_sfn: bool,
    pub data: Vec<u16>,
}

impl Filename {
    /// Compute the checksum of SFN.
    pub fn checksum(&self) -> u8 {
        debug_assert_eq!(self.is_sfn, true);
        let mut chksum = num::Wrapping(0_u8);
        for x in self.data.iter().map(|x| *x as u8) {
            chksum = (chksum << 7) + (chksum >> 1) + num::Wrapping(x);
        }
        chksum.0
    }

    /// Number of required entries to store this file name.
    pub fn nent(&self) -> usize {
        if self.is_sfn {
            1
        } else {
            1 + (self.data.len() + 12) / 13
        }
    }
    /// Generate SFN from LFN.
    pub fn gen_sfn(&self, mut i: usize) -> Result<Self> {
        assert_eq!(self.is_sfn, false);
        debug_assert!(1 <= i && i <= MAX_NUMERIC_TAIL);

        let mut data = Vec::new();
        data.try_reserve(8)?;
        for c in self.data[0..cmp::min(8, self.data.len())].iter() {
            let mut c = if *c > 0xFF { '_' } else { *c as u8 as char };
            if !valid_sfn_char(&c) || c == '.' {
                c = '_';
            }
            let c = c.to_ascii_uppercase();
            data.push(c as u16);
        }
        // Padded with '_'.
        while data.len() < 8 {
            data.push(b'_' as u16);
        }

        // Overwrite with "~xxx".
        let mut di = 7;
        while i != 0 {
            data[di] = b'0' as u16 + (i % 10) as u16;
            i /= 10;
            di -= 1;
        }
        data[di] = b'~' as u16;

        Ok(Self {
            base_len: 8,
            ext_len: 0,
            has_period: false,
            is_sfn: true,
            data,
        })
    }

    /// Dump SFN to buffer.
    pub fn dump_sfn(&self, buf: &mut [u8; 11]) {
        debug_assert_eq!(self.is_sfn, true);
        debug_assert!(self.base_len <= 8 && self.ext_len <= 3);
        for b in buf.iter_mut() {
            *b = b' ';
        }
        for (mut i, b) in self.data.iter().enumerate() {
            if i >= self.base_len {
                i = if self.has_period {
                    if i == self.base_len {
                        continue;
                    } else {
                        8 + i - self.base_len - 1
                    }
                } else {
                    8 + i - self.base_len
                };
            }
            buf[i] = *b as u8;
        }
    }
}

impl TryFrom<&[u8]> for Filename {
    type Error = Error;
    /// The rule for LFN is slightly different from FAT32 specification.
    /// We allow any bytes in LFN.
    fn try_from(bytes: &[u8]) -> core::result::Result<Self, Self::Error> {
        if bytes.len() > 0 && (bytes[0] == 0 || bytes[0] == 0xE5) {
            return Err(Error::BadRequest);
        }

        let mut data = Vec::new();
        let str: &str = str::from_utf8(bytes).map_err(|_| Error::BadRequest)?;
        let mut is_sfn = true;
        let mut nperiod = 0;
        for c in str.chars() {
            if c == 0 as char {
                break;
            }
            // Valid character set of SFN.
            if valid_sfn_char(&c) {
                if c == '.' {
                    nperiod += 1;
                    if nperiod > 1 {
                        is_sfn = false;
                    }
                }
            } else {
                is_sfn = false;
            }
            let mut buf = [0u16; 2];
            let buf = c.encode_utf16(&mut buf);
            for x in buf {
                vec_push(&mut data, *x)?;
            }
        }

        if data.is_empty() || data.len() > 255 {
            return Err(Error::BadRequest);
        }

        let last_period = data.iter().enumerate().rfind(|(i, c)| **c == '.' as u16);
        let (base_len, ext_len, has_period) = if let Some((i, c)) = last_period {
            (i, data.len() - i - 1, true)
        } else {
            (data.len(), 0, false)
        };

        if base_len == 0 || base_len > 8 || ext_len > 3 {
            is_sfn = false;
        }
        if is_sfn {
            for x in data.iter_mut() {
                debug_assert!(*x <= 0xFF);
                *x = (*x as u8).to_ascii_uppercase() as u16;
            }
        }
        Ok(Self {
            base_len,
            ext_len,
            has_period,
            is_sfn,
            data,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sfn() {
        let ent: [u8; DIRENTSZ] = [
            b'a', b'b', b'c', b' ', b' ', b' ', b' ', b' ', b't', b'x', b't', 0x20, 0x18, 0x7D,
            0x11, 0xB8, 0x2C, 0x3B, 0x2C, 0x3B, 0, 0, 0x29, 0xB8, 0x2C, 0x3B, 0x03, 0, 0xC8, 0x07,
            0, 0,
        ];
        assert_eq!(sfn_size(&ent), 1992);
        assert_eq!(sfn_cno(&ent), 3);
    }

    #[test]
    fn test_invalid_filename() {
        assert_eq!(Filename::try_from(b"" as &[u8]).is_err(), true);
        assert_eq!(Filename::try_from(b"\0" as &[u8]).is_err(), true);
        assert_eq!(Filename::try_from(b"\xE5" as &[u8]).is_err(), true);
        assert_eq!(Filename::try_from(b"\xFF\xFF\xFF" as &[u8]).is_err(), true);
    }

    #[test]
    fn test_to_sfn() {
        let mut buf = [0u8; 11];

        let fname = Filename::try_from(b"foo.bar" as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"FOO     BAR");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, true);
        assert_eq!(fname.base_len, 3);
        assert_eq!(fname.ext_len, 3);

        let fname = Filename::try_from(b"foo\0.bar" as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"FOO        ");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, false);
        assert_eq!(fname.base_len, 3);
        assert_eq!(fname.ext_len, 0);

        let fname = Filename::try_from(b"Foo.Bar" as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"FOO     BAR");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, true);
        assert_eq!(fname.base_len, 3);
        assert_eq!(fname.ext_len, 3);

        let fname = Filename::try_from(b"foo" as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"FOO        ");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, false);
        assert_eq!(fname.base_len, 3);
        assert_eq!(fname.ext_len, 0);

        let fname = Filename::try_from(b"foo." as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"FOO        ");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, true);
        assert_eq!(fname.base_len, 3);
        assert_eq!(fname.ext_len, 0);

        let fname = Filename::try_from(b"PICKLE.A" as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"PICKLE  A  ");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, true);
        assert_eq!(fname.base_len, 6);
        assert_eq!(fname.ext_len, 1);

        let fname = Filename::try_from(b"prettybg.big" as &[u8]).unwrap();
        fname.dump_sfn(&mut buf);
        assert_eq!(&buf, b"PRETTYBGBIG");
        assert_eq!(fname.is_sfn, true);
        assert_eq!(fname.has_period, true);
        assert_eq!(fname.base_len, 8);
        assert_eq!(fname.ext_len, 3);
    }

    #[test]
    fn test_to_lfn() {
        let fname = Filename::try_from(b".big" as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 0);
        assert_eq!(fname.ext_len, 3);
        assert_eq!(fname.has_period, true);
        assert_eq!(
            fname.gen_sfn(1).unwrap().data,
            Filename::try_from(b"_big__~1" as &[u8]).unwrap().data
        );

        let fname = Filename::try_from(b"foo.bar1" as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 3);
        assert_eq!(fname.ext_len, 4);
        assert_eq!(fname.has_period, true);
        assert_eq!(
            fname.gen_sfn(1).unwrap().data,
            Filename::try_from(b"foo_ba~1" as &[u8]).unwrap().data
        );

        let fname = Filename::try_from(b"foo.bar." as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 7);
        assert_eq!(fname.ext_len, 0);
        assert_eq!(fname.has_period, true);
        assert_eq!(
            fname.gen_sfn(2).unwrap().data,
            Filename::try_from(b"foo_ba~2" as &[u8]).unwrap().data
        );

        let fname = Filename::try_from(b"f.bar.x" as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 5);
        assert_eq!(fname.ext_len, 1);
        assert_eq!(fname.has_period, true);
        assert_eq!(
            fname.gen_sfn(2).unwrap().data,
            Filename::try_from(b"f_bar_~2" as &[u8]).unwrap().data
        );

        let fname = Filename::try_from(b"foo bar" as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 7);
        assert_eq!(fname.ext_len, 0);
        assert_eq!(fname.has_period, false);
        assert_eq!(
            fname.gen_sfn(2).unwrap().data,
            Filename::try_from(b"foo_ba~2" as &[u8]).unwrap().data
        );

        let fname = Filename::try_from(b" " as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 1);
        assert_eq!(fname.ext_len, 0);
        assert_eq!(fname.has_period, false);
        assert_eq!(
            fname.gen_sfn(100).unwrap().data,
            Filename::try_from(b"____~100" as &[u8]).unwrap().data
        );

        let fname = Filename::try_from(b"\x10" as &[u8]).unwrap();
        assert_eq!(fname.is_sfn, false);
        assert_eq!(fname.base_len, 1);
        assert_eq!(fname.ext_len, 0);
        assert_eq!(fname.has_period, false);
        assert_eq!(
            fname.gen_sfn(999999).unwrap().data,
            Filename::try_from(b"_~999999" as &[u8]).unwrap().data
        );
    }

    #[test]
    fn test_lfn_set_name() {
        let mut buf = [0u8; DIRENTSZ];
        let name = "foo-bar-123";
        let name2 = utf8_to_utf16(name.as_bytes()).unwrap();

        lfn_set_name(&mut buf, &name2);
        let lname = lfn_name(&buf).unwrap();
        assert_eq!(name2, lname);
        assert_eq!(&buf[1..11], &[b'f', 0, b'o', 0, b'o', 0, b'-', 0, b'b', 0]);
        assert_eq!(
            &buf[14..26],
            &[b'a', 0, b'r', 0, b'-', 0, b'1', 0, b'2', 0, b'3', 0]
        );
        assert_eq!(&buf[28..32], &[0, 0, 0xFF, 0xFF]);
    }
}
