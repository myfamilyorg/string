#![no_std]

extern crate boxed;
extern crate display;
extern crate errors;
extern crate macros;
extern crate ptr;
extern crate rc;
extern crate result;
extern crate slice_ext;
extern crate str_ext;

use boxed::Box;
use core::cmp::Ordering;
use core::ops::{Index, Range, RangeFrom, RangeFull, RangeTo};
use core::slice::from_raw_parts;
use core::str::from_utf8_unchecked;
use display::{Display, Fmt};
use errors::*;
use macros::prelude::*;
use ptr::Ptr;
use rc::Rc;
use result::Result;
use slice_ext::SliceExt;
use str_ext::StrExt;

fn is_utf8_valid(bytes: &[u8]) -> Result<()> {
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        let len = if b <= 0x7F {
            // 1-byte (ASCII)
            1
        } else if (b & 0xE0) == 0xC0 {
            // 2-byte
            2
        } else if (b & 0xF0) == 0xE0 {
            // 3-byte
            3
        } else if (b & 0xF8) == 0xF0 {
            // 4-byte
            4
        } else {
            // Invalid leading byte
            return err!(Utf8Error);
        };

        // Check if there are enough bytes
        if i + len > bytes.len() {
            return err!(Utf8Error);
        }
        // Check continuation bytes
        for j in 1..len {
            if i + j < bytes.len() && (bytes[i + j] & 0xC0) != 0x80 {
                return err!(Utf8Error);
            }
        }

        i += len;
    }
    Ok(())
}

#[derive(Clone)]
pub struct StringDataStruct {
    value: Rc<Box<[u8]>>,
    end: usize,
    start: usize,
}

#[derive(Clone)]
pub struct SSODataStruct([u8; 24]);

#[derive(Clone)]
pub enum String {
    StringData(StringDataStruct),
    SSOData(SSODataStruct),
}

impl Ord for String {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for String {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl Eq for String {}

impl Display for String {
    fn format(&self, f: &mut dyn Fmt) -> Result<()> {
        writef!(f, "{}", self.as_str())
    }
}

impl Index<Range<usize>> for String {
    type Output = str; // Output is a string slice, not a String
    fn index(&self, r: Range<usize>) -> &Self::Output {
        let s = self.as_str();
        let len = s.len();
        if r.start > r.end
            || r.end > len
            || !s.is_char_boundary(r.start)
            || !s.is_char_boundary(r.end)
        {
            exit!(
                "invalid range [{}..{}], len={}, invalid UTF-8 boundaries",
                r.start,
                r.end,
                len
            );
        }
        // Safe to use get_unchecked after validation
        unsafe { s.get_unchecked(r.start..r.end) }
    }
}

impl Index<RangeFrom<usize>> for String {
    type Output = str; // Output is a string slice, not a String
    fn index(&self, r: RangeFrom<usize>) -> &Self::Output {
        let s = self.as_str();
        let len = s.len();
        if r.start > len || !s.is_char_boundary(r.start) {
            exit!(
                "invalid range [{}..], len={}, invalid UTF-8 boundaries",
                r.start,
                len
            );
        }
        // Safe to use get_unchecked after validation
        unsafe { s.get_unchecked(r.start..len) }
    }
}

impl Index<RangeTo<usize>> for String {
    type Output = str; // Output is a string slice, not a String
    fn index(&self, r: RangeTo<usize>) -> &Self::Output {
        let s = self.as_str();
        let len = s.len();
        if r.end > len || !s.is_char_boundary(r.end) {
            exit!(
                "invalid range [..{}], len={}, invalid UTF-8 boundaries",
                r.end,
                len
            );
        }
        // Safe to use get_unchecked after validation
        unsafe { s.get_unchecked(0..r.end) }
    }
}

impl Index<RangeFull> for String {
    type Output = str; // Output is a string slice, not a String
    fn index(&self, _r: RangeFull) -> &Self::Output {
        let s = self.as_str();
        let len = s.len();
        // Safe to use get_unchecked after validation
        unsafe { s.get_unchecked(0..len) }
    }
}

impl PartialEq for String {
    fn eq(&self, other: &String) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl AsRef<[u8]> for String {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_ref()
    }
}

impl String {
    pub fn new(s: &str) -> Result<Self> {
        let end = s.len();
        let start = 0;
        if end <= 23 {
            Ok(Self::sso(s))
        } else {
            let mut slice = try_box_slice!(0u8, end)?;
            slice.slice_copy(s.as_bytes())?;
            Ok(Self::StringData(StringDataStruct {
                value: Rc::new(slice)?,
                start,
                end,
            }))
        }
    }

    pub fn newb(b: &[u8]) -> Result<Self> {
        is_utf8_valid(b)?;
        unsafe { Self::new(from_utf8_unchecked(b)) }
    }

    pub fn empty() -> Self {
        Self::sso("")
    }

    pub fn as_ptr(&self) -> *const Self {
        self.as_str().as_ptr() as *const Self
    }

    pub fn as_str(&self) -> &str {
        match self {
            String::StringData(StringDataStruct { value, start, end }) => {
                let b = (*value).as_ref();
                unsafe { from_utf8_unchecked(&b[*start..*end]) }
            }
            String::SSOData(SSODataStruct(b)) => unsafe {
                let c = from_raw_parts(b.as_ptr().add(1), b[0] as usize);
                from_utf8_unchecked(c)
            },
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }

    pub fn substring(&self, nstart: usize, nend: usize) -> Result<Self> {
        if nstart > nend || nend - nstart > self.len() {
            return err!(OutOfBounds);
        }
        let s = self.as_str();
        if !s.is_char_boundary(nstart) || !s.is_char_boundary(nend) {
            return err!(Utf8Error);
        }
        let b = s.as_bytes();
        if nstart <= nend && nend <= b.len() {
            Self::newb(&b[nstart..nend])
        } else {
            err!(OutOfBounds)
        }
    }

    pub fn findn(&self, s: &str, offset: usize) -> Option<usize> {
        let str1 = self.as_str();
        str1.findn(s, offset)
    }

    pub fn find(&self, s: &str) -> Option<usize> {
        self.findn(s, 0)
    }

    pub fn rfindn(&self, s: &str, offset: usize) -> Option<usize> {
        let str1 = self.as_str();
        str1.rfindn(s, offset)
    }

    pub fn rfind(&self, s: &str) -> Option<usize> {
        self.rfindn(s, self.len())
    }

    pub fn len(&self) -> usize {
        match self {
            String::StringData(StringDataStruct {
                value: _,
                start,
                end,
            }) => end - start,
            String::SSOData(b) => b.0[0] as usize,
        }
    }

    fn sso(s: &str) -> Self {
        let len = s.len();
        let mut v = [0u8; 24];
        v[0] = len as u8;
        let sb = s.as_bytes();
        let _ = v[1..sb.len() + 1].slice_copy(sb);
        Self::SSOData(SSODataStruct(v))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[mytest]
    fn test_string1() -> Result<()> {
        Ok(())
    }
}
