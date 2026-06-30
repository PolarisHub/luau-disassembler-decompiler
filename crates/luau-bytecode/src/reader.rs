//! A bounds-checked cursor over the input bytes.
//!
//! Mirrors the primitive reads in `VM/src/lvmload.cpp` (`read<T>`, `readVarInt`,
//! `readVarInt64`) but every read is checked and returns a `Result` instead of doing an
//! unchecked `memcpy`. The cursor is the only place that touches raw bytes, so if it is
//! correct, nothing downstream can read out of bounds.

use crate::error::{Error, ErrorKind, Result};

pub struct Cursor<'a> {
    data: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Cursor { data, offset: 0 }
    }

    #[inline]
    pub fn offset(&self) -> usize {
        self.offset
    }

    #[inline]
    pub fn remaining(&self) -> usize {
        self.data.len() - self.offset
    }

    /// The rest of the buffer from the current offset, consuming it. Used for the
    /// version-0 compile-error sentinel where the tail is a message.
    pub fn take_rest(&mut self) -> &'a [u8] {
        let rest = &self.data[self.offset..];
        self.offset = self.data.len();
        rest
    }

    fn err(&self, kind: ErrorKind) -> Error {
        Error::new(self.offset, kind)
    }

    /// Borrow `len` bytes without copying, advancing past them.
    pub fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        if len > self.remaining() {
            return Err(self.err(ErrorKind::UnexpectedEof {
                needed: len,
                available: self.remaining(),
            }));
        }
        let start = self.offset;
        self.offset += len;
        Ok(&self.data[start..self.offset])
    }

    pub fn u8(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    pub fn u32(&mut self) -> Result<u32> {
        let b = self.take(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    pub fn i32(&mut self) -> Result<i32> {
        Ok(self.u32()? as i32)
    }

    pub fn f32(&mut self) -> Result<f32> {
        Ok(f32::from_bits(self.u32()?))
    }

    pub fn f64(&mut self) -> Result<f64> {
        let b = self.take(8)?;
        Ok(f64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    /// 7-bits-per-byte LEB128-style varint, exactly as `readVarInt` decodes it
    /// (low 7 bits are data, high bit is continuation). Capped at 5 bytes: a u32 needs at
    /// most ceil(32/7) = 5 bytes, so anything longer is malformed and we reject it rather
    /// than looping or shifting out of range.
    pub fn varint(&mut self) -> Result<u32> {
        let mut result: u32 = 0;
        let mut shift: u32 = 0;
        for _ in 0..5 {
            let byte = self.u8()?;
            // The 5th byte only has 4 meaningful low bits for a u32; masking keeps us
            // from overflowing the shift. Real bytecode never sets the discarded bits.
            result |= ((byte & 0x7f) as u32).wrapping_shl(shift);
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
        Err(self.err(ErrorKind::VarIntTooLong { max_bytes: 5 }))
    }

    /// 64-bit varint (`readVarInt64`); capped at 10 bytes (ceil(64/7)).
    pub fn varint64(&mut self) -> Result<u64> {
        let mut result: u64 = 0;
        let mut shift: u32 = 0;
        for _ in 0..10 {
            let byte = self.u8()?;
            result |= ((byte & 0x7f) as u64).wrapping_shl(shift);
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
        Err(self.err(ErrorKind::VarIntTooLong { max_bytes: 10 }))
    }

    /// Reject a declared element count that cannot possibly fit in the remaining input,
    /// where each element consumes at least `min_each` bytes. This is the guard against
    /// "allocate based on an unchecked length field": we never reserve capacity for more
    /// elements than the buffer could contain.
    pub fn guard_count(&self, count: u32, min_each: usize, what: &'static str) -> Result<()> {
        let bytes_needed = (count as u64).saturating_mul(min_each as u64);
        if bytes_needed > self.remaining() as u64 {
            return Err(self.err(ErrorKind::ImplausibleLength {
                what,
                count: count as u64,
                remaining: self.remaining(),
            }));
        }
        Ok(())
    }
}
