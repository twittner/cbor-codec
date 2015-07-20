// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! CBOR ([RFC 7049](http://tools.ietf.org/html/rfc7049))
//! encoder implementation.

use byteorder::{self, BigEndian, WriteBytesExt};
use std::io;
use std::error::Error;
use std::fmt;
use types::{Tag, Type};
use values::{Bytes, Key, Simple, Text, Value};

// Encoder Error Type ///////////////////////////////////////////////////////

pub type EncodeResult = Result<(), EncodeError>;

#[derive(Debug)]
pub enum EncodeError {
    /// Some I/O error
    IoError(io::Error),
    /// The end of file has been encountered unexpectedly
    UnexpectedEOF,
    /// The provided `Simple` value is neither unassigned nor reserved
    InvalidSimpleValue(Simple),
    /// Too many elements have been written to this `EncoderSlice`.
    /// When encoding arrays or objects the length parameter has
    /// to match the number of elements to encode.
    EndOfEncoderSlice,
    /// When encoding an array, the provided length parameter is greater
    /// than the number of elements which have actually been encoded.
    InvalidArrayLen,
    /// When encoding an object, the provided length parameter is greater
    /// than the number of elements which have actually been encoded.
    InvalidObjectLen,
    /// Certain values (e.g. `Value::Break`) are not legal to encode as
    /// independent units. Attempting to do so will trigger this error.
    InvalidValue(Value)
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            EncodeError::IoError(ref e)      => write!(f, "EncodeError: I/O error: {}", *e),
            EncodeError::UnexpectedEOF       => write!(f, "EncodeError: unexpected end-of-file"),
            EncodeError::EndOfEncoderSlice   => write!(f, "EncodeError: end of decoder slice"),
            EncodeError::InvalidArrayLen     => write!(f, "EncodeError: not enough array elements"),
            EncodeError::InvalidObjectLen    => write!(f, "EncodeError: not enough object elements"),
            EncodeError::InvalidValue(ref v) => write!(f, "EncodeError: invalid value {:?}", v),
            EncodeError::InvalidSimpleValue(ref s) => write!(f, "EncodeError: invalid simple value {:?}", s)
        }
    }
}

impl Error for EncodeError {
    fn description(&self) -> &str {
        "EncodeError"
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            EncodeError::IoError(ref e) => Some(e),
            _                           => None
        }
    }
}

impl From<byteorder::Error> for EncodeError {
    fn from(e: byteorder::Error) -> EncodeError {
        match e {
            byteorder::Error::UnexpectedEOF => EncodeError::UnexpectedEOF,
            byteorder::Error::Io(e)         => EncodeError::IoError(e)
        }
    }
}

impl From<io::Error> for EncodeError {
    fn from(e: io::Error) -> EncodeError {
        EncodeError::IoError(e)
    }
}

// Encoder //////////////////////////////////////////////////////////////////

/// The actual encoder type definition
pub struct Encoder<W> {
    writer: W
}

impl<W: WriteBytesExt> Encoder<W> {
    pub fn new(w: W) -> Encoder<W> {
        Encoder { writer: w }
    }

    pub fn into_writer(self) -> W {
        self.writer
    }

    pub fn value(&mut self, x: &Value) -> EncodeResult {
        match x {
            &Value::Array(ref vv) => self.array(vv.len(), |mut e| {
                for v in vv {
                    try!(e.value(v))
                }
                Ok(())
            }),
            &Value::Bytes(Bytes::Bytes(ref bb))  => self.bytes(&bb[..]),
            &Value::Bytes(Bytes::Chunks(ref bb)) => self.bytes_indef(|mut e| {
                for b in bb {
                    try!(e.bytes(&b[..]))
                }
                Ok(())
            }),
            &Value::Text(Text::Text(ref txt))   => self.text(txt),
            &Value::Text(Text::Chunks(ref txt)) => self.text_indef(|mut e| {
                for t in txt {
                    try!(e.text(&t[..]))
                }
                Ok(())
            }),
            &Value::Map(ref m) => self.object(m.len(), |mut e| {
                for (k, v) in m {
                    try!(e.key(k));
                    try!(e.value(v))
                }
                Ok(())
            }),
            &Value::Tagged(t, box ref val) => self.tagged(t, |mut e| e.value(val)),
            &Value::Undefined => self.writer.write_u8(0b111_00000 | 23).map_err(From::from),
            &Value::Null      => self.writer.write_u8(0b111_00000 | 22).map_err(From::from),
            &Value::Simple(s) => self.simple(s),
            &Value::Bool(b)   => self.bool(b),
            &Value::U8(n)     => self.u8(n),
            &Value::U16(n)    => self.u16(n),
            &Value::U32(n)    => self.u32(n),
            &Value::U64(n)    => self.u64(n),
            &Value::F32(n)    => self.f32(n),
            &Value::F64(n)    => self.f64(n),
            &Value::I8(n)     => self.i8(n),
            &Value::I16(n)    => self.i16(n),
            &Value::I32(n)    => self.i32(n),
            &Value::I64(n)    => self.i64(n),
            &Value::Break     => Err(EncodeError::InvalidValue(Value::Break))
        }
    }

    pub fn key(&mut self, x: &Key) -> EncodeResult {
        match x {
            &Key::Bool(b) => self.bool(b),
            &Key::I8(n)   => self.i8(n),
            &Key::I16(n)  => self.i16(n),
            &Key::I32(n)  => self.i32(n),
            &Key::I64(n)  => self.i64(n),
            &Key::U8(n)   => self.u8(n),
            &Key::U16(n)  => self.u16(n),
            &Key::U32(n)  => self.u32(n),
            &Key::U64(n)  => self.u64(n),
            &Key::Bytes(Bytes::Bytes(ref bb))  => self.bytes(&bb[..]),
            &Key::Bytes(Bytes::Chunks(ref bb)) => self.bytes_indef(|mut e| {
                for b in bb {
                    try!(e.bytes(&b[..]))
                }
                Ok(())
            }),
            &Key::Text(Text::Text(ref txt))   => self.text(txt),
            &Key::Text(Text::Chunks(ref txt)) => self.text_indef(|mut e| {
                for t in txt {
                    try!(e.text(&t[..]))
                }
                Ok(())
            })
        }
    }

    pub fn u8(&mut self, x: u8) -> EncodeResult {
        let ref mut w = self.writer;
        match x {
            0...23 => w.write_u8(x).map_err(From::from),
            _      => w.write_u8(24).and(w.write_u8(x)).map_err(From::from)
        }
    }

    pub fn u16(&mut self, x: u16) -> EncodeResult {
        let ref mut w = self.writer;
        match x {
            0...23    => w.write_u8(x as u8).map_err(From::from),
            24...0xFF => w.write_u8(24).and(w.write_u8(x as u8)).map_err(From::from),
            _         => w.write_u8(25).and(w.write_u16::<BigEndian>(x)).map_err(From::from)
        }
    }

    pub fn u32(&mut self, x: u32) -> EncodeResult {
        let ref mut w = self.writer;
        match x {
            0...23         => w.write_u8(x as u8).map_err(From::from),
            24...0xFF      => w.write_u8(24).and(w.write_u8(x as u8)).map_err(From::from),
            0x100...0xFFFF => w.write_u8(25).and(w.write_u16::<BigEndian>(x as u16)).map_err(From::from),
            _              => w.write_u8(26).and(w.write_u32::<BigEndian>(x)).map_err(From::from)
        }
    }

    pub fn u64(&mut self, x: u64) -> EncodeResult {
        let ref mut w = self.writer;
        match x {
            0...23                => w.write_u8(x as u8).map_err(From::from),
            24...0xFF             => w.write_u8(24).and(w.write_u8(x as u8)).map_err(From::from),
            0x100...0xFFFF        => w.write_u8(25).and(w.write_u16::<BigEndian>(x as u16)).map_err(From::from),
            0x100000...0xFFFFFFFF => w.write_u8(26).and(w.write_u32::<BigEndian>(x as u32)).map_err(From::from),
            _                     => w.write_u8(27).and(w.write_u64::<BigEndian>(x)).map_err(From::from)
        }
    }

    pub fn i8(&mut self, x: i8) -> EncodeResult {
        let ref mut w = self.writer;
        match (-1 - x) as u8 {
            n @ 0...23 => w.write_u8(0b001_00000 | n).map_err(From::from),
            n          => w.write_u8(0b001_00000 | 24).and(w.write_u8(n)).map_err(From::from)
        }
    }

    pub fn i16(&mut self, x: i16) -> EncodeResult {
        let ref mut w = self.writer;
        match (-1 - x) as u16 {
            n @ 0...23    => w.write_u8(0b001_00000 | n as u8).map_err(From::from),
            n @ 24...0xFF => w.write_u8(0b001_00000 | 24).and(w.write_u8(n as u8)).map_err(From::from),
            n             => w.write_u8(0b001_00000 | 25).and(w.write_u16::<BigEndian>(n)).map_err(From::from)
        }
    }

    pub fn i32(&mut self, x: i32) -> EncodeResult {
        let ref mut w = self.writer;
        match (-1 - x) as u32 {
            n @ 0...23         => w.write_u8(0b001_00000 | n as u8).map_err(From::from),
            n @ 24...0xFF      => w.write_u8(0b001_00000 | 24).and(w.write_u8(n as u8)).map_err(From::from),
            n @ 0x100...0xFFFF => w.write_u8(0b001_00000 | 25).and(w.write_u16::<BigEndian>(n as u16)).map_err(From::from),
            n                  => w.write_u8(0b001_00000 | 26).and(w.write_u32::<BigEndian>(n)).map_err(From::from)
        }
    }

    pub fn i64(&mut self, x: i64) -> EncodeResult {
        let ref mut w = self.writer;
        match (-1 - x) as u64 {
            n @ 0...23                => w.write_u8(0b001_00000 | n as u8).map_err(From::from),
            n @ 24...0xFF             => w.write_u8(0b001_00000 | 24).and(w.write_u8(n as u8)).map_err(From::from),
            n @ 0x100...0xFFFF        => w.write_u8(0b001_00000 | 25).and(w.write_u16::<BigEndian>(n as u16)).map_err(From::from),
            n @ 0x100000...0xFFFFFFFF => w.write_u8(0b001_00000 | 26).and(w.write_u32::<BigEndian>(n as u32)).map_err(From::from),
            n                         => w.write_u8(0b001_00000 | 27).and(w.write_u64::<BigEndian>(n)).map_err(From::from)
        }
    }

    pub fn f32(&mut self, x: f32) -> EncodeResult {
        self.writer.write_u8(0b111_00000 | 26)
            .and(self.writer.write_f32::<BigEndian>(x))
            .map_err(From::from)
    }

    pub fn f64(&mut self, x: f64) -> EncodeResult {
        self.writer.write_u8(0b111_00000 | 27)
            .and(self.writer.write_f64::<BigEndian>(x))
            .map_err(From::from)
    }

    pub fn bool(&mut self, x: bool) -> EncodeResult {
        self.writer.write_u8(0b111_00000 | if x {21} else {20}).map_err(From::from)
    }

    pub fn simple(&mut self, x: Simple) -> EncodeResult {
        let ref mut w = self.writer;
        match x {
            Simple::Unassigned(n) => match n {
                0...19 | 28...30 => w.write_u8(0b111_00000 | n).map_err(From::from),
                32...255         => w.write_u8(0b111_00000 | 24).and(w.write_u8(n)).map_err(From::from),
                _                => Err(EncodeError::InvalidSimpleValue(x))
            },
            Simple::Reserved(n) => match n {
                0...31 => w.write_u8(0b111_00000 | 24).and(w.write_u8(n)).map_err(From::from),
                _      => Err(EncodeError::InvalidSimpleValue(x))
            }
        }
    }

    pub fn bytes(&mut self, x: &[u8]) -> EncodeResult {
        self.type_len(Type::Bytes, x.len() as u64)
            .and(self.writer.write_all(x).map_err(From::from))
    }

    /// Indefinite byte string encoding. (RFC 7049 section 2.2.2)
    pub fn bytes_indef<F>(&mut self, mut f: F) -> EncodeResult
    where F: FnMut(BytesEncoder<W>) -> EncodeResult
    {
        try!(self.writer.write_u8(0b010_11111));
        try!(f(BytesEncoder::new(self)));
        self.writer.write_u8(0b111_11111).map_err(From::from)
    }

    pub fn text(&mut self, x: &str) -> EncodeResult {
        self.type_len(Type::Text, x.len() as u64)
            .and(self.writer.write_all(x.as_bytes()).map_err(From::from))
    }

    /// Indefinite string encoding. (RFC 7049 section 2.2.2)
    pub fn text_indef<F>(&mut self, mut f: F) -> EncodeResult
    where F: FnMut(TextEncoder<W>) -> EncodeResult
    {
        try!(self.writer.write_u8(0b011_11111));
        try!(f(TextEncoder::new(self)));
        self.writer.write_u8(0b111_11111).map_err(From::from)
    }

    pub fn opt<F, A>(&mut self, x: Option<A>, mut f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>, &A) -> EncodeResult
    {
        match x {
            Some(ref a) => f(self, a),
            None        => self.writer.write_u8(0b111_00000 | 22).map_err(From::from)
        }
    }

    pub fn tagged<F>(&mut self, x: Tag, mut f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>) -> EncodeResult
    {
        self.type_len(Type::Tagged, x.to()).and(f(self))
    }

    pub fn array<F>(&mut self, len: usize, mut f: F) -> EncodeResult
    where F: FnMut(&mut EncoderSlice<W>) -> EncodeResult
    {
        try!(self.type_len(Type::Array, len as u64));
        let mut eslice = EncoderSlice::new(self, len);
        try!(f(&mut eslice));
        if eslice.at_end() {
            Ok(())
        } else {
            Err(EncodeError::InvalidArrayLen)
        }
    }

    /// Indefinite array encoding. (RFC 7049 section 2.2.1)
    pub fn array_indef<F>(&mut self, mut f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>) -> EncodeResult
    {
        try!(self.writer.write_u8(0b100_11111));
        try!(f(self));
        self.writer.write_u8(0b100_11111).map_err(From::from)
    }

    pub fn object<F>(&mut self, len: usize, mut f: F) -> EncodeResult
    where F: FnMut(&mut EncoderSlice<W>) -> EncodeResult
    {
        try!(self.type_len(Type::Object, len as u64));
        let mut eslice = EncoderSlice::new(self, len * 2);
        try!(f(&mut eslice));
        if eslice.at_end() {
            Ok(())
        } else {
            Err(EncodeError::InvalidObjectLen)
        }
    }

    /// Indefinite object encoding. (RFC 7049 section 2.2.1)
    pub fn object_indef<F>(&mut self, mut f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>) -> EncodeResult
    {
        try!(self.writer.write_u8(0b101_11111));
        try!(f(self)); // TODO: Ensure key-value pairs are written
        self.writer.write_u8(0b101_11111).map_err(From::from)
    }

    fn type_len(&mut self, t: Type, x: u64) -> EncodeResult {
        let ref mut w = self.writer;
        match x {
            0...23                => w.write_u8(t.major() << 5 | x as u8).map_err(From::from),
            24...0xFF             => w.write_u8(t.major() << 5 | 24).and(w.write_u8(x as u8)).map_err(From::from),
            0x100...0xFFFF        => w.write_u8(t.major() << 5 | 25).and(w.write_u16::<BigEndian>(x as u16)).map_err(From::from),
            0x100000...0xFFFFFFFF => w.write_u8(t.major() << 5 | 26).and(w.write_u32::<BigEndian>(x as u32)).map_err(From::from),
            _                     => w.write_u8(t.major() << 5 | 27).and(w.write_u64::<BigEndian>(x)).map_err(From::from)
        }
    }
}

// Bytes Encoder ////////////////////////////////////////////////////////////

/// A restricted encoder type to be used for encoding indefinite byte strings.
pub struct BytesEncoder<'r, W: 'r> {
    encoder: &'r mut Encoder<W>
}

impl<'r, W: WriteBytesExt + 'r> BytesEncoder<'r, W> {
    pub fn new(e: &'r mut Encoder<W>) -> BytesEncoder<'r, W> {
        BytesEncoder { encoder: e }
    }

    pub fn bytes(&mut self, x: &[u8]) -> EncodeResult {
        self.encoder.bytes(x)
    }
}

// Text Encoder ////////////////////////////////////////////////////////////

/// A restricted encoder type to be used for encoding indefinite strings.
pub struct TextEncoder<'r, W: 'r> {
    encoder: &'r mut Encoder<W>
}

impl<'r, W: WriteBytesExt + 'r> TextEncoder<'r, W> {
    pub fn new(e: &'r mut Encoder<W>) -> TextEncoder<'r, W> {
        TextEncoder { encoder: e }
    }

    pub fn text(&mut self, x: &str) -> EncodeResult {
        self.encoder.text(x)
    }
}

// EncoderSlice /////////////////////////////////////////////////////////////

/// An `EncoderSlice` exposes the same API as `Encoder`, but only supports a
/// limited number of encoding steps.
pub struct EncoderSlice<'r, W: 'r> {
    encoder: &'r mut Encoder<W>,
    limit: usize,
    count: usize
}

impl<'r, W: WriteBytesExt + 'r> EncoderSlice<'r, W> {
    pub fn new(e: &'r mut Encoder<W>, max: usize) -> EncoderSlice<'r, W> {
        EncoderSlice { encoder: e, limit: max, count: 0 }
    }

    pub fn limit(&self) -> usize {
        self.limit
    }

    pub fn at_end(&self) -> bool {
        self.count == self.limit
    }

    pub fn value(&mut self, x: &Value) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.value(x)
    }

    pub fn key(&mut self, x: &Key) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.key(x)
    }

    pub fn u8(&mut self, x: u8) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.u8(x)
    }

    pub fn u16(&mut self, x: u16) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.u16(x)
    }

    pub fn u32(&mut self, x: u32) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.u32(x)
    }

    pub fn u64(&mut self, x: u64) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.u64(x)
    }

    pub fn i8(&mut self, x: i8) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.i8(x)
    }

    pub fn i16(&mut self, x: i16) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.i16(x)
    }

    pub fn i32(&mut self, x: i32) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.i32(x)
    }

    pub fn i64(&mut self, x: i64) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.i64(x)
    }

    pub fn f32(&mut self, x: f32) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.f32(x)
    }

    pub fn f64(&mut self, x: f64) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.f64(x)
    }

    pub fn bool(&mut self, x: bool) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.bool(x)
    }

    pub fn simple(&mut self, x: Simple) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.simple(x)
    }

    pub fn bytes(&mut self, x: &[u8]) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.bytes(x)
    }

    pub fn bytes_indef<F>(&mut self, f: F) -> EncodeResult
    where F: FnMut(BytesEncoder<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.bytes_indef(f)
    }

    pub fn text(&mut self, x: &str) -> EncodeResult {
        try!(self.check_and_bump_limit());
        self.encoder.text(x)
    }

    pub fn text_indef<F>(&mut self, f: F) -> EncodeResult
    where F: FnMut(TextEncoder<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.text_indef(f)
    }

    pub fn opt<F, A>(&mut self, x: Option<A>, f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>, &A) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.opt(x, f)
    }

    pub fn tagged<F>(&mut self, x: Tag, f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.tagged(x, f)
    }

    pub fn array<F>(&mut self, len: usize, f: F) -> EncodeResult
    where F: FnMut(&mut EncoderSlice<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.array(len, f)
    }

    pub fn array_indef<F>(&mut self, f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.array_indef(f)
    }

    pub fn object<F>(&mut self, len: usize, f: F) -> EncodeResult
    where F: FnMut(&mut EncoderSlice<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.object(len, f)
    }

    pub fn object_indef<F>(&mut self, f: F) -> EncodeResult
    where F: FnMut(&mut Encoder<W>) -> EncodeResult
    {
        try!(self.check_and_bump_limit());
        self.encoder.object_indef(f)
    }

    #[inline(always)]
    fn check_and_bump_limit(&mut self) -> EncodeResult {
        if self.count >= self.limit {
            return Err(EncodeError::EndOfEncoderSlice)
        }
        self.count += 1;
        Ok(())
    }
}

// Tests ////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use rustc_serialize::hex::FromHex;
    use std::{f32, f64};
    use std::io::Cursor;
    use super::*;
    use types::Tag;
    use values::Simple;

    #[test]
    fn unsigned() {
        encoded("00", |mut e| e.u8(0));
        encoded("01", |mut e| e.u8(1));
        encoded("0a", |mut e| e.u8(10));
        encoded("17", |mut e| e.u8(23));
        encoded("1818", |mut e| e.u8(24));
        encoded("1819", |mut e| e.u8(25));
        encoded("1864", |mut e| e.u8(100));
        encoded("1903e8", |mut e| e.u16(1000));
        encoded("1a000f4240", |mut e| e.u32(1000000));
        encoded("1b000000e8d4a51000", |mut e| e.u64(1000000000000));
        encoded("1bffffffffffffffff", |mut e| e.u64(18446744073709551615))
    }

    #[test]
    fn signed() {
        encoded("20", |mut e| e.i8(-1));
        encoded("29", |mut e| e.i8(-10));
        encoded("3863", |mut e| e.i8(-100));
        encoded("3901f3", |mut e| e.i16(-500));
        encoded("3903e7", |mut e| e.i16(-1000));
        encoded("3a00053d89", |mut e| e.i32(-343434));
        encoded("3b000000058879da85", |mut e| e.i64(-23764523654))
    }

    #[test]
    fn bool() {
        encoded("f4", |mut e| e.bool(false));
        encoded("f5", |mut e| e.bool(true))
    }

    #[test]
    fn simple() {
        encoded("f0", |mut e| e.simple(Simple::Unassigned(16)));
        encoded("f818", |mut e| e.simple(Simple::Reserved(24)));
        encoded("f8ff", |mut e| e.simple(Simple::Unassigned(255)))
    }

    #[test]
    fn float() {
        encoded("fa47c35000", |mut e| e.f32(100000.0));
        encoded("fa7f7fffff", |mut e| e.f32(3.4028234663852886e+38));
        encoded("fbc010666666666666", |mut e| e.f64(-4.1));

        encoded("fa7f800000", |mut e| e.f32(f32::INFINITY));
        encoded("faff800000", |mut e| e.f32(-f32::INFINITY));
        encoded("fa7fc00000", |mut e| e.f32(f32::NAN));

        encoded("fb7ff0000000000000", |mut e| e.f64(f64::INFINITY));
        encoded("fbfff0000000000000", |mut e| e.f64(-f64::INFINITY));
        encoded("fb7ff8000000000000", |mut e| e.f64(f64::NAN));
    }

    #[test]
    fn bytes() {
        encoded("4401020304", |mut e| e.bytes(&vec![1,2,3,4][..]));
    }

    #[test]
    fn text() {
        encoded("62c3bc", |mut e| e.text("\u{00fc}"));
        encoded("781f64667364667364660d0a7364660d0a68656c6c6f0d0a736466736673646673", |mut e| {
            e.text("dfsdfsdf\r\nsdf\r\nhello\r\nsdfsfsdfs")
        });
    }

    #[test]
    fn indefinite_text() {
        encoded("7f657374726561646d696e67ff", |mut e| {
            let input = vec!["strea", "ming"];
            e.text_indef(|mut e| {
                for s in &input {
                    try!(e.text(s))
                }
                Ok(())
            })
        })
    }

    #[test]
    fn indefinite_bytes() {
        encoded("5f457374726561446d696e67ff", |mut e| {
            let input = vec!["strea".as_bytes(), "ming".as_bytes()];
            e.bytes_indef(|mut e| {
                for b in &input {
                    try!(e.bytes(b))
                }
                Ok(())
            })
        })
    }

    #[test]
    fn option() {
        let none: Option<u8> = None;
        let some: Option<u8> = Some(1);
        encoded("f6", |mut e| {
            e.opt(none, |e, &x| e.u8(x))
        });
        encoded("01", |mut e| {
            e.opt(some, |e, &x| e.u8(x))
        })
    }

    #[test]
    fn tagged() {
        encoded("c11a514b67b0", |mut e| e.tagged(Tag::Timestamp, |e| e.u32(1363896240)))
    }

    #[test]
    fn array() {
        encoded("83010203", |mut e| e.array(3, |e| {
            try!(e.u32(1));
            try!(e.u32(2));
            e.u32(3)
        }));
        encoded("8301820203820405", |mut e| e.array(3, |e| {
            try!(e.u8(1));
            try!(e.array(2, |e| e.u8(2).and(e.u8(3))));
            e.array(2, |e| e.u8(4).and(e.u8(5)))
        }))
    }

    #[test]
    fn object() {
        encoded("a26161016162820203", |mut e| e.object(2, |e| {
            try!(e.text("a")); try!(e.u8(1));
            try!(e.text("b")); e.array(2, |e| e.u8(2).and(e.u8(3)))
        }))
    }

    fn encoded<F>(expected: &str, mut f: F)
    where F: FnMut(Encoder<Cursor<&mut [u8]>>) -> EncodeResult
    {
        let mut buffer = vec![0u8; 128];
        assert!(f(Encoder::new(Cursor::new(&mut buffer[..]))).is_ok());
        assert_eq!(&expected.from_hex().unwrap()[..], &buffer[0 .. expected.len() / 2])
    }
}


