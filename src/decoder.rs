// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! CBOR ([RFC 7049](http://tools.ietf.org/html/rfc7049))
//! decoder implementation supporting the following features:
//!
//! - Generic decoding using an intermediate representation
//! - Tag validation
//! - Resource limits (e.g. maximum nesting level)
//! - Direct decoding into Rust types
//! - Indefinite sized bytes, strings, arrays and objects

use byteorder::{self, BigEndian, ReadBytesExt};
use std::{u64, usize};
use std::collections::{BTreeMap, LinkedList};
use std::cmp::Eq;
use std::error::Error;
use std::f32;
use std::fmt::{self, Debug};
use std::io;
use std::string;
use types::{Tag, Type};
use values::{self, Bytes, Key, Simple, Text, Value};

// Decoder Configuration ////////////////////////////////////////////////////

/// `Config` contains various settings which limit resource consumption
/// or enable certain validation options. Please note that the various
/// maximum length/size values apply to an individual element only.
///
/// This is mainly to prevent attackers from providing CBOR values whose
/// length is larger than the available memory. In combination the memory
/// consumption can still become large and it is best to limit the incoming
/// bytes to a specific upper bound, e.g. by using `std::io::Take`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    /// Maximum number of array elements
    pub max_len_array: usize,
    /// Maximum length of a byte string
    pub max_len_bytes: usize,
    /// Maximum length of a string
    pub max_len_text: usize,
    /// Maximum number of object fields
    pub max_size_map: usize,
    /// Maximum recursion steps when decoder `Value`s
    pub max_nesting: usize,
    /// Ignore `Tag`s when decoding `Value`s
    pub skip_tags: bool,
    /// Validate `Value` type matches `Tag`.
    pub check_tags: bool
}

const DEFAULT_CONFIG: Config = Config
    { max_len_array: 1000
    , max_len_bytes: 0x500000
    , max_len_text: 0x500000
    , max_size_map: 1000
    , max_nesting: 16
    , skip_tags: false
    , check_tags: true
    };

impl Config {
    /// Create default configuration with
    ///
    /// - `max_len_array` = 1000
    /// - `max_len_bytes` = 5 MB
    /// - `max_len_text` = 5 MB
    /// - `max_size_map` = 1000
    /// - `max_nesting` = 16
    /// - `skip_tags` = false
    /// - `check_tags` = true
    pub fn default() -> Config { DEFAULT_CONFIG }
}

// Decode Error Type ////////////////////////////////////////////////////////

pub type DecodeResult<A> = Result<A, DecodeError>;

#[derive(Debug)]
pub enum DecodeError {
    /// An object contains the same key multiple times
    DuplicateKey(Box<Debug>),
    /// The `DecoderSlice` has reached its end and can not go any further
    EndOfDecoderSlice,
    /// The decoded `Value` can not serve as a `Key` in an object
    InvalidKey(Value),
    /// The type of `Value` is not what is expected for a `Tag`
    InvalidTag(Value),
    /// The string is not encoded in UTF-8
    InvalidUtf8(string::FromUtf8Error),
    /// Some I/O error
    IoError(io::Error),
    /// The maximum configured length is exceeded
    TooLong { max: usize, actual: u64 },
    /// `Value`s are nested deeper than the configured maximum
    TooNested,
    /// The end of file has been encountered unexpectedly
    UnexpectedEOF,
    /// And unexpected type has been encountered
    UnexpectedType { datatype: Type, info: u8 },
    /// A break was encountered at some unexpected point while
    /// decoding an indefinite object.
    UnexpectedBreak
}

impl DecodeError {
    pub fn is_break(&self) -> bool {
        match *self {
            DecodeError::UnexpectedType { datatype: Type::Break, .. } => true,
            _ => false
        }
    }
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            DecodeError::DuplicateKey(ref k) => write!(f, "DecodeError: duplicate key: {:?}", *k),
            DecodeError::EndOfDecoderSlice   => write!(f, "DecodeError: end of decoder slice"),
            DecodeError::InvalidKey(ref k)   => write!(f, "DecodeError: unsuitable map key: {:?}", *k),
            DecodeError::InvalidTag(ref v)   => write!(f, "DecodeError: value does not match tag: {:?}", *v),
            DecodeError::InvalidUtf8(ref e)  => write!(f, "DecodeError: Invalid UTF-8 encoding: {}", *e),
            DecodeError::IoError(ref e)      => write!(f, "DecodeError: I/O error: {}", *e),
            DecodeError::TooNested           => write!(f, "DecodeError: value is too nested"),
            DecodeError::UnexpectedEOF       => write!(f, "DecodeError: unexpected end-of-file"),
            DecodeError::UnexpectedBreak     => write!(f, "DecodeError: unexpected break"),
            DecodeError::TooLong{max:m, actual:a} => write!(f, "DecodeError: value is too long {} (max={})", a, m),
            DecodeError::UnexpectedType{datatype:t, info:i} => write!(f, "DecodeError: unexpected type {:?} (info={})", t, i)
        }
    }
}

impl Error for DecodeError {
    fn description(&self) -> &str {
        "DecodeError"
    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            DecodeError::IoError(ref e)     => Some(e),
            DecodeError::InvalidUtf8(ref e) => Some(e),
            _                               => None
        }
    }
}

impl From<byteorder::Error> for DecodeError {
    fn from(e: byteorder::Error) -> DecodeError {
        match e {
            byteorder::Error::UnexpectedEOF => DecodeError::UnexpectedEOF,
            byteorder::Error::Io(e)         => DecodeError::IoError(e)
        }
    }
}

impl From<io::Error> for DecodeError {
    fn from(e: io::Error) -> DecodeError {
        DecodeError::IoError(e)
    }
}

impl From<string::FromUtf8Error> for DecodeError {
    fn from(e: string::FromUtf8Error) -> DecodeError {
        DecodeError::InvalidUtf8(e)
    }
}

// Decoder Kernel ///////////////////////////////////////////////////////////

pub type TypeInfo = (Type, u8);

/// This decoding kernel reads from an underlying `std::io::Read` type
/// primitive CBOR values such as unsigned and signed integers as well
/// as raw bytes.
/// It forms the basis on which `Decoder` adds logic for handling
/// `Tag`s, heterogenous data and generic value decoding.
pub struct Kernel<R> {
    reader: R
}

impl<R: ReadBytesExt> Kernel<R> {
    pub fn new(r: R) -> Kernel<R> {
        assert!(usize::BITS <= u64::BITS);
        Kernel { reader: r }
    }

    pub fn into_reader(self) -> R {
        self.reader
    }

    pub fn typeinfo(&mut self) -> DecodeResult<TypeInfo> {
        Type::read(&mut self.reader).map_err(From::from)
    }

    pub fn simple(&mut self, ti: &TypeInfo) -> DecodeResult<Simple> {
        match ti.0 {
            Type::Unassigned { major: 7, info: a } => Ok(Simple::Unassigned(a)),
            Type::Reserved   { major: 7, info: a } => Ok(Simple::Reserved(a)),
            _                                      => unexpected_type(ti)
        }
    }

    pub fn bool(&mut self, ti: &TypeInfo) -> DecodeResult<bool> {
        match *ti {
            (Type::Bool, 20) => Ok(false),
            (Type::Bool, 21) => Ok(true),
            _                => unexpected_type(ti)
        }
    }

    pub fn u8(&mut self, ti: &TypeInfo) -> DecodeResult<u8> {
        match *ti {
            (Type::UInt8, n @ 0...23) => Ok(n),
            (Type::UInt8, 24) => self.reader.read_u8().map_err(From::from),
            _                 => unexpected_type(ti)
        }
    }

    pub fn u16(&mut self, ti: &TypeInfo) -> DecodeResult<u16> {
        match *ti {
            (Type::UInt8, n @ 0...23) => Ok(n as u16),
            (Type::UInt8, 24)  => self.reader.read_u8().map(|n| n as u16).map_err(From::from),
            (Type::UInt16, 25) => self.reader.read_u16::<BigEndian>().map_err(From::from),
            _                  => unexpected_type(ti)
        }
    }

    pub fn u32(&mut self, ti: &TypeInfo) -> DecodeResult<u32> {
        match *ti {
            (Type::UInt8, n @ 0...23) => Ok(n as u32),
            (Type::UInt8, 24)  => self.reader.read_u8().map(|n| n as u32).map_err(From::from),
            (Type::UInt16, 25) => self.reader.read_u16::<BigEndian>().map(|n| n as u32).map_err(From::from),
            (Type::UInt32, 26) => self.reader.read_u32::<BigEndian>().map_err(From::from),
            _                  => unexpected_type(ti)
        }
    }

    pub fn u64(&mut self, ti: &TypeInfo) -> DecodeResult<u64> {
        match *ti {
            (Type::UInt8, n @ 0...23) => Ok(n as u64),
            (Type::UInt8, 24)  => self.reader.read_u8().map(|n| n as u64).map_err(From::from),
            (Type::UInt16, 25) => self.reader.read_u16::<BigEndian>().map(|n| n as u64).map_err(From::from),
            (Type::UInt32, 26) => self.reader.read_u32::<BigEndian>().map(|n| n as u64).map_err(From::from),
            (Type::UInt64, 27) => self.reader.read_u64::<BigEndian>().map_err(From::from),
            _                  => unexpected_type(ti)
        }
    }

    pub fn i8(&mut self, ti: &TypeInfo) -> DecodeResult<i8> {
        match *ti {
            (Type::Int8, n @ 0...23) => Ok(-1 - n as i8),
            (Type::Int8, 24) => self.reader.read_u8().map(|n| -1 - n as i8).map_err(From::from),
            _                => unexpected_type(ti)
        }
    }

    pub fn i16(&mut self, ti: &TypeInfo) -> DecodeResult<i16> {
        match *ti {
            (Type::Int8, n @ 0...23) => Ok(-1 - n as i16),
            (Type::Int8, 24)  => self.reader.read_u8().map(|n| -1 - n as i16).map_err(From::from),
            (Type::Int16, 25) => self.reader.read_u16::<BigEndian>().map(|n| -1 - n as i16).map_err(From::from),
            _                 => unexpected_type(ti)
        }
    }

    pub fn i32(&mut self, ti: &TypeInfo) -> DecodeResult<i32> {
        match *ti {
            (Type::Int8, n @ 0...23) => Ok(-1 - n as i32),
            (Type::Int8, 24)  => self.reader.read_u8().map(|n| -1 - n as i32).map_err(From::from),
            (Type::Int16, 25) => self.reader.read_u16::<BigEndian>().map(|n| -1 - n as i32).map_err(From::from),
            (Type::Int32, 26) => self.reader.read_u32::<BigEndian>().map(|n| -1 - n as i32).map_err(From::from),
            _                 => unexpected_type(ti)
        }
    }

    pub fn i64(&mut self, ti: &TypeInfo) -> DecodeResult<i64> {
        match *ti {
            (Type::Int8, n @ 0...23) => Ok(-1 - n as i64),
            (Type::Int8, 24)  => self.reader.read_u8().map(|n| -1 - n as i64).map_err(From::from),
            (Type::Int16, 25) => self.reader.read_u16::<BigEndian>().map(|n| -1 - n as i64).map_err(From::from),
            (Type::Int32, 26) => self.reader.read_u32::<BigEndian>().map(|n| -1 - n as i64).map_err(From::from),
            (Type::Int64, 27) => self.reader.read_u64::<BigEndian>().map(|n| -1 - n as i64).map_err(From::from),
            _                 => unexpected_type(ti)
        }
    }

    pub fn f16(&mut self, ti: &TypeInfo) -> DecodeResult<f32> {
        match ti.0 {
            Type::Float16 => {
                // Copied from RFC 7049 Appendix D:
                let half  = try!(self.reader.read_u16::<BigEndian>());
                let exp   = half >> 10 & 0x1F;
                let mant  = half & 0x3FF;
                let value = match exp {
                    0  => f32::ldexp(mant as f32, -24),
                    31 => if mant == 0 { f32::INFINITY } else { f32::NAN },
                    _  => f32::ldexp(mant as f32 + 1024.0, exp as isize - 25)
                };
                Ok(if half & 0x8000 == 0 { value } else { - value })
            }
            _ => unexpected_type(ti)
        }
    }

    pub fn f32(&mut self, ti: &TypeInfo) -> DecodeResult<f32> {
        match ti.0 {
            Type::Float32 => self.reader.read_f32::<BigEndian>().map_err(From::from),
            _             => unexpected_type(ti)
        }
    }

    pub fn f64(&mut self, ti: &TypeInfo) -> DecodeResult<f64> {
        match ti.0 {
            Type::Float64 => self.reader.read_f64::<BigEndian>().map_err(From::from),
            _             => unexpected_type(ti)
        }
    }

    /// Decode `first` and potentially the following bytes as an
    /// unsigned value following the rules of major type 0.
    pub fn unsigned(&mut self, first: u8) -> DecodeResult<u64> {
        match first {
            n @ 0...23 => Ok(n as u64),
            24 => self.reader.read_u8().map(|n| n as u64).map_err(From::from),
            25 => self.reader.read_u16::<BigEndian>().map(|n| n as u64).map_err(From::from),
            26 => self.reader.read_u32::<BigEndian>().map(|n| n as u64).map_err(From::from),
            27 => self.reader.read_u64::<BigEndian>().map_err(From::from),
            _  => unexpected_type(&(Type::UInt64, first))
        }
    }

    /// Read `begin` as the length and return that many raw bytes.
    /// If length is greater than the given `max_len`, `DecodeError::TooLong`
    /// is returned instead.
    pub fn raw_data(&mut self, begin: u8, max_len: usize) -> DecodeResult<Vec<u8>> {
        let len = try!(self.unsigned(begin));
        if len > max_len as u64 {
            return Err(DecodeError::TooLong { max: max_len, actual: len })
        }
        let n = len as usize;
        let mut v = vec![0u8; n];
        let mut i = 0;
        while i < n {
            match self.reader.read(&mut v[i..]) {
                Ok(0)  => return Err(DecodeError::UnexpectedEOF),
                Ok(j)  => i += j,
                Err(e) =>
                    if e.kind() != io::ErrorKind::Interrupted {
                        return Err(DecodeError::IoError(e))
                    }
            }
        }
        Ok(v)
    }
}

#[inline(always)]
fn unexpected_type<A>(ti: &TypeInfo) -> DecodeResult<A> {
    Err(DecodeError::UnexpectedType { datatype: ti.0, info: ti.1 })
}

// Decoder //////////////////////////////////////////////////////////////////

/// The actual decoder type definition
pub struct Decoder<R> {
    kernel: Kernel<R>,
    config: Config,
    nesting: usize
}

impl<R: ReadBytesExt> Decoder<R> {
    pub fn new(c: Config, r: R) -> Decoder<R> {
        assert!(usize::BITS <= u64::BITS);
        Decoder { kernel: Kernel::new(r), config: c, nesting: 0 }
    }

    pub fn into_reader(self) -> R {
        self.kernel.into_reader()
    }

    pub fn simple(&mut self) -> DecodeResult<Simple> {
        self.typeinfo().and_then(|ti| self.kernel.simple(&ti))
    }

    pub fn bool(&mut self) -> DecodeResult<bool> {
        self.typeinfo().and_then(|ti| self.kernel.bool(&ti))
    }

    pub fn u8(&mut self) -> DecodeResult<u8> {
        self.typeinfo().and_then(|ti| self.kernel.u8(&ti))
    }

    pub fn u16(&mut self) -> DecodeResult<u16> {
        self.typeinfo().and_then(|ti| self.kernel.u16(&ti))
    }

    pub fn u32(&mut self) -> DecodeResult<u32> {
        self.typeinfo().and_then(|ti| self.kernel.u32(&ti))
    }

    pub fn u64(&mut self) -> DecodeResult<u64> {
        self.typeinfo().and_then(|ti| self.kernel.u64(&ti))
    }

    pub fn i8(&mut self) -> DecodeResult<i8> {
        self.typeinfo().and_then(|ti| self.kernel.i8(&ti))
    }

    pub fn i16(&mut self) -> DecodeResult<i16> {
        self.typeinfo().and_then(|ti| self.kernel.i16(&ti))
    }

    pub fn i32(&mut self) -> DecodeResult<i32> {
        self.typeinfo().and_then(|ti| self.kernel.i32(&ti))
    }

    pub fn i64(&mut self) -> DecodeResult<i64> {
        self.typeinfo().and_then(|ti| self.kernel.i64(&ti))
    }

    pub fn f16(&mut self) -> DecodeResult<f32> {
        self.typeinfo().and_then(|ti| self.kernel.f16(&ti))
    }

    pub fn f32(&mut self) -> DecodeResult<f32> {
        self.typeinfo().and_then(|ti| self.kernel.f32(&ti))
    }

    pub fn f64(&mut self) -> DecodeResult<f64> {
        self.typeinfo().and_then(|ti| self.kernel.f64(&ti))
    }

    /// Decode into a `Value`, i.e. an intermediate representation which
    /// can be further deconstructed using `ValueDecoder`.
    /// This supports indefinite decoding as well as tag validation
    /// (if not disabled).
    pub fn value(&mut self) -> DecodeResult<Value> {
        match try!(self.kernel.typeinfo()) {
            ti@(Type::UInt8, _)   => self.kernel.u8(&ti).map(Value::U8),
            ti@(Type::UInt16, _)  => self.kernel.u16(&ti).map(Value::U16),
            ti@(Type::UInt32, _)  => self.kernel.u32(&ti).map(Value::U32),
            ti@(Type::UInt64, _)  => self.kernel.u64(&ti).map(Value::U64),
            ti@(Type::Int8, _)    => self.kernel.i8(&ti).map(Value::I8),
            ti@(Type::Int16, _)   => self.kernel.i16(&ti).map(Value::I16),
            ti@(Type::Int32, _)   => self.kernel.i32(&ti).map(Value::I32),
            ti@(Type::Int64, _)   => self.kernel.i64(&ti).map(Value::I64),
            ti@(Type::Float16, _) => self.kernel.f16(&ti).map(Value::F32),
            ti@(Type::Float32, _) => self.kernel.f32(&ti).map(Value::F32),
            ti@(Type::Float64, _) => self.kernel.f64(&ti).map(Value::F64),
            ti@(Type::Bool, _)    => self.kernel.bool(&ti).map(Value::Bool),
            (Type::Null, _)       => Ok(Value::Null),
            (Type::Undefined, _)  => Ok(Value::Undefined),
            (Type::Break, _)      => Ok(Value::Break),
            (Type::Bytes, 31)     => { // indefinite byte string
                let mut i = 0u64;
                let mut v = LinkedList::new();
                loop {
                    match self.bytes() {
                        Ok(chunk) => {
                            i += chunk.len() as u64;
                            if i > self.config.max_len_bytes as u64 {
                                return Err(DecodeError::TooLong { max: self.config.max_len_bytes, actual: i })
                            }
                            v.push_back(chunk)
                        }
                        Err(ref e) if e.is_break() => break,
                        Err(e) => return Err(e)
                    }
                }
                Ok(Value::Bytes(Bytes::Chunks(v)))
            }
            (Type::Bytes, a) => {
                let max = self.config.max_len_bytes;
                self.kernel.raw_data(a, max).map(|x| Value::Bytes(Bytes::Bytes(x)))
            }
            (Type::Text, 31) => { // indefinite string
                let mut i = 0u64;
                let mut v = LinkedList::new();
                loop {
                    match self.text() {
                        Ok(chunk) => {
                            i += chunk.len() as u64;
                            if i > self.config.max_len_text as u64 {
                                return Err(DecodeError::TooLong { max: self.config.max_len_text, actual: i })
                            }
                            v.push_back(chunk)
                        }
                        Err(ref e) if e.is_break() => break,
                        Err(e) => return Err(e)
                    }
                }
                Ok(Value::Text(Text::Chunks(v)))
            }
            (Type::Text, a) => {
                let max  = self.config.max_len_text;
                let data = try!(self.kernel.raw_data(a, max));
                String::from_utf8(data).map(|x| Value::Text(Text::Text(x))).map_err(From::from)
            }
            (Type::Array, 31) => { // indefinite length array
                if self.nesting > self.config.max_nesting {
                    return Err(DecodeError::TooNested)
                }
                let mut i = 0u64;
                let mut v = Vec::new();
                loop {
                    i += 1;
                    if i > self.config.max_len_array as u64 {
                        return Err(DecodeError::TooLong { max: self.config.max_len_array, actual: i })
                    }
                    self.nesting += 1;
                    match self.value() {
                        Ok(Value::Break) => {
                            self.nesting -= 1;
                            break
                        }
                        Ok(x) => v.push(x),
                        e     => return e
                    }
                    self.nesting -= 1;
                }
                Ok(Value::Array(v))
            }
            (Type::Array, a) => {
                if self.nesting > self.config.max_nesting {
                    return Err(DecodeError::TooNested)
                }
                let len = try!(self.kernel.unsigned(a));
                if len > self.config.max_len_array as u64 {
                    return Err(DecodeError::TooLong { max: self.config.max_len_array, actual: len })
                }
                let n = len as usize;
                let mut v = Vec::with_capacity(n);
                for _ in 0 .. n {
                    self.nesting += 1;
                    v.push(try!(self.value()));
                    self.nesting -= 1;
                }
                Ok(Value::Array(v))
            }
            (Type::Object, 31) => { // indefinite size object
                if self.nesting > self.config.max_nesting {
                    return Err(DecodeError::TooNested)
                }
                let mut i = 0u64;
                let mut m = BTreeMap::new();
                loop {
                    i += 1;
                    if i > self.config.max_size_map as u64 {
                        return Err(DecodeError::TooLong { max: self.config.max_size_map, actual: i })
                    }
                    self.nesting += 1;
                    match self.key() {
                        Ok(key) => {
                            if m.contains_key(&key) {
                                return Err(DecodeError::DuplicateKey(Box::new(key)))
                            }
                            match try!(self.value()) {
                                Value::Break => return Err(DecodeError::UnexpectedBreak),
                                value        => { m.insert(key, value); }
                            }
                        }
                        Err(DecodeError::InvalidKey(Value::Break)) => {
                            self.nesting -= 1;
                            break
                        }
                        Err(e) => return Err(e)
                    }
                    self.nesting -= 1;
                }
                Ok(Value::Map(m))
            }
            (Type::Object, a) => {
                if self.nesting > self.config.max_nesting {
                    return Err(DecodeError::TooNested)
                }
                let len = try!(self.kernel.unsigned(a));
                if len > self.config.max_size_map as u64 {
                    return Err(DecodeError::TooLong { max: self.config.max_size_map, actual: len })
                }
                let n = len as usize;
                let mut m = BTreeMap::new();
                for _ in 0 .. n {
                    self.nesting += 1;
                    let key = try!(self.key());
                    if m.contains_key(&key) {
                        return Err(DecodeError::DuplicateKey(Box::new(key)))
                    }
                    m.insert(key, try!(self.value()));
                    self.nesting -= 1;
                }
                Ok(Value::Map(m))
            }
            (Type::Tagged, a) => {
                let tag = try!(self.kernel.unsigned(a).map(Tag::of));
                if self.config.skip_tags {
                    return self.value()
                }
                if self.nesting > self.config.max_nesting {
                    return Err(DecodeError::TooNested)
                }
                self.nesting += 1;
                let val = try!(self.value().map(|v| Value::Tagged(tag, Box::new(v))));
                if self.config.check_tags && !values::check(&val) {
                    return Err(DecodeError::InvalidTag(val))
                }
                self.nesting -= 1;
                Ok(val)
            }
            (Type::Unassigned { major: 7, info: a }, _) => Ok(Value::Simple(Simple::Unassigned(a))),
            (Type::Reserved { major: 7, info: a }, _)   => Ok(Value::Simple(Simple::Reserved(a))),
            ti => unexpected_type(&ti)
        }
    }

    fn key(&mut self) -> DecodeResult<Key> {
        match try!(self.value()) {
            Value::Bool(x)   => Ok(Key::Bool(x)),
            Value::Bytes(x)  => Ok(Key::Bytes(x)),
            Value::I8(x)     => Ok(Key::I8(x)),
            Value::I16(x)    => Ok(Key::I16(x)),
            Value::I32(x)    => Ok(Key::I32(x)),
            Value::I64(x)    => Ok(Key::I64(x)),
            Value::Text(x)   => Ok(Key::Text(x)),
            Value::U8(x)     => Ok(Key::U8(x)),
            Value::U16(x)    => Ok(Key::U16(x)),
            Value::U32(x)    => Ok(Key::U32(x)),
            Value::U64(x)    => Ok(Key::U64(x)),
            other            => Err(DecodeError::InvalidKey(other))
        }
    }

    /// Decode a single byte string.
    ///
    /// Please note that indefinite byte strings are not supported by this
    /// method (Consider using `Decoder::value()` for this use-case).
    pub fn bytes(&mut self) -> DecodeResult<Vec<u8>> {
        match try!(self.typeinfo()) {
            (Type::Bytes, i) => {
                let max = self.config.max_len_bytes;
                self.kernel.raw_data(i, max)
            }
            ti => unexpected_type(&ti)
        }
    }

    /// Decode a single UTF-8 encoded String.
    ///
    /// Please note that indefinite strings are not supported by this method
    /// (Consider using `Decoder::value()` for this use-case).
    pub fn text(&mut self) -> DecodeResult<String> {
        match try!(self.typeinfo()) {
            (Type::Text, i) => {
                let max  = self.config.max_len_text;
                let data = try!(self.kernel.raw_data(i, max));
                String::from_utf8(data).map_err(From::from)
            }
            ti => unexpected_type(&ti)
        }
    }

    /// Decode a `Tag` and pass it together with a `DecoderSlice` to the
    /// given callback function. If no tag is found an `UnexpectedType`
    /// error is returned.
    pub fn tagged<F, A>(&mut self, mut f: F) -> DecodeResult<A>
    where F: FnMut(&mut DecoderSlice<R>, Tag) -> DecodeResult<A>
    {
        match try!(self.kernel.typeinfo()) {
            (Type::Tagged, i) => {
                let tag = try!(self.kernel.unsigned(i).map(Tag::of));
                f(&mut DecoderSlice::new(self, 1), tag)
            }
            ti => unexpected_type(&ti)
        }
    }

    /// Decode an optional value, i.e. return either `None` if a CBOR `Null`
    /// is found, or the actual value wrapped in `Some`.
    pub fn opt<F, A>(&mut self, mut f: F) -> DecodeResult<Option<A>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        match f(&mut DecoderSlice::new(self, 1)) {
            Ok(x) => Ok(Some(x)),
            Err(DecodeError::UnexpectedType { datatype: Type::Null, .. }) => Ok(None),
            Err(e) => Err(e)
        }
    }

    /// Decode a potentially undefined value (cf. RFC 7049 section 3.8).
    /// If a CBOR `Undefined` is encountered it is mapped to `None`,
    /// otherwise the value is wrapped in `Some`.
    pub fn def<F, A>(&mut self, mut f: F) -> DecodeResult<Option<A>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        match f(&mut DecoderSlice::new(self, 1)) {
            Ok(x) => Ok(Some(x)),
            Err(DecodeError::UnexpectedType { datatype: Type::Undefined, .. }) => Ok(None),
            Err(e) => Err(e)
        }
    }

    /// Decode a potentially heterogenous CBOR array. The provided function is
    /// applied to a `DecoderSlice`, i.e. a decoder which can be used over the
    /// entire array length but no further. Whatever the function returns
    /// becomes the result of `array`. If you want to decode a homogenous array
    /// you may consider using `vector` instead.
    ///
    /// Please note that indefinite arrays are not supported by this method
    /// (Consider using `Decoder::value()` for this use-case).
    pub fn array<F, A>(&mut self, mut f: F) -> DecodeResult<A>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        match try!(self.typeinfo()) {
            (Type::Array, 31) => unexpected_type(&(Type::Array, 31)),
            (Type::Array,  a) => {
                let len = try!(self.kernel.unsigned(a));
                if len > self.config.max_len_array as u64 {
                    return Err(DecodeError::TooLong { max: self.config.max_len_array, actual: len })
                }
                f(&mut DecoderSlice::new(self, len as usize))
            }
            ti => unexpected_type(&ti)
        }
    }

    /// Like `array`, but `f` is applied to the `DecoderSlice` for every
    /// array element. `vector` aggregates the results in a `Vec` which is
    /// returned on completion.
    ///
    /// Please note that indefinite arrays are not supported by this method
    /// (Consider using `Decoder::value()` for this use-case).
    pub fn vector<F, A>(&mut self, mut f: F) -> DecodeResult<Vec<A>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        self.array(|d| {
            let mut v = Vec::with_capacity(d.limit());
            for _ in 0 .. d.limit() {
                v.push(try!(f(d)))
            }
            Ok(v)
        })
    }

    /// CBOR maps are potentially heterogenous collections. Decoding these
    /// can be done through `Decoder::value()`. This method is for decoding
    /// `BTreeMap`s. The provided callback function is applied to a `DecoderSlice`
    /// to decode a single key-value pair. The whole map is returned as result.
    pub fn treemap<F, K, V>(&mut self, mut f: F) -> DecodeResult<BTreeMap<K, V>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<(K, V)>,
          K: Ord + Debug + 'static
    {
        match try!(self.typeinfo()) {
            (Type::Object, 31) => { // indefinite length map
                let mut i = 064;
                let mut m = BTreeMap::new();
                loop {
                    i += 1;
                    if i > self.config.max_size_map as u64 {
                        return Err(DecodeError::TooLong { max: self.config.max_size_map, actual: i })
                    }
                    match f(&mut DecoderSlice::new(self, 2)) {
                        Ok((k, v)) => {
                            if m.contains_key(&k) {
                                return Err(DecodeError::DuplicateKey(Box::new(k)))
                            }
                            m.insert(k, v);
                        }
                        Err(ref e) if e.is_break() => break,
                        Err(e) => return Err(e)
                    }
                }
                Ok(m)
            }
            (Type::Object, a) => {
                let len = try!(self.kernel.unsigned(a));
                if len > self.config.max_size_map as u64 {
                    return Err(DecodeError::TooLong { max: self.config.max_size_map, actual: len })
                }
                let mut m = BTreeMap::new();
                for _ in 0 .. len {
                    let (k, v) = try!(f(&mut DecoderSlice::new(self, 2)));
                    if m.contains_key(&k) {
                        return Err(DecodeError::DuplicateKey(Box::new(k)))
                    }
                    m.insert(k, v);
                }
                Ok(m)
            }
            ti => unexpected_type(&ti)
        }
    }

    // Decode type information while skipping tags
    fn typeinfo(&mut self) -> DecodeResult<TypeInfo> {
        match try!(self.kernel.typeinfo()) {
            (Type::Tagged, i) => {
                if self.nesting > self.config.max_nesting {
                    return Err(DecodeError::TooNested)
                }
                self.nesting += 1;
                let ti = self.kernel.unsigned(i).and(self.typeinfo());
                self.nesting -= 1;
                ti
            }
            ti => Ok(ti)
        }
    }
}

/// A `DecoderSlice` exposes the same API as `Decoder`, but is limited to
/// a smaller ranger than the `Decoder` that constructed the `DecoderSlice`.
pub struct DecoderSlice<'r, R: 'r> {
    decoder: &'r mut Decoder<R>,
    limit: usize,
    count: usize
}

impl<'r, R: ReadBytesExt + 'r> DecoderSlice<'r, R> {
    pub fn new(d: &'r mut Decoder<R>, max: usize) -> DecoderSlice<'r, R> {
        DecoderSlice { decoder: d, limit: max, count: 0 }
    }

    pub fn limit(&self) -> usize {
        self.limit
    }

    pub fn value(&mut self) -> DecodeResult<Value> {
        try!(self.check_and_bump_limit());
        self.decoder.value()
    }

    pub fn simple(&mut self) -> DecodeResult<Simple> {
        try!(self.check_and_bump_limit());
        self.decoder.simple()
    }

    pub fn bool(&mut self) -> DecodeResult<bool> {
        try!(self.check_and_bump_limit());
        self.decoder.bool()
    }

    pub fn u8(&mut self) -> DecodeResult<u8> {
        try!(self.check_and_bump_limit());
        self.decoder.u8()
    }

    pub fn u16(&mut self) -> DecodeResult<u16> {
        try!(self.check_and_bump_limit());
        self.decoder.u16()
    }

    pub fn u32(&mut self) -> DecodeResult<u32> {
        try!(self.check_and_bump_limit());
        self.decoder.u32()
    }

    pub fn u64(&mut self) -> DecodeResult<u64> {
        try!(self.check_and_bump_limit());
        self.decoder.u64()
    }

    pub fn i8(&mut self) -> DecodeResult<i8> {
        try!(self.check_and_bump_limit());
        self.decoder.i8()
    }

    pub fn i16(&mut self) -> DecodeResult<i16> {
        try!(self.check_and_bump_limit());
        self.decoder.i16()
    }

    pub fn i32(&mut self) -> DecodeResult<i32> {
        try!(self.check_and_bump_limit());
        self.decoder.i32()
    }

    pub fn i64(&mut self) -> DecodeResult<i64> {
        try!(self.check_and_bump_limit());
        self.decoder.i64()
    }

    pub fn f16(&mut self) -> DecodeResult<f32> {
        try!(self.check_and_bump_limit());
        self.decoder.f16()
    }

    pub fn f32(&mut self) -> DecodeResult<f32> {
        try!(self.check_and_bump_limit());
        self.decoder.f32()
    }

    pub fn f64(&mut self) -> DecodeResult<f64> {
        try!(self.check_and_bump_limit());
        self.decoder.f64()
    }

    pub fn bytes(&mut self) -> DecodeResult<Vec<u8>> {
        try!(self.check_and_bump_limit());
        self.decoder.bytes()
    }

    pub fn text(&mut self) -> DecodeResult<String> {
        try!(self.check_and_bump_limit());
        self.decoder.text()
    }

    pub fn tagged<F, A>(&mut self, f: F) -> DecodeResult<A>
    where F: FnMut(&mut DecoderSlice<R>, Tag) -> DecodeResult<A>
    {
        try!(self.check_and_bump_limit());
        self.decoder.tagged(f)
    }

    pub fn opt<F, A>(&mut self, f: F) -> DecodeResult<Option<A>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        try!(self.check_and_bump_limit());
        self.decoder.opt(f)
    }

    pub fn def<F, A>(&mut self, f: F) -> DecodeResult<Option<A>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        try!(self.check_and_bump_limit());
        self.decoder.def(f)
    }

    pub fn array<F, A>(&mut self, f: F) -> DecodeResult<A>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        try!(self.check_and_bump_limit());
        self.decoder.array(f)
    }

    pub fn vector<F, A>(&mut self, f: F) -> DecodeResult<Vec<A>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<A>
    {
        try!(self.check_and_bump_limit());
        self.decoder.vector(f)
    }

    pub fn treemap<F, K, V>(&mut self, f: F) -> DecodeResult<BTreeMap<K, V>>
    where F: FnMut(&mut DecoderSlice<R>) -> DecodeResult<(K, V)>,
          K: Ord + Debug + 'static
    {
        try!(self.check_and_bump_limit());
        self.decoder.treemap(f)
    }

    #[inline(always)]
    fn check_and_bump_limit(&mut self) -> DecodeResult<()> {
        if self.count >= self.limit {
            return Err(DecodeError::EndOfDecoderSlice)
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
    use std::collections::{BTreeMap, LinkedList};
    use std::io::Cursor;
    use super::*;
    use types::{Tag, Type};
    use values::{Key, Simple, Text, Value, ValueDecoder};

    #[test]
    fn unsigned() {
        assert_eq!(Some(0), decoder("00").u8().ok());
        assert_eq!(Some(1), decoder("01").u8().ok());
        assert_eq!(Some(10), decoder("0a").u8().ok());
        assert_eq!(Some(23), decoder("17").u8().ok());
        assert_eq!(Some(24), decoder("1818").u8().ok());
        assert_eq!(Some(25), decoder("1819").u8().ok());
        assert_eq!(Some(100), decoder("1864").u8().ok());
        assert_eq!(Some(1000), decoder("1903e8").u16().ok());
        assert_eq!(Some(1000000), decoder("1a000f4240").u32().ok());
        assert_eq!(Some(1000000000000), decoder("1b000000e8d4a51000").u64().ok());
        assert_eq!(Some(18446744073709551615), decoder("1bffffffffffffffff").u64().ok());
    }

    #[test]
    fn signed() {
        assert_eq!(Some(-1), decoder("20").i8().ok());
        assert_eq!(Some(-10), decoder("29").i8().ok());
        assert_eq!(Some(-100), decoder("3863").i8().ok());
        assert_eq!(Some(-500), decoder("3901f3").i16().ok());
        assert_eq!(Some(-1000), decoder("3903e7").i16().ok());
        assert_eq!(Some(-343434), decoder("3a00053d89").i32().ok());
        assert_eq!(Some(-23764523654), decoder("3b000000058879da85").i64().ok())
    }

    #[test]
    fn float() {
        assert_eq!(Some(0.0), decoder("f90000").f16().ok());
        assert_eq!(Some(-0.0), decoder("f98000").f16().ok());
        assert_eq!(Some(1.0), decoder("f93c00").f16().ok());
        assert_eq!(Some(1.5), decoder("f93e00").f16().ok());
        assert_eq!(Some(65504.0), decoder("f97bff").f16().ok());
        assert_eq!(Some(f32::INFINITY), decoder("f97c00").f16().ok());
        assert_eq!(Some(-f32::INFINITY), decoder("f9fc00").f16().ok());
        assert!(decoder("f97e00").f16().ok().unwrap().is_nan());

        assert_eq!(Some(100000.0), decoder("fa47c35000").f32().ok());
        assert_eq!(Some(3.4028234663852886e+38), decoder("fa7f7fffff").f32().ok());
        assert_eq!(Some(-4.1), decoder("fbc010666666666666").f64().ok());

        assert_eq!(Some(f32::INFINITY), decoder("fa7f800000").f32().ok());
        assert_eq!(Some(-f32::INFINITY), decoder("faff800000").f32().ok());
        assert!(decoder("fa7fc00000").f32().ok().unwrap().is_nan());

        assert_eq!(Some(1.0e+300), decoder("fb7e37e43c8800759c").f64().ok());
        assert_eq!(Some(f64::INFINITY), decoder("fb7ff0000000000000").f64().ok());
        assert_eq!(Some(-f64::INFINITY), decoder("fbfff0000000000000").f64().ok());
        assert!(decoder("fb7ff8000000000000").f64().ok().unwrap().is_nan())
    }

    #[test]
    fn bool() {
        assert_eq!(Some(false), decoder("f4").bool().ok());
        assert_eq!(Some(true), decoder("f5").bool().ok());
    }

    #[test]
    fn simple() {
        assert_eq!(Some(Simple::Unassigned(16)), decoder("f0").simple().ok());
        assert_eq!(Some(Simple::Reserved(24)), decoder("f818").simple().ok());
        assert_eq!(Some(Simple::Unassigned(255)), decoder("f8ff").simple().ok())
    }

    #[test]
    fn bytes() {
        assert_eq!(Some(vec![1,2,3,4]), decoder("4401020304").bytes().ok())
    }

    #[test]
    fn text() {
        let expected1 = String::from("dfsdfsdf\r\nsdf\r\nhello\r\nsdfsfsdfs");
        assert_eq!(Some(expected1), decoder("781f64667364667364660d0a7364660d0a68656c6c6f0d0a736466736673646673").text().ok());

        let expected2 = String::from("\u{00fc}");
        assert_eq!(Some(expected2), decoder("62c3bc").text().ok());

        let mut streaming = LinkedList::new();
        streaming.push_back(String::from("strea"));
        streaming.push_back(String::from("ming"));
        assert_eq!(
            Some(&streaming),
            ValueDecoder::new(&decoder("7f657374726561646d696e67ff").value().unwrap()).text_chunked()
        );
    }

    #[test]
    fn option() {
        let none: Option<u8> = None;
        let some: Option<u8> = Some(1);
        assert_eq!(Some(none), decoder("f6").opt(|d| d.u8()).ok());
        assert_eq!(Some(some), decoder("01").opt(|d| d.u8()).ok())
    }

    #[test]
    fn undefined() {
        let undef: Option<u8> = None;
        let def: Option<u8> = Some(1);
        assert_eq!(Some(undef), decoder("f7").def(|d| d.u8()).ok());
        assert_eq!(Some(def), decoder("01").def(|d| d.u8()).ok())
    }

    #[test]
    fn empty_arrays() {
        assert_eq!(Some(Value::Array(vec![])), decoder("9fff").value().ok());

        // Indefinite arrays not supported in direct decoding.
        match decoder("9fff").array(|_| Ok(())) {
            Err(DecodeError::UnexpectedType { datatype: Type::Array, info: 31}) => (),
            other => panic!("unexcted result: {:?}", other)
        }
    }

    #[test]
    fn array() {
        let result = decoder("83010203").array(|a| {
            assert_eq!(3, a.limit());
            assert_eq!(Some(1u32), a.u32().ok());
            assert_eq!(Some(2u32), a.u32().ok());
            assert_eq!(Some(3u32), a.u32().ok());
            Ok(())
        });
        assert_eq!(Some(()), result.ok())
    }

    #[test]
    fn vector() {
        assert_eq!(Some(vec![1,2,3]), decoder("83010203").vector(|d| d.u32()).ok())
    }

    #[test]
    fn treemap() {
        let mut map = BTreeMap::new();
        map.insert(String::from("a"), 1u8);
        map.insert(String::from("b"), 2u8);
        map.insert(String::from("c"), 3u8);
        assert_eq!(
            Some(map),
            decoder("a3616101616202616303").treemap(|d| Ok((try!(d.text()), try!(d.u8())))).ok()
        )
    }

    #[test]
    fn array_of_array() {
        let result = decoder("828301020383010203").array(|outer| {
            let mut v = Vec::with_capacity(outer.limit());
            for _ in 0 .. outer.limit() {
                v.push(outer.array(|inner| {
                    let mut w = Vec::with_capacity(inner.limit());
                    for _ in 0 .. inner.limit() {
                        w.push(inner.u8().ok().unwrap())
                    }
                    Ok(w)
                }).ok().unwrap())
            }
            Ok(v)
        });
        assert_eq!(Some(vec![vec![1, 2, 3], vec![1, 2, 3]]), result.ok())
    }

    #[test]
    fn object() {
        let v = decoder("a2616101028103").value().ok().unwrap();
        let d = ValueDecoder::new(&v);
        assert_eq!(Some(1), d.get(Key::Text(Text::Text(String::from("a")))).u8());
        assert_eq!(Some(3), d.get(Key::U8(2)).at(0).u8())
    }

    #[test]
    fn tagged() {
        // by default, tags are ignored
        assert_eq!(Some(1363896240), decoder("c11a514b67b0").u32().ok());
        // but can be extracted if desired
        let result = decoder("c11a514b67b0").tagged(|d, t| {
            assert_eq!(Tag::Timestamp, t);
            d.u32()
        });
        assert_eq!(Some(1363896240), result.ok())
    }

    #[test]
    fn tagged_value() {
        match decoder("c11a514b67b0").value().ok() {
            Some(Value::Tagged(Tag::Timestamp, box Value::U32(1363896240))) => (),
            other => panic!("impossible tagged value: {:?}", other)
        }
        match decoder("c1fb41d452d9ec200000").value().ok() {
            Some(Value::Tagged(Tag::Timestamp, box Value::F64(1363896240.5))) => (),
            other => panic!("impossible tagged value: {:?}", other)
        }
    }

    fn decoder(s: &str) -> Decoder<Cursor<Vec<u8>>> {
        Decoder::new(Config::default(), Cursor::new(s.from_hex().unwrap()))
    }
}
