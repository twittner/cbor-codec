// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! CBOR types and tags definitions.

use byteorder::{Error, ReadBytesExt};

/// The CBOR types.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Type {
    Array,
    Bool,
    Break,
    Bytes,
    Float16,
    Float32,
    Float64,
    Int16,
    Int32,
    Int64,
    Int8,
    Null,
    Object,
    Tagged,
    Text,
    UInt16,
    UInt32,
    UInt64,
    UInt8,
    Undefined,
    Unknown { major: u8, info: u8 },
    Reserved { major: u8, info: u8 },
    Unassigned { major: u8, info: u8 }
}

impl Type {
    pub fn read<R: ReadBytesExt>(r: &mut R) -> Result<(Type, u8), Error> {
        let b = try!(r.read_u8());
        match ((b & 0b111_00000) >> 5, b & 0b000_11111) {
            (0, a @ 0...24)  => Ok((Type::UInt8, a)),
            (0, 25)          => Ok((Type::UInt16, 25)),
            (0, 26)          => Ok((Type::UInt32, 26)),
            (0, 27)          => Ok((Type::UInt64, 27)),
            (1, a @ 0...24)  => Ok((Type::Int8, a)),
            (1, 25)          => Ok((Type::Int16, 25)),
            (1, 26)          => Ok((Type::Int32, 26)),
            (1, 27)          => Ok((Type::Int64, 27)),
            (2, a)           => Ok((Type::Bytes, a)),
            (3, a)           => Ok((Type::Text, a)),
            (4, a)           => Ok((Type::Array, a)),
            (5, a)           => Ok((Type::Object, a)),
            (6, a)           => Ok((Type::Tagged, a)),
            (7, a @ 0...23)  => Ok(Type::simple(a)),
            (7, 24)          => Ok(Type::simple(try!(r.read_u8()))),
            (7, 25)          => Ok((Type::Float16, 25)),
            (7, 26)          => Ok((Type::Float32, 26)),
            (7, 27)          => Ok((Type::Float64, 27)),
            (7, a @ 28...30) => Ok((Type::Unassigned { major: 7, info: a }, a)),
            (7, 31)          => Ok((Type::Break, 31)),
            (m, a)           => Ok((Type::Unknown { major: m, info: a }, a))
        }
    }

    fn simple(b: u8) -> (Type, u8) {
        match b {
            a @ 0...19  => (Type::Unassigned { major: 7, info: a }, a),
            20          => (Type::Bool, 20),
            21          => (Type::Bool, 21),
            22          => (Type::Null, 22),
            23          => (Type::Undefined, 23),
            a @ 24...31 => (Type::Reserved { major: 7, info: a }, a),
            a           => (Type::Unassigned { major: 7, info: a }, a)
        }
    }
}

/// CBOR tags (corresponding to `Type::Tagged`).
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Tag {
    DateTime,
    Timestamp,
    Bignum,
    NegativeBignum,
    Decimal,
    Bigfloat,
    Unassigned(u64),
    ToBase64Url,
    ToBase64,
    ToBase16,
    Cbor,
    Uri,
    Base64Url,
    Base64,
    Regex,
    Mime,
    CborSelf
}

impl Tag {
    pub fn of(x: u64) -> Tag {
        match x {
            0     => Tag::DateTime,
            1     => Tag::Timestamp,
            2     => Tag::Bignum,
            3     => Tag::NegativeBignum,
            4     => Tag::Decimal,
            5     => Tag::Bigfloat,
            21    => Tag::ToBase64Url,
            22    => Tag::ToBase64,
            23    => Tag::ToBase16,
            24    => Tag::Cbor,
            32    => Tag::Uri,
            33    => Tag::Base64Url,
            34    => Tag::Base64,
            35    => Tag::Regex,
            36    => Tag::Mime,
            55799 => Tag::CborSelf,
            _     => Tag::Unassigned(x)
        }
    }
}
