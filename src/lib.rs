// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! CBOR (RFC 7049) encoder and decoder implementations.

#![feature(box_patterns, float_extras, num_bits_bytes)]

extern crate byteorder;

#[cfg(test)]
extern crate rustc_serialize;

#[cfg(feature="random")]
extern crate quickcheck;

#[cfg(feature="random")]
extern crate rand;

pub mod types;
pub mod values;
pub mod decoder;
pub mod encoder;

#[cfg(feature="random")]
pub mod random;

pub use decoder::{Decoder, DecodeError, DecodeResult, Config};
pub use decoder::{opt, maybe, or_break};
pub use encoder::{Encoder, EncodeError, EncodeResult};
