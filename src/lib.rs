// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_patterns, float_extras, num_bits_bytes)]

extern crate byteorder;

pub mod types;
pub mod values;
pub mod decoder;
pub mod encoder;

pub use decoder::{Decoder, DecodeError, DecodeResult, Config};
pub use encoder::{Encoder, EncodeError, EncodeResult};

#[cfg(test)]
extern crate rustc_serialize;

#[cfg(feature="arbitraries")]
extern crate quickcheck;

#[cfg(feature="arbitraries")]
extern crate rand;

#[cfg(feature="arbitraries")]
pub mod arbitraries;
