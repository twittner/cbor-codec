// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

use cbor::encoder::{Encoder, EncodeResult};
use cbor::decoder::{Config, Decoder};
use std::io::Cursor;

pub fn identity<F, G>(len: usize, enc: F, dec: G) -> bool
where F: Fn(Encoder<Cursor<&mut [u8]>>) -> EncodeResult,
      G: Fn(Decoder<Cursor<&[u8]>>) -> bool
{
    let mut buffer = vec![0u8; len];
    match enc(Encoder::new(Cursor::new(&mut buffer[..]))) {
        Ok(_)  => (),
        Err(e) => panic!("encoder failure: {:?}", e)
    }
    dec(Decoder::new(Config::default(), Cursor::new(&buffer)))
}
