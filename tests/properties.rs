// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

use cbor::{Config, Decoder, Encoder, EncodeResult};
use std::{i8, i16, i32, i64};
use std::io::Cursor;

#[quickcheck]
fn identity_u8(x: u8) -> bool {
    identity(|mut e| e.u8(x), |mut d| d.u8().unwrap() == x)
}

#[quickcheck]
fn identity_u16(x: u16) -> bool {
    identity(|mut e| e.u16(x), |mut d| d.u16().unwrap() == x)
}

#[quickcheck]
fn identity_u32(x: u32) -> bool {
    identity(|mut e| e.u32(x), |mut d| d.u32().unwrap() == x)
}

#[quickcheck]
fn identity_u64(x: u64) -> bool {
    identity(|mut e| e.u64(x), |mut d| d.u64().unwrap() == x)
}

#[quickcheck]
fn identity_i8(x: i8) -> bool {
    identity(|mut e| e.i8(x), |mut d| d.i8().unwrap() == x);
    identity(|mut e| e.i16(x as i16), |mut d| d.i8().unwrap() == x);
    identity(|mut e| e.i32(x as i32), |mut d| d.i8().unwrap() == x);
    identity(|mut e| e.i64(x as i64), |mut d| d.i8().unwrap() == x)
}

#[quickcheck]
fn identity_i16(x: i16) -> bool {
    identity(|mut e| e.i16(x), |mut d| d.i16().unwrap() == x);
    identity(|mut e| e.i32(x as i32), |mut d| d.i16().unwrap() == x);
    identity(|mut e| e.i64(x as i64), |mut d| d.i16().unwrap() == x)
}

#[quickcheck]
fn identity_i32(x: i32) -> bool {
    identity(|mut e| e.i32(x), |mut d| d.i32().unwrap() == x);
    identity(|mut e| e.i64(x as i64), |mut d| d.i32().unwrap() == x)
}

#[quickcheck]
fn identity_i64(x: i64) -> bool {
    identity(|mut e| e.i64(x), |mut d| d.i64().unwrap() == x)
}

#[quickcheck]
fn identity_u8_i8(x: u8) -> bool {
    let y = x % i8::MAX as u8;
    identity(|mut e| e.u8(y), |mut d| d.i8().unwrap() as u8 == y)
}

#[quickcheck]
fn identity_u16_i16(x: u16) -> bool {
    let y = x % i16::MAX as u16;
    identity(|mut e| e.u16(y), |mut d| d.i16().unwrap() as u16 == y)
}

#[quickcheck]
fn identity_u32_i32(x: u32) -> bool {
    let y = x % i32::MAX as u32;
    identity(|mut e| e.u32(y), |mut d| d.i32().unwrap() as u32 == y)
}

#[quickcheck]
fn identity_u64_i64(x: u64) -> bool {
    let y = x % i64::MAX as u64;
    identity(|mut e| e.u64(y), |mut d| d.i64().unwrap() as u64 == y)
}

#[quickcheck]
fn identity_f32(x: f32) -> bool {
    identity(|mut e| e.f32(x), |mut d| d.f32().unwrap() == x)
}

#[quickcheck]
fn identity_f64(x: f64) -> bool {
    identity(|mut e| e.f64(x), |mut d| d.f64().unwrap() == x)
}

#[quickcheck]
fn identity_bytes(x: Vec<u8>) -> bool {
    identity(|mut e| e.bytes(&x[..]), |mut d| d.bytes().unwrap() == x)
}

#[quickcheck]
fn identity_bytes_stream(v: Vec<Vec<u8>>) -> bool {
    identity(|mut e| e.bytes_iter(v.iter().map(|x| &x[..])),
             |mut d| d.bytes_iter().unwrap().zip(v.iter()).all(|(x, y)| &x.unwrap() == y))
}

#[quickcheck]
fn identity_text(x: String) -> bool {
    identity(|mut e| e.text(&x[..]), |mut d| d.text().unwrap() == x)
}

#[quickcheck]
fn identity_text_stream(v: Vec<String>) -> bool {
    identity(|mut e| e.text_iter(v.iter().map(|x| &x[..])),
             |mut d| d.text_iter().unwrap().zip(v.iter()).all(|(x, y)| &x.unwrap() == y))
}

pub fn identity<F, G>(enc: F, dec: G) -> bool
where F: Fn(Encoder<&mut Cursor<Vec<u8>>>) -> EncodeResult,
      G: Fn(Decoder<&mut Cursor<Vec<u8>>>) -> bool
{
    let mut buffer = Cursor::new(Vec::new());
    match enc(Encoder::new(&mut buffer)) {
        Ok(_)  => (),
        Err(e) => panic!("encoder failure: {:?}", e)
    }
    buffer.set_position(0);
    dec(Decoder::new(Config::default(), &mut buffer))
}
