// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

use util::identity;

#[cfg(feature="random")]
mod value;

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
    identity(|mut e| e.i8(x), |mut d| d.i8().unwrap() == x)
}

#[quickcheck]
fn identity_i16(x: i16) -> bool {
    identity(|mut e| e.i16(x), |mut d| d.i16().unwrap() == x)
}

#[quickcheck]
fn identity_i32(x: i32) -> bool {
    identity(|mut e| e.i32(x), |mut d| d.i32().unwrap() == x)
}

#[quickcheck]
fn identity_i64(x: i64) -> bool {
    identity(|mut e| e.i64(x), |mut d| d.i64().unwrap() == x)
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
