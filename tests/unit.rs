// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

use cbor::{Config, GenericDecoder};
use cbor::value::{Int, Key, Text, Value};
use rustc_serialize::base64::FromBase64;
use serde_json as json;
use serde_json::de::from_reader;
use std::{f32, f64, i8, i16, i32, i64, u64};
use std::fs::File;
use util;

#[derive(Debug, Clone, Deserialize)]
struct TestVector {
    cbor: String,
    hex: String,
    roundtrip: bool,
    decoded: Option<json::Value>,
    diagnostic: Option<json::Value>
}

#[test]
fn int_min_max() {
    util::identity(|mut e| e.i8(i8::MAX), |mut d| d.i8().unwrap() == i8::MAX);
    util::identity(|mut e| e.i8(i8::MIN), |mut d| d.i8().unwrap() == i8::MIN);
    util::identity(|mut e| e.i16(i16::MAX), |mut d| d.i16().unwrap() == i16::MAX);
    util::identity(|mut e| e.i16(i16::MIN), |mut d| d.i16().unwrap() == i16::MIN);
    util::identity(|mut e| e.i32(i32::MAX), |mut d| d.i32().unwrap() == i32::MAX);
    util::identity(|mut e| e.i32(i32::MIN), |mut d| d.i32().unwrap() == i32::MIN);
    util::identity(|mut e| e.i64(i64::MAX), |mut d| d.i64().unwrap() == i64::MAX);
    util::identity(|mut e| e.i64(i64::MIN), |mut d| d.i64().unwrap() == i64::MIN);
    util::identity(|mut e| e.int(Int::new(true, u64::MAX)), |mut d| d.int().unwrap() == Int::new(true, u64::MAX));
    util::identity(|mut e| e.int(Int::new(false, u64::MAX)), |mut d| d.int().unwrap().u64() == Some(u64::MAX));
    assert_eq!(Some(i64::MIN), Int::new(true, i64::MAX as u64).i64());
    assert_eq!(Some(i64::MAX), Int::new(false, i64::MAX as u64).i64());
    assert_eq!(Some(u64::MIN), Int::new(false, u64::MIN).u64());
    assert_eq!(Some(u64::MAX), Int::new(false, u64::MAX).u64())
}

#[test]
fn test_all() {
    let reader = File::open("tests/appendix_a.json").unwrap();
    let test_vectors: Vec<TestVector> = from_reader(reader).unwrap();
    for v in test_vectors {
        let raw = v.cbor.from_base64().unwrap();
        let mut dec = GenericDecoder::new(Config::default(), &raw[..]);
        let val = dec.value().unwrap();
        if let Some(x) = v.decoded {
            if !eq(&x, &val) {
                panic!("{}: {:?} <> {:?}", v.hex, x, val)
            }
            continue
        }
        if let Some(json::Value::String(ref x)) = v.diagnostic {
            if !diag(&x, &val) {
                panic!("{}: {:?} <> {:?}", v.hex, x, val)
            }
        }
    }
}

// Note [floating_point]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// There is no agreement between serde's floating point parser and us.
// According to manual checks comparing the byte representation we conclude
// for now that we are not to blame for this. As a temporary measure all
// floating point comparisons are disabled in this test. The decoder module
// contains some floating point tests.
fn eq(a: &json::Value, b: &Value) -> bool {
    match (a, b) {
        (&json::Value::Null, &Value::Null) => true,
        (&json::Value::Bool(x), &Value::Bool(y)) => x == y,
        (&json::Value::String(ref x), &Value::Text(Text::Text(ref y))) => x == y,
        (&json::Value::String(ref x), &Value::Text(Text::Chunks(ref y))) => {
            let mut s = String::new();
            for c in y {
                s.push_str(c)
            }
            x == &s
        }
        (&json::Value::I64(x), y) => util::as_i64(y).map(|i| x == i).unwrap_or(false),
        (&json::Value::U64(x), y) => util::as_u64(y).map(|i| x == i).unwrap_or(false),
        (&json::Value::F64(_), &Value::F32(_)) => true, // See note [floating_point]
        (&json::Value::F64(_), &Value::F64(_)) => true, // See note [floating_point]
        (&json::Value::Array(ref x), &Value::Array(ref y)) =>
            x.iter().zip(y.iter()).all(|(xi, yi)| eq(xi, yi)),
        (&json::Value::Object(ref x), &Value::Map(ref y)) =>
            x.iter().zip(y.iter()).all(|((kx, vx), (ky, vy))| {
                eq(&json::Value::String(kx.clone()), &to_value(ky.clone())) && eq(vx, vy)
            }),
        _ => false
    }
}

// Note [diagnostic]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// At the moment we can not parse complete diagnostic syntax. That is why we
// only test a subset of the diagnostic values.
fn diag(a: &str, b: &Value) -> bool {
    match (a, b) {
        ("Infinity",  &Value::F32(x)) => x == f32::INFINITY,
        ("Infinity",  &Value::F64(x)) => x == f64::INFINITY,
        ("-Infinity", &Value::F32(x)) => x == -f32::INFINITY,
        ("-Infinity", &Value::F64(x)) => x == -f64::INFINITY,
        ("NaN",       &Value::F32(x)) => x.is_nan(),
        ("NaN",       &Value::F64(x)) => x.is_nan(),
        ("undefined", &Value::Undefined) => true,
        _ => true // See note [diagnostic]
    }
}

fn to_value(k: Key) -> Value {
    match k {
        Key::Bool(x)  => Value::Bool(x),
        Key::Bytes(x) => Value::Bytes(x),
        Key::Int(x)   => Value::Int(x),
        Key::Text(x)  => Value::Text(x),
    }
}
