// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

use cbor::values::{Key, Value};
use quickcheck::{QuickCheck, StdGen};
use rand;
use util::identity;

#[test]
fn prop_identity_value() {
    fn prop(x: Value) -> bool {
        identity(|mut e| e.value(&x), |mut d| {
            let y = d.value().unwrap();
            if eq(&x, &y) {
                true
            } else {
                println!("input  = {:?}\n\noutput = {:?}", x, y);
                false
            }
        })
    }
    QuickCheck::new()
        .tests(200)
        .gen(StdGen::new(rand::thread_rng(), 8))
        .quickcheck(prop as fn(Value) -> bool)
}

fn as_u64(x: &Value) -> Option<u64> {
    match x {
        &Value::U8(n)  => Some(n as u64),
        &Value::U16(n) => Some(n as u64),
        &Value::U32(n) => Some(n as u64),
        &Value::U64(n) => Some(n),
        _              => None
    }
}

fn key_as_u64(x: &Key) -> Option<u64> {
    match x {
        &Key::U8(n)  => Some(n as u64),
        &Key::U16(n) => Some(n as u64),
        &Key::U32(n) => Some(n as u64),
        &Key::U64(n) => Some(n),
        _            => None
    }
}


fn as_i64(x: &Value) -> Option<i64> {
    match x {
        &Value::I8(n)  => Some(n as i64),
        &Value::I16(n) => Some(n as i64),
        &Value::I32(n) => Some(n as i64),
        &Value::I64(n) => Some(n),
        _              => None
    }
}

fn key_as_i64(x: &Key) -> Option<i64> {
    match x {
        &Key::I8(n)  => Some(n as i64),
        &Key::I16(n) => Some(n as i64),
        &Key::I32(n) => Some(n as i64),
        &Key::I64(n) => Some(n),
        _            => None
    }
}


fn eq_pair(a: (&Key, &Value), b: (&Key, &Value)) -> bool {
    match (a.0, b.0) {
        (&Key::Bool(x), &Key::Bool(y))           => x == y && eq(a.1, b.1),
        (&Key::Bytes(ref x), &Key::Bytes(ref y)) => x == y && eq(a.1, b.1),
        (&Key::Text(ref x), &Key::Text(ref y))   => x == y && eq(a.1, b.1),
        _ => (key_as_u64(a.0) == key_as_u64(b.0) || key_as_i64(a.0) == key_as_i64(b.0)) && eq(a.1, b.1)
    }
}
fn eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (&Value::Array(ref x), &Value::Array(ref y)) => x.iter().zip(y.iter()).all(|(vx, vy)| eq(vx, vy)),
        (&Value::Bool(x), &Value::Bool(y))           => x == y,
        (&Value::Bytes(ref x), &Value::Bytes(ref y)) => x == y,
        (&Value::Text(ref x), &Value::Text(ref y))   => x == y,
        (&Value::Simple(x), &Value::Simple(y))       => x == y,
        (&Value::Null, &Value::Null)                 => true,
        (&Value::Undefined, &Value::Undefined)       => true,
        (&Value::F32(x), &Value::F32(y))             => x.is_nan() && y.is_nan() || x == y,
        (&Value::F64(x), &Value::F64(y))             => x.is_nan() && y.is_nan() || x == y,
        (&Value::Map(ref x), &Value::Map(ref y))     => x.iter().zip(y.iter()).all(|(ex, ey)| eq_pair(ex, ey)),
        (&Value::Tagged(ta, box ref x), &Value::Tagged(tb, box ref y)) => ta == tb && eq(x, y),
        _                                            => as_u64(a) == as_u64(b) || as_i64(a) == as_i64(b)
    }
}
