// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! Instances for quickcheck's `Arbitrary` trait. Only enabled
//! with `--feature="arbitraries"`.

use quickcheck::{Arbitrary, Gen};
use rand::Rng;
use std::collections::{BTreeMap, LinkedList};
use types::Tag;
use values::{Value, Simple, Key, Bytes, Text};

impl Arbitrary for Value {
    fn arbitrary<G: Gen>(g: &mut G) -> Value {
        match g.gen_range(0, 19) {
            0  => Value::Null,
            1  => Value::Undefined,
            2  => Value::U8(g.gen()),
            3  => Value::U16(g.gen()),
            4  => Value::U32(g.gen()),
            5  => Value::U64(g.gen()),
            6  => Value::I8(g.gen()),
            7  => Value::I16(g.gen()),
            8  => Value::I32(g.gen()),
            9  => Value::I64(g.gen()),
            10 => Value::F32(g.gen()),
            11 => Value::F64(g.gen()),
            12 => Value::Text(Arbitrary::arbitrary(g)),
            13 => Value::Bytes(Arbitrary::arbitrary(g)),
            14 => Value::Array(Arbitrary::arbitrary(g)),
            15 => Value::Bool(g.gen()),
            16 => Value::Simple(Arbitrary::arbitrary(g)),
            17 => Value::Map(gen_map(g)),
            _  => gen_tagged(g)
        }
    }
}

impl Arbitrary for Key {
    fn arbitrary<G: Gen>(g: &mut G) -> Key {
        match g.gen_range(0, 11) {
            0 => Key::U8(g.gen()),
            1 => Key::U16(g.gen()),
            2 => Key::U32(g.gen()),
            3 => Key::U64(g.gen()),
            4 => Key::I8(g.gen()),
            5 => Key::I16(g.gen()),
            6 => Key::I32(g.gen()),
            7 => Key::I64(g.gen()),
            8 => Key::Text(Arbitrary::arbitrary(g)),
            9 => Key::Bytes(Arbitrary::arbitrary(g)),
            _ => Key::Bool(g.gen()),
        }
    }
}

impl Arbitrary for Tag {
    fn arbitrary<G: Gen>(g: &mut G) -> Tag {
        match g.gen_range(0, 20) {
            0  => Tag::DateTime,
            1  => Tag::Timestamp,
            2  => Tag::Bignum,
            3  => Tag::NegativeBignum,
            4  => Tag::Decimal,
            5  => Tag::Bigfloat,
            6  => Tag::ToBase64Url,
            7  => Tag::ToBase64,
            8  => Tag::ToBase16,
            9  => Tag::Cbor,
            10 => Tag::Uri,
            11 => Tag::Base64Url,
            12 => Tag::Base64,
            13 => Tag::Regex,
            14 => Tag::Mime,
            15 => Tag::CborSelf,
            tg => Tag::Unassigned(tg)
        }
    }
}

impl Arbitrary for Text {
    fn arbitrary<G: Gen>(g: &mut G) -> Text {
        match g.gen() {
            true  => Text::Text(Arbitrary::arbitrary(g)),
            false => Text::Chunks(gen_chunks(g))
        }
    }
}

impl Arbitrary for Bytes {
    fn arbitrary<G: Gen>(g: &mut G) -> Bytes {
        match g.gen() {
            true  => Bytes::Bytes(Arbitrary::arbitrary(g)),
            false => Bytes::Chunks(gen_chunks(g))
        }
    }
}

impl Arbitrary for Simple {
    fn arbitrary<G: Gen>(g: &mut G) -> Simple {
        match g.gen() {
            true => match g.gen() {
                n @ 0u8...19 | n @ 28...30 => Simple::Unassigned(n),
                n @ 32...255               => Simple::Unassigned(n),
                _                          => Simple::Unassigned(0)
            },
            false => match g.gen() {
                n @ 0u8...31 => Simple::Reserved(n),
                _            => Simple::Reserved(0)
            }
        }
    }
}

fn gen_chunks<A: Arbitrary, G: Gen>(g: &mut G) -> LinkedList<A> {
    let mut xs = LinkedList::new();
    for _ in 0 .. g.gen_range(1, 17) {
        xs.push_back(Arbitrary::arbitrary(g))
    }
    xs
}

fn gen_map<G: Gen>(g: &mut G) -> BTreeMap<Key, Value> {
    let len = g.gen_range(1, 17);
    let mut m = BTreeMap::new();
    for _ in 0 .. len {
        m.insert(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g));
    }
    m
}

fn gen_tagged<G: Gen>(g: &mut G) -> Value {
    match Arbitrary::arbitrary(g) {
        t@Tag::DateTime  => Value::Tagged(t, Box::new(Value::Text(Arbitrary::arbitrary(g)))),
        t@Tag::Timestamp => match g.gen() {
            0 => Value::Tagged(t, Box::new(Value::U8(Arbitrary::arbitrary(g)))),
            1 => Value::Tagged(t, Box::new(Value::U16(Arbitrary::arbitrary(g)))),
            2 => Value::Tagged(t, Box::new(Value::U32(Arbitrary::arbitrary(g)))),
            3 => Value::Tagged(t, Box::new(Value::U64(Arbitrary::arbitrary(g)))),
            4 => Value::Tagged(t, Box::new(Value::I8(Arbitrary::arbitrary(g)))),
            5 => Value::Tagged(t, Box::new(Value::I16(Arbitrary::arbitrary(g)))),
            6 => Value::Tagged(t, Box::new(Value::I32(Arbitrary::arbitrary(g)))),
            7 => Value::Tagged(t, Box::new(Value::I64(Arbitrary::arbitrary(g)))),
            8 => Value::Tagged(t, Box::new(Value::F32(Arbitrary::arbitrary(g)))),
            _ => Value::Tagged(t, Box::new(Value::F64(Arbitrary::arbitrary(g))))
        },
        t@Tag::Bignum         => Value::Tagged(t, Box::new(Value::Bytes(Arbitrary::arbitrary(g)))),
        t@Tag::NegativeBignum => Value::Tagged(t, Box::new(Value::Bytes(Arbitrary::arbitrary(g)))),
        t@Tag::Uri            => Value::Tagged(t, Box::new(Value::Text(Arbitrary::arbitrary(g)))),
        t@Tag::Base64         => Value::Tagged(t, Box::new(Value::Text(Arbitrary::arbitrary(g)))),
        t@Tag::ToBase64Url    => Value::Tagged(t, Box::new(Value::Text(Arbitrary::arbitrary(g)))),
        t@Tag::Regex          => Value::Tagged(t, Box::new(Value::Text(Arbitrary::arbitrary(g)))),
        t@Tag::Decimal        => Value::Tagged(t, Box::new(Value::Array(vec![Value::U64(g.gen()), Value::U64(g.gen())]))),
        t@Tag::Bigfloat       => Value::Tagged(t, Box::new(Value::Array(vec![Value::U64(g.gen()), Value::U64(g.gen())]))),
        _                     => Value::Tagged(Tag::Mime, Box::new(Value::Text(Arbitrary::arbitrary(g))))
    }
}
