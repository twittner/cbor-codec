// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(test)]

extern crate cbor;
extern crate quickcheck;
extern crate rand;
extern crate test;

use cbor::random::gen_value;
use cbor::{Config, Decoder, Encoder};
use quickcheck::StdGen;
use rand::thread_rng;
use std::io::Cursor;
use std::vec::Vec;
use test::Bencher;

fn mk_value(min: usize) -> Vec<u8> {
    let mut g = StdGen::new(thread_rng(), 255);
    let mut e = Encoder::new(Cursor::new(Vec::new()));
    e.array(min, |e| {
        for _ in 0 .. min {
            try!(e.value(&gen_value(3, &mut g)))
        }
        Ok(())
    }).unwrap();
    e.into_writer().into_inner()
}

#[bench]
fn random_value_roundtrip(b: &mut Bencher) {
    let mut w = Cursor::new(mk_value(30));
    b.iter(|| {
        assert!(Decoder::new(Config::default(), &mut w).value().ok().is_some());
        w.set_position(0);
    });
    let m = w.get_ref().len() as f64 / 1048576.0;
    let s = b.ns_per_iter() as f64 * 0.000000001;
    println!("{:.3} MB/s", m/s)
}
