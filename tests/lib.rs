// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_patterns, custom_derive, plugin)]
#![plugin(quickcheck_macros, serde_macros)]

extern crate cbor;
extern crate quickcheck;
extern crate rand;
extern crate rustc_serialize;
extern crate serde;
extern crate serde_json;

mod properties;
mod unit;
mod util;
