// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! `ReadSlice` trait to allow efficient reading of slices without copying
use std::io::{Cursor, Result, Error, ErrorKind};

/// Type which supports reading a slice from internal buffer
///
/// The underlying thing is only required to keep a single slice in memory, but
/// of arbitrary length. So it theoretically be implemented for thing like
/// BufReader with growable internal buffer.
///
pub trait ReadSlice {
    /// Borrow slice from underlying buffer and advance cursor position
    fn read_slice<'x>(&'x mut self, n: u64) -> Result<&'x [u8]>;
}

impl ReadSlice for Cursor<Vec<u8>> {
    fn read_slice<'x>(&'x mut self, n: u64) -> Result<&'x [u8]> {
        let start = self.position();
        let end = start + n;
        if self.get_ref().len() < end as usize {
            return Err(Error::new(ErrorKind::InvalidInput, "eof reached"));
        }
        self.set_position(end);
        Ok(&self.get_ref()[start as usize..end as usize])
    }
}

impl<'a> ReadSlice for Cursor<&'a [u8]> {
    fn read_slice<'x>(&'x mut self, n: u64) -> Result<&'x [u8]> {
        let start = self.position();
        let end = start + n;
        if self.get_ref().len() < end as usize {
            return Err(Error::new(ErrorKind::InvalidInput, "eof reached"));
        }
        self.set_position(end);
        Ok(&self.get_ref()[start as usize..end as usize])
    }
}
