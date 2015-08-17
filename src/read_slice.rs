// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.

//! `ReadSlice` trait to allow efficient reading of slices without copying
use std::io::{Cursor, Seek, SeekFrom, Result};
use std::ops::{Index, Range};

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

impl<T> ReadSlice for Cursor<T>
    where Cursor<T>: Seek, T: Index<Range<usize>, Output=[u8]>
{
    fn read_slice<'x>(&'x mut self, n: u64) -> Result<&'x [u8]> {
        let start = try!(self.seek(SeekFrom::Current(0))) as usize;
        let end = try!(self.seek(SeekFrom::Current(n as i64))) as usize;
        Ok(&self.get_ref()[start..end])
    }
}
