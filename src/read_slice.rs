// This Source Code Form is subject to the terms of
// the Mozilla Public License, v. 2.0. If a copy of
// the MPL was not distributed with this file, You
// can obtain one at http://mozilla.org/MPL/2.0/.


//! `ReadSlice` trait to allow efficient reading of slices without copying
use std::io::{self, Cursor};
use DecodeError;

pub enum Error {
    Io(io::Error),
    UnexpectedEOF,
}

/// Type which supports reading a slice from internal buffer
///
/// The underlying thing is only required to keep a single slice in memory, but
/// of arbitrary length. So it theoretically be implemented for thing like
/// BufReader with growable internal buffer.
///
pub trait ReadSlice {
    /// Borrow slice from underlying buffer and advance cursor position
    fn read_slice<'x>(&'x mut self, n: usize) -> Result<&'x [u8], Error>;
}

impl From<Error> for DecodeError {
    fn from(e: Error) -> DecodeError {
        match e {
            Error::Io(e) => DecodeError::IoError(e),
            Error::UnexpectedEOF => DecodeError::UnexpectedEOF,
        }
    }
}

impl ReadSlice for Cursor<Vec<u8>> {
    fn read_slice<'x>(&'x mut self, n: usize) -> Result<&'x [u8], Error> {
        let start = self.position() as usize;
        let end = start + n;
        if self.get_ref().len() < end {
            return Err(Error::UnexpectedEOF);
        }
        self.set_position(end as u64);
        Ok(&self.get_ref()[start..end])
    }
}

impl<'a> ReadSlice for Cursor<&'a [u8]> {
    fn read_slice<'x>(&'x mut self, n: usize) -> Result<&'x [u8], Error> {
        let start = self.position() as usize;
        let end = start + n;
        if self.get_ref().len() < end {
            return Err(Error::UnexpectedEOF);
        }
        self.set_position(end as u64);
        Ok(&self.get_ref()[start..end])
    }
}
