use failure::Error;
use crc::{crc32, Hasher32};

pub const BLOCK_SIZE: usize = 32768;
pub const CHECKSUM_SIZE: usize = 4;
pub const LENGTH_SIZE: usize = 2;
pub const RECORD_TYPE_SIZE: usize = 1;
pub const HEADER_SIZE: usize = CHECKSUM_SIZE + LENGTH_SIZE + RECORD_TYPE_SIZE;
pub const MAX_FRAGMENT_SIZE: usize = BLOCK_SIZE - HEADER_SIZE;

#[derive(PartialEq, Debug)]
pub enum RecordType {
    Full,
    FragmentStart,
    FragmentMiddle,
    FragmentEnd,
}

impl RecordType {
    pub fn from_byte(byte: u8) -> Result<RecordType, Error> {
        match byte {
            1 => Ok(RecordType::Full),
            2 => Ok(RecordType::FragmentStart),
            3 => Ok(RecordType::FragmentMiddle),
            4 => Ok(RecordType::FragmentEnd),
            _ => Err(format_err!("Unknown record type: {}", byte))
        }
    }

    pub fn as_byte(&self) -> u8 {
        match *self {
            RecordType::Full => 1,
            RecordType::FragmentStart => 2,
            RecordType::FragmentMiddle => 3,
            RecordType::FragmentEnd => 4
        }
    }
}