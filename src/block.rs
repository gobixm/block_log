use super::utils::*;
use failure::Error;
use std::mem::transmute;
use std::io::Write;
use crc::{crc32, Hasher32};

pub struct BlockReader<'a> {
    data: &'a [u8],
    position: usize,
}

pub struct BlockReaderRecord<'a> {
    record_type: RecordType,
    data: &'a [u8],
}

pub struct BlockWriter<T: Write> {
    position: usize,
    write: T,
}

impl<'a> BlockReaderRecord<'a> {
    fn new(data: &[u8]) -> Result<BlockReaderRecord, Error> {
        let c = [data[0], data[1], data[2], data[3]];
        let checksum = unsafe { transmute::<[u8; 4], u32>(c) };

        let l = [data[4], data[5]];
        let data_length = unsafe { transmute::<[u8; 2], u16>(l) } as usize;
        if data_length > data.len() - HEADER_SIZE {
            return Err(format_err!("Log corrupted: length"));
        }

        let sum = crc32::checksum_ieee(&data[4..4 + data_length + LENGTH_SIZE + RECORD_TYPE_SIZE]);
        if sum != checksum {
            return Err(format_err!("Log corrupted"));
        }


        let record_type = RecordType::from_byte(data[6])?;
        let d = &data[7..7 + data_length];

        Ok(BlockReaderRecord {
            record_type,
            data: d,
        })
    }
}

impl<'a> BlockReader<'a> {
    pub fn new(block: &[u8]) -> BlockReader {
        BlockReader {
            data: block,
            position: 0,
        }
    }
}

impl<'b> Iterator for BlockReader<'b> {
    type Item = BlockReaderRecord<'b>;

    fn next(&mut self) -> Option<BlockReaderRecord<'b>> {
        match self.position {
            p if self.data.len() - p > HEADER_SIZE => {
                match BlockReaderRecord::new(&self.data[p..]) {
                    Ok(record) => {
                        self.position += record.data.len() + HEADER_SIZE;
                        Some(record)
                    }
                    Err(E) => None
                }
            }
            _ => None
        }
    }
}

impl<T: Write> BlockWriter<T> {
    pub fn new(writer: T) -> BlockWriter<T> {
        BlockWriter {
            write: writer,
            position: 0,
        }
    }

    fn get_left(&self) -> usize {
        BLOCK_SIZE - self.position
    }

    fn get_required(&self, data: &[u8]) -> usize {
        data.len() + HEADER_SIZE
    }

    fn new_block(&mut self) {
        self.position = 0;
    }

    pub fn write(&mut self, data: &[u8]) -> Result<(), Error> {
        let written = 0usize;
        let mut read = data;
        let mut in_fragment = false;
        loop {
            let left = self.get_left();
            let required = self.get_required(read);

            if left < HEADER_SIZE {
                self.write.write_all(&vec![0u8; left])?;
                self.new_block();
                continue;
            }

            let record_type = match left {
                l if l < required => {
                    match in_fragment {
                        true => RecordType::FragmentMiddle,
                        false => RecordType::FragmentStart
                    }
                }
                _ => {
                    match in_fragment {
                        true => RecordType::FragmentEnd,
                        false => RecordType::Full
                    }
                }
            };

            let mut header = [0u8; HEADER_SIZE];
            let mut digest = crc32::Digest::new(crc32::IEEE);

            let fragment = match record_type {
                RecordType::FragmentMiddle | RecordType::FragmentStart => &read[..left - HEADER_SIZE],
                _ => read
            };

            header[CHECKSUM_SIZE] = ((fragment.len() << 8) >> 8) as u8;
            header[CHECKSUM_SIZE + 1] = (fragment.len() >> 8) as u8;
            header[CHECKSUM_SIZE + LENGTH_SIZE] = record_type.as_byte();

            digest.write(&header[CHECKSUM_SIZE..]);
            digest.write(&fragment);
            let checksum = unsafe { transmute::<u32, [u8; 4]>(digest.sum32()) };
            for (i, elem) in checksum.iter().enumerate() {
                header[i] = *elem
            }

            self.write.write_all(&header)?;
            self.write.write_all(fragment)?;
            self.write.flush();
            self.position += fragment.len() + HEADER_SIZE;
            read = &read[fragment.len()..];

            if self.position == BLOCK_SIZE {
                self.new_block();
            }
            println!("{}", self.position);

            if read.len() == 0 {
                break;
            }

            in_fragment = true;
        }
        Ok(())
    }
}

#[cfg(test)]
mod block__test {
    use super::*;
    use std::io::Cursor;
    use std::io::SeekFrom;
    use std::io::prelude::*;
    use byteorder::{ReadBytesExt, WriteBytesExt, LittleEndian};
    use test::Bencher;
    use test::black_box;

    fn write_record(cursor: &mut Cursor<Vec<u8>>, record_type: RecordType, data: &[u8], length: usize) {
        let pos = cursor.position();
        cursor.write_u32::<LittleEndian>(0);
        cursor.write_u16::<LittleEndian>(length as u16);
        cursor.write_u8(record_type.as_byte());
        cursor.write(&data);

        let shift = pos as usize + 4;
        let sum = crc32::checksum_ieee(&cursor.get_ref()[shift..shift + data.len() + RECORD_TYPE_SIZE + LENGTH_SIZE]);
        cursor.set_position(pos);
        cursor.write_u32::<LittleEndian>(sum);
        cursor.set_position(pos + HEADER_SIZE as u64 + data.len() as u64)
    }

    #[test]
    fn new_record__constructed() {
        let vec = vec![0u8; 0];
        let data = vec![5u8, 13, 17];
        let mut buff = Cursor::new(vec);
        write_record(&mut buff, RecordType::Full, &data, data.len());

        let result = BlockReaderRecord::new(buff.get_ref());
        assert!(result.is_ok());

        let record = result.unwrap();
        assert_eq!(record.data[0..3], data[0..3]);
        assert_eq!(record.record_type, RecordType::Full);
    }

    #[test]
    fn iter__multiple_read() {
        let vec = vec![0u8; 0];
        let data1 = vec![5u8, 13, 17];
        let data2 = vec![23u8, 31, 37];
        let mut buff = Cursor::new(vec);
        write_record(&mut buff, RecordType::FragmentStart, &data1, data1.len());
        write_record(&mut buff, RecordType::FragmentEnd, &data2, data2.len());

        let block = BlockReader::new(&buff.get_ref());
        let mut iter = block.into_iter();
        let record1 = iter.next();
        let record2 = iter.next();
        let record3 = iter.next();

        assert!(record1.is_some());
        assert_eq!(RecordType::FragmentStart, record1.unwrap().record_type);

        assert!(record2.is_some());
        assert_eq!(RecordType::FragmentEnd, record2.unwrap().record_type);

        assert!(record3.is_none());
    }

    #[test]
    fn iter__corrupted_length__failed() {
        let vec = vec![0u8; 0];
        let data1 = vec![5u8, 13, 17];
        let data2 = vec![23u8, 31, 37];
        let mut buff = Cursor::new(vec);
        write_record(&mut buff, RecordType::FragmentStart, &data1, data1.len());
        write_record(&mut buff, RecordType::FragmentEnd, &data2, data2.len() + 1);


        let block = BlockReader::new(&buff.get_ref());
        let mut iter = block.into_iter();
        let record1 = iter.next();
        let record2 = iter.next();

        assert!(record1.is_some());
        assert!(record2.is_none());
    }

    #[test]
    fn iter__corrupted_content__failed() {
        let vec = vec![0u8; 0];
        let data1 = vec![5u8, 13, 17];
        let data2 = vec![23u8, 31, 37];
        let mut buff = Cursor::new(vec);
        write_record(&mut buff, RecordType::FragmentStart, &data1, data1.len());
        write_record(&mut buff, RecordType::FragmentEnd, &data2, data2.len());
        buff.seek(SeekFrom::Current(-1));
        buff.write_u8(0);

        let block = BlockReader::new(&buff.get_ref());
        let mut iter = block.into_iter();
        let record1 = iter.next();
        let record2 = iter.next();

        assert!(record1.is_some());
        assert!(record2.is_none());
    }

    #[test]
    fn write__full__written() {
        let vec = vec![0u8; 0];
        let mut buff = Cursor::new(vec);
        let data1 = vec![5u8, 13, 17];
        let data2 = vec![7u8, 11, 37, 43];

        let mut writer = BlockWriter::new(buff);
        let result = writer.write(&data1);
        assert!(result.is_ok());
        assert_eq!(HEADER_SIZE + data1.len(), writer.position);
        let result = writer.write(&data2);
        assert!(result.is_ok());
        assert_eq!(HEADER_SIZE + data2.len() + HEADER_SIZE + data1.len(), writer.position);

        writer.write.set_position(0);
        let mut reader = BlockReader::new(writer.write.get_ref());
        let record1 = reader.next();
        let record2 = reader.next();

        assert_eq!(data1, record1.unwrap().data);
        assert_eq!(data2, record2.unwrap().data);
    }

    #[test]
    fn write__fragment_start_end__written() {
        let vec = vec![0u8; 0];
        let mut buff = Cursor::new(vec);
        let data = vec![0u8; MAX_FRAGMENT_SIZE + 1];

        let mut writer = BlockWriter::new(buff);
        let result = writer.write(&data);
        assert!(result.is_ok());
        assert_eq!(1 + HEADER_SIZE, writer.position);

        writer.write.set_position(0);
        let mut reader = BlockReader::new(&writer.write.get_ref()[..BLOCK_SIZE]);
        let record1 = reader.next().unwrap();

        assert_eq!(&data[..MAX_FRAGMENT_SIZE], record1.data);
        assert_eq!(RecordType::FragmentStart, record1.record_type);

        let mut reader = BlockReader::new(&writer.write.get_ref()[BLOCK_SIZE..]);
        let record2 = reader.next().unwrap();

        assert_eq!(&data[MAX_FRAGMENT_SIZE..], record2.data);
        assert_eq!(RecordType::FragmentEnd, record2.record_type);
    }

    #[test]
    fn write__empty_tail__written() {
        let vec = vec![0u8; 0];
        let mut buff = Cursor::new(vec);
        let data1 = vec![0u8; MAX_FRAGMENT_SIZE - HEADER_SIZE + 1];
        let data2 = vec![0u8];

        let mut writer = BlockWriter::new(buff);
        let result = writer.write(&data1);
        assert!(result.is_ok());

        let result = writer.write(&data2);
        assert!(result.is_ok());
        assert_eq!(HEADER_SIZE + data2.len(), writer.position);

        writer.write.set_position(0);
        let mut reader = BlockReader::new(&writer.write.get_ref()[..BLOCK_SIZE]);
        let record1 = reader.next().unwrap();

        assert_eq!(data1, record1.data);

        let mut reader = BlockReader::new(&writer.write.get_ref()[BLOCK_SIZE..]);
        let record2 = reader.next().unwrap();

        assert_eq!(data2, record2.data);
    }

    #[test]
    fn write__fragment_start_middle_end__written() {
        let vec = vec![0u8; 0];
        let mut buff = Cursor::new(vec);
        let data = vec![0u8; MAX_FRAGMENT_SIZE * 2 + 1];

        let mut writer = BlockWriter::new(buff);
        let result = writer.write(&data);
        assert!(result.is_ok());
        assert_eq!(1 + HEADER_SIZE, writer.position);

        writer.write.set_position(0);
        let mut reader = BlockReader::new(&writer.write.get_ref()[..BLOCK_SIZE]);
        let record1 = reader.next().unwrap();

        assert_eq!(&data[..MAX_FRAGMENT_SIZE], record1.data);
        assert_eq!(RecordType::FragmentStart, record1.record_type);

        let mut reader = BlockReader::new(&writer.write.get_ref()[BLOCK_SIZE..BLOCK_SIZE * 2]);
        let record1 = reader.next().unwrap();

        assert_eq!(&data[MAX_FRAGMENT_SIZE..MAX_FRAGMENT_SIZE * 2], record1.data);
        assert_eq!(RecordType::FragmentMiddle, record1.record_type);

        let mut reader = BlockReader::new(&writer.write.get_ref()[BLOCK_SIZE * 2..]);
        let record1 = reader.next().unwrap();

        assert_eq!(&data[MAX_FRAGMENT_SIZE * 2..], record1.data);
        assert_eq!(RecordType::FragmentEnd, record1.record_type);
    }

    #[bench]
    fn bench__block_writer__write_mem__1b_x_1000(b: &mut Bencher) {
        let vec = vec![0u8; 0];
        let data = vec![0u8];
        let mut buff = Cursor::new(vec);

        let mut writer = BlockWriter::new(buff);
        b.iter(|| {
            for i in 0..1000 {
                black_box(writer.write(&data));
            }
        });
    }

    #[bench]
    fn bench__block_writer__write_mem__1kb_x_1000(b: &mut Bencher) {
        let vec = vec![0u8; 0];
        let data = vec![0u8; 1000];
        let mut buff = Cursor::new(vec);

        let mut writer = BlockWriter::new(buff);
        b.iter(|| {
            for i in 0..1000 {
                black_box(writer.write(&data));
            }
        });
    }
}
