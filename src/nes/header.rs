use crate::nes::flags::{Flags6, Flags7};
use crate::reader::{Reader, ReaderError, LE};
use std::array::TryFromSliceError;

const NES_MAGIC: &[u8] = b"NES\x1a";

// Represents a Kilobyte unit in bytes size
const KB: usize = 1024;

/// Represents ther header structure for the iNES file format
#[derive(Debug)]
pub struct Header {
    // Size of PRG ROM, which is the ROM connected to the CPU. The size itself
    // is stored as a count of 16KiB units. But here we will store it directly
    // in bytes after reading it such that it is easier to manipulate
    prg_rom_size: usize,
    // Size of CHR ROM, which is the ROM connected to the PPU. The size is
    // stored in the file format as a count of 8KiB units. Here we will store
    // it as count of bytes after parsing it from the file such that it is
    // easier to manipulate. Value `0` means the board uses CHR RAM
    chr_rom_size: usize,
    // Flags 6 parsing
    flags6: Flags6,
    // Flags 7 - not really used
    flags7: Flags7,
    // Size of PRG RAM in 8 KB units. The size is represented here in bytes.
    // A value 0 in the file infers 8KB for compatibility.
    prg_ram_size: usize,
    // Flags 9 - not really used
    flags9: u8,
    // Flags 10 - not really used
    flags10: u8,
}

impl Header {
    pub fn parse(reader: &mut Reader) -> Result<Self, HeaderError> {
        let magic_read = reader.read_bytes(NES_MAGIC.len())?;

        if magic_read != NES_MAGIC {
            return Err(HeaderError::UnknownMagic(magic_read.try_into()?));
        }

        // Read the number of 16KiB PRG ROM blocks
        let prg_rom_block_count = reader.read::<u8, LE>()? as usize;
        let prg_rom_size = prg_rom_block_count * 16 * KB;

        // Read the number of 8KiB CHR ROM blocks
        let chr_rom_block_count = reader.read::<u8, LE>()? as usize;
        let chr_rom_size = chr_rom_block_count * 8 * KB;

        // Read the flags6
        let flags6 = Flags6::from(reader.read::<u8, LE>()?);
        // Read the flags7
        let flags7 = Flags7::from(reader.read::<u8, LE>()?);
        // Read the flags8
        let flags8 = reader.read::<u8, LE>()?;
        // Read the possible RAM size.
        let prg_ram_size = match flags8 {
            0 => 8 * KB,
            _ => flags8 as usize * KB,
        };
        // Read the flags
        let flags9 = reader.read::<u8, LE>()?;
        // Read the flags
        let flags10 = reader.read::<u8, LE>()?;

        // Read the remaining padding
        let _padding = reader.read_bytes(5)?;

        Ok(Self {
            prg_rom_size,
            chr_rom_size,
            flags6,
            flags7,
            prg_ram_size,
            flags9,
            flags10,
        })
    }

    pub fn prg_rom_size(&self) -> usize {
        self.prg_rom_size
    }

    pub fn chr_rom_size(&self) -> usize {
        self.chr_rom_size
    }

    pub fn trainer(&self) -> bool {
        self.flags6.trainer()
    }
}

#[derive(Debug)]
pub enum HeaderError {
    ReaderError(ReaderError),
    UnknownMagic([u8; 3]),
    TryFromSliceError(TryFromSliceError),
}

impl From<ReaderError> for HeaderError {
    fn from(err: ReaderError) -> Self {
        Self::ReaderError(err)
    }
}

impl From<TryFromSliceError> for HeaderError {
    fn from(err: TryFromSliceError) -> Self {
        Self::TryFromSliceError(err)
    }
}
