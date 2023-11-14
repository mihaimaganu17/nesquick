use crate::reader::{Reader, ReaderError, LE};
use std::array::TryFromSliceError;

const NES_MAGIC: &[u8] = b"NES";

/// Represents the file format used by NES emulators. We are using this format in order to test our
/// own NES Emulator implementation, because majority of the tests are in this format.
/// This represents the iNES file format. We dropped the `i` for better naming
// TODO: We might want to switch the memory/address size below to u16
pub struct INes {
    // Size of PRG ROM, which is the ROM connected to the CPU. The size itself is stored as a count
    // of 16KiB units. But here we will store it directly in bytes after reading it such that it is
    // easier to manipulate
    prg_rom_size: usize,
    // Size of CHR ROM, which is the ROM connected to the PPU. The size is stored in the file
    // format as a count of 8KiB units. Here we will store it as count of bytes after parsing it
    // from the file such that it is easier to manipulate.
    // Value `0` means the board uses CHR RAM
    chr_rom_size: usize,
}

// Represents a Kilobyte unit in bytes size
const KB: usize = 1024;

impl INes {
    pub fn parse(reader: &mut Reader) -> Result<Self, INesError> {
        let magic_read = reader.read_bytes(NES_MAGIC.len())?;

        if magic_read != NES_MAGIC {
            return Err(INesError::UnknownMagic(magic_read.try_into()?));
        }

        // Read the number of 16KiB PRG ROM blocks
        let prg_rom_block_count = reader.read::<u8, LE>()? as usize;
        let prg_rom_size = prg_rom_block_count * 16 * KB;

        // Read the number of 8KiB CHR ROM blocks
        let chr_rom_block_count = reader.read::<u8, LE>()? as usize;
        let chr_rom_size = chr_rom_block_count * 8 * KB;

        Ok(Self{
            prg_rom_size,
            chr_rom_size,
        })
    }
}

#[derive(Debug)]
pub enum INesError {
    ReaderError(ReaderError),
    UnknownMagic([u8; 3]),
    TryFromSliceError(TryFromSliceError),
}

impl From<ReaderError> for INesError {
    fn from(err: ReaderError) -> Self {
        Self::ReaderError(err)
    }
}

impl From<TryFromSliceError> for INesError {
    fn from(err: TryFromSliceError) -> Self {
        Self::TryFromSliceError(err)
    }
}
