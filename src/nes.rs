mod flags;
mod header;

use crate::reader::{Reader, ReaderError};
use header::{Header, HeaderError};

// This is the default trainer size
const TRAINER_SIZE: usize = 512;

/// Represents the file format used by NES emulators. We are using this format
/// in order to test our own NES Emulator implementation, because majority of
/// the tests are in this format.
/// This represents the iNES file format. We dropped the `i` for better naming
// TODO: We might want to switch the memory/address size below to u16
#[derive(Debug)]
pub struct INes {
    // Header, first 16 bytes
    header: Header,
    // Trainer, if present, of size 512
    trainer: Option<Vec<u8>>,
    // PRG rom data
    prg_rom: Vec<u8>,
    // CHR rom data
    chr_rom: Vec<u8>,
}

impl INes {
    // Parse the INes file format
    pub fn parse(reader: &mut Reader) -> Result<Self, HeaderError> {
        // Read the INes header
        let header = Header::parse(reader)?;
        // Read the trainer if present.
        let trainer = if header.trainer() {
            let trainer_bytes = reader.read_bytes(TRAINER_SIZE)?.to_vec();
            Some(trainer_bytes)
        } else {
            None
        };
        // Read the CHR ROM
        let prg_rom = reader.read_bytes(header.prg_rom_size())?.to_vec();
        // Read the CHR ROM
        let chr_rom = reader.read_bytes(header.chr_rom_size())?.to_vec();

        // Following are the PlayChoice ROM data,
        // that we simply ignore for this emulator

        Ok(Self {
            header,
            trainer,
            prg_rom,
            chr_rom,
        })
    }

    pub fn header(&self) -> &Header {
        &self.header
    }

    pub fn trainer(&self) -> Option<&[u8]> {
        self.trainer.as_deref()
    }

    pub fn prg_rom(&self) -> &[u8] {
        &self.prg_rom
    }

    pub fn chr_rom(&self) -> &[u8] {
        &self.chr_rom
    }
}

#[derive(Debug)]
pub enum INesError {
    HeaderError(HeaderError),
    ReaderError(ReaderError),
}

impl From<HeaderError> for INesError {
    fn from(err: HeaderError) -> Self {
        Self::HeaderError(err)
    }
}

impl From<ReaderError> for INesError {
    fn from(err: ReaderError) -> Self {
        Self::ReaderError(err)
    }
}
