use core::ops::Range;
use crate::emulator::{NesEffect, ppu};

/// Represents the NES CPU memory management unit.
// Why we are not using a Vec directly? Simply because we want to control the
// indexing and the maximum fixed size.
#[derive(Debug)]
pub struct CpuMmu {
    // Size
    size: usize,
    // Data
    data: Vec<u8>,
}

const DEFAULT_CPU_MMU_SIZE: usize = u16::MAX as usize + 1;
const STACK_RANGE: Range<usize> = 0x0100..0x0200;

impl Default for CpuMmu {
    fn default() -> Self {
        // Initialize the data
        let mut data = Vec::with_capacity(DEFAULT_CPU_MMU_SIZE);
        // Fill it with zeros
        data.resize(DEFAULT_CPU_MMU_SIZE, 0);

        CpuMmu {
            size: DEFAULT_CPU_MMU_SIZE,
            data,
        }
    }
}

impl CpuMmu {
    /// Returns the total memory size in bytes
    pub fn size(&self) -> usize {
        self.size
    }

    pub fn stack_mut(&mut self) -> Option<&mut [u8]> {
        self.data.get_mut(STACK_RANGE)
    }

    /// Sets the received `bytes` at the specified `offset` in the memory unit.
    /// If the memory points to mapped registers from other devices other than
    /// the CPU, we want to notify the emulator about that.
    pub fn set_bytes(
        &mut self,
        offset: usize,
        bytes: &[u8],
    ) -> Result<NesEffect, CpuMmuError> {
        // Define a range, which is easier to work with
        let range = offset..(offset + bytes.len());

        // Set that specific range with the given bytes
        self.data
            .get_mut(range.clone())
            .ok_or(CpuMmuError::OutOfBoundsAccess(range))?
            .clone_from_slice(bytes);

        // If the size of the bytes is only 16KB, or even less(which should not
        // happen, but we don't take chances)
        // AND
        // If the offset is at 0x8000, we know that we have a ROM and we have
        // to load it at $8000-$bfff and $c000-$ffff
        if bytes.len() <= (16 * 1024) && offset == 0x8000 {
            // Define another range, that mirrors the address
            let range_mirror = 0xc000..(0xc000 + bytes.len());
            self.data[range_mirror].clone_from_slice(bytes);
        }

        // If we wrote a single byte, it is possible that we wrote to a memory
        // mapped register of another device, than the CPU
        let nes_effect = if bytes.len() == 1 {
            // Based on the offset we wrote, we want to notify the NES of
            // potential other effects
            match offset {
                ppu::PPU_ADDR_CPU_MMU_ADDR => {
                    NesEffect::Ppu(ppu::PpuEffect::PpuAddrWrite)
                }
                _ => NesEffect::None
            }
        } else {
            NesEffect::None
        };

        Ok(nes_effect)
    }

    /// Sets each byte in the given `range` of memory to the specified `value`.
    pub fn set_with_value(
        &mut self,
        range: Range<usize>,
        value: u8,
    ) -> Result<(), CpuMmuError> {
        // Set that specific range with the given bytes
        self.data
            .get_mut(range.clone())
            .ok_or(CpuMmuError::OutOfBoundsAccess(range.clone()))?
            .clone_from_slice(
                &std::iter::repeat(value)
                    .take(range.end)
                    .collect::<Vec<u8>>(),
            );
        Ok(())
    }

    /// Read a u16, with Little Endian at the specified `addr`
    pub fn read_u16_le(&self, addr: usize) -> Option<u16> {
        // Read 2 bytes from the address
        let bytes = self.data.get(addr..(addr + 2))?;
        // Convert them into a u16 value
        let value = u16::from_le_bytes(bytes.try_into().ok()?);
        // Return that value
        Some(value)
    }

    /// Read a byte at the specified `addr`
    pub fn read_u8(&self, addr: usize) -> Option<u8> {
        self.data.get(addr).copied()
    }

    /// Set a single byte to the desired location
    pub fn set(
        &mut self,
        addr: usize,
        value: u8,
    ) -> Result<NesEffect, CpuMmuError> {
        self.set_bytes(addr, &[value])
    }

    /// Return a slice of bytes from within the given `range`
    pub fn get_bytes(&self, range: Range<usize>) -> Option<&[u8]> {
        self.data.get(range)
    }
}

#[derive(Debug)]
pub enum CpuMmuError {
    OutOfBoundsAccess(Range<usize>),
    FailedToGetPpuStatus,
}

// The PPU addresses a 14-bit (16kB) address space, $0000-3FFF,
// completely separate from the CPU's address bus. It is either directly
// accessed by the PPU itself, or via the CPU with memory mapped registers
// at $2006 and $2007.
const PPU_MMU_MEMORY_MAP_SIZE: usize = 16 * 1024;
const PPU_OAM_SIZE: usize = 4 * 64;

pub struct PpuMmu {
    // Memory map of the Ppu
    data: [u8; PPU_MMU_MEMORY_MAP_SIZE],
    // Object Attribute memory
    oam: [u8; PPU_OAM_SIZE],
}

impl PpuMmu {
    /// Sets the received `bytes` at the specified `offset` in the PPU memory
    /// unit
    pub fn set_bytes(
        &mut self,
        offset: usize,
        bytes: &[u8],
    ) -> Result<(), PpuMmuError> {
        // Define a range, which is easier to work with
        let range = offset..(offset + bytes.len());

        // Set that specific range with the given bytes
        self.data
            .get_mut(range.clone())
            .ok_or(PpuMmuError::OutOfBoundsAccess(range))?
            .clone_from_slice(bytes);

        // If we write in the range 0x2000 to 0x2EFF inclusive, we want to
        // mirror this as well in 0x3000 to 0x3EFF
        if offset == 0x2000 && (offset + bytes.len()) < 0x3000 {
            // Set the mirror range
            let mirror_range = offset + 0x1000
                ..(offset + bytes.len() + 0x1000);
            // Set that specific range with the given bytes
            self.data
                .get_mut(mirror_range.clone())
                .ok_or(PpuMmuError::OutOfBoundsAccess(mirror_range))?
                .clone_from_slice(bytes);
        }

        // If we write in the range 0x3F00 to 0x3F1F inclusive, we want to
        // mirror this as well in 0x3F20 to 0x3FFF inclusive. This means copy
        // the exact same bytes to the rest of the 7 intervals
        if offset == 0x3F00 && (offset + bytes.len()) < 0x3F20 {
            for idx in 1..8 {
                let start = offset + idx * 0x20;
                let end = start + bytes.len();
                let mirror_range = start..end;

                // Set that specific range with the given bytes
                self.data
                    .get_mut(mirror_range.clone())
                    .ok_or(PpuMmuError::OutOfBoundsAccess(mirror_range))?
                    .clone_from_slice(bytes);
            }
        }

        Ok(())
    }

    /// Returns the pattern table with the given `index`. Only indexes 0 and 1
    /// are available for the PPU memory map. Each pattern table has a size
    /// of 0x1000 bytes
    pub fn pattern_table(&self, index: usize) -> Result<&[u8], PpuMmuError> {
        if index > 1 {
            return Err(PpuMmuError::InvalidPatternTableIndex(index));
        }
        let start = 0x1000 * index;
        let range = start..start + 0x1000;

        self.data.get(range.clone())
            .ok_or(PpuMmuError::OutOfBoundsAccess(range))
    }

    /// Returns the name table with the given `index`.
    /// Only indexes 0, 1, 2 and 3 are available for the PPU memory map. Each
    /// name table has a size of 0x400 bytes.
    pub fn name_table(&self, index: usize) -> Result<&[u8], PpuMmuError> {
        if index > 3 {
            return Err(PpuMmuError::InvalidNameTableIndex(index));
        }
        let start = 0x2000 + (0x400 * index);
        let range = start..start + 0x400;

        self.data.get(range.clone())
            .ok_or(PpuMmuError::OutOfBoundsAccess(range))
    }

    /// Palette RAM indexes
    pub fn palette_ram(&self) -> Result<&[u8], PpuMmuError> {
        let range = 0x3F00..0x3F20;
        self.data.get(range.clone())
            .ok_or(PpuMmuError::OutOfBoundsAccess(range))
    }

    /// Get the sprite information at position `index` in the OAM
    pub fn sprite_oam(&self, index: usize) -> Result<OamEntry, PpuMmuError> {
        // OAM contains 256 bytes, which is 64 entries of 4 bytes each.
        if index > 63 {
            return Err(PpuMmuError::InvalidSpriteOamIndex(index));
        }
        let start = index * 4;
        let range = start..start+4;
        let bytes = self.oam.get(range.clone())
            .ok_or(PpuMmuError::OutOfBoundsAccess(range))?;

        Ok(OamEntry {
            sprite_y: bytes[0],
            sprite_number: bytes[1],
            sprite_attr: bytes[2],
            sprite_x: bytes[3],
        })
    }
}

#[derive(Debug)]
pub struct OamEntry {
    // Sprite Y coordinate
    sprite_y: u8,
    // Sprite tile number
    sprite_number: u8,
    // Sprite attribute
    sprite_attr: u8,
    // Sprite X coordinate
    sprite_x: u8,
}

impl Default for PpuMmu {
    fn default() -> Self {
        Self {
            data: [0; PPU_MMU_MEMORY_MAP_SIZE],
            oam: [0; PPU_OAM_SIZE],
        }
    }
}

#[derive(Debug)]
pub enum PpuMmuError {
    OutOfBoundsAccess(Range<usize>),
    InvalidPatternTableIndex(usize),
    InvalidNameTableIndex(usize),
    InvalidSpriteOamIndex(usize),
}
