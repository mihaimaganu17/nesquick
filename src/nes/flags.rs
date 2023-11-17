//! In the iNES format, cartridge boards are divided into classes called
//! "mappers" based on similar board hardware and behavior.

/// First set of flags found in the NES file format
#[derive(Debug)]
pub struct Flags6 {
    // This is the u8 value read from the file
    value: u8,
    // Nametable Mirroring
    mirroring: Mirroring,
    // Cartrige contains battery-backed PRG RAMG ($6000-7FFF) or other
    // persistent memory. Container in the second bit of flags 6.
    contains_persistence_memory: bool,
    // 512-byte trainer at $7000-$71FF (stored before PRG data)
    // The trainer usually contains mapper register translation and CHR-RAM
    // caching code for early RAM cartridges that could not mimic mapper ASICs
    // and only had 32 KiB of CHR-RAM;
    // - Nesticle, an old but influential NES emulator for DOS.
    // - It is not used on unmodified dumps of original ROM cartridges.
    // Contained in the 3rd bit of flags6
    trainer: bool,
    // Ignore mirroring control or above mirroring bit; instead provide
    // four-screen VRAM.
    // Contained in the 4th bit of flags 6
    four_screen_vram: bool,
    // Lower nybble of mapper number
    // Contained in the last 4 bits of flags6
    mapper_low_4bits: u8,
}

impl From<u8> for Flags6 {
    fn from(flags: u8) -> Self {
        // Extract the needed information from the flags
        let mirroring = Mirroring::from(flags & 1);
        let contains_persistence_memory = u8_to_bool((flags >> 1) & 1);
        let trainer = u8_to_bool((flags >> 2) & 1);
        let four_screen_vram = u8_to_bool((flags >> 3) & 1);
        let mapper_low_4bits = (flags >> 4) & 0xF;

        Self {
            value: flags,
            mirroring,
            contains_persistence_memory,
            trainer,
            four_screen_vram,
            mapper_low_4bits,
        }
    }
}

/// Represents Nametable Mirroring
// For mappers with hard-wired mirroring, connecting CIRAM A10 to PPU A10 or
// A11 for a vertical or horizontal arrangement is specified by bit 0.
// More on Mirroring: https://www.nesdev.org/wiki/Mirroring#4-screen
#[derive(Debug)]
pub enum Mirroring {
    // Vertical arrangement (CIRAM A10 = PPU A11)
    Vertical,
    // Horizontal arrangement (CIRAM A10 = PPU A10)
    Horizontal
}

impl From<u8> for Mirroring {
    fn from(value: u8) -> Self {
        match value & 1 {
            0 => Self::Horizontal,
            1 => Self::Vertical,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
pub struct Flags7 {
    // The value read from the file
    value: u8,
    // VS Unisystem. Vs. games have a coin slot and different palettes.
    vs_unisystem: bool,
    // PlayChoice-10 (8 KB of Hint Screen data stored after CHR data)
    playchoice_10: bool,
    // If equal to 2, flags 8-15 are in NES 2.0 format
    nes2_format: bool,
    // Upper nybble of mapper number
    mapper_high_4bits: u8,
}

impl From<u8> for Flags7 {
    fn from(flags: u8) -> Self {
        let vs_unisystem = u8_to_bool(flags & 1);
        let playchoice_10 = u8_to_bool((flags >> 1) & 1);
        let nes2_format = if (flags >> 2) & 0b11 == 2 {
            true
        } else {
            false
        };
        let mapper_high_4bits = (flags >> 4) & 0xF;

        Self {
            value: flags,
            vs_unisystem,
            playchoice_10,
            nes2_format,
            mapper_high_4bits,
        }
    }
}

fn u8_to_bool(value: u8) -> bool {
    if value != 0 { true } else { false }
}
