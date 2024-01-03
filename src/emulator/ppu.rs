//! Module representint a NES emulator Picture Processing Unit (PPU)
use crate::emulator::{CpuMmu, CpuMmuError};
use std::sync::{Arc, Mutex};

// Trait that needs to be implemented by a register that is memory mapped
// This is usually needed by registers used to communicate between the CPU
// and the PPU of the NES. This trait and its methods are not public since some
// registers are (or at least they were designed initially) as read-only or 
// write-only.
trait MemoryMappedReg {
    /// Address where the mapped memory register resides
    const CPU_ADDR: u16;

    /// Get method to get the register from the specified `mmu` memory unit
    fn get(&self, cpu_mmu: &CpuMmu) -> Option<u8>;

    /// Get method to get the register from the specified memmory unit.
    fn set(&self, cpu_mmu: &mut CpuMmu, value: u8) -> Result<(), CpuMmuError>;
}

// The PPU registers are repeated every 8 bytes between addresses 0x2000 and
// 0x3FFF of the CPU memory map

/// Specified end of PPU memory mapped registries mirrors
const PPU_REGS_MIRROR_END_ADDR: u16 = 0x4000;

/// PPU controller register. Access: write
/// Contains various flags controlling PPU operation.
#[derive(Debug)]
pub struct PpuCtrl {
    // Base nametable address
    // (0 = $2000; 1 = $2400; 2 = $2800; 3 = $2C00)
    base_nt_addr: u16,
    // VRAM address increment
    vram_inc: VramInc,
    // Sprite pattern table address for 8x8 sprites, ignored in 8x16 mode
    // (0: $0000; 1: $1000;)
    sprite_pt_addr: u16,
    // Background patter table address
    // (0: $0000; 1: $1000;)
    bg_pt_addr: u16,
    // Sprite size
    sprite_size: SpriteSize,
    // master/slave select
    ms_select: u8,
    // Generate an NMI at the start of the vertical blanking interval
    gen_nmi: u8,
}

impl From<u8> for PpuCtrl {
    fn from(value: u8) -> Self {
        let base_nt_bits = value & 0b11;
        let base_nt_addr = match base_nt_bits {
            0 => 0x2000,
            1 => 0x2400,
            2 => 0x2800,
            3 => 0x2C00,
            _ => unreachable!(),
        };
        let vram_inc = VramInc::from((value >> 2) & 1);
        let sprite_pt_bit = (value >> 3) & 1;
        let sprite_pt_addr = match sprite_pt_bit {
            0 => 0x0000,
            1 => 0x1000,
            _ => unreachable!(),
        };
        let bg_pt_bit = (value >> 4) & 1;
        let bg_pt_addr = match bg_pt_bit {
            0 => 0x0000,
            1 => 0x1000,
            _ => unreachable!(),
        };
        let sprite_size = SpriteSize::from((value >> 5) & 1);
        let ms_select = (value >> 6) & 1;
        let gen_nmi = (value >> 7) & 1;

        Self {
            base_nt_addr,
            vram_inc,
            sprite_pt_addr,
            bg_pt_addr,
            sprite_size,
            ms_select,
            gen_nmi,
        }
    }
}

/// VRAM address increment per CPU read/write
#[derive(Debug)]
pub enum VramInc {
    // Add 1, going across
    Add1X,
    // Add 32, going down
    Add1D,
}

impl From<u8> for VramInc {
    fn from(value: u8) -> Self {
        match value & 1 {
            0 => Self::Add1X,
            1 => Self::Add1D,
            _ => unreachable!(),
        }
    }
}

impl VramInc {
    pub fn as_u8(&self) -> u8 {
        match self {
            Self::Add1X => 0,
            Self::Add1D => 1,
        }
    }
}

/// Sprite size; see PPU OAM#Byte 1
#[derive(Debug)]
pub enum SpriteSize {
    // 8x8 pixels sprite size
    Size8x8,
    // 8x16 pixesl sprite size
    Size8x16,
}

impl From<u8> for SpriteSize {
    fn from(value: u8) -> Self {
        match value & 1 {
            0 => Self::Size8x8,
            1 => Self::Size8x16,
            _ => unreachable!(),
        }
    }
}

impl SpriteSize {
    pub fn as_u8(&self) -> u8 {
        match self {
            Self::Size8x8=> 0,
            Self::Size8x16 => 1,
        }
    }
}

/// PPU mask register. Access: write
/// This register controls the rendering of sprites and backgrounds, as well
/// as colour effects.
#[derive(Debug)]
pub struct PpuMask;

/// Description: PPU status register
/// Access: read
/// This register reflects the state of various functions inside the PPU. It is
/// often used for determining timing. To determine when the PPU has reached a
/// given pixel of the screen, put an opaque (non-transparent) pixel of
/// sprite 0 there.
#[derive(Debug)]
pub struct PpuStatus;

// Macro that implements the trait `MemoryMappedReg` for memory mapped PPU
// registers in the CPU's memory.
macro_rules! memory_map_ppu_reg {
    ($reg:ty, $addr:literal) => {
        impl MemoryMappedReg for $reg {
            const CPU_ADDR: u16 = $addr;

            fn get(&self, cpu_mmu: &CpuMmu) -> Option<u8> {
                cpu_mmu.read_u8(Self::CPU_ADDR as usize)
            }

            fn set(&self, cpu_mmu: &mut CpuMmu, value: u8) -> Result<(), CpuMmuError> {
                // Initialize the first byte as the original address of the memory
                // mapped register to be stored
                let mut addr: u16 = Self::CPU_ADDR;

                // Mmu registers are mirrored every 8 bytes between
                // the 0x2000 and 0x3FFF inclusive range
                while addr < PPU_REGS_MIRROR_END_ADDR && (addr as usize) < cpu_mmu.size() {
                    // Set the new value for the register
                    cpu_mmu.set(addr as usize, value)?;
                    // Mirror the action every 8 bytes
                    addr += 8;
                }
                Ok(())
            }
        }
    };
}

memory_map_ppu_reg!(PpuCtrl, 0x2000);
memory_map_ppu_reg!(PpuMask, 0x2001);

impl MemoryMappedReg for PpuStatus {
    const CPU_ADDR: u16 = 0x2002;

    fn get(&self, cpu_mmu: &CpuMmu) -> Option<u8> {
        // Get the register from memory
        let ppu_status = cpu_mmu.read_u8(Self::CPU_ADDR as usize)?;

        // Reading the status register will clear bit 7 mentioned above and
        // also the address latch used by PPUSCROLL and PPUADDR. It does not
        // clear the sprite 0 hit or overflow bit.
        let ppu_status = (0xFF - 1) & ppu_status;

        Some(ppu_status)
    }

    // This register is supposed to be read only
    fn set(&self, cpu_mmu: &mut CpuMmu, value: u8) -> Result<(), CpuMmuError> {
        // Initialize the first byte as the original address of the memory
        // mapped register to be stored
        let mut addr: u16 = Self::CPU_ADDR;

        // Mmu registers are mirrored every 8 bytes between
        // the 0x2000 and 0x3FFF inclusive range
        while addr < PPU_REGS_MIRROR_END_ADDR && (addr as usize) < cpu_mmu.size() {
            // Set the new value for the register
            cpu_mmu.set(addr as usize, value)?;
            // Mirror the action every 8 bytes
            addr += 8;
        }
        Ok(())
    }
}

/// Defines the Power Processing Unit (PPU)
#[derive(Debug)]
pub struct Ppu {
    ppu_ctrl: PpuCtrl,
    ppu_mask: PpuMask,
    ppu_status: PpuStatus,
}

impl Ppu {
    pub fn power_up(cpu_mmu: Arc<Mutex<CpuMmu>>) -> Self {
        // Acquire the lock to write memory
        let mut cpu_mmu = cpu_mmu.lock().unwrap();
        // If we fail to set registers, we want to fail early
        let ppu_ctrl = PpuCtrl::from(0);
        ppu_ctrl.set(&mut *cpu_mmu, 0).expect("Cannot set PPU CTRL");
        let ppu_mask = PpuMask;
        ppu_mask.set(&mut *cpu_mmu, 0).expect("Cannot set PPU Mask");
        let ppu_status = PpuStatus;
        ppu_status.set(&mut *cpu_mmu, 0b1010_0000).expect("Cannot set PPU Status");

        Self {
           ppu_ctrl,
           ppu_mask,
           ppu_status,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_ppu_reg_value {
        ($value:literal, $reg:expr) => {
            let mut cpu_mmu = CpuMmu::default();
            let ppu_reg = $reg;

            // Set the register
            ppu_reg.set(&mut cpu_mmu, $value);

            let ppu_reg_value = ppu_reg.get(&cpu_mmu)
                .expect("Failed to fetch ppu reg");

            assert!(ppu_reg_value == $value);
        };
    }

    #[test]
    fn test_get_ppu_ctrl() {
        test_ppu_reg_value!(0x10, PpuCtrl::from(0x10));
        test_ppu_reg_value!(0x19, PpuMask);
    }
}
