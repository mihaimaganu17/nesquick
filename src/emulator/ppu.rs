//! Module representint a NES emulator Picture Processing Unit (PPU)
use crate::emulator::{CpuMmu, CpuMmuError};
use std::sync::{Arc, Mutex};

pub const PPU_CTRL_CPU_MMU_ADDR: usize = 0x2000;
pub const PPU_MASK_CPU_MMU_ADDR: usize = 0x2001;
pub const PPU_STATUS_CPU_MMU_ADDR: usize = 0x2002;
pub const PPU_OAMADDR_CPU_MMU_ADDR: usize = 0x2003;
pub const PPU_OAMDATA_CPU_MMU_ADDR: usize = 0x2004;
pub const PPU_SCROLL_CPU_MMU_ADDR: usize = 0x2005;
pub const PPU_ADDR_CPU_MMU_ADDR: usize = 0x2006;
pub const PPU_DATA_CPU_MMU_ADDR: usize = 0x2007;
pub const PPU_OAMDMA_CPU_MMU_ADDR: usize = 0x2007;

#[derive(Debug)]
pub enum PpuEffect {
    PpuStatusRead,
    PpuStatusWrite,
    PpuAddrRead,
    PpuAddrWrite,
}

// Trait that needs to be implemented by a register that is memory mapped
// This is usually needed by registers used to communicate between the CPU
// and the PPU of the NES. This trait and its methods are not public since some
// registers are (or at least they were designed initially) as read-only or 
// write-only.
trait MemoryMappedReg {
    /// Address where the mapped memory register resides
    const CPU_ADDR: u16;

    /// Get method to get the register from the specified `mmu` memory unit
    fn get(&self, cpu_mmu: &mut CpuMmu) -> Option<u8>;

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
struct PpuCtrl {
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
enum VramInc {
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
struct PpuMask;

// Macro that implements the trait `MemoryMappedReg` for memory mapped PPU
// registers in the CPU's memory.
macro_rules! memory_map_ppu_reg {
    ($reg:ty, $addr:literal) => {
        impl MemoryMappedReg for $reg {
            const CPU_ADDR: u16 = $addr;

            fn get(&self, cpu_mmu: &mut CpuMmu) -> Option<u8> {
                let (value, _nes_effect) = cpu_mmu
                    .read_u8(Self::CPU_ADDR as usize)
                    .ok()?;
                Some(value)
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

/// Description: PPU status register
/// Access: read
/// This register reflects the state of various functions inside the PPU. It is
/// often used for determining timing. To determine when the PPU has reached a
/// given pixel of the screen, put an opaque (non-transparent) pixel of
/// sprite 0 there.
#[derive(Debug)]
struct PpuStatus;

impl PpuStatus {
    /// Sets the vertical blank bit, which is bit 7 of the register
    pub fn set_vblank(&self, cpu_mmu: &mut CpuMmu) -> Result<(), CpuMmuError> {
        if let Some(tmp_status) = self.get(cpu_mmu) {
            // We set the last bit (bit 7, counting from 0) of the status
            let new_status = tmp_status | 0b1000_0000;
            // Write changes
            self.set(cpu_mmu, new_status)
        } else {
            Err(CpuMmuError::FailedToGetPpuStatus)
        }
    }
}

impl MemoryMappedReg for PpuStatus {
    const CPU_ADDR: u16 = 0x2002;

    fn get(&self, cpu_mmu: &mut CpuMmu) -> Option<u8> {
        // Get the register from memory
        let (ppu_status, _nes_effect) = cpu_mmu
            .read_u8(Self::CPU_ADDR as usize)
            .ok()?;

        // Reading the status register will clear bit 7 mentioned above and
        // also the address latch used by PPUSCROLL and PPUADDR. It does not
        // clear the sprite 0 hit or overflow bit.
        let ppu_status = (0xFF - 1) & ppu_status;
        // Set the new value for the register
        self.set(cpu_mmu, ppu_status).ok()?;

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

/// The CPU can access the PPU memory, by writing to the PPU Addr the address
/// where the CPU wants to write in VRAM. This is accomplished by writing twice
/// to the PPU, essentially splitting a `u16` address into two bytes, writing
/// the upper byte first.
/// We wrap a u16 into the `PpuAddr` to keep a cache of the current PPU value.
#[derive(Debug)]
pub struct PpuAddr(u16);

impl MemoryMappedReg for PpuAddr {
    const CPU_ADDR: u16 = PPU_ADDR_CPU_MMU_ADDR as u16;

    fn get(&self, cpu_mmu: &mut CpuMmu) -> Option<u8> {
        // Get the register from memory. Logic for the NesEffect is already
        // implemented in the CPU Mmu code
        let (ppu_addr, _nes_effect) = cpu_mmu.read_u8(Self::CPU_ADDR as usize)
            .ok()?;

        Some(ppu_addr)
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
    pub ppu_addr: PpuAddr,
    // Folowing are the 4 PPU internal registers
    v_reg: VReg,
    t_reg: TReg,
    x_reg: XReg,
    pub w_reg: WReg,
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
        let ppu_addr = PpuAddr(0);
        ppu_addr.set(&mut *cpu_mmu, 0b0000_0000).expect("Cannot set PPU Addr");

        Self {
           ppu_ctrl,
           ppu_mask,
           ppu_status,
           ppu_addr,
           v_reg: VReg(0),
           t_reg: TReg(0),
           x_reg: XReg(0),
           w_reg: WReg(0),
        }
    }

    pub fn set_vblank(
        &self,
        cpu_mmu: Arc<Mutex<CpuMmu>>,
    ) -> Result<(), CpuMmuError> {
        // Acquire the lock to write memory
        let mut cpu_mmu = cpu_mmu.lock().unwrap();
        // Set vblank flag
        self.ppu_status.set_vblank(&mut *cpu_mmu)
    }

    pub fn set_ppuaddr(
        &mut self,
        cpu_mmu: &mut CpuMmu,
    ) -> Result<(), CpuMmuError> {
        // Acquire the lock to write memory
        //let mut cpu_mmu = cpu_mmu.lock().unwrap();
        // We first fetch the address that was written to.
        let value = self.ppu_addr.get(cpu_mmu)
            .ok_or(CpuMmuError::FailedToGetPpuAddr)?;
        println!("[Debug] Value {:?}", value);
        //println!("[Debug] Value: {}", value);
        // Depending on the value of the `w` register latch, we will update our
        // internal caches ppu address accordingly.
        if self.w_reg.0 == 0 {
            self.ppu_addr = PpuAddr(value as u16);
        } else {
            self.ppu_addr = PpuAddr((self.ppu_addr.0 << 8) | value as u16);
        }

        self.w_reg = WReg(1 - self.w_reg.0);
        Ok(())
    }

    pub fn read_ppustatus(
        &mut self,
        cpu_mmu: &mut CpuMmu,
    ) -> Result<(), CpuMmuError> {
        // When the `PpuStatus` is read, bit 7 is cleared. This logic is
        // already implemented in `get` method.
        // We first fetch the address that was written to.
        let value = self.ppu_status.get(cpu_mmu)
            .ok_or(CpuMmuError::FailedToGetPpuStatus)?;

        // The latch of the `w` register is also cleared
        self.w_reg = WReg(0);

        Ok(())
    }

    /// PPU sprite evaluation is an operation done by the PPU once each
    /// scanline. It prepares the set of sprites and fetches their data to be
    /// rendered on the next scanline. This is a separate step from sprite
    /// rendering.
    /// https://www.nesdev.org/wiki/PPU_sprite_evaluation
    /// Each scanline, the PPU reads the spritelist
    /// (that is, Object Attribute Memory) to see which
    /// to draw:
    ///     1. First, it clears the list of sprites to draw.
    ///     2. Second, it reads through OAM, checking which sprites will be on
    ///     this scanline. It chooses the first eight it finds that do.
    ///     3. Third, if eight sprites were found, it checks (in a
    ///     wrongly-implemented fashion) for further sprites on the scanline to
    ///     see if the sprite overflow flag should be set.
    ///     4. Fourth, using the details for the eight (or fewer) sprites
    ///     chosen, it determines which pixels each has on the scanline and
    ///     where to draw them.
    pub fn sprite_eval() -> Option<()> {
        Some(())
    }
}

#[derive(Debug, Default)]
pub struct VReg(u8);
#[derive(Debug, Default)]
pub struct TReg(u8);
#[derive(Debug, Default)]
pub struct XReg(u8);
/// Denotes the first or second write toggle. Toggles on each write to either
/// PPUSCROLL or PPUADDR, indicating whether this is the first or second write.
/// Clears on reads of PPUSTATUS. Sometimes called the 'write latch' or
/// 'write toggle'.
#[derive(Debug, Default)]
pub struct WReg(pub u8);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_ppu_reg_value {
        ($value:literal, $reg:expr) => {
            let mut cpu_mmu = CpuMmu::default();
            let ppu_reg = $reg;

            // Set the register
            ppu_reg.set(&mut cpu_mmu, $value).expect("Cannot set the PPU register");

            let ppu_reg_value = ppu_reg.get(&mut cpu_mmu)
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
