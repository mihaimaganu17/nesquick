//! Module representint a NES emulator Picture Processing Unit (PPU)
use crate::emulator::{CpuMmu, CpuMmuError, Message};
use std::sync::{Arc, Mutex, Condvar, mpsc};
use core::sync::atomic::{AtomicUsize, Ordering};

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
    OamAddrRead,
    OamAddrWrite,
    OamDataRead,
    OamDataWrite,
    OamDmaRead,
    OamDmaWrite(u8),
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

impl PpuMask {
    pub fn render_background(&self, cpu_mmu: &mut CpuMmu) -> Option<bool> {
        Some((self.get(cpu_mmu)? >> 3) & 1 != 0)
    }
    pub fn render_sprites(&self, cpu_mmu: &mut CpuMmu) -> Option<bool> {
        Some((self.get(cpu_mmu)? >> 4) & 1 != 0)
    }
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

#[derive(Debug)]
pub struct OamAddr;
#[derive(Debug)]
pub struct OamData;
#[derive(Debug)]
pub struct OamDma;

memory_map_ppu_reg!(OamAddr, 0x2003);
memory_map_ppu_reg!(OamData, 0x2004);
memory_map_ppu_reg!(OamDma, 0x4014);

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
    // The PPU renders 262 scanlines per frame. Each scanline lasts for
    // 341 PPU clock cycles
    // (113.667 CPU clock cycles; 1 CPU cycle = 3 PPU cycles),
    // with each clock cycle producing one pixel. The line numbers given here
    // correspond to how the internal PPU frame counters count lines.
    // PPUCC = CPUCC * 3
    // Scanline = PPUCC div 341 - 21;   X- coordinate
    // PixelOfs = PPUCC mod 341;        Y- coordinate
    // CPUcollisionCC = ((Y+21)*341+X)/3
    // The PPU renders 3 pixels in one CPU clock. Therefore, by multiplying the
    // CPU CC figure by 3, we get the total amount of pixels that have been
    // rendered (including non-displayed ones) since the VINT.
    // 341 pixels are rendered per scanline (although only 256 are displayed).
    // Therefore, by dividing PPUCC by this, we get the # of completely
    // rendered scanlines since the VINT. 21 blank scanlines are rendered
    // before the first visible one is displayed. So, to get a scanline offset
    // into the actual on-screen image, we simply subtract the amount of
    // non-displayed scanlines. Note that if this yeilds a negative number, the
    // PPU is still in the V-blank period.
    pub cycles: usize,
    pub scanline: usize,
    pub frame_counter: usize,

    // OAM read/write address. Write the address of `Oam` you want to access
    // here. Most games just write 0x00 here and then use `OamDma`.
    // DMA is implemented in the 2A03 chip and works by repeatedly writing
    // to OAMDATA.
    pub oam_addr: OamAddr,
    // OAM data read/write
    pub oam_data: OamData,
    // OAM DMA high address
    pub oam_dma: OamDma,
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
           cycles: 0,
           // We mimick -1 here, as if this is the previous dummy scanline
           scanline: 261,
           frame_counter: 0,
           oam_addr: OamAddr,
           oam_data: OamData,
           oam_dma: OamDma,
        }
    }

    /// PPU sprite evaluation is an operation done by the PPU once each
    /// scanline. It prepares the set of sprites and fetches their data to be
    /// rendered on the next scanline.
    pub fn sprite_evaluation(&mut self, cpu_mmu: Arc<Mutex<CpuMmu>>) {

    }

    /// Execute the PPU for `max_scanline` count
    pub fn execute(
        &mut self,
        tx: mpsc::Sender<Message>,
        cpu_mmu: Arc<Mutex<CpuMmu>>,
        sync_cycles: Arc<(Mutex<bool>, Mutex<bool>, AtomicUsize, Condvar, Condvar)>,
    ) -> Result<(), PpuError> {
        // We let the cpu start
        let (lock, dma_lock, cpu_cycles, condvar, dma_cond) = &*sync_cycles;
        // The PPU renders 262 scanlines per frame.
        const SCANLINES_IN_A_FRAME: usize = 262;
        // Each scanline lasts for 341 PPU clock cycles. Each clock cycles
        // producing one pixel.
        const PPU_CYCLE_PER_SCANLINE: usize = 341;

        println!("here_ppu");
        // Let render 10k frames
        let frames_to_render = 1000000;
        for frame_count in 0..frames_to_render {
            println!("here_ppu {:?} {:#?} cpu {:?}", frame_count, self.cycles,
                cpu_cycles.load(Ordering::SeqCst));
            while (self.scanline + 1) % SCANLINES_IN_A_FRAME != 0 {
                //println!("here_ppu 3 {:#?}", self.cycles);
                // Figure out in which scanline we are
                match self.scanline {
                    // These are the visible scanlines, which contain the
                    // graphics to be displayed on the screen. During these
                    // scanlines, the PPU is busy fetching data, so the
                    // program should not access PPU memory during this time,
                    // unless rendering is turned off.
                    0..=239 => {
                        // 1. Check the PPUMASK to see if rendering is enabled
                        // or not.
                        {
                            let mut cpu_mmu = cpu_mmu.lock().unwrap();

                            let render_background = self.ppu_mask
                                .render_background(&mut *cpu_mmu)
                                .ok_or(PpuError::CannotGetPpuMask)?;
                                //std::process::exit(1);
                            let render_sprites = self.ppu_mask
                                .render_sprites(&mut *cpu_mmu)
                                .ok_or(PpuError::CannotGetPpuMask)?;
                        }
                        // 2. Read about cycles.
                        while (self.cycles + 1) % PPU_CYCLE_PER_SCANLINE != 0 {
                            match self.cycles % PPU_CYCLE_PER_SCANLINE {
                                // This is an idle cycle.
                                0 => {}
                                1..=256 => {
                                    // The data for each tile is fetched during
                                    // this phase. Each memory access takes
                                    // 2 PPU cycles to complete and 4 accesse
                                    // must be completed per tile
                                    // 1. Nametable byte
                                    // 2. Attribute table byte
                                    // 3. Pattern table tile low
                                    // 4. Pattern table tile high (+8 bytes
                                    // from pattern table tile low)

                                    // OAM sprite evaluation begins at tick
                                    // 65 of the visible scanline.
                                    // The value of `OamAddr` at this tick
                                    // determines the starting address for
                                    // sprite evaluation for this scanline,
                                    // whic can cause the sprite at `OamAddr`
                                    // to be treated as it was sprite 0, both
                                    // for `sprite-0 hit` and priority.
                                }
                                257..=320 => {
                                    // OamAddr is set to 0 during this ticks.
                                    // This also means that at the end of a
                                    // normal complete rendered frame,
                                    // `OamAddr` will always have returned at 0.
                                    {
                                        let mut cpu_mmu =
                                            cpu_mmu.lock().unwrap();
                                        self.oam_addr
                                            .set(&mut *cpu_mmu, 0)?;
                                    }
                                }
                                321..=336 => {
                                }
                                337..=340 => {
                                }
                                _ => unreachable!(),
                            }
                            self.sync_cycles_with_cpu(sync_cycles.clone());
                            // While we still have to catch up, we are catching up
                            // Normal PPU operations here
                            self.cycles += 1
                        }
                    }
                    // The PPU just idles during this scanline. Even though
                    // accessing PPU memory from the program would be safe here,
                    // the VBlank flag isn't set until !after! this scanline
                    240 => {
                        while (self.cycles + 1) % PPU_CYCLE_PER_SCANLINE != 0 {
                            self.sync_cycles_with_cpu(sync_cycles.clone());
                            // While we still have to catch up, we are catching up
                            // Normal PPU operations here
                            self.cycles += 1
                        }
                    }
                    // The VBlank flag of the PPU is set at tick 1 (the second
                    // tick) of scanline 241, where the VBlank NMI also occurs.
                    // The PPU makes no memory accesses during these scanlines,
                    // so PPU memory can be freely accessed by the program.
                    241..=260 => {
                        while (self.cycles + 1) % PPU_CYCLE_PER_SCANLINE != 0 {
                            self.sync_cycles_with_cpu(sync_cycles.clone());
                            // While we still have to catch up, we are catching up
                            // Normal PPU operations here
                            self.cycles += 1
                        }
                    }
                    // This is a dummy scanline, whose sole purpose is to
                    // fill the shift registers with the data for the first 2
                    // tiles of the next scanline.
                    // Although no pixels are rendered for this scanline, the
                    // PPU still makes the same memory accesses it would for a
                    // regular scanline, using whatever the current value of
                    // the PPU's V register is, and for the sprite fetches,
                    // whatever data is currently in secondary OAM (e.g., the
                    // results from scanline 239's sprite evaluation from the
                    // previous frame).
                    261 => {
                        while (self.cycles + 1) % PPU_CYCLE_PER_SCANLINE != 0 {
                            self.sync_cycles_with_cpu(sync_cycles.clone());
                            // While we still have to catch up, we are catching up
                            // Normal PPU operations here
                            self.cycles += 1
                        }
                    }
                    _ => unreachable!(),
                };
                self.sync_cycles_with_cpu(sync_cycles.clone());
                // Go to the next cycle count set
                self.cycles += 1;
                // Go to the next scanline
                self.scanline += 1;
            }
            assert!(self.scanline == (SCANLINES_IN_A_FRAME - 1));
            self.scanline = 0;
        }
        Ok(())
    }

    fn sync_cycles_with_cpu(
        &mut self,
        sync_cycles: Arc<(Mutex<bool>, Mutex<bool>, AtomicUsize, Condvar, Condvar)>
    ) {
        let (lock, dma_lock, cpu_cycles, cond_var, dma_cond) = &*sync_cycles;

        {
            // Since `DMA` lock is the first lock that can always occur, we treat
            // it him first
            let mut copy_dma = dma_lock.lock().unwrap();

            if *copy_dma == true {
                // 1.Copy DMA from CPU over to OAM
                println!("We are copying DMA...");
                *copy_dma = false;
            }

        }
        // 2.Notify the threads we have copied the DMA over. This notify has
        // to take place after we have drop the lock, such that the other
        // threads can acquire it.
        dma_cond.notify_all();

        // Tread the cycle synchronization
        while cpu_cycles.load(Ordering::SeqCst) * 3 <= self.cycles {
            // After acquiring this lock, we know it is time to execute and the
            // CPU waits for us
            let mut is_synced = lock.lock().unwrap();
            // We mark the fact that we synced
            *is_synced = true;
            // At this point, we have caught up with the CPU and we can wake
            // the CPU to continue its execution
            cond_var.notify_all();
            println!("[PPU is sync] Cpu cycles: {:?} -> Ppu cycles: {:?}",
                cpu_cycles.load(Ordering::SeqCst),
                self.cycles,
            );

            // After we have notified all, we wait until we are notified that
            // we are out of sync again
            while *is_synced {
                is_synced = cond_var.wait(is_synced).unwrap();
            }
            println!("[PPU is NOT sync] Cpu cycles: {:?} -> Ppu cycles: {:?}",
                cpu_cycles.load(Ordering::SeqCst),
                self.cycles,
            );
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

#[derive(Debug)]
pub enum PpuError {
    CpuMmuError(CpuMmuError),
    CannotGetPpuMask,
}

impl From<CpuMmuError> for PpuError {
    fn from(e: CpuMmuError) -> Self {
        Self::CpuMmuError(e)
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
