mod cpu;
mod mmu;
mod ppu;

use crate::nes::INes;
use cpu::{Cpu, CpuError};
use mmu::{CpuMmu, CpuMmuError, PpuMmu, PpuMmuError};
use ppu::{Ppu, PpuEffect};
use std::{
    sync::{Arc, Mutex, mpsc},
    thread,
};

pub struct Emulator {
    cpu: Cpu,
    // Cpu's Memory unit, that needs to be accessed by both the CPU and the PPU
    // Sinces that is the case and the access needs to be mutable, we will
    // wrap it in an Arc and Mutex to be able to share it between threads.
    cpu_mmu: Arc<Mutex<CpuMmu>>,
    ppu: Ppu,
    ppu_mmu: PpuMmu,
}

impl Emulator {
    pub fn new() -> Self {
        let cpu = Cpu::power_up();
        let cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));
        let ppu = Ppu::power_up(cpu_mmu.clone());
        let ppu_mmu = PpuMmu::default();

        Emulator {
            cpu,
            cpu_mmu,
            ppu,
            ppu_mmu,
        }
    }

    pub fn load_nes(&mut self, nes: INes) -> Result<(), EmulatorError> {
        // Load CPU memory
        {
            // Acquire a lock to the CPU memory unit
            let mut cpu_mmu = self.cpu_mmu.lock().unwrap();
            // Load the cpu memory
            cpu_mmu.set_bytes(0x8000, nes.prg_rom())?;
        }

        // Load PPU memory
        {
            // Acquire a lock to the CPU memory unit
            let mut ppu_mmu = &mut self.ppu_mmu;
            // Load the cpu memory
            ppu_mmu.set_bytes(0x0000, nes.chr_rom())?;

            // Following snippet renders the PPU tiles from the pattern tables
            // as bits in a terminal

            // Get the bytes of the pattern table
            let pattern_table = ppu_mmu.pattern_table(0).unwrap();

            for tile_idx in 0..(0x1000/16) {
                let start = tile_idx * 16;
                let end = (tile_idx + 1) * 16;
                println!("Start Of Tile: {start} -> {end}");
                for pos in start..(end-8) {
                    let plane_0_byte = pattern_table[pos];
                    let plane_1_byte = pattern_table[pos + 8];
                    for bit in (1..8).rev() {
                        let res = (plane_0_byte >> bit) & 1
                            | ((plane_1_byte >> bit) & 1) << 1;
                        print!("{:02b}", res);
                    }
                    println!();
                    //let pixel = pattern_table[plane_0_byte] 
                    //print!("{:08b}", pattern_table[pixel_byte]);
                }

                println!("End Of Tile");
            }
        }

        Ok(())
    }

    pub fn execute(mut self) -> Result<(), EmulatorError> {
        // Get the address of the entrypoint
        let entrypoint = {
            // Acquire a lock to the CPU memory unit. The lock will drop at the
            // end of the scope
            let cpu_mmu = self.cpu_mmu.lock().unwrap();

            cpu_mmu
                .read_u16_le(0xFFFC)
                .ok_or(EmulatorError::CannotReadEntrypoint)?
        };

        // Move the pc counter there
        self.cpu.set_pc(entrypoint);

        // Create a multi-producer single-consumer channel that with the
        // following characteristics
        // Producers:
        // - CPU
        // - PPU
        // Receiver
        // - Emulator
        let (tx, rx) = mpsc::channel();

        let cpu_thread_handle = {
            // Clone the CPU MMU unit in order to send it to the CPU
            let cpu_mmu = self.cpu_mmu.clone();
            // Clone the transmitter
            let tx = tx.clone();

            thread::spawn(move || -> Result<(), CpuError> {
                self.cpu.execute(cpu_mmu, tx)
            })
        };

        while let Ok(message) = rx.recv() {
            match message {
                Message::Cycles(cycles) => {
                    // We wait until we pass 2 important CPU milestones, to mimic the
                    // behaviour of the PPU, which is:

                    // We let 27484 cycles pass such that we set the PPUSTATUS again to
                    // mimick the PPU hardware behaviour
                    if cycles < 27384 { continue; }
                    {
                        let mut cpu_mmu = self.cpu_mmu.clone();
                        self.ppu.set_vblank(cpu_mmu);
                    }

                    // We let 57165 cycles pass such that we set the PPUSTATUS again to
                    // mimick the PPU hardware behaviour
                    if cycles < 57165 { continue; }
                    {
                        let mut cpu_mmu = self.cpu_mmu.clone();
                        self.ppu.set_vblank(cpu_mmu);
                    }
                }
                Message::NesEffect(effect) => {
                    match effect {
                        NesEffect::Ppu(ppu_effect) => {
                            match ppu_effect {
                                PpuEffect::PpuAddrWrite => {
                                    println!("addr_write");
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        let res = cpu_thread_handle.join();

        Ok(())
    }
}

#[derive(Debug)]
pub enum NesEffect {
    Ppu(PpuEffect),
    None,
}

#[derive(Debug)]
pub enum Message {
    NesEffect(NesEffect),
    Cycles(usize),
}

#[derive(Debug)]
pub enum EmulatorError {
    CpuError(CpuError),
    CpuMmuError(CpuMmuError),
    PpuMmuError(PpuMmuError),
    CannotReadEntrypoint,
}

impl From<CpuMmuError> for EmulatorError {
    fn from(err: CpuMmuError) -> Self {
        Self::CpuMmuError(err)
    }
}

impl From<PpuMmuError> for EmulatorError {
    fn from(err: PpuMmuError) -> Self {
        Self::PpuMmuError(err)
    }
}

impl From<CpuError> for EmulatorError {
    fn from(err: CpuError) -> Self {
        Self::CpuError(err)
    }
}

#[cfg(test)]
mod test {
    use crate::emulator::Emulator;
    use crate::nes::INes;
    use crate::reader::Reader;

    #[test]
    fn emu_cpu_mmu() {
        let path = "testdata/cpu_dummy_reads.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        let mut emu = Emulator::new();
        emu.load_nes(ines).expect("Failed to load file in Emulator");
        //emu.execute().expect("Failed to execute emulator");
    }
}
