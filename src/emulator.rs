mod cpu;
mod mmu;
mod ppu;

use crate::nes::INes;
use cpu::{Cpu, CpuError};
use mmu::{CpuMmu, CpuMmuError, PpuMmu};
use ppu::{Ppu};
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
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));
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
        // Acquire a lock to the CPU memory unit
        let mut cpu_mmu = self.cpu_mmu.lock().unwrap();
        // Load the cpu memory
        cpu_mmu.set_bytes(0x8000, nes.prg_rom())?;

        Ok(())
    }

    pub fn execute(mut self) -> Result<(), EmulatorError> {
        // Get the address of the entrypoint
        let entrypoint = {
            // Acquire a lock to the CPU memory unit. The lock will drop at the
            // end of the scope
            let mut cpu_mmu = self.cpu_mmu.lock().unwrap();

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
        //let (tx, rx) = mpsc::channel();

        let mut cpu_mmu = self.cpu_mmu.clone();

        let cpu_thread_handle = thread::spawn(move || -> Result<(), CpuError> {
            self.cpu.execute(cpu_mmu)
        });

        let res = cpu_thread_handle.join();

        Ok(())
    }
}

#[derive(Debug)]
pub enum EmulatorError {
    CpuError(CpuError),
    CpuMmuError(CpuMmuError),
    CannotReadEntrypoint,
}

impl From<CpuMmuError> for EmulatorError {
    fn from(err: CpuMmuError) -> Self {
        Self::CpuMmuError(err)
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
        let path = "testdata/color_test.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        let mut emu = Emulator::new();
        emu.load_nes(ines).expect("Failed to load file in Emulator");
        emu.execute().expect("Failed to execute emulator");
    }
}
