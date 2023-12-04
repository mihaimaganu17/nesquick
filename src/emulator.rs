mod mmu;
mod cpu;

use mmu::{CpuMmu, CpuMmuError};
use cpu::{Cpu, CpuError};
use crate::nes::INes;

pub struct Emulator {
    cpu_mmu: CpuMmu,
    cpu: Cpu,
}

impl Emulator {
    pub fn new() -> Self {
        Emulator {
            cpu_mmu: CpuMmu::with_size(2_usize.pow(16)),
            cpu: Cpu::power_up(),
        }
    }

    pub fn load_nes(&mut self, nes: INes) -> Result<(), EmulatorError> {
        // Load the cpu memory
        self.cpu_mmu.set_bytes(0x8000, nes.prg_rom())?;

        Ok(())
    }

    pub fn execute(&mut self) -> Result<(), EmulatorError> {
        // Get the address of the entrypoint
        let entrypoint = self
            .cpu_mmu
            .read_u16_le(0xFFFC)
            .ok_or(EmulatorError::CannotReadEntrypoint)?;

        // Move the pc counter there
        self.cpu.set_pc(entrypoint);

        // Execute instructions
        self.cpu.execute(&mut self.cpu_mmu)?;

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
    use crate::nes::INes;
    use crate::reader::Reader;
    use crate::emulator::Emulator;

    #[test]
    fn emu_cpu_mmu() {
        let path = "testdata/cpu_dummy_reads.nes";
        let data = std::fs::read(path).expect("Failed to read file from disk");
        let mut reader = Reader::new(data);
        let ines = INes::parse(&mut reader).expect("Failed to parse INes");

        let mut emu = Emulator::new();
        emu.load_nes(ines).expect("Failed to load file in Emulator");
        emu.execute().expect("Failed to execute emulator");
    }
}
