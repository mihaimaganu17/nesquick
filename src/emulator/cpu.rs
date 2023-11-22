//! Module representing a NES 6502 CPU(without a decimal mode)

use crate::emulator::CpuMmu;

/// Represents an 8-bit 6502 microprocessor. This CPU utilizes a 16-bit memory
/// address space, meaning there are 2^16 bytes available for memory addresses,
/// 0x0000 to 0xFFFF.
// The CPU memory is actualy stored in the `Emulator` structure from
// src/emulator.rs
/// Every execution cycle, the CPU will fetsch an 8-bit operation code from
/// this memory space. Many of these assembly instructions require an operand
/// to work with, and this operand is indicated by the 1 or 2 bytes immediately
/// following the opcode in memory. Some instruction however do no require any
/// operand and the opcode is sufficient
/// Therefore, instructions have variable lengths and will require 1, 2 or 3
/// bytes of data.
///
/// When the CPU fetches an opcode, besides decoding the assembly instruction,
/// it will also decode and addressing mode that will determine the number
/// of bytes needed for operands. These addressing modes are described below
#[derive(Debug)]
pub struct Cpu {
    // Accumulator is byte-wide and along with arithmetic logic unit(ALU),
    // supports using the status register for carrying, overflow detection, and
    // so on
    acc: u8,
    // X and Y are byte_wide and used for several addressing modes. Not being
    // the accumulator, they have limited addressing modes themselves when
    // loading and saving
    x: u8,
    y: u8,
    // Program counter, 2-bytes and support 65536 direct (unbanked) memory
    // locations, however not all values are sent to the cartrige.
    pc: u16,
    // Stack pointer is byte-wide and it indexes into a 256-byte stack at
    // $0100 - $01FF
    s: u8,
    // Status register, used by the ALU, but is byte-wide.
    p: StatusRegister,
}

#[derive(Debug)]
pub struct StatusRegister {
    // Bit 0
    pub carry: bool,
    // Bit 1
    // After most instructions that have a value result, this flag will either
    // be set of cleared based on whether or not that value is equal to zero.
    pub zero: bool,
    // Bit 2
    // Interrupt disable
    pub int_disable: bool,
    // Bit 3
    // On the NES, decimal mode is disable and so this flag has no effect.
    pub decimal: bool,
    // Bit 4, the B flag
    pub b_flag: bool,
    // Bit 5, always 1
    pub always_1: bool,
    // Bit 6, Overflow
    pub overflow: bool,
    // Bit 7, Negative
    pub negative: bool,
}

impl From<u8> for StatusRegister {
    fn from(value: u8) -> Self {
        Self {
            carry: Self::u8_to_bool(value & 1),
            zero: Self::u8_to_bool(value >> 1 & 1),
            int_disable: Self::u8_to_bool(value >> 2 & 1),
            decimal: Self::u8_to_bool(value >> 3 & 1),
            b_flag: Self::u8_to_bool(value >> 4 & 1),
            always_1: Self::u8_to_bool(value >> 5 & 1),
            overflow: Self::u8_to_bool(value >> 6 & 1),
            negative: Self::u8_to_bool(value >> 7 & 1),
        }
    }
}

impl StatusRegister {
    // Convert any u8 into a boolean
    fn u8_to_bool(value: u8) -> bool {
        if value != 0 { true } else { false }
    }
    fn bool_to_u8(value: bool) -> u8 {
        if value == true { 1 } else { 0 }
    }

    /// Return the register as an u8
    pub fn as_u8(&self) -> u8 {
        Self::bool_to_u8(self.carry) |
            Self::bool_to_u8(self.zero) << 1 |
            Self::bool_to_u8(self.int_disable) << 2 |
            Self::bool_to_u8(self.decimal) << 3 |
            Self::bool_to_u8(self.b_flag) << 4 |
            Self::bool_to_u8(self.always_1) << 5 |
            Self::bool_to_u8(self.overflow) << 6 |
            Self::bool_to_u8(self.negative) << 7
    }
}

impl Cpu {
    /// Initialize the CPU with the state it has when the NES is powered up.
    // This initialization is from a US (NTSC) NES, original front-loading
    // design, RP2A03G CPU chi, NES-CPU-07 main board revision.
    pub fn power_up() -> Cpu {
        Self {
            p: 0x34.into(),
            acc: 0,
            x: 0,
            y: 0,
            s: 0xfd,
            pc: 0x00,
        }
    }

    /// Sets the current program counter to a new value
    pub fn set_pc(&mut self, pc: u16) {
        self.pc = pc;
    }

    /// Read and execute instructions existent in the given memory, at the
    /// current program counter
    // Note: We counld convert memory into a trait and then have CpuMmu
    // implement that trait
    pub fn execute(&mut self, memory: &mut CpuMmu) -> Result<(), CpuError> {
        // Go until death
        while let Ok(inst) = Instruction::from_pc(&mut self.pc, memory) {
            println!("Pc: {:?} -> Inst {inst:?}", self.pc);
        }
        Ok(())
    }
}

/// Represents a NES 6502 Instruction
#[derive(Debug)]
pub enum Instruction {
    Sed(Sed),
}

#[derive(Debug)]
pub enum InstructionError {
    OverflowPc,
}

impl Instruction {
    /// Reads and decodes a single instruction located at `pc` in the given `mmu`
    pub fn from_pc(
        pc: &mut u16,
        mmu: &mut CpuMmu
    ) -> Result<Self, InstructionError> {
        *pc = pc
            .checked_add(std::mem::size_of::<u8>() as u16)
            .ok_or(InstructionError::OverflowPc)?;
        Ok(Self::Sed(Sed))
    }
}

#[derive(Debug)]
pub struct Sed;

/// When the CPU fetches an opcode, besides decoding the assembly instruction,
/// it will also decode and addressing mode that will determine the number
/// of bytes needed for operands. There are 13 such addresing modes.
#[derive(Debug)]
pub enum AddrMode {
    // For many 6502 instructions the source and destination of the information
    // to be manipulated is implied directly by the function of the instruction
    // itself and no further operand needs to be specified. Operations like
    // 'Clear Carry Flag' (CLC) and 'Return from Subroutine' (RTS) are
    // implicit.
    Implied,
}

#[derive(Debug)]
pub enum CpuError {
}
