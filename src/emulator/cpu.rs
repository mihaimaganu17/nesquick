//! Module representing a NES 6502 CPU(without a decimal mode)
mod opcode;

use crate::emulator::CpuMmu;

/// Represents an 8-bit 6502 microprocessor. This CPU utilizes a 16-bit memory
/// address space, meaning there are 2^16 bytes available for memory addresses,
/// 0x0000 to 0xFFFF.
// The CPU memory is actualy stored in the `Emulator` structure from
// src/emulator.rs
/// Every execution cycle, the CPU will fetch an 8-bit operation code from
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
pub enum Idx {
    X,
    Y,
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
pub struct Instruction {
    opcode: Opcode,
    addr_mode: AddrMode,
    cycles: u8,
}

#[derive(Debug)]
pub enum Opcode {
    Sed(Sed),
    Sei(Sei),
    Cld(Cld),
    // LDX Immediate,
    LdxI(Ldx),
    // LDX Zero Page,
    LdxZp(Ldx),
    // LDX Zero Page, Y
    LdxZpY(Ldx),
    // LDX Absolute
    LdxA(Ldx),
    // Ldx Absolute, Y
    LdxAY(Ldx),
    // LDY Immediate,
    LdyI(Ldy),
    // LDY Zero Page,
    LdyZp(Ldy),
    // LDY Zero Page, X
    LdyZpX(Ldy),
    // LDY Absolute
    LdyA(Ldy),
    // LdY Absolute, X
    LdyAX(Ldy),
    // Transfer X to Stack Pointer
    Txs(Txs),
    // LDA Immediate,
    LdaI(Lda),
    // LDA Zero Page,
    LdaZp(Lda),
    // LDA Zero Page, X
    LdaZpX(Lda),
    // LDA Absolute
    LdaA(Lda),
    // LDA Absolute, X
    LdaAX(Lda),
    // LDA Absolute, Y
    LdaAY(Lda),
    // LDA Indirect, X
    LdaIX(Lda),
    // LDA Indirect, Y
    LdaIY(Lda),
    // LDA Zero Page,
    StaZp(Sta),
    // STA Zero Page, X
    StaZpX(Sta),
    // STA Absolute
    StaA(Sta),
    // STA Absolute, X
    StaAX(Sta),
    // STA Absolute, Y
    StaAY(Sta),
    // STA Indirect, X
    StaIX(Sta),
    // STA Indirect, Y
    StaIY(Sta),
    // STX Zero Page
    StxZp(Stx),
    // STX Zero Page, Y
    StxZpY(Stx),
    // STX Absolute
    StxA(Stx),
    // DEY - Decrement Y Register
    Dey(Dey),
    // BNE - Branch if Not Equal
    Bne(Bne),
}

#[derive(Debug)]
pub enum InstructionError {
    OverflowPc,
    FailedToAccessPc(u16),
    InvalidOpcode(u8),
    InvalidInstruction(u8),
}

impl Instruction {
    /// Reads and decodes a single instruction located at `pc` in the given `mmu`
    pub fn from_pc(
        pc: &mut u16,
        mmu: &mut CpuMmu
    ) -> Result<Self, InstructionError> {
        // Read the byte at the program counter
        let Some(byte) = mmu.read_u8(usize::from(*pc)) else {
            return Err(InstructionError::FailedToAccessPc(*pc))
        };

        println!("Byte {byte:x}");

        // Advance the program counter
        *pc = pc
            .checked_add(std::mem::size_of::<u8>() as u16)
            .ok_or(InstructionError::OverflowPc)?;

        let inst = match byte {
            opcode::SED => {
                Instruction {
                    opcode: Opcode::Sed(Sed),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::SEI => {
                Instruction {
                    opcode: Opcode::Sei(Sei),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::CLD => {
                Instruction {
                    opcode: Opcode::Cld(Cld),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::LDX_I => {
                // We also have to read the next byte, which is our operand
                let Some(next_byte) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::LdxI(Ldx),
                    addr_mode: AddrMode::Immediate(next_byte),
                    cycles: 2,
                }
            }
            opcode::LDY_I => {
                // We also have to read the next byte, which is our operand
                let Some(next_byte) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::LdyI(Ldy),
                    addr_mode: AddrMode::Immediate(next_byte),
                    cycles: 2,
                }
            }
            opcode::TXS => {
                Instruction {
                    opcode: Opcode::Txs(Txs),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::LDA_I => {
                // We also have to read the next byte, which is our operand
                let Some(next_byte) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::LdaI(Lda),
                    addr_mode: AddrMode::Immediate(next_byte),
                    cycles: 2,
                }
            }
            opcode::STA_A => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u16_le(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u16>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::StaA(Sta),
                    addr_mode: AddrMode::Absolute(addr),
                    cycles: 4,
                }
            }
            opcode::STA_ZP => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::StaZp(Sta),
                    addr_mode: AddrMode::ZeroPage(addr),
                    cycles: 3,
                }
            }
            opcode::STX_ZP => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::StxZp(Stx),
                    addr_mode: AddrMode::ZeroPage(addr),
                    cycles: 3,
                }
            }
            opcode::DEY=> {
                Instruction {
                    opcode: Opcode::Dey(Dey),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::STA_I_Y => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::StaIY(Sta),
                    addr_mode: AddrMode::IndirectIndexed(Idx::Y, addr),
                    cycles: 6,
                }
            }
            opcode::BNE => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signe integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bne(Bne),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            _ => return Err(InstructionError::InvalidOpcode(byte)),
        };
        Ok(inst)
    }
}

#[derive(Debug)]
pub struct Sed;
#[derive(Debug)]
pub struct Sei;
#[derive(Debug)]
pub struct Cld;
#[derive(Debug)]
pub struct Ldx;
#[derive(Debug)]
pub struct Ldy;
#[derive(Debug)]
pub struct Txs;
#[derive(Debug)]
pub struct Lda;
#[derive(Debug)]
pub struct Sta;
#[derive(Debug)]
pub struct Stx;
#[derive(Debug)]
pub struct Dey;
#[derive(Debug)]
pub struct Bne;

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
    // Immediate addressing allows the programmer to directly specify an 8 bit
    // constant within the instruction. It is indicated by a '#' symbol
    // followed by an numeric expression.
    // When decoding, the immediate numerical byte is followed directly after
    // the instruction byte
    Immediate(u8),
    // Instructions using absolute addressing contain a full 16 bit address to
    // identify the target location.
    Absolute(u16),
    // An instruction using zero page addressing mode has only an 8 bit address
    // operand. This limits it to addressing only the first 256 bytes of memory
    // (e.g. $0000 to $00FF) where the most significant byte of the address is
    // always zero. In zero page mode only the least significant byte of the
    // address is held in the instruction making it shorter by one byte
    // (important for space saving) and one less memory fetch during execution
    // (important for speed).
    //
    // An assembler will automatically select zero page addressing mode if the
    // operand evaluates to a zero page address and the instruction supports
    // the mode (not all do).
    // Zero page is wrapping aroung 256. Ex: (223 + 130) MOD 256 = 97;
    ZeroPage(u8),
    // Indirect Indexed
    // Indirect indexed addressing is the most common indirection mode used
    // on the 6502. In instruction contains the zero page location of the least
    // significant byte of 16 bit address. The Y register is dynamically added
    // to this value to generated the actual target address for operation.
    IndirectIndexed(Idx, u8),
    // Relative
    // Relative addressing mode is used by branch instructions
    // (e.g. BEQ, BNE, etc.) which contain a signed 8 bit relative offset
    // (e.g. -128 to +127) which is added to program counter if the condition
    // is true. As the program counter itself is incremented during instruction
    // execution by two the effective address range for the target instruction
    // must be with -126 to +129 bytes of the branch.
    Relative(i8),
}

#[derive(Debug)]
pub enum CpuError {
}

mod utils {
    /// Converts a i8 to a u8 without data loss through pointer transmuting
    pub fn u8_to_i8(value: u8) -> i8 {
        unsafe { std::mem::transmute::<u8, i8>(value) }
    }
}
