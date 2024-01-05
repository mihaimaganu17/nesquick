//! Module representing a NES 6502 CPU(without a decimal mode)
mod opcode;

use crate::emulator::{CpuMmu, CpuMmuError};
use std::sync::{Arc, Mutex, mpsc};

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
    // How many cycles have passed so far
    cycles: usize,
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
        if value != 0 {
            true
        } else {
            false
        }
    }
    fn bool_to_u8(value: bool) -> u8 {
        if value == true {
            1
        } else {
            0
        }
    }

    /// Return the register as an u8
    pub fn as_u8(&self) -> u8 {
        Self::bool_to_u8(self.carry)
            | Self::bool_to_u8(self.zero) << 1
            | Self::bool_to_u8(self.int_disable) << 2
            | Self::bool_to_u8(self.decimal) << 3
            | Self::bool_to_u8(self.b_flag) << 4
            | Self::bool_to_u8(self.always_1) << 5
            | Self::bool_to_u8(self.overflow) << 6
            | Self::bool_to_u8(self.negative) << 7
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
            cycles: 0,
        }
    }

    /// Sets the current program counter to a new value
    pub fn set_pc(&mut self, pc: u16) {
        self.pc = pc;
    }

    /// Returns the cycle count since the CPU power on
    pub fn cycles(&self) -> usize {
        self.cycles
    }

    /// Returns the status register
    pub fn p(&self) -> &StatusRegister {
        &self.p
    }

    /// Reset status register to 0
    pub fn reset_p(&mut self) {
        self.p = StatusRegister::from(0);
    }

    // Push a `value` onto the stack located in `memory`
    fn push(&mut self, memory: &mut CpuMmu, value: u8) -> Option<()> {
        // Get a reference to our stack
        let mut stack = memory.stack_mut()?;
        // We index into the stack using the `s` register
        let memory_value = stack.get_mut(self.s as usize).unwrap();

        // Update the value in memory
        *memory_value = value;
        // Update the stack pointer, wrapping it
        self.s = self.s.wrapping_sub(1);

        Some(())
    }

    // Pop a value from the stack located in `memory`
    fn pop(&mut self, memory: &mut CpuMmu) -> Option<u8> {
        // Get a reference to our stack
        if let Some(stack) = memory.stack_mut() {
            // Bump the stack pointer to get the last value, wrapping it
            self.s = self.s.wrapping_add(1);
            // We index into the stack using the `s` register
            if let Some(memory_value) = stack.get(self.s as usize) {
                Some(*memory_value)
            } else {
                None
            }
        } else {
            None
        }
    }

    // Push the current program counter onto the stack
    fn push_pc(&mut self, memory: &mut CpuMmu) {
        let pcl = self.pc & 0xFF;
        let pch = (self.pc >> 8) & 0xFF;

        self.push(memory, pch as u8);
        self.push(memory, pcl as u8);
    }

    // Pop 2 values from the stack and store them into the program counter
    fn pop_pc(&mut self, memory: &mut CpuMmu) -> Option<()> {
        let pcl = self.pop(memory)?;
        let pch = self.pop(memory)?;

        self.pc = ((pch as u16) << 8) | (pcl as u16);
        Some(())
    }

    /// Read and execute instructions existent in the given memory, at the
    /// current program counter
    // Note: We counld convert memory into a trait and then have CpuMmu
    // implement that trait.
    pub fn execute(
        &mut self,
        memory: Arc<Mutex<CpuMmu>>,
        tx: mpsc::Sender<usize>,
    ) -> Result<(), CpuError> {
        // Go until death
        while let Ok(inst) = Instruction::from_pc(&mut self.pc, memory.clone()) {
            // Aquire the memory mutex, in order to execute any potential
            // instructions that need the memory.
            // The lock is automatically dropped(fancy) at the end of the
            // enclosing scope. In our case at the end of each while iteration
            // loop
            let mut memory = memory.lock().unwrap();
            println!("{inst:?}");
            match inst.opcode() {
                Opcode::Sei(_) => {
                    // Set the interrupt disable flag to one.
                    self.p.int_disable = true;
                }
                Opcode::Sed(_) => {
                    // Set the decimal flag to one.
                    self.p.decimal = true;
                }
                Opcode::Sec(_) => {
                    // Set the carry flag
                    self.p.carry = true;
                }
                Opcode::Clc(_) => {
                    // Clear carry flag
                    self.p.carry= false;
                }
                Opcode::Cld(_) => {
                    // Clear decimal mode
                    self.p.decimal = false;
                }
                Opcode::Cli(_) => {
                    // Clear interrupt disable flag
                    self.p.int_disable= false;
                }
                Opcode::Clv(_) => {
                    // Clear overflow flag
                    self.p.overflow = false;
                }
                Opcode::Cmp(_) => {
                    // Load a byte of memory into the X register.
                    let value = match inst.addr_mode() {
                        AddrMode::Immediate(imm) => *imm,
                        _ => todo!(),
                    };
                    println!("{}", self.acc);
                    println!("{}", value);

                    // Get the result wrapping at the limits
                    let tmp = self.acc.wrapping_sub(value);
                    println!("{}", tmp);

                    self.p.zero = tmp == 0;
                    self.p.negative = ((tmp >> 7) & 1) == 1;
                    self.p.carry = value <= self.acc;
                }
                Opcode::Ldx(_) => {
                    // Load a byte of memory into the X register.
                    let value = match inst.addr_mode() {
                        AddrMode::Immediate(imm) => *imm,
                        AddrMode::ZeroPage(addr) => {
                            let zp_addr = *addr as usize;
                            let value = memory
                                .read_u8(zp_addr)
                                .ok_or(CpuError::MmuReadError(zp_addr))?;
                            value
                        }
                        _ => todo!(),
                    };
                    // Set X register to that value
                    self.x = value;
                    // Set the flags accordingly
                    self.p.zero = self.x == 0;
                    self.p.negative = (self.x >> 7 & 1) == 1;
                }
                Opcode::Txs(_) => {
                    self.s = self.x;
                }
                Opcode::Lda(_) => {
                    // Load a byte of memory into the X register.
                    let value = match inst.addr_mode() {
                        AddrMode::Immediate(imm) => *imm,
                        AddrMode::ZeroPage(addr) => {
                            let zp_addr = *addr as usize;
                            let value = memory
                                .read_u8(zp_addr)
                                .ok_or(CpuError::MmuReadError(zp_addr))?;
                            value
                        }
                        _ => todo!(),
                    };
                    // Set X register to that value
                    self.acc = value;
                    // Set the flags accordingly
                    self.p.zero = self.acc == 0;
                    self.p.negative = (self.acc >> 7 & 1) == 1;
                }
                Opcode::Ldy(_) => {
                    // Load a byte of memory into the X register.
                    let value = match inst.addr_mode() {
                        AddrMode::Immediate(imm) => imm,
                        _ => todo!(),
                    };
                    // Set Y register to that value
                    self.y = *value;
                    // Set the flags accordingly
                    self.p.zero = self.y == 0;
                    self.p.negative = (self.y >> 7 & 1) == 1;
                }
                Opcode::Sta(_) => {
                    // Load a byte of memory into the X register.
                    let addr: u16 = match inst.addr_mode() {
                        AddrMode::Absolute(abs_addr) => *abs_addr,
                        AddrMode::ZeroPage(addr) => *addr as u16,
                        AddrMode::IndirectIndexed(_, addr_lo) => {
                            // Convert into a u16 address
                            let read_addr_from = usize::from(*addr_lo as u16);
                            // Read the least significant byte of the 16-bit
                            // address
                            let addr_lo = memory
                                .read_u8(read_addr_from)
                                .ok_or(CpuError::MmuReadError(read_addr_from))?;
                            let addr_lo = addr_lo.wrapping_add(self.y);
                            // Read the most significant byte of the 16-bit
                            // address
                            let addr_hi = memory
                                .read_u8(read_addr_from + 1)
                                .ok_or(CpuError::MmuReadError(read_addr_from))?;
                            let addr = addr_hi as u16 >> 4 | addr_lo as u16;
                            addr
                        }
                        _ => todo!(),
                    };
                    memory.set_bytes(usize::from(addr), &[self.acc])?;
                }
                Opcode::Stx(_) => {
                    // Load a byte of memory into the X register.
                    let addr: u16 = match inst.addr_mode() {
                        AddrMode::Absolute(abs_addr) => *abs_addr,
                        AddrMode::ZeroPage(addr) => *addr as u16,
                        _ => todo!(),
                    };
                    memory.set_bytes(usize::from(addr), &[self.x])?;
                }
                Opcode::Dex(_) => {
                    // Set X register to that value
                    self.x = self.x.wrapping_sub(1);
                    // Set the flags accordingly
                    self.p.zero = self.x == 0;
                    self.p.negative = (self.x >> 7 & 1) == 1;
                }
                Opcode::Dey(_) => {
                    // Set Y register to that value
                    self.y = self.y.wrapping_sub(1);
                    // Set the flags accordingly
                    self.p.zero = self.y == 0;
                    self.p.negative = (self.y >> 7 & 1) == 1;
                }
                Opcode::Inx(_) => {
                    // Set X register to that value
                    self.x = self.x.wrapping_add(1);
                    // Set the flags accordingly
                    self.p.zero = self.x == 0;
                    self.p.negative = (self.x >> 7 & 1) == 1;
                }
                Opcode::Iny(_) => {
                    // Set Y register to that value
                    self.y = self.y.wrapping_add(1);
                    // Set the flags accordingly
                    self.p.zero = self.y == 0;
                    self.p.negative = (self.y >> 7 & 1) == 1;
                }
                Opcode::Bmi(_) => {
                    if self.p.negative {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bpl(_) => {
                    if !self.p.negative {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bcc(_) => {
                    if !self.p.carry {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bcs(_) => {
                    if self.p.carry {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Beq(_) => {
                    if self.p.zero {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bne(_) => {
                    if !self.p.zero {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bvs(_) => {
                    if self.p.overflow {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bvc(_) => {
                    if !self.p.overflow {
                        // For this instruction, typically there should be only
                        // one addressing mode, so we will only use that one
                        if let AddrMode::Relative(addr) = inst.addr_mode() {
                            // Se the program counter. Given we know the
                            // instruction was already read and decoded, we
                            // know that the counter is already to the right
                            // base value.
                            //
                            // Since at the time of this writing, we do not
                            // know how overflow works on the CPU, we just do
                            // a wrapping operation
                            self.pc = self.pc.wrapping_add_signed(*addr as i16);
                        }
                    }
                }
                Opcode::Bit(_) => {
                    // Get the value of the address we want to test
                    let value = match inst.addr_mode() {
                        AddrMode::Absolute(addr) => {
                            let to_read_from = usize::from(*addr);
                            let value = memory
                                .read_u8(to_read_from)
                                .ok_or(CpuError::MmuReadError(to_read_from))?;
                            value
                        }
                        _ => todo!(),
                    };
                    // Do a memory `and` with the accumulator, but do not store
                    // the result.
                    let tmp = value & self.acc;
                    // Fill the appropriate flags
                    self.p.zero = tmp == 0;
                    self.p.negative = (value >> 7 & 1) != 0;
                    self.p.overflow = (value >> 6 & 1) != 0;
                }
                Opcode::Jsr(_) => {
                    match inst.addr_mode() {
                        AddrMode::Absolute(addr) => {
                            // Push the program counter onto the stack
                            self.push_pc(&mut *memory);
                            // Set the new program counter
                            self.pc = *addr;
                        }
                        _ => unreachable!(),
                    }
                }
                Opcode::Rts(_) => {
                    match inst.addr_mode() {
                        AddrMode::Implied => {
                            // Get the program counter from the stack
                            self.pop_pc(&mut *memory);
                        }
                        _ => unreachable!(),
                    }
                }
                Opcode::Adc(_) => {
                    // Get the value we want to subtract from
                    let value = match inst.addr_mode() {
                        AddrMode::Immediate(imm) => *imm,
                        AddrMode::Absolute(addr) => {
                            let addr = *addr as usize;
                            let value = memory.read_u8(addr)
                                .ok_or(CpuError::MmuReadError(addr))?;
                            value
                        }
                        _ => unreachable!(),
                    };
                    self.adc(value);
                }
                Opcode::Sbc(_) => {
                    // Get the value we want to subtract from
                    let value = match inst.addr_mode() {
                        AddrMode::Immediate(imm) => *imm,
                        AddrMode::Absolute(addr) => {
                            let addr = *addr as usize;
                            let value = memory.read_u8(addr)
                                .ok_or(CpuError::MmuReadError(addr))?;
                            value
                        }
                        _ => unreachable!(),
                    };
                    self.adc(!value);
                }
                Opcode::Nop(_) => {}
                Opcode::Tax(_) => {
                    self.x = self.acc;
                    self.p.zero = self.x == 0;
                    self.p.negative = (self.x >> 7) == 1;
                },
                Opcode::Tay(_) => {
                    self.y = self.acc;
                    self.p.zero = self.x == 0;
                    self.p.negative = (self.x >> 7) == 1;
                },
                Opcode::Tsx(_) => {
                    self.x = self.s;
                    self.p.zero = self.x == 0;
                    self.p.negative = (self.x >> 7) == 1;
                },
                Opcode::Txa(_) => {
                    self.acc = self.x;
                    self.p.zero = self.acc == 0;
                    self.p.negative = (self.acc >> 7) == 1;
                },
                Opcode::Txs(_) => {
                    self.s = self.x;
                },
                Opcode::Tya(_) => {
                    self.y = self.acc;
                    self.p.zero = self.y == 0;
                    self.p.negative = (self.y >> 7) == 1;
                },
                _ => todo!(),
            }
            // Add cycles to the CPU
            self.cycles += inst.cycles();

            println!("{:#?}", self);

            // Send the cycles back to the emulator main frame
            tx.send(self.cycles);
        }
        Ok(())
    }

    fn adc(&mut self, value: u8) {
        // Preserver the current accumulator for flags computing
        let old_acc = self.acc;
        let (wrapped_tmp, overflow_tmp) =
            (StatusRegister::bool_to_u8(self.p.carry))
                .overflowing_add(value);
        let (wrapped_tmp2, overflow_tmp2) =
            self.acc.overflowing_add(wrapped_tmp);
        self.acc = wrapped_tmp2;
        // The final carry will either be present in the first
        // addition or the last addition
        self.p.carry = overflow_tmp | overflow_tmp2;
        // Fill the appropriate flags
        self.p.zero = wrapped_tmp == 0;
        self.p.negative = (self.acc >> 7 & 1) != 0;
        self.p.overflow =
            ((old_acc ^ self.acc) & (value ^ self.acc)) >> 7 == 1;
    }
}

/// Represents a NES 6502 Instruction
#[derive(Debug)]
pub struct Instruction {
    opcode: Opcode,
    addr_mode: AddrMode,
    cycles: usize,
}

#[derive(Debug)]
pub enum Opcode {
    // Set the decimal flag
    Sed(Sed),
    // Set the interrupt disable flag.
    Sei(Sei),
    // Set the carry flag.
    Sec(Sec),
    // Clead carry flag
    Clc(Clc),
    // Clead decimal mode
    Cld(Cld),
    // Clead interrupt disable
    Cli(Cli),
    // Clead overflow (V) flag
    Clv(Clv),
    // LDX,
    Ldx(Ldx),
    // LDY Immediate,
    Ldy(Ldy),
    // Load Accumulator,
    Lda(Lda),
    // Store Accumulator,
    Sta(Sta),
    // STX Store X register,
    Stx(Stx),
    // BNE - Branch on Result Minus (if the Negative bit is set)
    Bmi(Bmi),
    // BPL - Branch on result Plus (if the Negative bit is zero)
    Bpl(Bpl),
    // BCC - Branck on Carry Clear
    Bcc(Bcc),
    // BCC - Branck on Carry Set
    Bcs(Bcs),
    // BEQ - Branch on Result Zero (if the Zero flag is 0)
    Beq(Beq),
    // BNE - Branch if Not Equal / Result not zero (if the Zero flag is not 0)
    Bne(Bne),
    // BVS - Branch on Overflow Set (if the overflow (V) flas is set)
    Bvs(Bvs),
    // BVC - Branch on Overflow Clear (if the overflow (V) flas is not set)
    Bvc(Bvc),
    // BIT - Bit test
    Bit(Bit),
    // JSR - Jump to subroutine
    Jsr(Jsr),
    // DEX - Decrement X Register
    Dex(Dex),
    // DEY - Decrement Y Register
    Dey(Dey),
    // INX - Increment X Register
    Inx(Inx),
    // INY - Increment Y Register
    Iny(Iny),
    // RTS - Return from Subroutine
    Rts(Rts),
    // ADC - Add with carry
    Adc(Adc),
    // SBC - Substract with carry
    Sbc(Sbc),
    // CMP - Compare
    Cmp(Cmp),
    // NOP - Not an operation
    Nop(Nop),
    // TAX - Transfer Accumulator to X
    Tax(Tax),
    // TAX - Transfer Accumulator to X
    Tay(Tay),
    // TSX - Transfer Stack Pointer to X
    Tsx(Tsx),
    // TXA - Transfer X to Accumulator
    Txa(Txa),
    // TXS - Transfer X to Stack Pointer
    Txs(Txs),
    // TYA - Transfer Y to Accumulator
    Tya(Tya),
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
    pub fn from_pc(pc: &mut u16, mmu: Arc<Mutex<CpuMmu>>) -> Result<Self, InstructionError> {
        // Acquire the lock for the memory in order to decode the instruction.
        // Rust drops the lock at the end of this functions scope.
        let mmu = mmu.lock().unwrap();
        // Read the byte at the program counter
        let Some(byte) = mmu.read_u8(usize::from(*pc)) else {
            return Err(InstructionError::FailedToAccessPc(*pc));
        };

        println!("{pc:x} -> {byte:x}");

        // Advance the program counter
        *pc = pc
            .checked_add(std::mem::size_of::<u8>() as u16)
            .ok_or(InstructionError::OverflowPc)?;

        let inst = match byte {
            opcode::SED => Instruction {
                opcode: Opcode::Sed(Sed),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::SEI => Instruction {
                opcode: Opcode::Sei(Sei),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::SEC => Instruction {
                opcode: Opcode::Sec(Sec),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::CLC => Instruction {
                opcode: Opcode::Clc(Clc),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::CLD => Instruction {
                opcode: Opcode::Cld(Cld),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::CLI => Instruction {
                opcode: Opcode::Cli(Cli),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::CLV => Instruction {
                opcode: Opcode::Clv(Clv),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::CMP_I => {
                // We also have to read the next byte, which is our operand
                let Some(next_byte) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Cmp(Cmp),
                    addr_mode: AddrMode::Immediate(next_byte),
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
                    opcode: Opcode::Ldx(Ldx),
                    addr_mode: AddrMode::Immediate(next_byte),
                    cycles: 2,
                }
            }
            opcode::LDX_ZP => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Ldx(Ldx),
                    addr_mode: AddrMode::ZeroPage(addr),
                    cycles: 3,
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
                    opcode: Opcode::Ldy(Ldy),
                    addr_mode: AddrMode::Immediate(next_byte),
                    cycles: 2,
                }
            }
            opcode::TXS => Instruction {
                opcode: Opcode::Txs(Txs),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
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
                    opcode: Opcode::Lda(Lda),
                    addr_mode: AddrMode::Immediate(next_byte),
                    cycles: 2,
                }
            }
            opcode::LDA_ZP => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Lda(Lda),
                    addr_mode: AddrMode::ZeroPage(addr),
                    cycles: 3,
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
                    opcode: Opcode::Sta(Sta),
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
                    opcode: Opcode::Sta(Sta),
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
                    opcode: Opcode::Stx(Stx),
                    addr_mode: AddrMode::ZeroPage(addr),
                    cycles: 3,
                }
            }
            opcode::STX_A => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u16_le(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u16>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Stx(Stx),
                    addr_mode: AddrMode::Absolute(addr),
                    cycles: 4,
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
                    opcode: Opcode::Sta(Sta),
                    addr_mode: AddrMode::IndirectIndexed(Idx::Y, addr),
                    cycles: 6,
                }
            }
            opcode::BMI => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bmi(Bmi),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BPL => {
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
                    opcode: Opcode::Bpl(Bpl),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BCC => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bcc(Bcc),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BCS => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bcs(Bcs),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BEQ => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Beq(Beq),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BNE => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
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
            opcode::BVS => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bvs(Bvs),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BVC => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Convert the unsigned to signed integer, because the relative
                // offset can also be negative
                let addr = utils::u8_to_i8(addr);
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bvc(Bvc),
                    addr_mode: AddrMode::Relative(addr),
                    cycles: 2,
                }
            }
            opcode::BIT => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u16_le(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u16>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Bit(Bit),
                    addr_mode: AddrMode::Absolute(addr),
                    cycles: 4,
                }
            }
            opcode::JSR => {
                // We also have to read the next byte, which is our operand
                let Some(addr) = mmu.read_u16_le(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u16>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Jsr(Jsr),
                    addr_mode: AddrMode::Absolute(addr),
                    cycles: 4,
                }
            }
            opcode::DEX => Instruction {
                opcode: Opcode::Dex(Dex),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::DEY => Instruction {
                opcode: Opcode::Dey(Dey),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::INX => Instruction {
                opcode: Opcode::Inx(Inx),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::INY => Instruction {
                opcode: Opcode::Iny(Iny),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::NOP => Instruction {
                opcode: Opcode::Nop(Nop),
                addr_mode: AddrMode::Implied,
                cycles: 2,
            },
            opcode::RTS => Instruction {
                opcode: Opcode::Rts(Rts),
                addr_mode: AddrMode::Implied,
                cycles: 6,
            },
            opcode::SBC_A => {
                // We also have to read the next 2 bytes, which is our operand
                let Some(addr) = mmu.read_u16_le(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };
                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u16>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Sbc(Sbc),
                    addr_mode: AddrMode::Absolute(addr),
                    cycles: 4,
                }
            },
            opcode::ADC_I => {
                // We also have to read the next byte, which is our operand
                let Some(imm) = mmu.read_u8(usize::from(*pc)) else {
                    return Err(InstructionError::InvalidInstruction(byte));
                };

                // Advance the program counter
                *pc = pc
                    .checked_add(std::mem::size_of::<u8>() as u16)
                    .ok_or(InstructionError::OverflowPc)?;

                Instruction {
                    opcode: Opcode::Adc(Adc),
                    addr_mode: AddrMode::Immediate(imm),
                    cycles: 2,
                }
            },
            opcode::TAX => {
                Instruction {
                    opcode: Opcode::Tax(Tax),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::TAY => {
                Instruction {
                    opcode: Opcode::Tay(Tay),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::TSX => {
                Instruction {
                    opcode: Opcode::Tsx(Tsx),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            opcode::TXA => {
                Instruction {
                    opcode: Opcode::Txa(Txa),
                    addr_mode: AddrMode::Implied,
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
            opcode::TYA => {
                Instruction {
                    opcode: Opcode::Tya(Tya),
                    addr_mode: AddrMode::Implied,
                    cycles: 2,
                }
            }
            _ => return Err(InstructionError::InvalidOpcode(byte)),
        };
        Ok(inst)
    }

    pub fn opcode(&self) -> &Opcode {
        &self.opcode
    }
    pub fn addr_mode(&self) -> &AddrMode {
        &self.addr_mode
    }
    pub fn cycles(&self) -> usize {
        self.cycles
    }
}

#[derive(Debug)]
pub struct Sed;
#[derive(Debug)]
pub struct Sei;
#[derive(Debug)]
pub struct Sec;
#[derive(Debug)]
pub struct Clc;
#[derive(Debug)]
pub struct Cld;
#[derive(Debug)]
pub struct Cli;
#[derive(Debug)]
pub struct Clv;
#[derive(Debug)]
pub struct Ldx;
#[derive(Debug)]
pub struct Ldy;
#[derive(Debug)]
pub struct Lda;
#[derive(Debug)]
pub struct Sta;
#[derive(Debug)]
pub struct Stx;
#[derive(Debug)]
pub struct Bmi;
#[derive(Debug)]
pub struct Bpl;
#[derive(Debug)]
pub struct Bcc;
#[derive(Debug)]
pub struct Bcs;
#[derive(Debug)]
pub struct Beq;
#[derive(Debug)]
pub struct Bne;
#[derive(Debug)]
pub struct Bvs;
#[derive(Debug)]
pub struct Bvc;
#[derive(Debug)]
pub struct Bit;
#[derive(Debug)]
pub struct Jsr;
#[derive(Debug)]
pub struct Dex;
#[derive(Debug)]
pub struct Dey;
#[derive(Debug)]
pub struct Inx;
#[derive(Debug)]
pub struct Iny;
#[derive(Debug)]
pub struct Rts;
#[derive(Debug)]
pub struct Adc;
#[derive(Debug)]
pub struct Sbc;
#[derive(Debug)]
pub struct Cmp;
#[derive(Debug)]
pub struct Nop;
#[derive(Debug)]
pub struct Tax;
#[derive(Debug)]
pub struct Tay;
#[derive(Debug)]
pub struct Tsx;
#[derive(Debug)]
pub struct Txa;
#[derive(Debug)]
pub struct Txs;
#[derive(Debug)]
pub struct Tya;

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

impl AddrMode {
    /*
    // Decodes the operand based on the addressing mode
    pub fn decode_group_one_op(&self, mmu: &mut CpuMmu) -> Result<u8, AddrModeError> {
        // Load a byte of memory into the X register.
        let value = match self {
            AddrMode::Implied => {
                return Err(AddrModeError::ImpliedAlreadyDecoded);
            }
            AddrMode::Immediate(imm) => *imm,
            AddrMode::Absolute(addr) => {
                let addr = *addr as usize;
                let value = mmu.read_u8(addr)
                    .ok_or(AddrModeError::MmuReadError(addr))?;
                value
            }
            AddrMode::ZeroPage(addr) => {
                let zp_addr = *addr as usize;
                let value = mmu
                    .read_u8(zp_addr)
                    .ok_or(AddrModeError::MmuReadError(zp_addr))?;
                value
            }
        };
        Ok(value)
    }
    */
}

#[derive(Debug)]
pub enum AddrModeError {
    MmuReadError(usize),
    ImpliedAlreadyDecoded,
}

#[derive(Debug)]
pub enum CpuError {
    CpuMmuError(CpuMmuError),
    AddrModeError(AddrModeError),
    MmuReadError(usize),
}

impl From<CpuMmuError> for CpuError {
    fn from(err: CpuMmuError) -> Self {
        Self::CpuMmuError(err)
    }
}

impl From<AddrModeError> for CpuError {
    fn from(err: AddrModeError) -> Self {
        Self::AddrModeError(err)
    }
}

mod utils {
    /// Converts a i8 to a u8 without data loss through pointer transmuting
    pub fn u8_to_i8(value: u8) -> i8 {
        unsafe { std::mem::transmute::<u8, i8>(value) }
    }
}

#[cfg(test)]
mod cpu_tests {
    use crate::emulator::{Cpu, CpuMmu};
    use std::sync::{Arc, Mutex};

    #[test]
    fn test_adc_sign_overflow_set() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));

        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 0x50,     // LDA 80
                0x69, 0x50,     // ADC 80
            ]).expect("Failed to set bytes");
        }

        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == false);
        assert!(cpu.p().overflow == true);
        assert!(cpu.p().negative == true);
    }

    #[test]
    fn test_adc_no_flags_set() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));
        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 0x50,     // LDA 80
                0x69, 0x10,     // ADC 16
            ]).expect("Failed to set bytes");
        }
        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == false);
        assert!(cpu.p().overflow == false);
        assert!(cpu.p().negative == false);
    }

    #[test]
    fn test_adc_unsign_carry_set() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));
        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 0x50,     // LDA 80
                0x69, 0xd0,     // ADC 208
            ]).expect("Failed to set bytes");
        }
        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == true);
        assert!(cpu.p().overflow == false);
        assert!(cpu.p().negative == false);
    }

    #[test]
    fn test_adc_sign_overflow_set2() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));

        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 190,     // LDA -66
                0x69, 191,     // ADC -65
            ]).expect("Failed to set bytes");
        }

        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == true);
        assert!(cpu.p().overflow == true);
        assert!(cpu.p().negative == false);
    }

    #[test]
    fn test_adc_sign_no_overflow() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));

        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 251,     // LDA -5
                0x69, 249,     // ADC -7
            ]).expect("Failed to set bytes");
        }

        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == true);
        assert!(cpu.p().overflow == false);
        assert!(cpu.p().negative == true);
    }

    #[test]
    fn test_adc_sign_no_overflow_no_cary() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));

        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 5,     // LDA 5
                0x69, 249,     // ADC -7
            ]).expect("Failed to set bytes");
        }

        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == false);
        assert!(cpu.p().overflow == false);
        assert!(cpu.p().negative == true);
    }

    #[test]
    fn test_adc_sign_no_overflow_cary_set() {
        let mut cpu = Cpu::power_up();
        let (tx, rx) = std::sync::mpsc::channel();
        let mut cpu_mmu = Arc::new(Mutex::new(CpuMmu::default()));

        {
            (cpu_mmu.lock().unwrap()).set_bytes(0, &[
                0xA9, 5,     // LDA 5
                0x69, 253,   // ADC -3
            ]).expect("Failed to set bytes");
        }

        cpu.set_pc(0);
        cpu.execute(cpu_mmu.clone(), tx.clone()).expect("Failed to execute");

        assert!(cpu.p().carry == true);
        assert!(cpu.p().overflow == false);
        assert!(cpu.p().negative == false);
    }
}
