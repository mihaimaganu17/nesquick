//! Module that defines, manipulates and encodes addressing modes
use bitflags::bitflags;
use crate::emulator::{Cpu, CpuMmu, CpuError};

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
    // Absolute indexed address is absolute addressing with an index
    // register added to the absolute address.
    AbsoluteIndexed(Idx, u16),
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
    // ZeroPageIndexed is the same are zero page, with one of the index
    // registers X or Y added to it
    ZeroPageIndexed(Idx, u8),
    // Indirect Indexed
    // Indirect indexed addressing is the most common indirection mode used
    // on the 6502. In instruction contains the zero page location of the least
    // significant byte of 16 bit address. The Y register is dynamically added
    // to this value to generated the actual target address for operation.
    // This mode is only used with the Y register. It differs in the order that
    // Y is applied to the indirectly fetched address. An example instruction
    // that uses indirect index addressing is LDA ($86),Y . To calculate the
    // target address, the CPU will first fetch the address stored at
    // zero page location $86. That address will be added to register Y to get
    // the final target address. For LDA ($86),Y, if the address stored at $86
    // is $4028 (memory is 0086: 28 40, remember little endian) and register Y
    // contains $10, then the final target address would be $4038. Register A
    // will be loaded with the contents of memory at $4038.
    //
    // Indirect Indexed instructions are 2 bytes - the second byte is the
    // zero-page address - $86 in the example. (So the fetched address has to
    // be stored in the zero page.)
    //
    // While indexed indirect addressing will only generate a zero-page address,
    // this mode's target address is not wrapped - it can be anywhere in the
    // 16-bit address space.
    IndirectIndexedY(u8),
    // Indexed Indirect
    // Indexed indirect addressing is normally used in conjunction with a table
    // of address held on zero page. The address of the table is taken from the
    // instruction and the X register added to it (with zero page wrap around)
    // to give the location of the least significant byte of the target address.
    IndexedIndirectX(u8),
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
    // Decodes the operand based on the addressing mode
    pub fn decode_group_one_op(
        &self,
        memory: &CpuMmu,
        cpu: &Cpu,
        supp_addr_mode: SupportedAddrMode,
    ) -> Result<usize, AddrModeError> {
        // Load a byte of memory into the X register.
        let value = match self {
            AddrMode::Implied => {
                return Err(AddrModeError::ImpliedAlreadyDecoded);
            }
            AddrMode::Immediate(_) => {
                return Err(AddrModeError::ImmediateAlreadyDecoded);
            }
            AddrMode::Absolute(addr) => {
                if (supp_addr_mode & SupportedAddrMode::ABSOLUTE).bits() != 0 {
                    *addr as usize
                } else {
                    unreachable!()
                }
            }
            AddrMode::AbsoluteIndexed(idx, addr) => {
                let addr = match idx {
                    Idx::X => {
                        if (supp_addr_mode & SupportedAddrMode::ABSOLUTE_X).bits() != 0 {
                            (addr.wrapping_add(cpu.x as u16)) as usize
                        } else {
                            unreachable!()
                        }
                    }
                    Idx::Y => {
                        if (supp_addr_mode & SupportedAddrMode::ABSOLUTE_Y).bits() != 0 {
                            (addr.wrapping_add(cpu.y as u16)) as usize
                        } else {
                            unreachable!()
                        }
                    }
                };
                addr
            }
            AddrMode::ZeroPage(addr) => {
                if (supp_addr_mode & SupportedAddrMode::ZEROPAGE).bits() != 0 {
                    *addr as usize
                } else {
                    unreachable!()
                }
            }
            AddrMode::ZeroPageIndexed(idx, addr) => {
                match idx {
                    Idx::X => {
                        if (supp_addr_mode & SupportedAddrMode::ABSOLUTE_X).bits() != 0{
                            (addr.wrapping_add(cpu.x)) as usize
                        } else {
                            unreachable!()
                        }
                    }
                    Idx::Y => {
                        if (supp_addr_mode & SupportedAddrMode::ABSOLUTE_Y).bits() != 0{
                            (addr.wrapping_add(cpu.y)) as usize
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
            AddrMode::IndirectIndexedY(addr) => {
                if (supp_addr_mode & SupportedAddrMode::INDIRECT_INDEXED_Y).bits() != 0 {
                    // Convert into a u16 address
                    let read_addr_from = usize::from(*addr);
                    // Read the least significant byte of the 16-bit
                    // address
                    let tmp_addr = memory
                        .read_u16_le(read_addr_from)
                        .ok_or(AddrModeError::MmuReadError(read_addr_from))?;
                    tmp_addr.wrapping_add(cpu.y as u16) as usize
                } else {
                    unreachable!()
                }
            }
            AddrMode::IndexedIndirectX(addr) => {
                if (supp_addr_mode & SupportedAddrMode::INDEXED_INDIRECT_X).bits() != 0 {
                    // Convert into a u16 address and add x to it
                    let read_addr_from =
                        usize::from(addr.wrapping_add(cpu.x));
                    // Read the address at that location in the zero page
                    let addr = memory
                        .read_u16_le(read_addr_from)
                        .ok_or(AddrModeError::MmuReadError(read_addr_from))?;
                    addr as usize
                } else {
                    unreachable!()
                }
            }
            AddrMode::Relative(_) => {
                return Err(AddrModeError::RelativeAlreadyDecoded);
            }
        };
        Ok(value)
    }
}

bitflags! {
    /// Not every instruction implements all the addressing modes. In order to make
    /// sure that we decode valid addressing modes, we have this structure which
    /// is equivalent to a bit mask containing flags for the supported addressing
    /// modes of each instruction.
    /// Note: The addressing mode implied is omitted here on purpose since we will
    /// deal with that case at the moment of function evaluation.
    pub struct SupportedAddrMode: u16 {
        const ABSOLUTE = 0b0000_0001;
        const ABSOLUTE_X = 0b0000_0010;
        const ABSOLUTE_Y = 0b0000_0100;
        const ZEROPAGE = 0b0000_1000;
        const ZEROPAGE_X = 0b0001_0000;
        const ZEROPAGE_Y = 0b0010_0000;
        const INDEXED_INDIRECT_X = 0b0100_0000;
        const INDIRECT_INDEXED_Y = 0b1000_0000;
    }
}

#[derive(Debug)]
pub enum AddrModeError {
    MmuReadError(usize),
    ImpliedAlreadyDecoded,
    RelativeAlreadyDecoded,
    ImmediateAlreadyDecoded,
}

#[derive(Debug)]
pub enum Idx {
    X,
    Y,
}
