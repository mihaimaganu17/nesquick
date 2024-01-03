//! Module that holds opcode constants and definitions

/// Set the decimal mode flag to one.
pub const SED: u8 = 0xF8;
/// Set the interrupt disable flag to one.
pub const SEI: u8 = 0x78;
/// Sets the decimal mode flag to zero.
pub const CLD: u8 = 0xD8;
/// LDX - Load X Register
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_I: u8 = 0xA2;
pub const LDX_ZP: u8 = 0xA6;
pub const LDX_ZP_Y: u8 = 0xB6;
/// TXS - Transfer X to Stack Pointer
/// Copies the current contents of the X register into the stack register.
pub const TXS: u8 = 0x9A;
/// LDA - Load Acummulator - Immediate
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_I: u8 = 0xA9;
/// STA - Store Accumulator - Zero Page
/// Stores the contents of the accumulator into memory.
pub const STA_ZP: u8 = 0x85;
/// STA - Store Accumulator - Absolute
/// Stores the contents of the accumulator into memory.
pub const STA_A: u8 = 0x8D;
/// STA - Store Accumulator - (Indirect), Y
/// Stores the contents of the accumulator into memory.
pub const STA_I_Y: u8 = 0x91;
/// STX - Store X Register
/// Stores the contents of the X register into memory.
pub const STX_ZP: u8 = 0x86;
pub const STX_ZP_Y: u8 = 0x96;
pub const STX_A: u8 = 0x8E;
/// LDY - Load Y Register
/// Loads a byte of memory into the Y register setting the zero and negative
/// flags as appropriate.
pub const LDY_I: u8 = 0xA0;
/// DEY - Decrement Y Register
/// Subtracts one from the Y register setting the zero and negative flags as
/// appropriate.
pub const DEY: u8 = 0x88;
/// BNE - Branch if Not Equal
/// If the zero flag is clear then add the relative displacement to the program
/// counter to cause a branch to a new location.
pub const BNE: u8 = 0xD0;
/// BPL - Branch if Positive
///
/// If the negative flag is clear then add the relative displacement to the program counter to
/// cause a branch to a new location.
pub const BPL: u8 = 0x10;
/// BIT - Bit Test
/// This instructions is used to test if one or more bits are set in a target
/// memory location. The mask pattern in A is ANDed with the value in memory to
/// set or clear the zero flag, but the result is not kept. Bits 7 and 6 of the
/// value from memory are copied into the N and V flags.
pub const BIT: u8 = 0x2c;
/// JSR - Jump to Subroutine
///
/// The JSR instruction pushes the address (minus one) of the return point on
/// to the stack and then sets the program counter to the target memory address.
pub const JSR: u8 = 0x20;
/// DEX - Decrement X Register
/// Subtracts one from the X register setting the zero and negative flags as
/// appropriate.
pub const DEX: u8 = 0xCA;
