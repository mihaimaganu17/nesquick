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
/// TXS - Transfer X to Stack Pointer
/// Copies the current contents of the X register into the stack register.
pub const TXS: u8 = 0x9A;
/// LDA - Load Acummulator - Immediate
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_I: u8 = 0xA9;
/// STA - Store Accumulator - Absolute
/// Stores the contents of the accumulator into memory.
pub const STA_A: u8 = 0x8D;
/// LDY - Load Y Register
/// Loads a byte of memory into the Y register setting the zero and negative
/// flags as appropriate.
pub const LDY_I: u8 = 0xA0;
