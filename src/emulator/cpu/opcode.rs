//! Module that holds opcode constants and definitions

/// Set the decimal mode flag to one.
pub const SED: u8 = 0xF8;
/// Set the interrupt disable flag to one.
pub const SEI: u8 = 0x78;
/// Set the carry flag to one.
pub const SEC: u8 = 0x38;
/// Sets the carry flag to zero.
pub const CLC: u8 = 0x18;
/// Sets the decimal mode flag to zero.
pub const CLD: u8 = 0xD8;
/// Clears the interrupt disable flag allowing normal interrupt requests to be
/// serviced.
pub const CLI: u8 = 0x58;
/// Clears the overflow flag.
pub const CLV: u8 = 0xB8;
/// LDX - Load X Register
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_I: u8 = 0xA2;
pub const LDX_ZP: u8 = 0xA6;
pub const LDX_ZP_Y: u8 = 0xB6;
/// LDA - Load Acummulator - Immediate
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_I: u8 = 0xA9;
/// LDA - Load Acummulator - ZeroPage
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_ZP: u8 = 0xA5;
/// LDA - Load Acummulator - ZeroPage, X indexed
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_ZP_X: u8 = 0xB5;
/// LDA - Load Acummulator - Absolute
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_A: u8 = 0xAD;
/// LDA - Load Acummulator - Absolute, X Indexed
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_A_X: u8 = 0xBD;
/// LDA - Load Acummulator - Absolute, Y Indexed
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_A_Y: u8 = 0xB9;
/// LDA - Load Acummulator - (Indirect, X Indexed)
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_I_X: u8 = 0xA1;
/// LDA - Load Acummulator - (Indirect), Y Indexed
/// Loads a byte of memory into the accumulator setting the zero and negative
/// flags as appropriate.
pub const LDA_I_Y: u8 = 0xB1;
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
/// BIT - Bit Test
/// This instructions is used to test if one or more bits are set in a target
/// memory location. The mask pattern in A is ANDed with the value in memory to
/// set or clear the zero flag, but the result is not kept. Bits 7 and 6 of the
/// value from memory are copied into the N and V flags.
pub const BIT: u8 = 0x2c;
/// JSR - Jump to Subroutine
/// The JSR instruction pushes the address (minus one) of the return point on
/// to the stack and then sets the program counter to the target memory address.
pub const JSR: u8 = 0x20;
/// DEX - Decrement X Register
/// Subtracts one from the X register setting the zero and negative flags as
/// appropriate.
pub const DEX: u8 = 0xCA;
/// DEY - Decrement Y Register
/// Subtracts one from the Y register setting the zero and negative flags as
/// appropriate.
pub const DEY: u8 = 0x88;
/// INX - Increment X Register
/// Adds one to the X register setting the zero and negative flags as
/// appropriate.
pub const INX: u8 = 0xE8;
/// INY - Increment Y Register
/// Adds one to the Y register setting the zero and negative flags as
/// appropriate.
pub const INY: u8 = 0xC8;
/// RTS - Return from Subroutine
/// The RTS instruction is used at the end of a subroutine to return to the
/// calling routine. It pulls the program counter (minus one) from the stack.
pub const RTS: u8 = 0x60;
/// SBC - Subtract with Carry
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_A: u8 = 0xED;
/// CMP - Compare - Immediate
/// This instruction compares the contents of the accumulator with another
/// memory held value and sets the zero and carry flags as appropriate.
pub const CMP_I: u8 = 0xC9;
/// BPL - Branch if Positive
/// If the negative flag is clear then add the relative displacement to the
/// program counter to cause a branch to a new location.
pub const BPL: u8 = 0x10;
/// BMI - Branch if Minus
/// If the negative flag is set then add the relative displacement to the
/// program counter to cause a branch to a new location.
pub const BMI: u8 = 0x30;
/// BCC - Branch if Carry Clear
/// If the carry flag is clear then add the relative displacement to the
/// program counter to cause a branch to a new location.
pub const BCC: u8 = 0x90;
/// BNE - Branch if Not Equal
/// If the zero flag is clear then add the relative displacement to the program
/// counter to cause a branch to a new location.
pub const BNE: u8 = 0xD0;
/// BCS - Branch if Carry Set
/// If the carry flag is set then add the relative displacement to the program
/// counter to cause a branch to a new location.
pub const BCS: u8 = 0xB0;
/// BEQ - Branch if Equal
/// If the zero flag is set then add the relative displacement to the program
/// counter to cause a branch to a new location.
pub const BEQ: u8 = 0xF0;
/// BVS - Branch if Overflow Set
/// If the overflow flag is set then add the relative displacement to the
/// program counter to cause a branch to a new location.
pub const BVS: u8 = 0x70;
/// BVC - Branch if Overflow Clear
/// If the overflow flag is clear then add the relative displacement to the
/// program counter to cause a branch to a new location.
pub const BVC: u8 = 0x50;
/// ADC - Add with Carry - Immediate
/// This instruction adds the contents of a memory location to the accumulator
/// together with the carry bit. If overflow occurs the carry bit is set, this
/// enables multiple byte addition to be performed.
pub const ADC_I: u8 = 0x69;
/// NOP - No Operation
/// The NOP instruction causes no changes to the processor other than the
/// normal incrementing of the program counter to the next instruction.
pub const NOP: u8 = 0xEA;
/// TAX - Transfer Accumulator to X
/// Copies the current contents of the accumulator into the X register and sets
/// the zero and negative flags as appropriate.
pub const TAX: u8 = 0xAA;
/// TAY - Transfer Accumulator to Y
/// Copies the current contents of the accumulator into the Y register and sets
/// the zero and negative flags as appropriate.
pub const TAY: u8 = 0xA8;
/// TSX - Transfer Stack Pointer to X
/// Copies the current contents of the stack register into the X register and
/// sets the zero and negative flags as appropriate.
pub const TSX: u8 = 0xBA;
/// TXA - Transfer X to Accumulator
/// Copies the current contents of the X register into the accumulator and sets
/// the zero and negative flags as appropriate.
pub const TXA: u8 = 0x8A;
/// TXS - Transfer X to Stack Pointer
/// Copies the current contents of the X register into the stack register.
pub const TXS: u8 = 0x9A;
/// TYA - Transfer Y to Accumulator
/// Copies the current contents of the Y register into the accumulator and sets
/// the zero and negative flags as appropriate.
pub const TYA: u8 = 0x98;
