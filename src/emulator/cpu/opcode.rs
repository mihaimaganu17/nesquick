//! Module that holds opcode constants and definitions

/// The BRK instruction forces the generation of an interrupt request. The
/// program counter and processor status are pushed on the stack then the IRQ
/// interrupt vector at $FFFE/F is loaded into the PC and the break flag in the
/// status set to one. Set the decimal mode flag to one.
pub const BRK: u8 = 0x00;
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
/// LDX - Load X Register - Immediate
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_I: u8 = 0xA2;
/// LDX - Load X Register - ZeroPage
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_ZP: u8 = 0xA6;
/// LDX - Load X Register - ZeroPage, Y-indexed
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_ZP_Y: u8 = 0xB6;
/// LDX - Load X Register - Absolute
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_A: u8 = 0xAE;
/// LDX - Load X Register - Absolute, Y-indexed
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDX_A_Y: u8 = 0xBE;
/// LDY - Load Y Register - Immediate
/// Load a byte of memory into the Y register setting the zero and negative
/// flags as appropriate.
pub const LDY_I: u8 = 0xA0;
/// LDY - Load Y Register - ZeroPage
/// Load a byte of memory into the Y register setting the zero and negative
/// flags as appropriate.
pub const LDY_ZP: u8 = 0xA4;
/// LDY - Load Y Register - ZeroPage, X-indexed
/// Load a byte of memory into the Y register setting the zero and negative
/// flags as appropriate.
pub const LDY_ZP_X: u8 = 0xB4;
/// LDY - Load Y Register - Absolute
/// Load a byte of memory into the Y register setting the zero and negative
/// flags as appropriate.
pub const LDY_A: u8 = 0xAC;
/// LDX - Load X Register - Absolute, Y-indexed
/// Load a byte of memory into the X register setting the zero and negative
/// flags as appropriate.
pub const LDY_A_X: u8 = 0xBC;
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
/// STA - Store Accumulator - Zero Page, X - indexed
/// Stores the contents of the accumulator into memory.
pub const STA_ZP_X: u8 = 0x95;
/// STA - Store Accumulator - Absolute
/// Stores the contents of the accumulator into memory.
pub const STA_A: u8 = 0x8D;
/// STA - Store Accumulator - Absolute, X-indexed
/// Stores the contents of the accumulator into memory.
pub const STA_A_X: u8 = 0x9D;
/// STA - Store Accumulator - Absolute, Y-indexed
/// Stores the contents of the accumulator into memory.
pub const STA_A_Y: u8 = 0x99;
/// STA - Store Accumulator - Indexed, indirect X
/// Stores the contents of the accumulator into memory.
pub const STA_I_X: u8 = 0x81;
/// STA - Store Accumulator - Indirect indexed - Y
/// Stores the contents of the accumulator into memory.
pub const STA_I_Y: u8 = 0x91;
/// STX - Store X Register - ZeroPage
/// Stores the contents of the X register into memory.
pub const STX_ZP: u8 = 0x86;
/// STX - Store X Register - ZeroPage, Y-indexed
/// Stores the contents of the X register into memory.
pub const STX_ZP_Y: u8 = 0x96;
/// STX - Store X Register - Absolute
/// Stores the contents of the X register into memory.
pub const STX_A: u8 = 0x8E;
/// STY - Store X Register - ZeroPage
/// Stores the contents of the X register into memory.
pub const STY_ZP: u8 = 0x84;
/// STY - Store X Register - ZeroPage, X-indexed
/// Stores the contents of the X register into memory.
pub const STY_ZP_X: u8 = 0x94;
/// STY - Store X Register - Absolute
/// Stores the contents of the X register into memory.
pub const STY_A: u8 = 0x8C;
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
/// JMP - Jump - Absolute
/// Sets the program counter to the address specified by the operand.
pub const JMP_A: u8 = 0x4C;
/// JMP - Jump - Indirect
/// Sets the program counter to the address specified by the operand.
pub const JMP_I: u8 = 0x6C;
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
/// RTI - Return from Interrupt
/// The RTI instruction is used at the end of an interrupt processing routine.
/// It pulls the processor flags from the stack followed by the program counter.
pub const RTI: u8 = 0x40;
/// SBC - Subtract with Carry - Immediate
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_I: u8 = 0xE9;
/// SBC - Subtract with Carry - ZeroPage
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_ZP: u8 = 0xE5;
/// SBC - Subtract with Carry - ZeroPage, X-indexed
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_ZP_X: u8 = 0xF5;
/// SBC - Subtract with Carry - Absolute
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_A: u8 = 0xED;
/// SBC - Subtract with Carry - Absolute, X-indexed
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_A_X: u8 = 0xFD;
/// SBC - Subtract with Carry - Absolute, Y-indexed
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_A_Y: u8 = 0xF9;
/// SBC - Subtract with Carry - Indexed Indirect X
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_I_X: u8 = 0xE1;
/// SBC - Subtract with Carry - Indirect Indirect Y
/// This instruction subtracts the contents of a memory location to the
/// accumulator together with the not of the carry bit. If overflow occurs the
/// carry bit is clear, this enables multiple byte
/// subtraction to be performed.
pub const SBC_I_Y: u8 = 0xF1;
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

/// PHA - Push Accumulator
/// Pushes a copy of the accumulator on to the stack.
pub const PHA: u8 = 0x48;
/// PHP - Push Processor Status
/// Pushes a copy of the status flags on to the stack.
pub const PHP: u8 = 0x08;
/// PLA - Pull Accumulator
/// Pulls an 8 bit value from the stack and into the accumulator. The zero and
/// negative flags are set as appropriate.
pub const PLA: u8 = 0x68;
/// PLP - Pull Processor Status
/// Pulls an 8 bit value from the stack and into the processor flags. The flags
/// will take on new states as determined by the value pulled.
pub const PLP: u8 = 0x28;
/// ROL - Rotate Left - Accumulator
/// Move each of the bits in either A or M one place to the left. Bit 0 is
/// filled with the current value of the carry flag whilst the old bit 7
/// becomes the new carry flag value.
pub const ROL_ACC: u8 = 0x2A;
/// ROL - Rotate Left - ZeroPage
/// Move each of the bits in either A or M one place to the left. Bit 0 is
/// filled with the current value of the carry flag whilst the old bit 7
/// becomes the new carry flag value.
pub const ROL_ZP: u8 = 0x26;
/// ROL - Rotate Left - ZeroPage X-indexed
/// Move each of the bits in either A or M one place to the left. Bit 0 is
/// filled with the current value of the carry flag whilst the old bit 7
/// becomes the new carry flag value.
pub const ROL_ZP_X: u8 = 0x36;
/// ROL - Rotate Left - ZeroPage - Absolute
/// Move each of the bits in either A or M one place to the left. Bit 0 is
/// filled with the current value of the carry flag whilst the old bit 7
/// becomes the new carry flag value.
pub const ROL_A: u8 = 0x2E;
/// ROL - Rotate Left - ZeroPage - Absolute, X - Indexed
/// Move each of the bits in either A or M one place to the left. Bit 0 is
/// filled with the current value of the carry flag whilst the old bit 7
/// becomes the new carry flag value.
pub const ROL_A_X: u8 = 0x3E;
/// ROR - Rotate Right - Accumulator
/// Move each of the bits in either A or M one place to the right. Bit 7 is
/// filled with the current value of the carry flag whilst the old bit 0
/// becomes the new carry flag value.
pub const ROR_ACC: u8 = 0x6A;
/// ROR - Rotate Right - ZeroPage
/// Move each of the bits in either A or M one place to the right. Bit 7 is
/// filled with the current value of the carry flag whilst the old bit 0
/// becomes the new carry flag value.
pub const ROR_ZP: u8 = 0x66;
/// ROR - Rotate Right - ZeroPage - X - indexed
/// Move each of the bits in either A or M one place to the right. Bit 7 is
/// filled with the current value of the carry flag whilst the old bit 0
/// becomes the new carry flag value.
pub const ROR_ZP_X: u8 = 0x76;
/// ROR - Rotate Right - Absolute
/// Move each of the bits in either A or M one place to the right. Bit 7 is
/// filled with the current value of the carry flag whilst the old bit 0
/// becomes the new carry flag value.
pub const ROR_A: u8 = 0x6E;
/// ROR - Rotate Right - Absolute - X-indexed
/// Move each of the bits in either A or M one place to the right. Bit 7 is
/// filled with the current value of the carry flag whilst the old bit 0
/// becomes the new carry flag value.
pub const ROR_A_X: u8 = 0x7E;
/// AND - Logical AND - Immediate
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_I: u8 = 0x29;
/// AND - Logical AND - ZeroPage
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_ZP: u8 = 0x25;
/// AND - Logical AND - ZeroPage, X-indexed
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_ZP_X: u8 = 0x35;
/// AND - Logical AND - Absolute
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_A: u8 = 0x2D;
/// AND - Logical AND - Absolute, X-indexed
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_A_X: u8 = 0x3D;
/// AND - Logical AND - Absolute, Y-indexed
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_A_Y: u8 = 0x39;
/// AND - Logical AND - Indexed Indirect X
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_I_X: u8 = 0x21;
/// AND - Logical AND - Indirect Indexed Y
/// A logical AND is performed, bit by bit, on the accumulator contents using
/// the contents of a byte of memory.
pub const AND_I_Y: u8 = 0x31;
/// LSR - Logical Shift Right - Accumulator
/// Each of the bits in A or M is shift one place to the right. The bit that
/// was in bit 0 is shifted into the carry flag. Bit 7 is set to zero.
pub const LSR_ACC: u8 = 0x4A;
/// LSR - Logical Shift Right - ZeroPage
/// Each of the bits in A or M is shift one place to the right. The bit that
/// was in bit 0 is shifted into the carry flag. Bit 7 is set to zero.
pub const LSR_ZP: u8 = 0x46;
/// LSR - Logical Shift Right - ZeroPage - X-indexed
/// Each of the bits in A or M is shift one place to the right. The bit that
/// was in bit 0 is shifted into the carry flag. Bit 7 is set to zero.
pub const LSR_ZP_X: u8 = 0x56;
/// LSR - Logical Shift Right - Absolute
/// Each of the bits in A or M is shift one place to the right. The bit that
/// was in bit 0 is shifted into the carry flag. Bit 7 is set to zero.
pub const LSR_A: u8 = 0x4E;
/// LSR - Logical Shift Right - Absolute - X-indexed
/// Each of the bits in A or M is shift one place to the right. The bit that
/// was in bit 0 is shifted into the carry flag. Bit 7 is set to zero.
pub const LSR_A_X: u8 = 0x5E;
