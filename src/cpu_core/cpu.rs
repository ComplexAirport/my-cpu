//! This file contains interfaces for our simulated CPU \
//! This includes:
//! - [`CPU`] - Main CPU interface
//! - [`CPUInstr`] - Represents CPU instructions
//! - [`CPUFlag`] - Represents CPU flags
//! - [`CPUError`] - Represents CPU related errors
//! - etc.
use std::ops::{BitAnd, BitOr, BitXor}; // Used in CPU bit manipulation instructions
use crate::define_opcodes;  // Used to convert enums like CPUInstr and CPUFlag to bytes and vice-versa
pub use super::typing::{*};  // Used to wrap bytes into different data-types (like f64, i64, etc.)
pub use super::ram::{RamAddr, RAM};  // Access to RAM
pub use super::error::{ErrorType, CPUError};  // Error types


/// Represents a CPU instruction
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CPUInstr {
    // Halts the cpu (no more instructions are executing)
    Halt,

    // Sets value of #1 to value at #2
    // (Note: #1 is not allowed to be an immediate value)
    Set,

    // Unsigned instructions
    // These instructions interpret the operands as `u64` bytes */
    UAdd, USub, UMul, UMod, UDiv, // Arithmetic operators
    UOr, UXor, UAnd, UNot,        // Bitwise operators
    UShl, UShr,                   // Shift left (<<) and Shift right (>>) operators

    // Signed instructions
    // These instructions interpret the operands `i64` bytes
    IAdd, ISub, IMul, IMod, IDiv, // Arithmetic operators
    IOr, IXor, IAnd, INot,        // Bitwise operators
    IShl, IShr,                   // Shift left (<<) and Shift right (>>) operators

    // Floating operator instructions
    // These instructions interpret the operands as `f64` bytes
    FAdd, FSub, FMul, FDiv, // Arithmetic operators

    // Logical operators
    // (treats operands as boolean values: zero = false, nonzero = true)
    LOr, LXor, LAnd, LNot,

    // Jump instructions
    Jump,           // Jumps to a memory address
    JumpIf,         // Jumps to [1] if [2] is nonzero
    JumpIfNot,      // Jumps to [1] if [2] is zero

    // Unsigned comparison instructions
    UEqual,             // ==
    UGreater,           // >
    UGreaterEqual,      // >=
    ULess,              // <
    ULessEqual,         // <=

    // Signed comparison instructions
    IEqual,             // ==
    IGreater,           // >
    IGreaterEqual,      // >=
    ILess,              // <
    ILessEqual,         // <=

    // Float comparison instructions
    FEqual,             // ==
    FGreater,           // >
    FGreaterEqual,      // >=
    FLess,              // <
    FLessEqual,         // <=

    // Stack and function related instructions
    Push, Pop, // Push and pop values to the stack
    Call, Ret, // Call and return from functions

    Offset,   // Offsets a memory address and stores the result in the accu

    // Quickly store and load 8 bytes to/from a memory address
    Store,  // Store 8 bytes to a memory address (stores at [address..address+8))
    Load,   // Read 8 bytes from a memory address to a register

    // Syscall instruction
    Syscall,

    // Nop instruction - does literally nothing
    Nop,
}

impl CPUInstr {
     define_opcodes!(
        HALT,

        SET,

        UADD, USUB, UMUL, UMOD, UDIV,
        UOR, UXOR, UAND, UNOT,
        USHL, USHR,

        IADD, ISUB, IMUL, IMOD, IDIV,
        IOR, IXOR, IAND, INOT,
        ISHL, ISHR,


        FADD, FSUB, FMUL, FDIV,

        LOR, LXOR, LAND, LNOT,

        JUMP,
        JUMPIF,
        JUMPIFNOT,

        UEQUAL,
        UGREATER,
        UGREATEREQUAL,
        ULESS,
        ULESSEQUAL,

        IEQUAL,
        IGREATER,
        IGREATEREQUAL,
        ILESS,
        ILESSEQUAL,

        FEQUAL,
        FGREATER,
        FGREATEREQUAL,
        FLESS,
        FLESSEQUAL,

        PUSH,
        POP,
        CALL,
        RET,

        OFFSET,

        STORE,
        LOAD,

        SYSCALL,

        NOP
     );

    /// Represents the instruction in a byte
    pub const fn as_byte(&self) -> u8 {
        match &self {
            CPUInstr::Halt => Self::HALT,
            CPUInstr::Set => Self::SET,

            CPUInstr::UAdd => Self::UADD,
            CPUInstr::USub => Self::USUB,
            CPUInstr::UMul => Self::UMUL,
            CPUInstr::UMod => Self::UMOD,
            CPUInstr::UDiv => Self::UDIV,

            CPUInstr::UOr => Self::UOR,
            CPUInstr::UXor => Self::UXOR,
            CPUInstr::UAnd => Self::UAND,
            CPUInstr::UNot => Self::UNOT,

            CPUInstr::UShl => Self::USHL,
            CPUInstr::UShr => Self::USHR,

            CPUInstr::IAdd => Self::IADD,
            CPUInstr::ISub => Self::ISUB,
            CPUInstr::IMul => Self::IMUL,
            CPUInstr::IMod => Self::IMOD,
            CPUInstr::IDiv => Self::IDIV,

            CPUInstr::IOr => Self::IOR,
            CPUInstr::IXor => Self::IXOR,
            CPUInstr::IAnd => Self::IAND,
            CPUInstr::INot => Self::INOT,

            CPUInstr::IShl => Self::ISHL,
            CPUInstr::IShr => Self::ISHR,

            CPUInstr::FAdd => Self::FADD,
            CPUInstr::FSub => Self::FSUB,
            CPUInstr::FMul => Self::FMUL,
            CPUInstr::FDiv => Self::FDIV,

            CPUInstr::LOr => Self::LOR,
            CPUInstr::LXor => Self::LXOR,
            CPUInstr::LAnd => Self::LAND,
            CPUInstr::LNot => Self::LNOT,

            CPUInstr::Jump => Self::JUMP,
            CPUInstr::JumpIf => Self::JUMPIF,
            CPUInstr::JumpIfNot => Self::JUMPIFNOT,

            CPUInstr::UEqual => Self::UEQUAL,
            CPUInstr::UGreater => Self::UGREATER,
            CPUInstr::UGreaterEqual => Self::UGREATEREQUAL,
            CPUInstr::ULess => Self::ULESS,
            CPUInstr::ULessEqual => Self::ULESSEQUAL,

            CPUInstr::IEqual => Self::IEQUAL,
            CPUInstr::IGreater => Self::IGREATER,
            CPUInstr::IGreaterEqual => Self::IGREATEREQUAL,
            CPUInstr::ILess => Self::ILESS,
            CPUInstr::ILessEqual => Self::ILESSEQUAL,

            CPUInstr::FEqual => Self::FEQUAL,
            CPUInstr::FGreater => Self::FGREATER,
            CPUInstr::FGreaterEqual => Self::FGREATEREQUAL,
            CPUInstr::FLess => Self::FLESS,
            CPUInstr::FLessEqual => Self::FLESSEQUAL,

            CPUInstr::Push => Self::PUSH,
            CPUInstr::Pop => Self::POP,

            CPUInstr::Call => Self::CALL,
            CPUInstr::Ret => Self::RET,

            CPUInstr::Store => Self::STORE,
            CPUInstr::Load => Self::LOAD,

            CPUInstr::Offset => Self::OFFSET,

            CPUInstr::Syscall => Self::SYSCALL,

            CPUInstr::Nop => Self::NOP,
        }
    }

    /// Read an instruction from a byte
    pub const fn from_byte(byte: u8) -> Result<Self, CPUError> {
        match byte {
            Self::HALT => Ok(CPUInstr::Halt),
            Self::SET => Ok(CPUInstr::Set),

            Self::UADD => Ok(CPUInstr::UAdd),
            Self::USUB => Ok(CPUInstr::USub),
            Self::UMUL => Ok(CPUInstr::UMul),
            Self::UMOD => Ok(CPUInstr::UMod),
            Self::UDIV => Ok(CPUInstr::UDiv),

            Self::UOR => Ok(CPUInstr::UOr),
            Self::UXOR => Ok(CPUInstr::UXor),
            Self::UAND => Ok(CPUInstr::UAnd),
            Self::UNOT => Ok(CPUInstr::UNot),

            Self::USHL => Ok(CPUInstr::UShl),
            Self::USHR => Ok(CPUInstr::UShr),

            Self::IADD => Ok(CPUInstr::IAdd),
            Self::ISUB => Ok(CPUInstr::ISub),
            Self::IMUL => Ok(CPUInstr::IMul),
            Self::IMOD => Ok(CPUInstr::IMod),
            Self::IDIV => Ok(CPUInstr::IDiv),

            Self::IOR => Ok(CPUInstr::IOr),
            Self::IXOR => Ok(CPUInstr::IXor),
            Self::IAND => Ok(CPUInstr::IAnd),
            Self::INOT => Ok(CPUInstr::INot),

            Self::ISHL => Ok(CPUInstr::IShl),
            Self::ISHR => Ok(CPUInstr::IShr),

            Self::FADD => Ok(CPUInstr::FAdd),
            Self::FSUB => Ok(CPUInstr::FSub),
            Self::FMUL => Ok(CPUInstr::FMul),
            Self::FDIV => Ok(CPUInstr::FDiv),

            Self::LOR => Ok(CPUInstr::LOr),
            Self::LXOR => Ok(CPUInstr::LXor),
            Self::LAND => Ok(CPUInstr::LAnd),
            Self::LNOT => Ok(CPUInstr::LNot),

            Self::JUMP => Ok(CPUInstr::Jump),
            Self::JUMPIF => Ok(CPUInstr::JumpIf),
            Self::JUMPIFNOT => Ok(CPUInstr::JumpIfNot),

            Self::UEQUAL => Ok(CPUInstr::UEqual),
            Self::UGREATER => Ok(CPUInstr::UGreater),
            Self::UGREATEREQUAL => Ok(CPUInstr::UGreaterEqual),
            Self::ULESS => Ok(CPUInstr::ULess),
            Self::ULESSEQUAL => Ok(CPUInstr::ULessEqual),

            Self::IEQUAL => Ok(CPUInstr::IEqual),
            Self::IGREATER => Ok(CPUInstr::IGreater),
            Self::IGREATEREQUAL => Ok(CPUInstr::IGreaterEqual),
            Self::ILESS => Ok(CPUInstr::ILess),
            Self::ILESSEQUAL => Ok(CPUInstr::ILessEqual),

            Self::FEQUAL => Ok(CPUInstr::FEqual),
            Self::FGREATER => Ok(CPUInstr::FGreater),
            Self::FGREATEREQUAL => Ok(CPUInstr::FGreaterEqual),
            Self::FLESS => Ok(CPUInstr::FLess),
            Self::FLESSEQUAL => Ok(CPUInstr::FLessEqual),

            Self::PUSH => Ok(CPUInstr::Push),
            Self::POP => Ok(CPUInstr::Pop),
            Self::CALL => Ok(CPUInstr::Call),
            Self::RET => Ok(CPUInstr::Ret),

            Self::OFFSET => Ok(CPUInstr::Offset),

            Self::STORE => Ok(CPUInstr::Store),
            Self::LOAD => Ok(CPUInstr::Load),

            Self::SYSCALL => Ok(CPUInstr::Syscall),

            Self::NOP => Ok(CPUInstr::Nop),

            _ => Err(CPUError::InvalidInstruction(byte)),
        }
    }
}



/// Represents the type of the operand
/// # Example:
/// For example, in a [`CpuInstr::Add`] instruction,
/// both operands are preceded by the operand type like this:
/// - [`CPUInstr::ADD`]
/// - [`OperandType::Immediate`]
/// - `100`
/// - [`OperandType::Immediate`]
/// - `200`
///
/// Adds immediate value `100` to immediate value `200`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OperandType {
    MemoryAddress,  // Represents a memory address
    Register,       // Represents a CPU register
    Flag,           // Represents a CPU flag
    Immediate       // Represents an immediate value (which is 8 bytes)
}

impl OperandType {
    define_opcodes!(
        MEMORY_ADDRESS,
        REGISTER,
        FLAG,
        IMMEDIATE
    );

    /// Represents the operand type as a byte
    pub const fn as_byte(&self) -> u8 {
        match &self {
            OperandType::MemoryAddress => Self::MEMORY_ADDRESS,
            OperandType::Register => Self::REGISTER,
            OperandType::Flag => Self::FLAG,
            OperandType::Immediate => Self::IMMEDIATE,
        }
    }

    /// Reads the operand type from a byte
    pub const fn from_byte(byte: u8) -> Result<Self, CPUError> {
        match byte {
            Self::MEMORY_ADDRESS => Ok(OperandType::MemoryAddress),
            Self::REGISTER => Ok(OperandType::Register),
            Self::FLAG => Ok(OperandType::Flag),
            Self::IMMEDIATE => Ok(OperandType::Immediate),
            _ => Err(CPUError::InvalidOperandType(byte))
        }
    }
}



/// Represents a flag in the CPU (zero, overflow, etc.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CPUFlag {
    Zero, 
    Sign, 
    Overflow,
}

impl CPUFlag {
    define_opcodes!(
        ZERO,
        SIGN,
        OVERFLOW,
    );

    /// Represents the flag as a byte
    pub const fn as_byte(&self) -> u8 {
        match &self {
            CPUFlag::Zero => Self::ZERO,
            CPUFlag::Sign => Self::SIGN,
            CPUFlag::Overflow => Self::OVERFLOW,
        }
    }

    /// Reads the flag type from a byte
    pub const fn from_byte(byte: u8) -> Result<Self, CPUError> {
        match byte {
            Self::ZERO => Ok(CPUFlag::Zero),
            Self::SIGN => Ok(CPUFlag::Sign),
            Self::OVERFLOW => Ok(CPUFlag::Overflow),
            _ => Err(CPUError::InvalidFlag(byte))
        }
    }
}




/// Represents our simulated CPU interface
pub struct CPU {
    pub ram: RAM,

    /// - 8 general-purpose 8-byte registers
    /// - 1 special accumulator register
    registers: [RegType; CPU::REG_COUNT],

    /// Base stack pointer
    sb: RamAddr,

    /// Current stack pointer \
    /// Points to first memory address after the stack like this: \
    /// ```plain
    /// ... 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 | 0 0 0 0 0 0 0 0 ...
    ///                              sp ^   ^ stack ends here
    /// ```
    sp: RamAddr,

    /// The minimum address the stack can grow to (stack grows downwards)
    min_stack_addr: RamAddr,

    /// Special register which temporarily stores the current instruction
    instr_reg: CPUInstr,

    /// Holds the address of the next instruction to execute
    prog_counter: Option<RamAddr>,

    /// Set when an operation results in zero
    zero_flag: bool,

    /// Indicates whether the result of an operation is negative (based on the most significant bit)
    sign_flag: bool,

    /// Indicates when an arithmetic overflow occurs in signed arithmetic.
    overflow_flag: bool,

    /// Counts the instructions.
    /// At the moment exists only for debugging purposes, might delete later
    instruction_counter: usize,
}

/// General CPU methods
impl CPU {
    // Constants used in the CPU

    /***********************************************************/
    /* Constants related to registers                          */
    /***********************************************************/
    /// Represents the amount of general-purpose registers in the CPU
    pub const GEN_REG_COUNT: usize = 8;

    /// Represents the index of special accumulator register
    pub const ACCU_IDX: usize = Self::GEN_REG_COUNT;

    /// Represents the maximum limit of bytes the stack can grow to regardless of storage
    /// Note: if available RAM is less than this constant, another value will be used
    /// (refer to [`Self::with_ram`] implementation for details)
    pub const STACK_SIZE_LIMIT: usize = 32 * 1024; // 32KB

    /// Represents the total amount of registers in the CPU
    /// - [`GEN_REG_COUNT`] general-purpose
    /// - 1 special accumulator
    pub const REG_COUNT: usize = Self::GEN_REG_COUNT + 1;

    /// Represents the "index" of SP register. Although in our struct it's stored separately,
    /// we still refer to it by its "index" for simplicity purpose
    pub const SP_IDX: usize = Self::ACCU_IDX + 1;

    /// Represents the "index" of SB register. Although in our struct it's stored separately,
    /// we still refer to it by its "index" for simplicity purpose
    pub const SB_IDX: usize = Self::SP_IDX + 1;

    /***********************************************************/
    /* Amount of bytes of each type of operands                */
    /***********************************************************/

    /// Represents the amount of bytes 1 CPU instruction takes
    pub const INSTRUCTION_SIZE: usize = 1;

    /// Represents the amount of bytes 1 operand type takes
    pub const OPERAND_TYPE_SIZE: usize = 1;

    /// Represents the amount of bytes 1 memory address takes
    pub const MEMORY_ADDRESS_SIZE: usize = 8;

    /// Represents the amount of bytes 1 register number takes
    pub const REG_NUM_SIZE: usize = 1;

    /// Represents the amount of bytes 1 flag takes
    pub const FLAG_TYPE_SIZE: usize = 1;

    /// Represents the amount of bytes 1 immediate value takes \
    /// All immediate values are 8 bytes, but their bytes can be interpreted as float, i64, u64, etc.
    pub const IMMEDIATE_VALUE_SIZE: usize = 8;


    /// Represents the address of the first instruction for the CPU
    pub const START_ADDR: RamAddr = RamAddr(0x0_usize);

    pub fn with_ram(ram: RAM) -> Self {
        // Calculate the minimum address stack can grow to
        // The algorithm is `MIN(STACK_SIZE_LIMIT, ram.size() / 4)`
        let last_addr = ram.last_addr();
        let max_stack_size = Self::STACK_SIZE_LIMIT.min(ram.size() / 4);
        let min_stack_addr = last_addr.sub(max_stack_size).unwrap();

        Self {
            ram,
            registers: [0 as RegType; Self::REG_COUNT],
            sb: last_addr,
            sp: last_addr,
            min_stack_addr,
            instr_reg: CPUInstr::Halt,
            prog_counter: Some(CPU::START_ADDR),
            zero_flag: false,
            sign_flag: false,
            overflow_flag: false,
            instruction_counter: 0,
        }
    }

    /// Starts executing instructions
    pub fn start(&mut self) -> Result<(), ErrorType> {
        while self.prog_counter.is_some() {
            self.execute_next()?;
        }
        println!("CPU halted!");
        Ok(())
    }

    /// Fetch and execute the next instruction
    fn execute_next(&mut self) -> Result<(), ErrorType> {
        // The None case for program counter was already checked in the main loop, so unwrap it
        let mut pc = self.prog_counter.unwrap();

        // Fetch the byte at program counter address
        let instr_byte = self.ram.read_byte(pc)?;

        // Convert the byte representing the instruction to CPUInstr
        self.instr_reg = CPUInstr::from_byte(instr_byte)?;

        // Increment the program counter
        pc.inc(Self::INSTRUCTION_SIZE)?;
        self.set_program_counter(pc);

        let res = match self.instr_reg {
            CPUInstr::Halt => self.execute_halt(),
            CPUInstr::Set => self.execute_set(),
            CPUInstr::UAdd => self.execute_u_add(),
            CPUInstr::USub => self.execute_u_sub(),
            CPUInstr::UMul => self.execute_u_mul(),
            CPUInstr::UMod => self.execute_u_mod(),
            CPUInstr::UDiv => self.execute_u_div(),
            CPUInstr::UOr => self.execute_u_or(),
            CPUInstr::UXor => self.execute_u_xor(),
            CPUInstr::UAnd => self.execute_u_and(),
            CPUInstr::UNot => self.execute_u_not(),
            CPUInstr::UShl => self.execute_u_shl(),
            CPUInstr::UShr => self.execute_u_shr(),
            CPUInstr::IAdd => self.execute_i_add(),
            CPUInstr::ISub => self.execute_i_sub(),
            CPUInstr::IMul => self.execute_i_mul(),
            CPUInstr::IMod => self.execute_i_mod(),
            CPUInstr::IDiv => self.execute_i_div(),
            CPUInstr::IOr => self.execute_i_or(),
            CPUInstr::IXor => self.execute_i_xor(),
            CPUInstr::IAnd => self.execute_i_and(),
            CPUInstr::INot => self.execute_i_not(),
            CPUInstr::IShl => self.execute_i_shl(),
            CPUInstr::IShr => self.execute_i_shr(),
            CPUInstr::FAdd => self.execute_f_add(),
            CPUInstr::FSub => self.execute_f_sub(),
            CPUInstr::FMul => self.execute_f_mul(),
            CPUInstr::FDiv => self.execute_f_div(),
            CPUInstr::LOr => self.execute_l_or(),
            CPUInstr::LXor => self.execute_l_xor(),
            CPUInstr::LAnd => self.execute_l_and(),
            CPUInstr::LNot => self.execute_l_not(),
            CPUInstr::Jump => self.execute_jump(),
            CPUInstr::JumpIf => self.execute_jump_if(),
            CPUInstr::JumpIfNot => self.execute_jump_if_not(),
            CPUInstr::UEqual => self.execute_u_equal(),
            CPUInstr::UGreater => self.execute_u_greater(),
            CPUInstr::UGreaterEqual => self.execute_u_greater_equal(),
            CPUInstr::ULess => self.execute_u_less(),
            CPUInstr::ULessEqual => self.execute_u_less_equal(),
            CPUInstr::IEqual => self.execute_i_equal(),
            CPUInstr::IGreater => self.execute_i_greater(),
            CPUInstr::IGreaterEqual => self.execute_i_greater_equal(),
            CPUInstr::ILess => self.execute_i_less(),
            CPUInstr::ILessEqual => self.execute_i_less_equal(),
            CPUInstr::FEqual => self.execute_f_equal(),
            CPUInstr::FGreater => self.execute_f_greater(),
            CPUInstr::FGreaterEqual => self.execute_f_greater_equal(),
            CPUInstr::FLess => self.execute_f_less(),
            CPUInstr::FLessEqual => self.execute_f_less_equal(),
            CPUInstr::Push => self.execute_push(),
            CPUInstr::Pop => self.execute_pop(),
            CPUInstr::Call => self.execute_call(),
            CPUInstr::Ret => self.execute_ret(),
            CPUInstr::Offset => self.execute_offset(),
            CPUInstr::Store => self.execute_store(),
            CPUInstr::Load => self.execute_load(),
            CPUInstr::Syscall => self.execute_syscall(),
            CPUInstr::Nop => Ok(())
        };

        self.inc_instruction_counter();

        res
    }

    /// At the moment only exists for debugging purposes, might delete later | TODO: delete
    fn inc_instruction_counter(&mut self) {
        self.instruction_counter += 1;
        self.print();
        if DBG_SLEEP != 0 {
            std::thread::sleep(std::time::Duration::from_millis(DBG_SLEEP as u64));
        }
    }
}


/// This section contains main CPU instructions
/// Most of the instruction call helper methods instead of operating directly
impl CPU {
    // From here on in the comments:
    // Operand types are marked by op_t1, op_t2, ...
    // Operands are marked by op1, op2, ...

    /// Halt
    fn execute_halt(&mut self) -> Result<(), ErrorType> {
        self.halt_program_counter();
        Ok(())
    }

    /// Set op_t1 op1 op_t2 op2
    fn execute_set(&mut self) -> Result<(), ErrorType> {
        let operand_type = self.read_operand_type()?;
        match operand_type {
            OperandType::MemoryAddress => {
                let to_set = self.read_addr()?;
                let value: SingleByte = self.extract_operand()?.reinterpret();
                self.ram.write_byte(value, to_set)?;
            }
            OperandType::Register => {
                let to_set = self.read_reg()?;
                let value: RegType = self.extract_operand()?.reinterpret();
                self.set_reg(to_set, value)?;
            }
            OperandType::Flag => {
                let to_set = self.read_flag()?;
                let value: bool = self.extract_operand()?.as_bool();
                self.set_flag(to_set, value);
            }
            OperandType::Immediate => {
                return Err(CPUError::OperandTypeNotAllowed(operand_type).into());
            }
        }
        Ok(())
    }


    /// UAdd op_t1 op1 op_t2 op2
    fn execute_u_add(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| x.overflowing_add(y))
    }
    /// USub op_t1 op1 op_t2 op2
    fn execute_u_sub(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| x.overflowing_sub(y))
    }
    /// UMul op_t1 op1 op_t2 op2
    fn execute_u_mul(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| x.overflowing_mul(y))
    }
    /// UMod op_t1 op1 op_t2 op2
    ///
    /// note: if op2 is zero, the result is also zero and overflow flag is enabled
    fn execute_u_mod(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| {
            if y == 0 {
                (0, true)
            } else {
                (x % y, false)
            }
        })
    }
    /// UDiv op_t1 op1 op_t2 op2
    ///
    /// note: if op2 is zero, the result is also zero and overflow flag is enabled
    fn execute_u_div(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| {
            if y == 0 {
                (0, true)
            } else {
                x.overflowing_div(y)
            }
        })
    }

    /// UOr op_t1 op1 op_t2 op2
    fn execute_u_or(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| (x.bitor(y), false)) // Bitwise OR cannot overflow
    }
    /// UXor op_t1 op1 op_t2 op2
    fn execute_u_xor(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| (x.bitxor(y), false)) // Bitwise XOR cannot overflow

    }
    /// UAnd op_t1 op1 op_t2 op2
    fn execute_u_and(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| (x.bitand(y), false)) // Bitwise AND cannot overflow
    }
    /// UNot op_t1 op1
    fn execute_u_not(&mut self) -> Result<(), ErrorType> {
        self.unary_arith_op(|x: Unsigned64| (!x, false)) // Bitwise NOT cannot overflow
    }

    /// UShl op_t1 op1 op_t2 op2
    ///
    /// note: op2 must be safely convertible to `u32`
    fn execute_u_shl(&mut self) -> Result<(), ErrorType> {
        // TODO: add safe wrapper for `y as u32`
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| x.overflowing_shl(y as u32))
    }
    /// UShr op_t1 op1 op_t2 op2
    ///
    /// note: op2 must be safely convertible to `u32`
    fn execute_u_shr(&mut self) -> Result<(), ErrorType> {
        // TODO: add safe wrapper for `y as u32`
        self.binary_arith_op(|x: Unsigned64, y: Unsigned64| x.overflowing_shr(y as u32))
    }


    /// IAdd op_t1 op1 op_t2 op2
    fn execute_i_add(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| x.overflowing_add(y))
    }
    /// ISub op_t1 op1 op_t2 op2
    fn execute_i_sub(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| x.overflowing_sub(y))
    }
    /// IMul op_t1 op1 op_t2 op2
    fn execute_i_mul(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| x.overflowing_mul(y))
    }
    /// IMod op_t1 op1 op_t2 op2
    ///
    /// note: if op2 is zero, the result is also zero and overflow flag is enabled
    fn execute_i_mod(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| {
            if y == 0 {
                (0, true)
            } else {
                (x % y, false)
            }
        })
    }
    /// IDiv op_t1 op1 op_t2 op2
    ///
    /// note: if op2 is zero, the result is also zero and overflow flag is enabled
    fn execute_i_div(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| {
            if y == 0 {
                (0, true)
            } else {
                x.overflowing_div(y)
            }
        })
    }

    /// IOr op_t1 op1 op_t2 op2
    fn execute_i_or(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| (x.bitor(y), false)) // Bitwise OR cannot overflow
    }
    /// IXor op_t1 op1 op_t2 op2
    fn execute_i_xor(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| (x.bitxor(y), false)) // Bitwise XOR cannot overflow

    }
    /// IAnd op_t1 op1 op_t2 op2
    fn execute_i_and(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Signed64, y: Signed64| (x.bitand(y), false)) // Bitwise AND cannot overflow
    }
    /// INot op_t1 op1
    fn execute_i_not(&mut self) -> Result<(), ErrorType> {
        self.unary_arith_op(|x: Signed64| (!x, false)) // Bitwise NOT cannot overflow
    }

    /// IShl op_t1 op1 op_t2 op2
    ///
    /// note: op2 must be safely convertible to `u32`
    fn execute_i_shl(&mut self) -> Result<(), ErrorType> {
        // TODO: add safe wrapper for `y as u32`
        self.binary_arith_op(|x: Signed64, y: Signed64| x.overflowing_shl(y as u32))
    }
    /// IShr op_t1 op1 op_t2 op2
    ///
    /// note: op2 must be safely convertible to `u32`
    fn execute_i_shr(&mut self) -> Result<(), ErrorType> {
        // TODO: add safe wrapper for `y as u32`
        self.binary_arith_op(|x: Signed64, y: Signed64| x.overflowing_shr(y as u32))
    }


    /// FAdd op_t1 op1 op_t2 op2
    fn execute_f_add(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Float64, y: Float64| (x + y, false)) // Overflow is checked inside by .is_infinite()
    }
    /// FSub op_t1 op1 op_t2 op2
    fn execute_f_sub(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Float64, y: Float64| (x - y, false)) // Overflow is checked inside by .is_infinite()
    }
    /// FMul op_t1 op1 op_t2 op2
    fn execute_f_mul(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Float64, y: Float64| (x * y, false)) // Overflow is checked inside by .is_infinite()
    }
    /// FDiv op_t1 op1 op_t2 op2
    fn execute_f_div(&mut self) -> Result<(), ErrorType> {
        self.binary_arith_op(|x: Float64, y: Float64| (x / y, false)) // Overflow is checked inside by .is_infinite()
    }

    /// LOr op_t1 op1 op_t2 op2
    fn execute_l_or(&mut self) -> Result<(), ErrorType> {
        self.binary_logical_op(|x, y| x || y)
    }
    /// LXor op_t1 op1 op_t2 op2
    fn execute_l_xor(&mut self) -> Result<(), ErrorType> {
        self.binary_logical_op(|x, y| x ^ y)
    }
    /// LAnd op_t1 op1 op_t2 op2
    fn execute_l_and(&mut self) -> Result<(), ErrorType> {
        self.binary_logical_op(|x, y| x && y)
    }
    /// LNot op_t1 op1 op_t2 op2
    fn execute_l_not(&mut self) -> Result<(), ErrorType> {
        self.unary_logical_op(|x| !x)
    }

    /// Jump op_t1 jump_to
    ///
    /// note: op_t1 can ONLY be:
    /// - [`OperandType::Register`]
    /// - [`OperandType::MemoryAddress`]
    fn execute_jump(&mut self) -> Result<(), ErrorType> {
        let addr = self.extract_addr()?;
        self.set_program_counter(addr);
        Ok(())
    }
    /// JumpIf op_t1 condition op_t2 jump_to
    ///
    /// note: op_t2 can ONLY be:
    /// - [`OperandType::Register`]
    /// - [`OperandType::MemoryAddress`]
    fn execute_jump_if(&mut self) -> Result<(), ErrorType> {
        self.conditional_jump(|x| x.as_bool())
    }
    /// JumpIfNot op_t1 condition op_t2 jump_to
    ///
    /// note: op_t2 can ONLY be:
    /// - [`OperandType::Register`]
    /// - [`OperandType::MemoryAddress`]
    fn execute_jump_if_not(&mut self) -> Result<(), ErrorType> {
        self.conditional_jump(|x| !x.as_bool())
    }

    /// UEquals op_t1 op1 op_t2 op2
    fn execute_u_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Unsigned64, y: Unsigned64| x == y)
    }
    /// UGreater op_t1 op1 op_t2 op2
    fn execute_u_greater(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Unsigned64, y: Unsigned64| x > y)
    }
    /// UGreaterEqual op_t1 op1 op_t2 op2
    fn execute_u_greater_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Unsigned64, y: Unsigned64| x >= y)
    }
    /// ULess op_t1 op1 op_t2 op2
    fn execute_u_less(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Unsigned64, y: Unsigned64| x < y)
    }
    /// ULessEqual op_t1 op1 op_t2 op2
    fn execute_u_less_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Unsigned64, y: Unsigned64| x <= y)
    }

    /// IEquals op_t1 op1 op_t2 op2
    fn execute_i_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Signed64, y: Signed64| x == y)
    }
    /// IGreater op_t1 op1 op_t2 op2
    fn execute_i_greater(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Signed64, y: Signed64| x > y)
    }
    /// IGreaterEqual op_t1 op1 op_t2 op2
    fn execute_i_greater_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Signed64, y: Signed64| x >= y)
    }
    /// ILess op_t1 op1 op_t2 op2
    fn execute_i_less(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Signed64, y: Signed64| x < y)
    }
    /// ILessEqual op_t1 op1 op_t2 op2
    fn execute_i_less_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Signed64, y: Signed64| x <= y)
    }

    /// FEquals op_t1 op1 op_t2 op2
    fn execute_f_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Float64, y: Float64| x == y)
    }
    /// FGreater op_t1 op1 op_t2 op2
    fn execute_f_greater(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Float64, y: Float64| x > y)
    }
    /// FGreaterEqual op_t1 op1 op_t2 op2
    fn execute_f_greater_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Float64, y: Float64| x >= y)
    }
    /// FLess op_t1 op1 op_t2 op2
    fn execute_f_less(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Float64, y: Float64| x < y)
    }
    /// FLessEqual op_t1 op1 op_t2 op2
    fn execute_f_less_equal(&mut self) -> Result<(), ErrorType> {
        self.relational_op(|x: Float64, y: Float64| x <= y)
    }

    /// Push op_t1 op1
    fn execute_push(&mut self) -> Result<(), ErrorType> {
        let value = self.extract_operand()?;
        self.push_to_stack(value)?;
        Ok(())
    }

    /// Pop op_t1 op1
    /// `op` is one byte which represents a register number
    fn execute_pop(&mut self) -> Result<(), ErrorType> {
        let op_t1 = self.read_operand_type()?;
        if op_t1 != OperandType::Register {
            return Err(ErrorType::from(CPUError::OperandTypeNotAllowed(op_t1)))
        }

        let reg_num = self.read_reg()?;
        // Reinterpret the bytes as `RegType` to be able to store in the register
        let value: RegType = self.pop_from_stack()?.reinterpret();
        self.set_reg(reg_num, value)?;
        Ok(())
    }

    /// Call op_t1 op1
    ///
    /// note: op_t1 can ONLY be:
    /// - [`OperandType::Register`]
    /// - [`OperandType::MemoryAddress`]
    fn execute_call(&mut self) -> Result<(), ErrorType> {
        // Read a memory address to call
        let addr = self.extract_addr()?;

        // Get the return address (which is the memory address of the next instruction, which is
        // the program counter since `read_addr_for_jump` incremented it)
        let return_address = self.prog_counter.unwrap();

        // Reinterpret the bytes
        let addr_value: EightBytes = (return_address.0 as Unsigned64).reinterpret();

        // Push the return address to the stack
        self.push_to_stack(addr_value)?;

        // Jump to the address
        self.set_program_counter(addr);

        Ok(())
    }

    /// Ret
    fn execute_ret(&mut self) -> Result<(), ErrorType> {
        // Read the return address from the stack
        let addr_value = self.pop_from_stack()?;
        // Reinterpret the bytes to u64 (which represents a memory address) and wrap inside RamAddr
        let return_address = RamAddr(addr_value.reinterpret::<Unsigned64>() as usize);
        if self.ram.is_valid_addr(return_address) {
            // Jump to the return address
            self.set_program_counter(return_address);
            Ok(())
        } else {
            Err(ErrorType::from(CPUError::InvalidReturn(return_address)))
        }
    }

    /// Offset op_t1 op1 op_t2 op2
    ///
    /// - sets the Overflow flag if the offsetting overflowed
    ///
    /// note:
    /// - op_t1 can ONLY be [`OperandType::MemoryAddress`] or [`OperandType::Register`]
    /// - op2 is interpreted as bytes count
    ///
    /// NOTE: To get a value at (sb + offset), one must do Offset sb (offset+1) \
    /// Here is why:
    /// ```plain
    /// 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 2 2 2 2
    ///                                       ^ sb
    /// Offset sb -8
    ///                         _______________
    /// 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 2 2 2 2
    ///                       ^ offset sb
    /// ```
    /// Now when we do `Load sb`, the bytes loaded will be `0 1 1 1 1 2 2 2`, not
    /// `1 1 1 1 2 2 2 2`. If we want to get the latter, we would need to do `Offset sb -7`
    ///
    /// So the algorithm to get bytes at `[offset; offset + 7]` is:
    /// ```plain
    /// Offset sb (offset + 1)
    /// Load (register) accu
    /// ```
    fn execute_offset(&mut self) -> Result<(), ErrorType> {
        let mut addr = self.extract_addr()?;
        let offset: Signed64 = self.extract_operand()?.reinterpret::<Signed64>();

        if offset == i64::MIN {
            // todo: maybe handle this in more graceful way?
            self.enable_flag(CPUFlag::Overflow);
            self.set_accu_reg(RegType::MAX);
            return Ok(());
        }
        
        let absolute_offset = offset.unsigned_abs() as usize;

        // Do the offset
        if offset.is_negative() {
            addr.dec(absolute_offset)?;
        } else {
            addr.inc(absolute_offset)?;
        }
        
        let result = addr_to_reg_type(addr);

        // Set the accumulator register
        self.set_accu_reg(result);

        Ok(())
    }

    /// Store op_t1 op1 op_t2 op2
    ///
    /// note: op_t2 can ONLY be [`OperandType::MemoryAddress`]
    fn execute_store(&mut self) -> Result<(), ErrorType> {
        let value = self.extract_operand()?;
        let op_t = self.read_operand_type()?;
        if op_t != OperandType::MemoryAddress {
            return Err(ErrorType::from(CPUError::OperandTypeNotAllowed(op_t)));
        }

        let dest_addr = self.read_addr()?;
        self.ram.write_bytes(&value.to_bytes(), dest_addr)?;
        Ok(())
    }

    /// Load op_t1 op1 op_t2 op2
    ///
    /// note: op_t1 can ONLY be [`OperandType::MemoryAddress`] or [`OperandType::Register`]
    ///       op_t2 can ONLY be [`OperandType::Register`]
    fn execute_load(&mut self) -> Result<(), ErrorType> {
        let source_addr = self.extract_addr()?;

        let op_t2 = self.read_operand_type()?;
        if op_t2  != OperandType::Register { // Check if operand 2 is valid type
            return Err(ErrorType::from(CPUError::OperandTypeNotAllowed(op_t2)));
        }
        let dest_reg = self.read_reg()?;

        // Read 8 bytes starting from that address
        let bytes = self.ram.read_bytes::<8>(source_addr)?;
        // Load the value
        let value = RegType::from_bytes(bytes);

        self.set_reg(dest_reg, value)?;
        Ok(())
    }


    fn execute_syscall(&mut self) -> Result<(), ErrorType> { todo!() }
}


/// This section contains *general helper* methods for:
/// 1. Binary and unary arithmetic operators
/// 2. Binary and unary logical operators
/// 3. Relational (comparison) operators
impl CPU {
    /// Executes an **Arithmetic**, **Binary** (two arguments) operator.
    /// ## Usage
    /// The argument function is `(T, T) -> (T, bool)`, where `T` is `Reinterpret64 + SignClassifiable` \
    /// `bool` value in the returned tuple indicates whether the operator overflowed
    /// so the right flags can be set. \
    /// An example of `F` is
    /// ```rust
    /// |x, y| x.overflowing_add(y) // overflowing_add returns (Self, bool)
    /// ```
    /// In case of floating-point operators, for example, an addition, one should pass
    /// ```rust
    /// |x, y| (x + y, false) // overflow is always false
    /// ```
    /// Since Rust handles floating-point overflow in a different way, this method will
    /// internally check if the result is infinite (this means that the operator overflowed) and
    /// set according flags, so no need for `F` to return the overflow state
    ///
    /// ## Flags and registers
    /// This method:
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Overflow` flag if the operator overflowed.
    /// - Sets the `Zero` flag if the result is zero.
    /// - Sets the `Sign` flag if the result is negative.
    fn binary_arith_op<T, F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        T: Reinterpret64 + SignClassifiable,
        F: Fn(T, T) -> (T, bool)
    {
        let lhs = self.extract_operand()?.reinterpret();
        let rhs = self.extract_operand()?.reinterpret();

        let (result, overflowed) = op(lhs, rhs);
        self.handle_arith_result(result, overflowed);
        Ok(())
    }

    /// Executes an **Arithmetic**, **Unary** (one argument) operator.
    /// ## Usage
    /// The argument function is `(T) -> (T, bool)`, where `T` is `Reinterpret64 + SignClassifiable` \
    /// `bool` value in the returned tuple indicates whether the operator overflowed
    /// so the right flags can be set. \
    /// An example of `F` is
    /// ```rust
    /// |x| x.overflowing_neg() // overflowing_neg returns (Self, bool)
    /// ```
    /// In case of floating-point operators, for example, an addition, one should pass
    /// ```rust
    /// |x| (-x, false) // overflow is always false
    /// ```
    /// Since Rust handles floating-point overflow in a different way, this method will
    /// internally check if the result is infinite (this means that the operator overflowed) and
    /// set according flags, so no need for `F` to return the overflow state
    ///
    /// ## Flags and registers
    /// This method:
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Overflow` flag if the operator overflowed.
    /// - Sets the `Zero` flag if the result is zero.
    /// - Sets the `Sign` flag if the result is negative.
    fn unary_arith_op<T, F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        T: Reinterpret64 + SignClassifiable,
        F: Fn(T) -> (T, bool)
    {
        let lhs = self.extract_operand()?.reinterpret();
        let (result, overflowed) = op(lhs);
        self.handle_arith_result(result, overflowed);
        Ok(())
    }


    /// Executes a **Logical**, **Binary** (two arguments) operator.
    /// ## Usage
    /// The argument function is `(bool, bool) -> bool` \
    /// An example of `F` is
    /// ```rust
    /// |x, y| x && y // logical AND operator
    /// ```
    /// ## Flags and registers
    /// This method:
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Zero` flag if the result is `false`.
    /// - Does **not** set the `Overflow` flag since logical operators operate on `bool`-s and cannot
    ///     overflow
    fn binary_logical_op<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(bool, bool) -> bool
    {
        let lhs = self.extract_operand()?.as_bool();
        let rhs = self.extract_operand()?.as_bool();
        let result = op(lhs, rhs);
        self.handle_bool_result(result);
        Ok(())
    }


    /// Executes a **Logical**, **Unary** (one argument) operator.
    /// ## Usage
    /// The argument function is `(bool) -> bool` \
    /// An example of `F` is
    /// ```rust
    /// |x| x == 0 // logical NOT operator
    /// ```
    /// ## Flags and registers
    /// This method:
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Zero` flag if the result is `false`.
    /// - Does **not** set the `Overflow` flag since logical operators operate on `bool`-s and cannot
    ///   overflow
    fn unary_logical_op<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(bool) -> bool
    {
        let lhs = self.extract_operand()?.as_bool();
        let result = op(lhs);
        self.handle_bool_result(result);
        Ok(())
    }

    /// Executes a **Relational** operator (which compares the values of two operands).
    /// ## Usage
    /// The argument function is `(T, T) -> bool` where `T` is `Reinterpret64 + SignClassifiable` \
    /// An example of `F` is
    /// ```rust
    /// |x, y| x > y // relational greater operator
    /// ```
    /// ## Flags and registers
    /// This method:
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Zero` flag if the result is `false`.
    fn relational_op<T, F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        T: Reinterpret64 + SignClassifiable,
        F: Fn(T, T) -> bool
    {
        let lhs: T = self.extract_operand()?.reinterpret();
        let rhs: T = self.extract_operand()?.reinterpret();
        let result = op(lhs, rhs);
        self.handle_bool_result(result);
        Ok(())
    }


    /// Helper method. Sets flags and registers according to an arithmetic operator result
    /// - Sets the `Overflow` flag if overflowed is `true` is `result` is infinite (this means
    ///     [`Float64`] operator overflowed).
    /// - Sets the `Zero` flag if `result` is zero.
    /// - Sets the `Sign` flag if `result` is negative.
    fn handle_arith_result<T>(&mut self, result: T, overflowed: bool)
    where T: Reinterpret64 + SignClassifiable
    {
        // Reset the flags before setting them so that they represent the result
        // of the latest operation
        self.reset_flags();

        // If the operation overflowed, set the Overflow flag
        if overflowed || result.is_infinite() {
            self.enable_flag(CPUFlag::Overflow);
        }

        // If the operation overflowed, set the Overflow flag
        // If the result is negative, set the Sign flag
        if result.is_negative() {
            self.enable_flag(CPUFlag::Sign);
        }

        // If the result is zero, set the zero flag
        if result.is_zero() {
            self.enable_flag(CPUFlag::Zero);
        }

        self.set_accu_reg(result.reinterpret());
    }

    /// Helper method. Sets flags according to a `bool` result (from logical operators,
    /// relational operators, etc.)
    /// - Sets the `Zero` flag if `result` is `false`.
    fn handle_bool_result(&mut self, result: bool)
    {
        // Reset the flags before setting them so that they represent the result
        // of the latest operation
        self.reset_flags();

        if !result {
            self.enable_flag(CPUFlag::Zero);
            self.set_accu_reg(0); // `false` is implicitly converted to `0`
        } else {
            self.set_accu_reg(1); // `true` is implicitly converted to `1`
        }
    }


    /// Helper method for conditional Jump instructions. Accepts a function which takes an operand ([`EightBytes`])
    /// and returns `bool`, indicating whether the jump should happen or not.
    /// ## Usage
    /// ```rust
    /// |x| !x.as_bool(); // for JumpIfNot instruction
    /// |x| x.as_bool();  // for JumpIf instruction
    /// ```
    /// - Does NOT set any flags
    fn conditional_jump<F>(&mut self, op: F) -> Result<(), ErrorType>
    where F: Fn(EightBytes) -> bool {
        let operand = self.extract_operand()?;

        // Read the jump address regardless of whether we are going to jump to it or not
        // This is to adjust program counter to the next instruction if the jump doesn't happen
        let mem_addr = self.extract_addr()?;

        if op(operand) {
            self.set_program_counter(mem_addr);
        }

        Ok(())
    }
}


/// Helper methods for reading and extracting different of operands and their values
impl CPU {
    /// Extracts a value from the next operand value \
    /// This method operates in the following way:
    /// - It first reads an operand type.
    /// - If the operand type is a RAM address, the methods extracts the value at that address. ([`RamUnit`])
    /// - If the operand type is a register, the method extracts the value of that register ([`RegType`])
    /// - If the operand type is a flag, the method extracts the value of that flag (`bool`)
    /// - If the operand type is an immediate value, the method extracts that value ([`EightBytes`])
    ///
    /// Then, the value is reinterpreted as [`EightBytes`] and returned
    fn extract_operand(&mut self) -> Result<EightBytes, ErrorType> {
        let result: EightBytes = match self.read_operand_type()? {
            OperandType::MemoryAddress => self.read_and_extract_addr()?.reinterpret(),
            OperandType::Register => self.read_and_extract_reg()?.reinterpret(),
            OperandType::Flag => self.read_and_extract_flag()?.reinterpret(),
            OperandType::Immediate => self.read_immediate()?
        };

        Ok(result)
    }

    /// Reads the next 8 bytes, interprets them as a ram address ([`RamAddr`]), extracts the byte at that
    /// RAM address and returns it
    /// - Increments the program counter
    fn read_and_extract_addr(&mut self) -> Result<SingleByte, ErrorType> {
        let addr = self.read_addr()?;
        let extracted = self.ram.read_byte(addr)?;
        Ok(extracted)
    }

    /// Reads the next 8 bytes, interprets them as a register number (`usize`), extracts
    /// the value from that register and returns it as [`RegType`]
    /// - Increments the program counter
    fn read_and_extract_reg(&mut self) -> Result<RegType, ErrorType> {
        let num = self.read_reg()?;
        let extracted = self.get_reg(num)?;
        Ok(extracted)
    }

    /// Reads the next 1 byte, interprets it as CPU flag [`CPUFlag`], extracts
    /// the value of that flag and returns it as `bool`
    /// - Increments the program counter
    fn read_and_extract_flag(&mut self) -> Result<bool, ErrorType> {
        let flag = self.read_flag()?;
        let extracted = self.get_flag(flag);
        Ok(extracted)
    }

    /// Reads the next 8 bytes and returns it as [`RamAddr`].
    /// - Increments the program counter
    fn read_addr(&mut self) -> Result<RamAddr, ErrorType> {
        let bytes = self.ram.read_bytes::<8>(self.prog_counter.unwrap())?;
        let addr = RamAddr(Unsigned64::from_le_bytes(bytes) as usize);
        self.inc_prog_counter(Self::MEMORY_ADDRESS_SIZE)?;
        Ok(addr)
    }

    /// Reads the next 1 byte and returns it as `usize` (the register number).
    /// - Increments the program counter
    fn read_reg(&mut self) -> Result<usize, ErrorType> {
        let num = self.ram.read_byte(self.prog_counter.unwrap())? as usize;
        self.inc_prog_counter(Self::REG_NUM_SIZE)?;
        Ok(num)
    }

    /// Reads the next 1 byte and returns it as [`CPUFlag`]
    /// - Increments the program counter
    fn read_flag(&mut self) -> Result<CPUFlag, ErrorType> {
        let byte = self.ram.read_byte(self.prog_counter.unwrap())?;
        let flag = CPUFlag::from_byte(byte)?;
        self.inc_prog_counter(Self::FLAG_TYPE_SIZE)?;
        Ok(flag)
    }

    /// Reads the next 8 bytes and returns it as [`EightBytes`]
    /// - Increments the program counter
    fn read_immediate(&mut self) -> Result<EightBytes, ErrorType> {
        let bytes = self.ram.read_bytes::<8>(self.prog_counter.unwrap())?;
        let value: EightBytes = EightBytes::from_le_bytes(bytes);
        self.inc_prog_counter(Self::IMMEDIATE_VALUE_SIZE)?;
        Ok(value)
    }

    /// Reads the next 1 byte and returns it as [`OperandType`]
    /// - Increments the program counter
    fn read_operand_type(&mut self) -> Result<OperandType, ErrorType> {
        let operand_type_byte = self.ram.read_byte(self.prog_counter.unwrap())?;
        let operand_type = OperandType::from_byte(operand_type_byte)?;
        self.inc_prog_counter(Self::OPERAND_TYPE_SIZE)?;
        Ok(operand_type)
    }

    /// Reads an address directly or from a register. The difference between this method and
    /// `read_addr` is that this method also allows to encounter a register number. \
    /// If a register number is encountered, the method will extract the value of that register,
    /// convert to `MemAddr` and return it. \
    /// This method exists to use in `Jump` and `Call` instructions not to repeat code.
    /// - Returns an error if the address is not a valid RAM address, so the return RamAddr is
    ///     always valid
    /// - Increments the program counter
    pub fn extract_addr(&mut self) -> Result<RamAddr, ErrorType> {
        let op_t = self.read_operand_type()?;
        let addr = match op_t {
            OperandType::MemoryAddress => self.read_addr()?,
            OperandType::Register => reg_type_to_addr(self.read_and_extract_reg()?),
            _ => return Err(ErrorType::from(CPUError::OperandTypeNotAllowed(op_t)))
        };

        if self.ram.is_valid_addr(addr) {
            Ok(addr)
        } else {
            Err(ErrorType::CPUError(CPUError::InvalidAddr(addr)))
        }
    }
}


/// Stack related methods
impl CPU {
    /// Pushes an 8-byte value to the stack \
    /// For example, let's say we're pushing the value `25` \
    /// Stack before:
    /// ```plain
    /// ... 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    ///                                         ^ sp
    /// ```
    /// Stack after:
    /// ```plain
    ///                             pushed value
    ///                           ________________
    /// ... 0 0 0 0 0 0 0 0 0 0 0 25 0 0 0 0 0 0 0
    ///                         ^ sp
    /// ```
    pub fn push_to_stack(&mut self, value: EightBytes) -> Result<(), ErrorType> {
        // Decrement the stack pointer, create more space
        self.dec_sp(8)?;

        // Before:
        //                           value to write
        //                           _______________
        // ... 0 0 0 0 0 0 0 0 0 0 0 1 2 3 4 5 6 7 8
        //                                         ^ sp before
        //
        // After:
        //                           value to write
        //                           _______________
        // ... 0 0 0 0 0 0 0 0 0 0 0 1 2 3 4 5 6 7 8
        //                         ^ sp after
        //
        // As you can see, the value must be written to [sp+1; sp+8]
        let write_start_addr = self.get_sp().add(1)?; // sp+1

        // Write the value to the RAM
        let bytes = value.to_bytes();
        self.ram.write_bytes(&bytes, write_start_addr)?;

        Ok(())
    }

    /// Pops an 8-byte value from the stack \
    /// For example, let's say we're popping the value `25` \
    /// Stack before:
    /// ```plain
    ///                             value to pop
    ///                           ________________
    /// ... 0 0 0 0 0 0 0 0 0 0 0 25 0 0 0 0 0 0 0
    ///                         ^ sp
    /// ```
    /// Stack after:
    /// ```plain
    /// ... 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    ///                                         ^ sp
    /// ```
    pub fn pop_from_stack(&mut self) -> Result<EightBytes, ErrorType> {
        // Before:
        //                            value to read
        //                           _______________
        // ... 0 0 0 0 0 0 0 0 0 0 0 1 2 3 4 5 6 7 8
        //                         ^ sp before
        //
        // After:
        //                           value to read
        //                           _______________
        // ... 0 0 0 0 0 0 0 0 0 0 0 1 2 3 4 5 6 7 8
        //                                         ^ sp after
        //
        // As you can see, we must read the values at [sp+1; sp+8]
        let read_from = self.get_sp().add(1)?; // sp + 1

        // Read the value from the RAM
        let bytes = self.ram.read_bytes::<8>(read_from)?; // read [sp+1; sp+8]

        // Convert the bytes to `EightBytes`
        let value = EightBytes::from_bytes(bytes);

        // Increment the stack pointer, erase the value from the stack
        self.inc_sp(8)?;

        // todo: maybe remove this section later?
        // currently it's here so the code doesn't accidentally start executing wrong
        // instruction bytes.
        // (however in `set_sp()` this case is not handled TODO)
        self.ram.write_bytes(&[0u8; 8], read_from)?;

        Ok(value)
    }

    /// Returns the value of stack base pointer
    pub const fn get_sb(&self) -> RamAddr { self.sb }

    /// Sets the value of stack base pointer
    pub const fn set_sb(&mut self, addr: RamAddr) { self.sb = addr }

    /// Returns the value of current stack pointer
    pub const fn get_sp(&self) -> RamAddr { self.sp }

    /// Sets the value of current stack pointer
    pub const fn set_sp(&mut self, addr: RamAddr) { self.sp = addr }

    /// Decrement the value of current stack pointer by specified amount of bytes (thus create more space
    /// for stack because stack grows downwards) \
    /// - Doesn't let going down beyond `self.min_stack_addr`
    pub fn dec_sp(&mut self, amount: usize) -> Result<(), ErrorType> {
        let new_sp = self.get_sp().sub(amount)?;
        if new_sp < self.min_stack_addr {
            Err(ErrorType::from(CPUError::StackOverflow))
        } else {
            self.set_sp(new_sp);
            Ok(())
        }
    }

    /// Increment the value of current stack pointer by specified amount of bytes (thus shrink the
    /// stack space because stack grows downwards) \
    /// - Doesn't let going down beyond last ram address
    pub fn inc_sp(&mut self, amount: usize) -> Result<(), ErrorType> {
        let new_sp = self.get_sp().add(amount)?;
        if new_sp > self.ram.last_addr() {
            Err(ErrorType::from(CPUError::StackUnderflow))
        } else {
            self.set_sp(new_sp);
            Ok(())
        }
    }
}


/// Program Counter related methods
impl CPU {
    /// Returns the value of the program counter - address of the next instruction
    pub fn get_program_counter(&self) -> Option<RamAddr> {
        self.prog_counter
    }

    /// Returns the value of the program counter - address of the next instruction
    pub fn set_program_counter(&mut self, addr: RamAddr) {
        self.prog_counter = Some(addr);
    }

    /// Sets the value of the program counter to `None` - address of the next instruction
    pub fn halt_program_counter(&mut self) {
        self.prog_counter = None;
    }

    /// Returns `true` if the execution was halted
    pub const fn is_halted(&self) -> bool {
        self.prog_counter.is_none()
    }

    /// Increments program counter by a value
    pub fn inc_prog_counter(&mut self, val: usize) -> Result<(), ErrorType> {
        if let Some(counter) = &mut self.prog_counter {
            counter.inc(val)?;
            Ok(())
        } else {
            panic!("Attempt to increment program counter in a halted state")
        }
    }
}


/// General register related methods
impl CPU {
    /// Returns the value of the `n`-th register if it exists, Error otherwise
    pub fn get_reg(&self, n: usize) -> Result<RegType, CPUError> {
        if n < Self::REG_COUNT {  // Set a general purpose register
            Ok(self.registers[n])
        } else if n == Self::SP_IDX { // Set the SP register
            Ok(addr_to_reg_type(self.get_sp()))
        } else if n == Self::SB_IDX { // Set the SB register
            Ok(addr_to_reg_type(self.get_sb()))
        }  else {
            Err(CPUError::InvalidRegister(n))
        }
    }

    /// Sets the value of `n`-th register to `val` if it exists, Error otherwise.
    /// - Note: Can also set the SP and SB registers by index
    pub fn set_reg(&mut self, n: usize, val: RegType) -> Result<(), CPUError> {
        if n < Self::REG_COUNT {  // Set a general purpose register
            self.registers[n] = val;
            Ok(())
        } else if n == Self::SP_IDX { // Set the SP register
            self.set_sp(reg_type_to_addr(val));
            Ok(())
        } else if n == Self::SB_IDX { // Set the SB register
            self.set_sb(reg_type_to_addr(val));
            Ok(())
        }  else {
            Err(CPUError::InvalidRegister(n))
        }
    }


    /// Returns the value of the special accumulator register
    pub fn get_accu_reg(&self) -> RegType {
        self.get_reg(Self::ACCU_IDX).unwrap()
    }

    /// Sets the value of the special accumulator register to `val`
    pub fn set_accu_reg(&mut self, val: RegType) {
        self.set_reg(Self::ACCU_IDX, val).unwrap()
    }
}


/// Flag related methods
impl CPU {
    /// Get the value of the specified flag
    pub const fn get_flag(&self, flag: CPUFlag) -> bool {
        match flag {
            CPUFlag::Zero => { self.zero_flag }
            CPUFlag::Sign => { self.sign_flag }
            CPUFlag::Overflow => { self.overflow_flag }
        }
    }

    /// Sets the specified flag to `val`
    pub const fn set_flag(&mut self, flag: CPUFlag, val: bool) {
        match flag {
            CPUFlag::Zero => { self.zero_flag = val; }
            CPUFlag::Sign => { self.sign_flag = val; }
            CPUFlag::Overflow => { self.overflow_flag = val; }
        }
    }

    /// Toggles the specified flag
    pub const fn toggle_flag(&mut self, flag: CPUFlag) {
        self.set_flag(flag, !self.get_flag(flag));
    }

    /// Enables the specified flag
    pub const fn enable_flag(&mut self, flag: CPUFlag) {
        self.set_flag(flag, true);
    }

    /// Disables the specified flag
    pub const fn disable_flag(&mut self, flag: CPUFlag) {
        self.set_flag(flag, false);
    }

    /// Sets all the flags to `false`
    pub const fn reset_flags(&mut self) {
        self.disable_flag(CPUFlag::Overflow);
        self.disable_flag(CPUFlag::Zero);
        self.disable_flag(CPUFlag::Sign);
    }
}


/// Converts a [`RegType`] to [`RamAddr`] by reinterpreting its bytes. Since the general-purpose
/// registers' data type and [`RamAddr`]'s underlying data types are different, when we need the
/// conversion we will call this function
pub fn reg_type_to_addr(val: RegType) -> RamAddr {
    RamAddr(val.reinterpret::<Unsigned64>() as usize)
}

/// Converts a [`RamAddr`] to [`RegType`] by reinterpreting its bytes. Since the general-purpose
/// registers' data type and [`RamAddr`]'s underlying data types are different, when we need the
// conversion we will call this function
pub fn addr_to_reg_type(val: RamAddr) -> RegType {
    (val.0 as Unsigned64).reinterpret::<RegType>()
}



/*****************************************************************************************/
/* All code starting from this line is used only for debugging. It will be removed later */
/*****************************************************************************************/
pub const DBG_CLS: bool = false;      // TODO: delete
pub const DBG_SLEEP: usize = 0;   // TODO: delete
pub const DBG_PRINT: bool = true;    // TODO: delete


/** Prints the cpu state. NOTE: Only for debugging purposes */
impl CPU {
    pub fn print(&self) {
        if !DBG_PRINT {
            return;
        }

        // Clear the screen (only implemented for window)
        if DBG_CLS {
            std::process::Command::new("cmd")
                .args(["/c", "cls"])
                .status()
                .unwrap();
        }

        let sp = self.get_sp();

        println!("Instruction {}", self.instruction_counter);
        println!("Executed: {:?}\n", self.instr_reg);

        // Show the ram
        for (i, chunk)  in self.ram.mem.chunks(16).enumerate() {
            let mut s = String::new();
            for (j, byte) in chunk.iter().enumerate() {
                if RamAddr(i * 16 + j) == sp {
                    s.push('|');
                    s.push(' ');
                }
                
                s.push_str(byte.to_string().as_str());
                s.push(' ');
            }
            println!("{}", s);
        }

        // Show the value of registers
        for i in 0..Self::GEN_REG_COUNT / 2 {
            let reg1 = i;
            let reg2 = Self::GEN_REG_COUNT / 2 + i;
            println!("Reg {}\t= {}\t\tReg {}\t= {}",
                     reg1,
                     self.get_reg(reg1).unwrap(),
                     reg2,
                     self.get_reg(reg2).unwrap()
            );
        }

        println!("Accu = {}", self.get_accu_reg());
        println!("SP = {:?}", self.get_sp());
        println!("SB = {:?}", self.get_sb());
        println!("Overflow: {}\t\tZero: {}\t\tSign: {}\n",
                 self.get_flag(CPUFlag::Overflow),
                 self.get_flag(CPUFlag::Zero),
                 self.get_flag(CPUFlag::Sign)
        );
    }
}

