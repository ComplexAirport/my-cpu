use std::ops::{BitAnd, BitOr, BitXor};
use crate::define_opcodes;
pub use crate::ram::{RamAddr, RamUnit, RAM};
pub use crate::error::{ErrorType, CPUError};

/// Represents a CPU instruction
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CPUInstr {
    /// Halts the cpu (no more instructions are executing)
    Halt,

    /// Sets value of #1 to value at #2 (Note: #1 is not allowed to be an immediate value)
    Set,

    /// Adds the value at #1 to the value at #2 and stores the result in accu register
    Add,

    /// Subtracts the value at #2 from the value at #1 and stores the result in accu register
    Sub,

    /// Multiplies the value at #1 and the value at #2 and stores the result in accu register
    Mul,

    /// Does the value at #1 modulo the value at #2 and stores the result in accu register
    Mod,

    /// Divides the value at #1 by the value at #2 (round division, floors the result)
    /// and stores the result in accu register
    Div,


    /// Adds the value at #1 as float to the value at #2 as float and stores the result in accu register
    FAdd,

    /// Subtracts the value at #2 as float from the value at #1 as float
    /// and stores the result in accu register
    FSub,

    /// Multiplies the value at #2 as float from the value at #1 as float
    /// and stores the result in accu register
    FMul,

    /// Divides the value at #1 by the value at  #2 (float division, does not floor the result)
    /// and stores the result in accu register
    FDiv,


    /// Does boolean (the value at #1 **AND** the value at #2) and stores the result in accu register
    And,

    /// Does boolean (the value at #1 **OR** the value at #2) and stores the result in accu register
    Or,

    /// Does boolean (the value at #1 **XOR** the value at #2) and stores the result in accu register
    Xor,

    /// Does boolean (**NOT** the value at #1) and stores the result in accu register
    Not,


    /// Does bitwise NOT ~(the value at #1) and stores the result in accu register
    BitwiseAnd,

    /// Does bitwise NOT ~(the value at #1) and stores the result in accu register
    BitwiseOr,

    /// Does bitwise NOT ~(the value at #1) and stores the result in accu register
    BitwiseXor,

    /// Does bitwise NOT ~(the value at #1) and stores the result in accu register
    BitwiseNot,

    /// Shifts the value at #1 left by `n` positions and stores the result in accu register
    Shl,

    /// Shifts the value at #1 right by `n` positions and stores the result in accu register
    Shr,


    /// Jumps to the specified **memory address** #1 (_'jumps'_ means the next instruction will be
    /// the byte at the specified memory address)
    Jump,

    /// Jumps to the specified memory address (#2) if the value at #1 is non-zero
    JumpIf,

    /// Jumps to the specified memory address (#2) if the value at #1 is zero
    JumpIfNot,

    /// Jumps to the specified memory address (#3) if the value at #1 is greater than the value at #2
    JumpIfGreater,

    /// Jumps to the specified memory address (#3) if the value at #1 is less than the value at #2
    JumpIfLess,

    /// Jumps to the specified memory address (#3) if the value at #1 is equal to the value at #2
    JumpIfEqual
}

impl CPUInstr {
     define_opcodes!(
        HALT,

        SET,

        ADD,
        SUB,
        MUL,
        MOD,
        DIV,

        F_ADD,
        F_SUB,
        F_MUL,
        F_DIV,

        AND,
        OR,
        XOR,
        NOT,

        BITWISE_AND,
        BITWISE_OR,
        BITWISE_XOR,
        BITWISE_NOT,

        SHL,
        SHR,

        JUMP,
        JUMP_IF,
        JUMP_IF_NOT,
        JUMP_IF_GREATER,
        JUMP_IF_LESS,
        JUMP_IF_EQUAL
    );

    /// Represents the instruction in a byte
    pub const fn as_byte(&self) -> u8 {
        match &self {
            CPUInstr::Halt => Self::HALT,
            CPUInstr::Set => Self::SET,
            CPUInstr::Add => Self::ADD,
            CPUInstr::Sub => Self::SUB,
            CPUInstr::Mul => Self::MUL,
            CPUInstr::Mod => Self::MOD,
            CPUInstr::Div => Self::DIV,
            CPUInstr::FAdd => Self::F_ADD,
            CPUInstr::FSub => Self::F_SUB,
            CPUInstr::FMul => Self::F_MUL,
            CPUInstr::FDiv => Self::F_DIV,
            CPUInstr::And => Self::F_ADD,
            CPUInstr::Or => Self::OR,
            CPUInstr::Xor => Self::XOR,
            CPUInstr::Not => Self::NOT,
            CPUInstr::BitwiseAnd => Self::BITWISE_AND,
            CPUInstr::BitwiseOr => Self::BITWISE_OR,
            CPUInstr::BitwiseXor => Self::BITWISE_XOR,
            CPUInstr::BitwiseNot => Self::BITWISE_NOT,
            CPUInstr::Shl => Self::SHL,
            CPUInstr::Shr => Self::SHR,
            CPUInstr::Jump => Self::JUMP,
            CPUInstr::JumpIf => Self::JUMP_IF,
            CPUInstr::JumpIfNot => Self::JUMP_IF_NOT,
            CPUInstr::JumpIfGreater => Self::JUMP_IF_GREATER,
            CPUInstr::JumpIfLess => Self::JUMP_IF_LESS,
            CPUInstr::JumpIfEqual => Self::JUMP_IF_EQUAL,
        }
    }

    /// Read an instruction from a byte
    pub const fn from_byte(byte: u8) -> Result<Self, CPUError> {
        match byte {
            Self::HALT => Ok(CPUInstr::Halt),
            Self::SET => Ok(CPUInstr::Set),
            Self::ADD => Ok(CPUInstr::Add),
            Self::SUB => Ok(CPUInstr::Sub),
            Self::MUL => Ok(CPUInstr::Mul),
            Self::MOD => Ok(CPUInstr::Mod),
            Self::DIV => Ok(CPUInstr::Div),
            Self::F_ADD => Ok(CPUInstr::FAdd),
            Self::F_SUB => Ok(CPUInstr::FSub),
            Self::F_MUL => Ok(CPUInstr::FMul),
            Self::F_DIV => Ok(CPUInstr::FDiv),
            Self::AND => Ok(CPUInstr::And),
            Self::OR => Ok(CPUInstr::Or),
            Self::XOR => Ok(CPUInstr::Xor),
            Self::NOT => Ok(CPUInstr::Not),
            Self::BITWISE_AND => Ok(CPUInstr::BitwiseAnd),
            Self::BITWISE_OR => Ok(CPUInstr::BitwiseOr),
            Self::BITWISE_XOR => Ok(CPUInstr::BitwiseXor),
            Self::BITWISE_NOT => Ok(CPUInstr::BitwiseNot),
            Self::SHL => Ok(CPUInstr::Shl),
            Self::SHR => Ok(CPUInstr::Shr),
            Self::JUMP => Ok(CPUInstr::Jump),
            Self::JUMP_IF => Ok(CPUInstr::JumpIf),
            Self::JUMP_IF_NOT => Ok(CPUInstr::JumpIfNot),
            Self::JUMP_IF_GREATER => Ok(CPUInstr::JumpIfGreater),
            Self::JUMP_IF_LESS => Ok(CPUInstr::JumpIfLess),
            Self::JUMP_IF_EQUAL => Ok(CPUInstr::JumpIfEqual),
            _ => Err(CPUError::InvalidInstruction(byte))
        }
    }
}


/// Represents the type of the operand
/// # Example:
/// For example, in a [`CpuInstr::Add`] instruction,
/// both operands are preceded by the operand type like this: \
/// [`CPUInstr::ADD`] \
/// [`OperandType::IMMEDIATE`] \
/// `100` \
/// [`OperandType::IMMEDIATE`] \
/// `200` \
/// Adds immediate value `100` to immediate value `200`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OperandType {
    MemoryAddress,  // Represents a memory address
    Register,       // Represents a CPU register
    Flag,           // Represents a CPU flag
    Immediate       // Represents an immediate value - for example, a literal
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
            _ => Err(CPUError::InvalidInstruction(byte))
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
            _ => Err(CPUError::InvalidInstruction(byte))
        }
    }
}


/// Represents the amount of general registers in the processor
pub const GEN_REG_COUNT: usize = 8;

/// Represents the type of the general registers
pub type RegType = i64;

/// Represents the type of the immediate value
pub type ImmType = RegType;

/// Represents the address of the first instruction for the CPU
pub const CPU_START_ADDR: RamAddr = RamAddr(0x0_usize);

/// Represents the amount of bytes 1 cpu instruction takes
pub const INSTRUCTION_SIZE: usize = 1;

/// Represents the amount of bytes 1 memory address takes
pub const MEMORY_ADDRESS_SIZE: usize = 8;

/// Represents the amount of bytes 1 register takes
pub const REGISTER_SIZE: usize = 1;

/// Represents the amount of bytes 1 operand type takes
pub const OPERAND_TYPE_SIZE: usize = 1;

/// Represents the amount of bytes 1 flag takes
pub const FLAG_TYPE_SIZE: usize = 1;

/// Represents the amount of bytes 1 immediate value takes
pub const IMMEDIATE_VALUE_SIZE: usize = 8;


/// Represents the CPU itself
pub struct CPU {
    pub ram: RAM,

    /// 8 general-purpose i64 registers
    general_reg: [RegType; GEN_REG_COUNT],

    /// Special register which stores the result of the operations
    accu_reg: RegType,

    /// Special register which temporarily stores the current instruction
    instr_reg: CPUInstr,

    /// Holds the address of the next instruction to execute
    prog_counter: Option<RamAddr>,

    /// Set when an operation results in zero
    zero_flag: bool,

    /// Set when an arithmetic operation produces a carry-out (or borrow for subtraction)
    // carry_flag: bool,

    /// Indicates whether the result of an operation is negative (based on the most significant bit)
    sign_flag: bool,

    /// Indicates when an arithmetic overflow occurs in signed arithmetic.
    overflow_flag: bool,

    /// Counts the instructions.
    /// At the moment exists only for debugging purposes, might delete later
    instruction_counter: usize
}


/// Main CPU methods
impl CPU {
    pub fn new(ram: RAM) -> Self {
        Self {
            ram,
            general_reg: [0 as RegType; GEN_REG_COUNT],
            accu_reg: 0 as RegType,
            instr_reg: CPUInstr::Halt,
            prog_counter: Some(CPU_START_ADDR),
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
        let instr_byte = self.fetch_byte_at_addr(pc)?;

        // Convert the byte representing the instruction to CPUInstr
        self.instr_reg = CPUInstr::from_byte(instr_byte.0)?;

        // Increment the program counter
        pc.inc(INSTRUCTION_SIZE)?;
        self.set_program_counter(pc);

        let res = match self.instr_reg {
            CPUInstr::Halt => self.execute_halt(),
            CPUInstr::Set => self.execute_set(),
            CPUInstr::Add => self.execute_add(),
            CPUInstr::Sub => self.execute_sub(),
            CPUInstr::Mul => self.execute_mul(),
            CPUInstr::Mod => self.execute_mod(),
            CPUInstr::Div => self.execute_div(),
            CPUInstr::FAdd => self.execute_fadd(),
            CPUInstr::FSub => self.execute_fsub(),
            CPUInstr::FMul => self.execute_fmul(),
            CPUInstr::FDiv => self.execute_fdiv(),
            CPUInstr::And => self.execute_and(),
            CPUInstr::Or => self.execute_or(),
            CPUInstr::Xor => self.execute_xor(),
            CPUInstr::Not => self.execute_not(),
            CPUInstr::BitwiseAnd => self.execute_b_and(),
            CPUInstr::BitwiseOr => self.execute_b_or(),
            CPUInstr::BitwiseXor => self.execute_b_xor(),
            CPUInstr::BitwiseNot => self.execute_b_not(),
            CPUInstr::Shl => self.execute_shl(),
            CPUInstr::Shr => self.execute_shr(),
            CPUInstr::Jump => self.execute_jump(),
            CPUInstr::JumpIf => self.execute_jump_if(),
            CPUInstr::JumpIfNot => self.execute_jump_if_not(),
            CPUInstr::JumpIfGreater => self.execute_jump_if_greater(),
            CPUInstr::JumpIfLess => self.execute_jump_if_less(),
            CPUInstr::JumpIfEqual => self.execute_jump_if_equal(),
        };

        self.inc_instruction_counter();
        res
    }

    /// At the moment only exists for debugging purposes, might delete later
    fn inc_instruction_counter(&mut self) {
        self.instruction_counter += 1;
        self.print();
        std::thread::sleep(std::time::Duration::from_millis(2000));
    }
}


/** Main CPU instruction methods */
impl CPU {
    /// Halts instruction
    /// Sets the program counter to `None`
    fn execute_halt(&mut self) -> Result<(), ErrorType> {
        self.halt_program_counter();
        Ok(())
    }

    /// Set instruction
    fn execute_set(&mut self) -> Result<(), ErrorType> {
        let to_set_type = self.read_operand_type()?;
        let mut pc = self.prog_counter.unwrap();

        match to_set_type {
            OperandType::MemoryAddress => {
                let to_set = self.fetch_mem_addr(pc)?;
                pc.inc(MEMORY_ADDRESS_SIZE)?;
                self.set_program_counter(pc);
                let value = self.read_operand_value()? as u8;
                self.ram.write_byte(to_set, value)?;
                Ok(())
            }
            OperandType::Register => {
                let to_set = self.fetch_reg_number(pc)?;
                pc.inc(REGISTER_SIZE)?;
                self.set_program_counter(pc);
                let value = self.read_operand_value()?;
                self.set_reg(to_set, value)?;
                Ok(())
            }
            OperandType::Flag => {
                let to_set = self.fetch_flag_number(pc)?;
                pc.inc(FLAG_TYPE_SIZE)?;
                self.set_program_counter(pc);
                let value = self.read_operand_value()? != 0;
                self.set_flag(CPUFlag::from_byte(to_set)?, value);
                Ok(())
            }
            OperandType::Immediate => {
                Err(CPUError::OperandTypeNotAllowed(to_set_type).into())
            }
        }
    }

    /// Add instruction
    fn execute_add(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| x.overflowing_add(y))
    }

    /// Sub instruction
    fn execute_sub(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| x.overflowing_sub(y))
    }

    /// Mul instruction
    fn execute_mul(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| x.overflowing_mul(y))
    }

    /// Mod instruction
    fn execute_mod(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| (x % y, false)) // Modulo does not overflow
    }

    /// Div instruction
    fn execute_div(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| x.overflowing_div(y))
    }

    fn execute_fadd(&mut self) -> Result<(), ErrorType> { Ok(()) } // todo 

    fn execute_fsub(&mut self) -> Result<(), ErrorType> { Ok(()) } // todo 

    fn execute_fmul(&mut self) -> Result<(), ErrorType> { Ok(()) } // todo 

    fn execute_fdiv(&mut self) -> Result<(), ErrorType> { Ok(()) } // todo 

    /// Logical And instruction
    fn execute_and(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_log_operator(|x, y| (x != 0) && (y != 0))
    }

    /// Logical Or instruction
    fn execute_or(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_log_operator(|x, y| (x != 0) || (y != 0))
    }

    /// Logical Xor instruction
    fn execute_xor(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_log_operator(|x, y| (x != 0) ^ (y != 0))
    }

    /// Logical Not instruction
    fn execute_not(&mut self) -> Result<(), ErrorType> {
        self.execute_un_log_operator(|x| !(x != 0))
    }

    /// Bitwise And instruction
    fn execute_b_and(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| (x.bitand(y), false))
    }

    /// Bitwise Or instruction
    fn execute_b_or(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| (x.bitor(y), false))
    }

    /// Bitwise Xor instruction
    fn execute_b_xor(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| (x.bitxor(y), false))
    }

    /// Bitwise Not instruction
    fn execute_b_not(&mut self) -> Result<(), ErrorType> {
        self.execute_un_operator(|x| !x)
    }

    /// Shl (Shift Left) instruction
    fn execute_shl(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| x.overflowing_shl(y as u32))
    }

    /// Shr (Shift Right) instruction
    fn execute_shr(&mut self) -> Result<(), ErrorType> {
        self.execute_bin_operator(|x, y| x.overflowing_shr(y as u32))
    }

    /// Jump instruction
    fn execute_jump(&mut self) -> Result<(), ErrorType> {
        let _ = self.read_operand_type()?; // Read but omit the byte indicating memory address
        let addr = self.fetch_mem_addr(self.prog_counter.unwrap())?;
        self.set_program_counter(addr);
        Ok(())
    }

    // JumpIf instruction
    fn execute_jump_if(&mut self) -> Result<(), ErrorType> {
        self.execute_one_arg_conditional_jump(|x| (x != 0) == true)
    }

    // JumpIfNot instruction
    fn execute_jump_if_not(&mut self) -> Result<(), ErrorType> {
        self.execute_one_arg_conditional_jump(|x| (x == 0) == true)
    }

    // JumpIfGreater instruction
    fn execute_jump_if_greater(&mut self) -> Result<(), ErrorType> {
        self.execute_two_arg_conditional_jump(|x, y| x > y)
    }

    // JumpIfLess instruction
    fn execute_jump_if_less(&mut self) -> Result<(), ErrorType> {
        self.execute_two_arg_conditional_jump(|x, y| x < y)
    }

    // JumpIfEqual instruction
    fn execute_jump_if_equal(&mut self) -> Result<(), ErrorType> {
        self.execute_two_arg_conditional_jump(|x, y| x == y)
    }
}


/** General helper methods for CPU instructions */
impl CPU {
    /// Executes a binary operator. (operator with two arguments) \
    /// Accepts only overflowing operator which return `(RegType, bool)`. Second parameter is `true`
    /// if the operator overflowed
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Overflow` flag if the operation overflows.
    /// - Sets the `Zero` flag if the result  is zero.
    /// - Sets the `Sign` flag if the result is negative.
    fn execute_bin_operator<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(RegType, RegType) -> (RegType, bool),
    {
        let lhs = self.read_operand_value()?;
        let rhs = self.read_operand_value()?;

        let (result, overflowed) = op(lhs, rhs);

        // Reset the flags before setting them so that they represent the result
        // of the latest arithmetic operation
        self.reset_flags();

        // If the operation overflowed, set the Overflow flag
        if overflowed {
            self.enable_flag(CPUFlag::Overflow);
        }

        // If the result is negative, set the Sign flag
        if result.is_negative() {
            self.enable_flag(CPUFlag::Sign);
        }

        // If the result is zero, set the zero flag
        if result == 0 {
            self.enable_flag(CPUFlag::Zero);
        }

        self.set_accu_reg(result);

        Ok(())
    }

    /// Executes a unary operator. (operator with one argument) \
    ///  Accepts a function - the operation itself which returns `RegType`
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Zero` flag if the result  is zero.
    /// - Sets the `Sign` flag if the result is negative.
    fn execute_un_operator<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(RegType) -> RegType,
    {
        let lhs = self.read_operand_value()?;

        let result = op(lhs);

        // Reset the flags before setting them so that they represent the result
        // of the latest arithmetic operation
        self.reset_flags();

        // If the result is negative, set the Sign flag
        if result.is_negative() {
            self.enable_flag(CPUFlag::Sign);
        }

        // If the result is zero, set the zero flag
        if result == 0 {
            self.enable_flag(CPUFlag::Zero);
        }

        self.set_accu_reg(result);

        Ok(())
    }

    /// Executes a logical binary operator. (logical operator with two arguments) \
    /// Accepts a function - the operation itself which returns `bool`
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Zero` flag if the result is `false`.
    fn execute_bin_log_operator<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(RegType, RegType) -> bool,
    {
        let lhs = self.read_operand_value()?;
        let rhs = self.read_operand_value()?;

        let result = op(lhs, rhs);

        // Reset the flags before setting them so that they represent the result
        // of the latest arithmetic operation
        self.disable_flag(CPUFlag::Overflow);
        self.disable_flag(CPUFlag::Sign);
        self.disable_flag(CPUFlag::Zero);

        // If the result is `false`, set the Zero flag
        if result == false {
            self.enable_flag(CPUFlag::Zero);
        }

        self.set_accu_reg(result as RegType);

        Ok(())
    }

    /// Executes a logical unary operator. (logical operator with one argument) \
    ///  Accepts a function - the operation itself which returns `RegType`
    /// - Assigns the Accumulator register to the result of the operation
    /// - Sets the `Zero` flag if the result is `false`.
    fn execute_un_log_operator<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(RegType) -> bool,
    {
        let lhs = self.read_operand_value()?;

        let result = op(lhs);

        // Reset the flags before setting them so that they represent the result
        // of the latest arithmetic operation
        self.reset_flags();

        // If the result is zero, set the zero flag
        if result == false {
            self.enable_flag(CPUFlag::Zero);
        }

        self.set_accu_reg(result as RegType);

        Ok(())
    }


    /// Jump if the argument function which takes one argument and returns `bool` \
    /// returns `true`
    fn execute_one_arg_conditional_jump<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(RegType) -> bool,
    {
        let value = self.read_operand_value()?;
        let _ = self.read_operand_type()?; // Read but omit the byte indicating memory address

        let mut pc = self.prog_counter.unwrap();

        let addr = self.fetch_mem_addr(pc)?;
        pc.inc(MEMORY_ADDRESS_SIZE)?;

        if op(value) {
            self.set_program_counter(addr);
        } else {
            self.set_program_counter(pc)
        }

        Ok(())
    }

    /// Jump if the argument function which takes two arguments and returns `bool` \
    /// returns `true`
    fn execute_two_arg_conditional_jump<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(RegType, RegType) -> bool,
    {
        let value1 = self.read_operand_value()?;
        let value2 = self.read_operand_value()?;
        let _ = self.read_operand_type()?; // Read but omit the byte indicating memory address

        let mut pc = self.prog_counter.unwrap();
        let addr = self.fetch_mem_addr(self.prog_counter.unwrap())?;

        pc.inc(MEMORY_ADDRESS_SIZE)?;

        if op(value1, value2) {
            self.set_program_counter(addr);
        } else {
            self.set_program_counter(pc);
        }

        Ok(())
    }
}


/** Helper methods for reading different types of operands */
impl CPU {
    /// This method gets the value from the operand. It
    /// 1. Retrieves the operand type
    /// 2. Based on what operand type is given to it, it reads the underlying value
    /// For example, if the operand type is [`OperandType::MemoryAddress`], it will read the byte
    /// at that memory address and return it. \
    /// - The return data is represented in [`ImmType`]
    /// - Automatically increments the program counter.
    fn read_operand_value(&mut self) -> Result<ImmType, ErrorType> {
        let operand = self.read_operand_type()?;
        let mut pc = self.prog_counter.unwrap();
        match operand {
            OperandType::MemoryAddress => {
                let value = self.fetch_value_from_mem_addr(pc)?;
                pc.inc(MEMORY_ADDRESS_SIZE)?;
                self.set_program_counter(pc);
                Ok(value)
            }
            OperandType::Register => {
                let value = self.fetch_value_from_reg(pc)?;
                pc.inc(REGISTER_SIZE)?;
                self.set_program_counter(pc);
                Ok(value)
            }
            OperandType::Flag => {
                let value = self.fetch_value_from_flag(pc)?.as_byte() as RegType;
                pc.inc(FLAG_TYPE_SIZE)?;
                self.set_program_counter(pc);
                Ok(value)
            }
            OperandType::Immediate => {
                let value = self.fetch_imm(pc)?;
                pc.inc(IMMEDIATE_VALUE_SIZE)?;
                self.set_program_counter(pc);
                Ok(value)
            }
        }
    }

    /// Fetches the operand type byte returns the [`OperandType`] enum wrapper of it \
    /// Automatically increments the program counter
    fn read_operand_type(&mut self) -> Result<OperandType, ErrorType> {
        // The program counter is guaranteed not to be `None`, so we can unwrap it
        let mut pc = self.get_program_counter().unwrap();

        // Read the operand type byte (as u8)
        let operand_type_byte = self.fetch_byte_at_addr(pc)?.0;

        // Convert the operand type byte to the wrapper enum
        let operand_type = OperandType::from_byte(operand_type_byte)?;

        // Increment the program counter
        pc.inc(OPERAND_TYPE_SIZE)?;

        self.set_program_counter(pc);

        Ok(operand_type)
    }

    /** Fetching methods */
    /// Fetch the value in RAM at the specified address
    fn fetch_byte_at_addr(&self, addr: RamAddr) -> Result<&RamUnit, ErrorType> {
        Ok(self.ram.at(addr)?)
    }

    /// Gets the register number from the address and returns the value at that register
    fn fetch_value_from_reg(&self, addr: RamAddr) -> Result<ImmType, ErrorType> {
        let reg_number: usize = self.fetch_reg_number(addr)?;
        if reg_number == GEN_REG_COUNT { // The 9-th register is the accumulator register
            Ok(self.get_accu_reg())
        } else {
            Ok(self.get_reg(reg_number)?)
        }
    }

    /// Reads a memory address from address and returns the value at that memory address
    fn fetch_value_from_mem_addr(&self, addr: RamAddr) -> Result<RegType, ErrorType> {
        let mem_addr = self.fetch_mem_addr(addr)?;
        let val = self.ram.at(mem_addr)?;
        Ok(val.0 as RegType)
    }

    /// Reads a flag number from the address and returns a [`CPUFlag`] based on it
    fn fetch_value_from_flag(&self, addr: RamAddr) -> Result<CPUFlag, ErrorType> {
        let flag_number = self.fetch_flag_number(addr)?;
        Ok(CPUFlag::from_byte(flag_number)?)
    }

    /// Reads an immediate value and returns it as [`ImmType`]
    fn fetch_imm(&self, addr: RamAddr) -> Result<ImmType, ErrorType> {
        let value = self.ram.read_i64(addr)?;
        Ok(value)
    }

    /// Reads a register number from `addr`
    fn fetch_reg_number(&self, addr: RamAddr) -> Result<usize, ErrorType> {
        Ok(self.fetch_byte_at_addr(addr)?.0 as usize)
    }

    /// Reads a memory address from `addr`
    fn fetch_mem_addr(&self, addr: RamAddr) -> Result<RamAddr, ErrorType> {
        Ok(RamAddr(self.ram.read_u64(addr)? as usize))
    }

    /// Reads a flag number (u8, not a `CPUFlag`) from `addr`
    fn fetch_flag_number(&self, addr: RamAddr) -> Result<u8, ErrorType> {
        Ok(self.fetch_byte_at_addr(addr)?.0)
    }
}


/** Program Counter related methods */
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
    pub fn inc_prog_counter(&mut self, val: usize) {
        if let Some(counter) = &mut self.prog_counter {
            let _ = counter.inc(val); // TODO: use the Result
        } else {
            panic!("Attempt to increment program counter in a halted state")
        }
    }
}


/** Register related methods */
impl CPU {
    /// Returns the value of the `n`-th register if it exists, Error otherwise
    pub fn get_reg(&self, n: usize) -> Result<RegType, CPUError> {
        if n < GEN_REG_COUNT {
            Ok(self.general_reg[n])
        } else {
            Err(CPUError::InvalidRegister(n))
        }
    }

    /// Sets the value of `n`-th register to `val` if it exists, Error otherwise
    pub fn set_reg(&mut self, n: usize, val: RegType) -> Result<(), CPUError> {
        if n < GEN_REG_COUNT {
            self.general_reg[n] = val;
            Ok(())
        } else {
            Err(CPUError::InvalidRegister(n))
        }
    }

    /// Returns the value of the special accumulator register
    pub fn get_accu_reg(&self) -> RegType {
        self.accu_reg
    }

    /// Sets the value of the special accumulator register to `val`
    pub fn set_accu_reg(&mut self, val: RegType) {
        self.accu_reg = val;
    }
}


/** Flag related methods */
impl CPU {
    /// Get the value of the specified flag
    pub fn get_flag(&self, flag: CPUFlag) -> bool {
        match flag {
            CPUFlag::Zero => { self.zero_flag }
            CPUFlag::Sign => { self.sign_flag }
            CPUFlag::Overflow => { self.overflow_flag }
        }
    }

    /// Sets the specified flag to `val`
    pub fn set_flag(&mut self, flag: CPUFlag, val: bool) {
        match flag {
            CPUFlag::Zero => { self.zero_flag = val; }
            CPUFlag::Sign => { self.sign_flag = val; }
            CPUFlag::Overflow => { self.overflow_flag = val; }
        }
    }

    /// Toggles the specified flag
    pub fn toggle_flag(&mut self, flag: CPUFlag) {
        self.set_flag(flag, !self.get_flag(flag));
    }

    /// Enables the specified flag
    pub fn enable_flag(&mut self, flag: CPUFlag) {
        self.set_flag(flag, true);
    }

    /// Disables the specified flag
    pub fn disable_flag(&mut self, flag: CPUFlag) {
        self.set_flag(flag, false);
    }

    /// Sets all the flags to `false`
    pub fn reset_flags(&mut self) {
        self.disable_flag(CPUFlag::Overflow);
        self.disable_flag(CPUFlag::Zero);
        self.disable_flag(CPUFlag::Sign);
    }
}


/** Prints the cpu state. NOTE: Only for debugging purposes */
impl CPU {
    pub fn print(&self) {
        // Clear the screen (only implemented for window)
        std::process::Command::new("cmd")
            .args(["/c", "cls"])
            .status()
            .unwrap();

        println!("Instruction {}\n", self.instruction_counter);

        // Show the ram
        for chunk  in self.ram.mem.chunks(16) {
            let mut s = String::new();
            for i in chunk {
                s.push_str(i.0.to_string().as_str());
                s.push(' ');
            }
            println!("{}", s);
        }

        // Show the value of registers
        for i in 0..GEN_REG_COUNT / 2 {
            let reg1 = i;
            let reg2 = GEN_REG_COUNT / 2 + i;
            println!("Reg {}\t= {}\t\tReg {}\t= {}",
                     reg1,
                     self.get_reg(reg1).unwrap(),
                     reg2,
                     self.get_reg(reg2).unwrap()
            );
        }

        println!("Accu\t= {}", self.get_accu_reg());

        println!("Overflow:\t{}", self.get_flag(CPUFlag::Overflow));
        println!("Zero:\t\t{}", self.get_flag(CPUFlag::Zero));
        println!("Sign:\t\t{}", self.get_flag(CPUFlag::Sign));

        println!("Executed instruction: {:?}", self.instr_reg);
    }
}
