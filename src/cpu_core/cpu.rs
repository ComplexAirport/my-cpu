use std::ops::{BitAnd, BitOr, BitXor};
use crate::define_opcodes;
pub use super::typing::{*};
pub use super::ram::{RamAddr, RamUnit, RAM};
pub use super::error::{ErrorType, CPUError};

/// Represents a CPU instruction
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CPUInstr {
    /// Halts the cpu (no more instructions are executing)
    Halt,

    /// Sets value of #1 to value at #2
    /// (Note: #1 is not allowed to be an immediate value)
    Set,

    /// Unsigned instructions
    /// These instructions interpret the operands as `u64` bytes */
    UAdd, USub, UMul, UMod, UDiv, // Arithmetic operators
    UOr, UXor, UAnd, UNot,        // Bitwise operators
    UShl, UShr,                   // Shift left (<<) and Shift right (>>) operators

    /// Signed instructions
    /// These instructions interpret the operands `i64` bytes
    IAdd, ISub, IMul, IMod, IDiv, // Arithmetic operators
    IOr, IXor, IAnd, INot,        // Bitwise operators
    IShl, IShr,                   // Shift left (<<) and Shift right (>>) operators

    /// Floating operator instructions
    /// These instructions interpret the operands as `f64` bytes
    FAdd, FSub, FMul, FDiv, // Arithmetic operators

    /// Logical operators
    /// (treats operands as boolean values: zero = false, nonzero = true)
    LOr, LXor, LAnd, LNot,

    /// Jump instructions
    Jump,           // Jumps to a memory address
    JumpIf,         // Jumps to [1] if [2] is nonzero
    JumpIfNot,      // Jumps to [1] if [2] is zero

    /// Unsigned comparison instructions
    UEqual,             // ==
    UGreater,           // >
    UGreaterEqual,      // >=
    ULess,              // <
    ULessEqual,         // <=

    /// Signed comparison instructions
    IEqual,             // ==
    IGreater,           // >
    IGreaterEqual,      // >=
    ILess,              // <
    ILessEqual,         // <=

    /// Float comparison instructions
    FEqual,             // ==
    FGreater,           // >
    FGreaterEqual,      // >=
    FLess,              // <
    FLessEqual,         // <=

    /// Syscall instruction
    Syscall
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

        SYSCALL
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

            CPUInstr::Syscall => Self::SYSCALL,
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

            Self::SYSCALL => Ok(CPUInstr::Syscall),

            _ => Err(CPUError::InvalidInstruction(byte)),
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


/// Represents the amount of general-purpose registers in the CPU
pub const GEN_REG_COUNT: usize = 8;

/// Represents the index of special accumulator register
pub const ACCU_IDX: usize = GEN_REG_COUNT;

/// Represents the total amount of registers in the CPU
/// - [`GEN_REG_COUNT`] general-purpose
/// - 1 special accumulator
pub const REG_COUNT: usize = GEN_REG_COUNT + 1;

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


/// Represents the CPU itself
pub struct CPU {
    pub ram: RAM,

    /// - 8 general-purpose 8-byte registers
    /// - 1 special accumulator register
    registers: [RegType; REG_COUNT],

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

    /// Represents the address of the first instruction for the CPU
    pub const START_ADDR: RamAddr = RamAddr(0x0_usize);

    pub fn new(ram: RAM) -> Self {
        Self {
            ram,
            registers: [0 as RegType; REG_COUNT],
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
        let instr_byte = self.ram.at(pc)?;

        // Convert the byte representing the instruction to CPUInstr
        self.instr_reg = CPUInstr::from_byte(instr_byte)?;

        // Increment the program counter
        pc.inc(INSTRUCTION_SIZE)?;
        self.set_program_counter(pc);

        let res = match self.instr_reg {
            CPUInstr::Halt => {}
            CPUInstr::Set => {}
            CPUInstr::UAdd => {}
            CPUInstr::USub => {}
            CPUInstr::UMul => {}
            CPUInstr::UMod => {}
            CPUInstr::UDiv => {}
            CPUInstr::UOr => {}
            CPUInstr::UXor => {}
            CPUInstr::UAnd => {}
            CPUInstr::UNot => {}
            CPUInstr::UShl => {}
            CPUInstr::UShr => {}
            CPUInstr::IAdd => {}
            CPUInstr::ISub => {}
            CPUInstr::IMul => {}
            CPUInstr::IMod => {}
            CPUInstr::IDiv => {}
            CPUInstr::IOr => {}
            CPUInstr::IXor => {}
            CPUInstr::IAnd => {}
            CPUInstr::INot => {}
            CPUInstr::IShl => {}
            CPUInstr::IShr => {}
            CPUInstr::FAdd => {}
            CPUInstr::FSub => {}
            CPUInstr::FMul => {}
            CPUInstr::FDiv => {}
            CPUInstr::LOr => {}
            CPUInstr::LXor => {}
            CPUInstr::LAnd => {}
            CPUInstr::LNot => {}
            CPUInstr::Jump => {}
            CPUInstr::JumpIf => {}
            CPUInstr::JumpIfNot => {}
            CPUInstr::UEqual => {}
            CPUInstr::UGreater => {}
            CPUInstr::UGreaterEqual => {}
            CPUInstr::ULess => {}
            CPUInstr::ULessEqual => {}
            CPUInstr::IEqual => {}
            CPUInstr::IGreater => {}
            CPUInstr::IGreaterEqual => {}
            CPUInstr::ILess => {}
            CPUInstr::ILessEqual => {}
            CPUInstr::FEqual => {}
            CPUInstr::FGreater => {}
            CPUInstr::FGreaterEqual => {}
            CPUInstr::FLess => {}
            CPUInstr::FLessEqual => {}
            CPUInstr::Syscall => {}
        };

        self.inc_instruction_counter();

        Ok(())
        // res
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

}


/** This section contains methods for operations with integers */
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
        self.set_arith_result_flags(result, overflowed);
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
        self.set_arith_result_flags(result, overflowed);
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
    /// overflow
    fn binary_logical_op<F>(&mut self, op: F) -> Result<(), ErrorType>
    where
        F: Fn(bool, bool) -> bool
    {
        let lhs = self.extract_operand()?.as_bool();
        let rhs = self.extract_operand()?.as_bool();
        let result = op(lhs, rhs);
        self.set_logical_result_flags(result);
        Ok(())
    }



    /// Helper method. Sets flags according to an arithmetic operator result
    /// - Sets the `Overflow` flag if overflowed is `true` is `result` is infinite (this means
    /// [`Float64`] operator overflowed).
    /// - Sets the `Zero` flag if `result` is zero.
    /// - Sets the `Sign` flag if `result` is negative.
    fn set_arith_result_flags<T>(&mut self, result: T, overflowed: bool)
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

    /// Helper method. Sets flags according to a logical operator result
    /// - Sets the `Zero` flag if `result` is `false`.
    fn set_logical_result_flags(&mut self, result: bool)
    {
        // Reset the flags before setting them so that they represent the result
        // of the latest operation
        self.reset_flags();

        if result == false {
            self.enable_flag(CPUFlag::Zero);
            self.set_accu_reg(1); // `true` is implicitly converted to `1`
        } else {
            self.set_accu_reg(0); // `false` is implicitly converted to `0`
        }
    }
}


/** Helper methods for reading different types of operands */
impl CPU {
    /** Reading methods */
    /// Extracts the next operand value \
    /// This method operates in the following way: \
    /// It first reads an operand type.
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

    /// Reads the next 8 bytes, interprets them as a ram address ([`RamAddr`]), extracts the value at that
    /// RAM address and returns it
    /// - Increments the program counter
    fn read_and_extract_addr(&mut self) -> Result<RamUnit, ErrorType> {
        let addr = self.read_addr()?;
        let extracted = self.ram.at(addr)?;
        Ok(extracted)
    }

    /// Reads the next 8 bytes, interprets them as a register number (`usize`), extracts
    /// the value at that RAM address and returns it as [`RegType`]
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
        self.inc_prog_counter(MEMORY_ADDRESS_SIZE)?;
        Ok(addr)
    }

    /// Reads the next 8 bytes and returns it as `usize` (the register number).
    /// - Increments the program counter
    fn read_reg(&mut self) -> Result<usize, ErrorType> {
        let bytes = self.ram.read_bytes::<8>(self.prog_counter.unwrap())?;
        let num = Unsigned64::from_le_bytes(bytes) as usize;
        self.inc_prog_counter(REG_NUM_SIZE)?;
        Ok(num)
    }

    /// Reads the next 1 byte and returns it as [`CPUFlag`]
    /// - Increments the program counter
    fn read_flag(&mut self) -> Result<CPUFlag, ErrorType> {
        let byte = self.ram.read_byte(self.prog_counter.unwrap())?;
        let flag = CPUFlag::from_byte(byte)?;
        self.inc_prog_counter(FLAG_TYPE_SIZE)?;
        Ok(flag)
    }

    /// Reads the next 8 bytes and returns it as [`EightBytes`]
    /// - Increments the program counter
    fn read_immediate(&mut self) -> Result<EightBytes, ErrorType> {
        let bytes = self.ram.read_bytes::<8>(self.prog_counter.unwrap())?;
        let value: EightBytes = EightBytes::from_le_bytes(bytes);
        self.inc_prog_counter(IMMEDIATE_VALUE_SIZE)?;
        Ok(value)
    }

    /// Reads the next 1 byte and returns it as [`OperandType`]
    /// - Increments the program counter
    fn read_operand_type(&mut self) -> Result<OperandType, ErrorType> {
        let operand_type_byte = self.ram.at(self.prog_counter.unwrap())?;
        let operand_type = OperandType::from_byte(operand_type_byte)?;
        self.inc_prog_counter(OPERAND_TYPE_SIZE)?;
        Ok(operand_type)
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
    pub fn inc_prog_counter(&mut self, val: usize) -> Result<(), ErrorType> {
        if let Some(counter) = &mut self.prog_counter {
            counter.inc(val)?;
            Ok(())
        } else {
            panic!("Attempt to increment program counter in a halted state")
        }
    }
}


/** Register related methods */
impl CPU {
    /// Returns the value of the `n`-th register if it exists, Error otherwise
    pub fn get_reg(&self, n: usize) -> Result<RegType, CPUError> {
        if n < REG_COUNT {
            Ok(self.registers[n])
        } else {
            Err(CPUError::InvalidRegister(n))
        }
    }

    /// Sets the value of `n`-th register to `val` if it exists, Error otherwise
    pub fn set_reg(&mut self, n: usize, val: RegType) -> Result<(), CPUError> {
        if n < REG_COUNT {
            self.registers[n] = val;
            Ok(())
        } else {
            Err(CPUError::InvalidRegister(n))
        }
    }

    /// Returns the value of the special accumulator register
    pub fn get_accu_reg(&self) -> RegType {
        self.get_reg(ACCU_IDX).unwrap()
    }

    /// Sets the value of the special accumulator register to `val`
    pub fn set_accu_reg(&mut self, val: RegType) {
        self.set_reg(ACCU_IDX, val).unwrap()
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
                s.push_str(i.to_string().as_str());
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

