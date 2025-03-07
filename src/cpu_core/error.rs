use thiserror::Error;
use super::cpu::{RamAddr, OperandType};

/// Represents a general error type which can be used throughout this project
#[derive(Debug, Error)]
pub enum ErrorType {
    #[error(transparent)]
    RAMError(#[from] RAMError),

    #[error(transparent)]
    CPUError(#[from] CPUError),
}

/// Represents errors related to our RAM (Random Access Memory)
#[derive(Debug, Error)]
pub enum RAMError {
    /// Represents a failure to read a RAM address
    #[error("Bad read at RAM address {0:?}")]
    BadRead(RamAddr),

    /// Represents a failure to write to a RAM address
    #[error("Bad write to RAM address {0:?}")]
    BadWrite(RamAddr),

    /// Represents an overflow of a RAM address
    /// For example, if we try to do `RamAddr(usize::MAX).add()`, this error will occur
    #[error("RAM address overflow occurred at {0:?}")]
    AddressOverflow(RamAddr)
}

/// Represents errors related to our CPU
#[derive(Debug, Error)]
pub enum CPUError {
    /// Read an invalid instruction byte (the byte doesn't represent any instruction). \
    /// Accepts the byte that was an invalid instruction
    #[error("Invalid cpu instruction: {0}")]
    InvalidInstruction(u8),
    
    /// Read an invalid operand byte (the byte doesn't represent any operand) \
    /// Accepts the byte that was an invalid operand
    #[error("Invalid operand type: {0}")]
    InvalidOperandType(u8),

    /// Read an invalid register number (for example, there are only `8` registers,
    /// but the number was `11`). \
    /// Accepts the attempted register number.
    #[error("Invalid register number: {0}")]
    InvalidRegister(usize),

    /// Read an invalid flag number (See [`crate::cpu::CPUFlag`]) for more info. \
    /// Accepts the attempted flag number.
    #[error("Invalid flag number: {0}")]
    InvalidFlag(u8),

    /// Received an invalid jump address (for example, the address is out of bounds)
    #[error("Invalid jump address: {0:?}")]
    InvalidJump(RamAddr),

    /// Operand type is not allowed in that instruction (or part of the instruction) \
    /// Accepts the operand type that was not allowed.
    #[error("Operand type {0:?} is not allowed.")]
    OperandTypeNotAllowed(OperandType),
    
    /// Divided by zero
    #[error("Division by zero")]
    DivisionByZero,

    /// Stack overflow error
    #[error("Stack limit reached")]
    StackOverflow,

    /// Stack underflow error
    #[error("Tried to pop or remove from an empty stack")] // todo: right error message?
    StackUnderflow,
}
