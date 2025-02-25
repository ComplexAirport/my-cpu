use thiserror::Error;
use crate::cpu::{RamAddr, OperandType};

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
    /// Not enough contiguous free space to allocate.
    /// Accepts the amount of bytes that was requested to allocate.
    #[error("Not enough memory to allocate {0} bytes.")]
    OutOfMemory(usize),

    /// Attempted to free a segment that goes out of bounds or overlaps illegally.
    /// Accepts the start address and size of the region that was requested to be freed.
    #[error("Invalid free operation of size {1} at start address {0:?}")]
    InvalidFree(RamAddr, usize),

    /// Generic out-of-bounds error for other operations.
    /// Accepts the address that was out of bounds.
    #[error("Address out of bounds: {0:?}")]
    OutOfBounds(RamAddr),

    /// Read invalid block of memory.
    /// Accepts the start address and size of the region that was tried to be read.
    #[error("Invalid read operation of size {1} at start address {0:?}")]
    InvalidRead(RamAddr, usize),
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

    /// Operand type is not allowed in that instruction (or part of the instruction) \
    /// Accepts the operand type that was not allowed.
    #[error("Operand type {0:?} is not allowed.")]
    OperandTypeNotAllowed(OperandType),
}
