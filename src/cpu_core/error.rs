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


    /// Attempted to do an addition on memory address which lead to overflow
    #[error("Address {0:?} overflowed when increased by {1}")]
    AddrAddError(RamAddr, usize),

    /// Attempted to subtract from memory address which lead to overflow
    #[error("Failed to subtract {1} from {0:?} (getting negative address)")]
    AddrSubError(RamAddr, usize),
    
    /// Attempted to allocate `0` bytes
    #[error("Tried to allocate zero bytes")]
    AllocatingZero,

    
    /// Not enough memory to allocate bytes (allocation starting from specified address)
    #[error("Not enough in RAM region [{1:?}; [end]) to allocate {0} bytes.")]
    NotEnoughMemory(usize, RamAddr),
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

    #[error("Invalid jump address: {0:?}")]
    InvalidJump(RamAddr),

    /// Operand type is not allowed in that instruction (or part of the instruction) \
    /// Accepts the operand type that was not allowed.
    #[error("Operand type {0:?} is not allowed.")]
    OperandTypeNotAllowed(OperandType),
}
