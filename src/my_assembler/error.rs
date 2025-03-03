use thiserror::Error;
use super::text_loc::CharLoc;

/// Represents a general error type which can be used throughout this project
#[derive(Debug, Error)]
pub enum ErrorType {
    #[error(transparent)]
    Assembler0Error(#[from] Assembler0Error),
}

/// Represents errors related to Assembler 0
#[derive(Debug, Error)]
pub enum Assembler0Error {
    #[error("Unexpected token encountered at {0}")]
    UnexpectedToken(String),

    #[error("Unexpected dot encountered at {0}")]
    UnexpectedNumberDot(String),

    #[error("Got address too long (>16) at {0}")]
    AddressTooLong(String),

    #[error("Expected an address at {0}")]
    ExpectedAddress(String),
}