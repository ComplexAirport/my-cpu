use thiserror::Error;
use crate::cpu_core::cpu::CPUInstr;

#[derive(Debug, Error)]
pub enum AsmError {
    #[error("Parser Error\n{0}")]
    ParserError(String),
    
    #[error("{0:?}: expected {1} arguments, got {2}")]
    ArgumentError(CPUInstr, usize, usize)
}