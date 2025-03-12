pub use crate::cpu_core::typing::{Signed64, Float64};
pub use crate::cpu_core::cpu::{CPUInstr, CPUFlag, CPU};
pub use crate::cpu_core::ram::{RamAddr};

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Operand {
    Int(Signed64),
    Float(Float64),
    Addr(RamAddr),
    Register(usize),
    Flag(CPUFlag),
    Label(String)
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Statement {
    Instruction(CPUInstr, Vec<Operand>),
    LabelDecl(String),
}
