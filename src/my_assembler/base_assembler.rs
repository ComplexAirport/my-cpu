use std::collections::HashMap;
use crate::cpu_core::cpu::{*};

use super::ast;
use super::error::AsmError;

use lalrpop_util::lalrpop_mod;


lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    pub asm,
    "/my_assembler/asm.rs"
);

/// Represents an operand
/// In our CPU "language", there are currently four types of operand (as can be seen in
/// [`OperandType`]). This enum represents the type of the operand and the value
/// (for example, a memory address)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Operand {
    MemoryAddress(RamAddr),
    Register(usize),
    Flag(CPUFlag),
    Immediate(EightBytes),
}

impl Operand {
    /// Get size of the operand in bytes
    pub const fn size(&self) -> usize {
        CPU::OPERAND_TYPE_SIZE + match self {
            Operand::MemoryAddress(_) => CPU::MEMORY_ADDRESS_SIZE,
            Operand::Register(_) => CPU::REG_NUM_SIZE,
            Operand::Flag(_) => CPU::FLAG_TYPE_SIZE,
            Operand::Immediate(_) => CPU::IMMEDIATE_VALUE_SIZE,
        }
    }

    /// Returns the operand value in bytes
    pub fn value_bytes(&self) -> Vec<u8> {
        match self {
            Operand::MemoryAddress(addr) => addr.0.to_le_bytes().into(),
            Operand::Register(reg) => (*reg as u8).to_le_bytes().into(),
            Operand::Flag(flag) => vec![flag.as_byte()],
            Operand::Immediate(imm) => imm.to_le_bytes().into(),
        }
    }

    /// Returns the operand type + operand value representation in bytes
    pub fn operand_bytes(&self) -> Vec<u8> {
        let mut res: Vec<u8> = Vec::with_capacity(1 + self.size());
        res.push(match self {
            Operand::MemoryAddress(_) => OperandType::MEMORY_ADDRESS,
            Operand::Register(_) => OperandType::REGISTER,
            Operand::Flag(_) => OperandType::FLAG,
            Operand::Immediate(_) => OperandType::IMMEDIATE,
        });
        res.extend(self.value_bytes());
        res
    }
}


/// Represents a unit in our assembly language which is resolved,
/// which means that it can be converted into bytes
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ResolvedUnit {
    Instr(CPUInstr),
    Operand(Operand),
}

impl ResolvedUnit {
    /// Returns the size of the resolved unit in bytes
    pub const fn size(&self) -> usize {
        match self {
            ResolvedUnit::Instr(_) => CPU::INSTRUCTION_SIZE,
            ResolvedUnit::Operand(o) => o.size()
        }
    }

    /// Returns the resolved unit represented in bytes
    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            ResolvedUnit::Instr(i) => { vec![i.as_byte()] },
            ResolvedUnit::Operand(o) => o.operand_bytes()
        }
    }
}


/// Represents a label the real memory address of which is not yet clear. This may happen when
/// the user does `jump ^label`. Since the program does not know at what address it's going to be
/// allocated, the real address of `^label` is unclear until it's resolved in the future.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct UnresolvedAddress(pub String);

impl UnresolvedAddress {
    pub const SIZE: usize = 1 + CPU::MEMORY_ADDRESS_SIZE; // operand type 1 byte + address 8 bytes
}


/// Represents a single "unit" in our assembler language
/// The "unit" can either be resolved or unresolved.
/// All unresolved units will get resolved in the end when the real address is clear.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum BaseAssemblerUnit {
    Resolved(ResolvedUnit),
    UnresolvedAddr(UnresolvedAddress)
}

impl BaseAssemblerUnit {
    /// Returns the size of this assembler "unit" in bytes
    pub const fn size(&self) -> usize {
        match self {
            BaseAssemblerUnit::Resolved(r) => r.size(),
            BaseAssemblerUnit::UnresolvedAddr(_) => UnresolvedAddress::SIZE,
        }
    }
}


/// Represents tha **assembler**, the base "tool" for building byte-code for our CPU.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct _BaseAssembler {
    symbol_table: HashMap<String, usize>,
    instructions: Vec<BaseAssemblerUnit>
}

impl _BaseAssembler {
    pub fn new() -> Self {
        Self {
            symbol_table: HashMap::new(),
            instructions: Vec::new(),
        }
    }

    /// Finalize the assembly "code" and return the bytes (readable by CPU). \
    /// This operation:
    /// - Resolves all symbols (based on `start_addr` field which represents the final start address
    ///     of the instructions in RAM)
    /// - Converts all the resulting [`ResolvedUnit`]-s into bytes
    /// - Returns those bytes
    pub fn to_bytes(&self, start_addr: RamAddr) -> Vec<u8> {
        self.resolve(start_addr)
            .iter()
            .flat_map(|f| f.as_bytes())
            .collect()
    }

    /// Resolves the symbols and returns a vector of resolved units.
    fn resolve(&self, start_addr: RamAddr) -> Vec<ResolvedUnit> {
        self.instructions
            .iter()
            .map(|i| match i {
                BaseAssemblerUnit::Resolved(u) => *u,
                BaseAssemblerUnit::UnresolvedAddr(u) => {
                    let real_addr = start_addr.add(*self.symbol_table.get(&u.0).unwrap()).unwrap();
                    ResolvedUnit::Operand(Operand::MemoryAddress(real_addr))
            }})
            .collect()
    }


    /// Adds a [`CPUInstr`] to the instructions
    fn add_instr(&mut self, instr: CPUInstr) {
        self.add_resolved(ResolvedUnit::Instr(instr));
    }

    /// Adds a [`RamAddr`] to the instructions
    fn add_addr(&mut self, addr: RamAddr) {
        self.add_resolved(ResolvedUnit::Operand(Operand::MemoryAddress(addr)));
    }

    /// Adds a register to the instructions
    fn add_reg(&mut self, reg: usize) {
        self.add_resolved(ResolvedUnit::Operand(Operand::Register(reg)));
    }

    /// Adds a [`CPUFlag`] to the instructions
    fn add_flag(&mut self, flag: CPUFlag) {
        self.add_resolved(ResolvedUnit::Operand(Operand::Flag(flag)));
    }

    /// Adds an immediate value to the instructions
    fn add_imm(&mut self, imm: EightBytes) {
        self.add_resolved(ResolvedUnit::Operand(Operand::Immediate(imm)));
    }

    /// Add a float to the instruction. In reality, this method
    /// reinterprets the float's bytes as integer bytes in does `add_imm`
    fn add_float(&mut self, f: Float64) {
        self.add_imm(f.reinterpret())
    }


    /// Adds a new "label". This operation saves current "relative" address,
    /// so the jump instructions' real addresses can be resolved at the end.
    fn add_label(&mut self, sym: String) {
        let relative_index = self.size();
        self.symbol_table.insert(sym, relative_index);
    }

    /// Adds a [`ResolvedUnit`] to the instructions
    fn add_resolved(&mut self, u: ResolvedUnit) {
        self.instructions.push(BaseAssemblerUnit::Resolved(u));
    }

    /// Adds a [`UnresolvedAddress`] to the instructions
    fn add_unresolved_addr(&mut self, label: String) {
        self.instructions.push(BaseAssemblerUnit::UnresolvedAddr(UnresolvedAddress(label)))
    }

    /// Returns current total size of the instructions
    pub fn size(&self) -> usize {
        self.instructions.iter().map(|u| u.size()).sum()
    }
}

impl Default for _BaseAssembler {
    fn default() -> Self {
        Self::new()
    }
}


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assembler {
    code: String,
}

impl Assembler {
    pub fn from<S: Into<String>>(code: S) -> Self {
        Self { code: code.into() }
    }

    //noinspection ALL
    pub fn parse(&self) -> Result<_BaseAssembler, AsmError> {
        use ast::{Statement, Operand};

        let mut assembler = _BaseAssembler::new();

        let result: Result<Vec<Statement>, _> = asm::ProgramParser::new().parse(self.code.as_str());
        let statements = result.map_err(|e| AsmError::ParserError(e.to_string()))?;

        for statement in statements {
            match statement {
                Statement::Instruction(instr, operands) => {
                    assembler.add_instr(instr);

                    for operand in operands {
                        match operand {
                            Operand::Int(o) => assembler.add_imm(o),
                            Operand::Float(o) => assembler.add_float(o),
                            Operand::Addr(o) => assembler.add_addr(o),
                            Operand::Register(o) => assembler.add_reg(o),
                            Operand::Flag(o) => assembler.add_flag(o),
                            Operand::Label(o) => assembler.add_unresolved_addr(o),
                        }
                    }
                }

                Statement::LabelDecl(label) => {
                    assembler.add_label(label);
                }
            }
        }

        Ok(assembler)
    }
}
