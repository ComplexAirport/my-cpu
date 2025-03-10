use std::collections::HashMap;
pub use crate::cpu_core::cpu::{*};

/// Represents an operand
/// In our CPU "language", there are currently four types of operand (as can be seen in
/// [`OperandType`]). This enum represents the type of the operand and the value
/// (for example, a memory address)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operand {
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


/// Represents a "symbol" or a "label" in our assembly language
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label(String);

impl<T: Into<String>> From<T> for Label {
    fn from(value: T) -> Self {
        Self(value.into())
    }
}


/// Represents a unit in our assembly language which is resolved,
/// which means that it can be converted into bytes
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ResolvedUnit {
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


/// Represents a unit in our assembly language which is not resolved,
/// which means that it cannot yet be converted into bytes.
/// this happens, for example, when there is a jump instruction, but the real memory address
/// of the jump is not yet clear
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnresolvedJump {
    Jump(Label),
    JumpIf(Operand, Label),
    JumpIfNot(Operand, Label),
    Call(Label),
}

impl UnresolvedJump {
    /// Returns the size of the unresolved unit in bytes
    /// (this is possible because despite not knowing the real memory address of the jump,
    /// we know it's size)
    pub const fn size(&self) -> usize {
        match self {
            UnresolvedJump::Jump(_) => {
                CPU::INSTRUCTION_SIZE + CPU::OPERAND_TYPE_SIZE + CPU::MEMORY_ADDRESS_SIZE
            }
            UnresolvedJump::JumpIf(u, _) => {
                CPU::INSTRUCTION_SIZE + u.size() + CPU::OPERAND_TYPE_SIZE + CPU::MEMORY_ADDRESS_SIZE
            }
            UnresolvedJump::JumpIfNot(u, _) => {
                CPU::INSTRUCTION_SIZE + u.size() + CPU::OPERAND_TYPE_SIZE + CPU::MEMORY_ADDRESS_SIZE
            }
            UnresolvedJump::Call(_) => {
                CPU::INSTRUCTION_SIZE  + CPU::OPERAND_TYPE_SIZE + CPU::MEMORY_ADDRESS_SIZE
            }
        }
    }

    /// Returns the "label" of the jump (the symbol it should jump to)
    pub fn label(&self) -> &String {
        match self {
            UnresolvedJump::Jump(s) => &s.0,
            UnresolvedJump::JumpIf(_, s) => &s.0,
            UnresolvedJump::JumpIfNot(_, s) => &s.0,
            UnresolvedJump::Call(s) => &s.0,
        }
    }

    /// Consumes `self` and returns a `Vec<ResolvedUnit>` based on. Requires the real memory address
    /// so it can be resolved.
    pub fn resolve(&self, real_addr: RamAddr) -> Vec<ResolvedUnit> {
        let mut res: Vec<ResolvedUnit> = Vec::with_capacity(3);
        match self {
            UnresolvedJump::Jump(_) => {
                res.push(ResolvedUnit::Instr(CPUInstr::Jump));
                res.push(ResolvedUnit::Operand(Operand::MemoryAddress(real_addr)));
            }
            UnresolvedJump::JumpIf(o, _) => {
                res.push(ResolvedUnit::Instr(CPUInstr::JumpIf));
                res.push(ResolvedUnit::Operand(*o));
                res.push(ResolvedUnit::Operand(Operand::MemoryAddress(real_addr)));
            },
            UnresolvedJump::JumpIfNot(o, _) => {
                res.push(ResolvedUnit::Instr(CPUInstr::JumpIfNot));
                res.push(ResolvedUnit::Operand(*o));
                res.push(ResolvedUnit::Operand(Operand::MemoryAddress(real_addr)));
            },
            UnresolvedJump::Call(_) => {
                res.push(ResolvedUnit::Instr(CPUInstr::Call));
                res.push(ResolvedUnit::Operand(Operand::MemoryAddress(real_addr)));
            }
        }
        res
    }
}


/// Represents a single "unit" in our assembler language
/// The "unit" can either be resolved or unresolved.
/// All unresolved units will get resolved in the end when the real address is clear.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AssemblerUnit {
    Resolved(ResolvedUnit),
    UnresolvedJump(UnresolvedJump)
}


impl AssemblerUnit {
    /// Returns the size of this assembler "unit" in bytes
    pub const fn size(&self) -> usize {
        match self {
            AssemblerUnit::Resolved(r) => r.size(),
            AssemblerUnit::UnresolvedJump(u) => u.size(),
        }
    }
}

/// Represents tha **assembler**, the main "tool" for building our code (byte) for our CPU.
pub struct Assembler {
    symbol_table: HashMap<String, usize>,
    instructions: Vec<AssemblerUnit>
}


impl Assembler {
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
    /// - Converts all `ResolvedUnit`-s into bytes
    /// - Returns those bytes
    pub fn as_bytes(&mut self, start_addr: RamAddr) -> Vec<u8> {
        let mut res: Vec<u8> = Vec::with_capacity(self.total_size());
        let resolved = self.resolve_symbols(start_addr);
        for i in resolved {
            res.extend(i.as_bytes());
        }
        res
    }

    pub fn write_to_ram(&mut self, ram: &mut RAM, start_addr: RamAddr) -> Result<(), ErrorType> {
        let bytes: Vec<SingleByte> = self.as_bytes(start_addr);
        ram.write_bytes(&bytes, start_addr)?;
        Ok(())
    }

    /// Resolves the symbols and returns a vector of resolved units.
    /// - Consumes `self`
    pub fn resolve_symbols(&mut self, start_addr: RamAddr) -> Vec<ResolvedUnit> {
        let mut resolved_instr: Vec<ResolvedUnit> = Vec::with_capacity(self.instructions.len());

        for i in &self.instructions {
            match i {
                AssemblerUnit::Resolved(r) => { resolved_instr.push(*r) }
                AssemblerUnit::UnresolvedJump(u) => {
                    let relative_addr = self.symbol_table.get(u.label());

                    if relative_addr.is_none() {
                        println!("Unresolved symbol found!");
                        break;
                    }
                    let real_addr = start_addr.add(*relative_addr.unwrap()).unwrap();
                    resolved_instr.extend(u.resolve(real_addr));
                }
            }
        }

        resolved_instr
    }

    /// Adds a [`CPUInstr`] to the instructions
    pub fn add_instr(&mut self, instr: CPUInstr) {
        self.add_resolved(ResolvedUnit::Instr(instr));
    }

    /// Adds a [`RamAddr`] to the instructions
    pub fn add_addr(&mut self, addr: RamAddr) {
        self.add_resolved(ResolvedUnit::Operand(Operand::MemoryAddress(addr)));
    }

    /// Adds a register to the instructions
    pub fn add_reg(&mut self, reg: usize) {
        self.add_resolved(ResolvedUnit::Operand(Operand::Register(reg)));
    }

    /// Adds the accumulator register to the instructions
    pub fn add_accu(&mut self) {
        self.add_reg(CPU::GEN_REG_COUNT);
    }

    /// Adds a [`CPUFlag`] to the instructions
    pub fn add_flag(&mut self, flag: CPUFlag) {
        self.add_resolved(ResolvedUnit::Operand(Operand::Flag(flag)));
    }

    /// Adds an immediate value to the instructions
    pub fn add_imm(&mut self, imm: EightBytes) {
        self.add_resolved(ResolvedUnit::Operand(Operand::Immediate(imm)));
    }

    /// Add a float to the instruction. In reality, this method
    /// reinterprets the float's bytes as integer bytes in does `add_imm`
    pub fn add_float(&mut self, f: Float64) {
        self.add_imm(f.reinterpret())
    }

    /// Adds a [`CPUInstr::Jump`] to the instructions with specified label
    pub fn add_jump(&mut self, label: Label) {
        self.add_unresolved_jump(UnresolvedJump::Jump(label));
    }

    /// Adds a [`CPUInstr::JumpIf`] to the instructions with specified label
    pub fn add_jump_if(&mut self, op: Operand, sym: Label) {
        self.add_unresolved_jump(UnresolvedJump::JumpIf(op, sym));
    }

    /// Adds a [`CPUInstr::JumpIfNot`] to the instructions with specified label
    pub fn add_jump_if_not(&mut self, op: Operand, sym: Label) {
        self.add_unresolved_jump(UnresolvedJump::JumpIfNot(op, sym));
    }

    /// Adds a [`CPUInstr::Call`] to the instructions with specified label
    pub fn add_call(&mut self, sym: Label) {
        self.add_unresolved_jump(UnresolvedJump::Call(sym));
    }

    /// Adds a new "label". This operation saves current "relative" address,
    /// so the jump instructions' real addresses can be resolved at the end.
    pub fn add_label(&mut self, sym: Label) {
        let relative_address = self.total_size();
        println!("{:?}", self.instructions);
        println!("total size was {relative_address}");
        self.symbol_table.insert(sym.0, relative_address);
    }

    /// Returns current total size of our "code" in bytes
    pub fn total_size(&self) -> usize {
        self.instructions.iter().map(|u| u.size()).sum()
    }

    /// Adds a [`ResolvedUnit`] to the instructions
    fn add_resolved(&mut self, u: ResolvedUnit) {
        self.instructions.push(AssemblerUnit::Resolved(u));
    }

    /// Adds a [`UnresolvedJump`] to the instructions
    fn add_unresolved_jump(&mut self, u: UnresolvedJump) {
        self.instructions.push(AssemblerUnit::UnresolvedJump(u));
    }
}
