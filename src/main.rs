#![allow(unused)]

mod ram;
mod cpu;
mod error;

use cpu::{*};

struct InstrBuilder {
    result: Vec<u8>,

    /// Address of the previous instruction and its size in bytes
    instr_addrs: Vec<(RamAddr, usize)>
}

impl InstrBuilder {
    pub fn new() -> Self {
        Self {
            result: vec![],
            instr_addrs: vec![]
        }
    }

    pub fn bin_op_imm(mut self, instr: CPUInstr, op1: i64, op2: i64) -> Self {
        let before = self.result.len();
        self.result.push(instr.as_byte());
        self.result.push(OperandType::IMMEDIATE);
        self.result.extend(op1.to_le_bytes());
        self.result.push(OperandType::IMMEDIATE);
        self.result.extend(op2.to_le_bytes());
        self.update_last_instr(self.result.len() - before);
        self
    }

    pub fn bin_op_reg(mut self, instr: CPUInstr, reg1: u8, reg2: u8) -> Self {
        let before = self.result.len();
        self.result.push(instr.as_byte());
        self.result.push(OperandType::REGISTER);
        self.result.push(reg1);
        self.result.push(OperandType::REGISTER);
        self.result.push(reg2);
        self.update_last_instr(self.result.len() - before);
        self
    }

    pub fn set_reg_to_imm(mut self, reg: u8, imm: u64) -> Self {
        let before = self.result.len();
        self.result.push(CPUInstr::SET);
        self.result.push(OperandType::REGISTER);
        self.result.push(reg);
        self.result.push(OperandType::IMMEDIATE);
        self.result.extend(imm.to_le_bytes());
        self.update_last_instr(self.result.len() - before);
        self
    }

    pub fn set_reg_to_reg(mut self, reg1: u8, reg2: u8) -> Self {
        let before = self.result.len();
        self.result.push(CPUInstr::SET);
        self.result.push(OperandType::REGISTER);
        self.result.push(reg1);
        self.result.push(OperandType::REGISTER);
        self.result.push(reg2);
        self.update_last_instr(self.result.len() - before);
        self
    }

    pub fn halt(mut self) -> Self {
        self.result.push(CPUInstr::HALT);
        self.update_last_instr(1);
        self
    }

    pub fn jump(mut self, addr: RamAddr) -> Self {
        let before = self.result.len();
        self.result.push(CPUInstr::JUMP);
        self.result.extend(addr.0.to_le_bytes());
        self.update_last_instr(self.result.len() - before);
        self
    }

    pub fn jump_back(mut self, n: usize) -> Self {
        let before = self.result.len();
        self.result.push(CPUInstr::JUMP);
        let addr = self.instr_addrs[self.instr_addrs.len() - n].0;
        self.result.extend(addr.0.to_le_bytes());
        self.update_last_instr(self.result.len() - before);
        self
    }

    pub fn update_last_instr(&mut self, size: usize) {
        if self.instr_addrs.is_empty() {
            self.instr_addrs.push((CPU_START_ADDR, size))
        } else {
            let (addr, s) = self.instr_addrs.last().unwrap();
            self.instr_addrs.push((RamAddr(addr.0 + s), size))
        }
    }

    pub fn finalize(self) -> Vec<u8> {
        self.result
    }
}


fn main() {
    let mut mem = RAM::new(128);

    let i = InstrBuilder::new()
        .set_reg_to_imm(0, 2)
        .bin_op_reg(CPUInstr::Add, 0, 0)
        .set_reg_to_reg(0, 8)
        .jump_back(2)
        .halt();

    println!("{:?}", i.instr_addrs);

    mem.alloc_bytes(i.finalize());


    let mut cpu = CPU::new(mem);
    cpu.start().unwrap_or_else(|e| eprintln!("Error:\n{e}"));
}
