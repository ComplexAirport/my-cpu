#![allow(unused)]
#[macro_use]

use my_cpu::cpu::{*};
use my_cpu::my_assembler::{Assembler, Label, Operand};

fn main() {
    // An example program with our assembler
    
    let mut assembler = Assembler::new();

    assembler.add_instr(CPUInstr::Set);
    assembler.add_reg(0);
    assembler.add_imm(-1);

    assembler.add_label(Label::from("begin"));

    assembler.add_instr(CPUInstr::Sub);
    assembler.add_reg(0);
    assembler.add_imm(1);

    assembler.add_instr(CPUInstr::Set);
    assembler.add_reg(0);
    assembler.add_accu();

    assembler.add_jump_if_not(Operand::Flag(CPUFlag::Sign), Label::from("begin"));

    assembler.add_jump(Label::from("begin"));
    
    let mut ram = RAM::new(128);
    assembler.write_to_ram(&mut ram).unwrap();
    let mut cpu = CPU::new(ram);
    cpu.start().unwrap();
}
