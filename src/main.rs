#![allow(unused)]
#[macro_use]

use my_cpu::cpu::{*};
use my_cpu::my_assembler::{Assembler, Label, Operand};

fn main() {
    // An example program with our assembler
    
    let mut assembler = Assembler::new();
    
    assembler.add_instr(CPUInstr::Set);
    assembler.add_reg(0);
    assembler.add_float(2.0);
    
    assembler.add_instr(CPUInstr::Halt);
    
    
    let mut ram = RAM::new(128);
    assembler.write_to_ram(&mut ram).unwrap();
    let mut cpu = CPU::new(ram);
    cpu.start().unwrap();
}
