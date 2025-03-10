#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};

fn main() {
    let mut asm = Assembler::new();

    // loop1:
    asm.add_label(Label::from("f1"));
    
    asm.add_instr(CPUInstr::ULess);
    asm.add_reg(1);
    asm.add_imm(1024);

    asm.add_jump_if_not(Operand::Register(CPU::ACCU_IDX), Label::from("exit"));

    asm.add_instr(CPUInstr::UAdd);
    asm.add_reg(1);
    asm.add_imm(1);

    asm.add_instr(CPUInstr::Set);
    asm.add_reg(1);
    asm.add_accu();

    // JumpIf accu loop1
    asm.add_call(Label::from("f1"));

    asm.add_label(Label::from("exit"));
    asm.add_instr(CPUInstr::UAdd);
    asm.add_imm(10);
    asm.add_imm(20);
    asm.add_instr(CPUInstr::Halt);


    let mut ram = RAM::with_size(32 * 1024);

    println!("{:?}", asm.as_bytes(RamAddr(0)));

    if let Err(e) = asm.write_to_ram(&mut ram, RamAddr(0)) {
        eprintln!("{}", e);
        return;
    }

    let mut cpu = CPU::with_ram(ram);

    if let Err(e) = cpu.start() {
        eprintln!("{}", e);
    }
}
