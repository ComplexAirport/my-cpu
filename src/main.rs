#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};

fn main() {
    let mut ram = RAM::with_size(128);

    let mut asm = Assembler::new();
    // [52, 0, 10, 0, 0, 0, 0, 0, 0, 0, 55, 2, 3, 15, 0, 0, 0, 0, 0, 0, 0, 3, 25, 0, 0, 0, 0, 0, 0, 0, 53]

    // call start
    asm.add_call(Label::from("start"));

    // @inner_loop:
    asm.add_label(Label::from("inner_loop"));
    // uadd r0 r1
    asm.add_instr(CPUInstr::UAdd);
    asm.add_reg(0);
    asm.add_imm(1);
    // set r0 accu
    asm.add_instr(CPUInstr::Set);
    asm.add_reg(0);
    asm.add_accu();
    // jump inner_loop
    asm.add_jump(Label::from("inner_loop"));

    // @start:
    asm.add_label(Label::from("start"));
    // uadd 15 25
    asm.add_instr(CPUInstr::UAdd);
    asm.add_imm(15);
    asm.add_imm(25);
    // ret
    asm.add_instr(CPUInstr::Ret);

    println!("{:?}", asm.as_bytes(RamAddr(0)));
    if let Err(e) = asm.write_to_ram(&mut ram, RamAddr(0)) {
        eprintln!("{}", e);
        return;
    }

    let mut cpu = CPU::with_ram(ram);

    if let Err(e) = cpu.start() {
        eprintln!("{}", e);
        return;
    }
}
