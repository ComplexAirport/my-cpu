#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};

fn main() {
    let mut asm = Assembler::new();

    // Store 3.14159265358979323846264338327950288 0xf8
    asm.add_instr(CPUInstr::Store);
    asm.add_float(std::f64::consts::PI);
    asm.add_addr(RamAddr(256 - 8));

    // Load 0xf8 0
    asm.add_instr(CPUInstr::Load);
    asm.add_addr(RamAddr(256 - 8));
    asm.add_reg(0);

    let mut ram = RAM::with_size(256);

    if let Err(e) = asm.write_to_ram(&mut ram, RamAddr(0)) {
        eprintln!("{}", e);
        return;
    }

    let mut cpu = CPU::with_ram(ram);

    if let Err(e) = cpu.start() {
        eprintln!("{}", e);
    }
}
