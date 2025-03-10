#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};

fn main() {
    let mut ram = RAM::with_size(128);

    let mut asm = Assembler::new();

    asm.add_instr(CPUInstr::Store);
    asm.add_float(1000.0);
    asm.add_addr(RamAddr(100));

    asm.add_instr(CPUInstr::Load);
    asm.add_addr(RamAddr(100));
    asm.add_reg(0);

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
