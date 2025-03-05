#![allow(unused)]
#[macro_use]

use my_cpu::cpu_core::cpu::{CPUInstr, CPU, RAM};


fn main() {
    let mut ram = RAM::new(128);

    ram.alloc_u8(CPUInstr::SET);

    let mut cpu = CPU::new(ram);
    let res = cpu.start();

    match res {
        Ok(_) => {},
        Err(e) => eprintln!("{}", e)
    }

}
