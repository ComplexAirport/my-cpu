#![allow(unused)]
#[macro_use]

use my_cpu::cpu_core::cpu::{*};

fn main() {
    let mut ram = RAM::new(128);

    ram.alloc_u8(CPUInstr::UADD);
    ram.alloc_u8(OperandType::IMMEDIATE);
    ram.alloc_u64(0);
    ram.alloc_u8(OperandType::IMMEDIATE);
    ram.alloc_u64(0);

    ram.alloc_u8(CPUInstr::UGREATEREQUAL);
    ram.alloc_u8(OperandType::REGISTER);
    ram.alloc_u8(ACCU_IDX as u8);
    ram.alloc_u8(OperandType::IMMEDIATE);
    ram.alloc_u64(0);

    ram.alloc_u8(CPUInstr::JUMPIFNOT);
    ram.alloc_u8(OperandType::FLAG);
    ram.alloc_u8(CPUFlag::ZERO);
    ram.alloc_u64(0b0000000000000000000000000000000000000000000000000000000000000000);

    ram.alloc_u8(CPUInstr::HALT);
    println!("{}", ram.used_size());

    let mut cpu = CPU::new(ram);
    let res = cpu.start();

    match res {
        Ok(_) => {},
        Err(e) => eprintln!("{}", e)
    }
}
