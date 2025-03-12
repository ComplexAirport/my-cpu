#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};
use my_cpu::cpu_core::cpu::CPUInstr::{*};
use my_cpu::cpu_core::cpu::RAM;
use my_cpu::my_assembler::ast::{*};

fn main() {
    let code: &str = "
    call ^main
    halt
    ----- main -----
    set r0 0

      --- loop ---
      uadd r0 1
      set r0 _

    ult r0 1000
    jump_if _ ^loop
    ret
    ";

    let bytes = Assembler::from(code).parse().unwrap().to_bytes(RamAddr(0));
    println!("{:?}", bytes);
    let mut ram = RAM::with_size(128);
    ram.write_bytes(&bytes, RamAddr(0)).unwrap();

    let mut cpu = CPU::with_ram(ram);
    cpu.start().unwrap();
}
