#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};
use my_cpu::cpu_core::cpu::CPUInstr::{*};

fn main() {
    let mut asm = Assembler::new();
    asm.add_instr(Push);
    asm.add_imm(69);

    asm.add_call(Label::from("main"));
    asm.add_instr(Halt);


    asm.add_label(Label::from("main"));
    // prologue
    asm.add_instr(Push); // push sb;
    asm.add_sb();

    asm.add_instr(Set); // set sb sp;
    asm.add_sb();
    asm.add_sp();

    // Main code
    asm.add_instr(Push); // Local variable 1
    asm.add_imm(123);
    asm.add_instr(Push); // Local variable 2
    asm.add_imm(123);

    asm.add_get_sb(2 * 8, 0); // Store the first argument to register 0
    asm.add_get_sb(-8, 1); // Store the first local variable to register 1
    
    // epilogue
    asm.add_instr(Set); // set sp sb;
    asm.add_sp();
    asm.add_sb();

    asm.add_instr(Pop); // pop sb;
    asm.add_sb();

    asm.add_instr(Ret);


    let mut ram = RAM::with_size(200);

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
