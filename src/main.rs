#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::base_assembler::{*};
use my_cpu::cpu_core::cpu::CPUInstr::{*};

fn main() {
    let mut asm = Assembler::new();

    /*
    ***   argument 1    ***
    ***   argument 2    ***
    ...
    ***  return address ***
    ***    saved sb     ***  <- sb
    ...

    *** local variable 1 ***
    *** local variable 2 ***

    GetBp +0 -> old base pointer address
    GetBp +1 -> return address

    GetBp +2 -> first argument
    GetBp +3 -> second argument

    GetBp -1 -> local variable 1
    GetBp -2 -> local variable 2

    function:
    // prologue:
    push sb;    // save old base pointer
    set sb sp;  // Set current base pointer to old base pointer address

    *** function body ***
    offset sb +2; // Get first argument
    load r0 _;

    offset sb +3; // Get second argument
    load r1 _;

    add r0 r1;   // Add two registers
    set r0 _;   // Store the result

    // epilogue:
    set sp sb; // Move stack pointer to base pointer address (erase all local variables)
    pop sb;   // Restore old base pointer address
    ret;



    // IDEAS
    offset_addr sb -1;
    load _;

    offset_addr sb -2;
    load _;

    */

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

    asm.add_instr(Offset); // access the first argument
    asm.add_sb();
    asm.add_imm(2 * 8);
    asm.add_instr(Load);
    asm.add_accu();
    asm.add_reg(0);

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
