pub mod base_assembler;
pub mod error;
pub mod ast;

use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub asm, "/my_assembler/asm.rs");
