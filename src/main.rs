#![allow(unused)]
#[macro_use]

use my_cpu::my_assembler::assembler0::{*};


fn main() {
    // An example program with our assembler
    let code: &'static str = ";


    
";
    
    let src = Source::new("test.txt", code);

    let lexer = Lexer::new(&src);
    let res = lexer.read_tokens();
    if res.is_err() {
        println!("{}", res.unwrap_err())
    } else {
        for i in res.unwrap() {
            println!("{:?}", i);
        }
    }
}
