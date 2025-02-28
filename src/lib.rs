#![allow(unused_imports)]

pub mod macros;
pub mod ram;
pub mod cpu;
pub mod error;
pub use cpu::{*};
pub use cpu::CPUInstr::{*};


#[cfg(test)]
mod tests {
    use super::{*};

    #[test]
    fn test_ram() {
        
    }
}
