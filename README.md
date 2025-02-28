# Virtual CPU and Memory Emulator

## Overview
This project implements a **virtual CPU and memory system** in Rust, designed to simulate basic instruction execution, memory allocation, and register-based computation. It includes a custom CPU architecture, a RAM module, an instruction set, and an execution loop.

## Features
- **Virtual CPU with Registers**
    - 8 General-purpose registers (`GEN_REG_COUNT = 8`)
    - 1 Accumulator register for storing computation results
    - Program counter for instruction flow control
    - Flag registers (Zero, Carry, Sign, Overflow)
- **Memory Management**
    - 1 MB of RAM (`MEM_SIZE = 1 * 1024 * 1024`)
    - Allocates memory using a segment list for efficient space utilization
    - Supports reading and writing various data types (`u8`, `u16`, `u32`, `u64`, `i8`, `i16`, etc.)
- **Instruction Set**
    - Basic arithmetic (`ADD`, `SUB`, `MUL`)
    - Memory operations (`LOAD`, `SET`)
    - Program control (`HALT`, `JUMP`)
    - System calls (`SYSCALL`)
- **Cross-platform Terminal Handling** (using `crossterm`)
    - Supports clearing the screen
    - Prints CPU state and debug messages

## Project Structure
```
.
├── src
│   ├── main.rs           # Entry point of the program
│   ├── cpu.rs            # Virtual CPU implementation
│   ├── ram.rs            # Memory management system
│   ├── instruction.rs    # Instruction definitions
│   ├── error.rs          # Custom error handling
│   ├── macros.rs         # Utility macros for reducing boilerplate
├── Cargo.toml            # Rust package configuration
└── README.md             # Project documentation
```

## Getting Started
### Prerequisites
- Rust (latest stable version)
- Cargo package manager

### Installation
Clone the repository:
```sh
git clone https://github.com/your-username/virtual-cpu.git
cd virtual-cpu
```

### Build and Run
To compile the project:
```sh
cargo build --release
```
To run the virtual CPU:
```sh
cargo run
```

## Usage
### Writing to Memory
The CPU allows storing values in memory using an **allocation system**.
```rust
let addr = ram.alloc_u32(42).unwrap();
let value = ram.read_u32(addr).unwrap();
assert_eq!(value, 42);
```
### Executing Instructions
CPU instructions are fetched, decoded, and executed in a loop.
```rust
cpu.execute_next().unwrap();
```
### Custom Macros for Memory Operations
The project includes a macro for handling memory allocations:
```rust
impl_alloc_read! {
    u8: u8 => 1,
    u16: u16 => 2,
    u32: u32 => 4,
    u64: u64 => 8,
    u128: u128 => 16,
    i8: i8 => 1,
    i16: i16 => 2,
    i32: i32 => 4,
    i64: i64 => 8,
    i128: i128 => 16,
}
```

## Future Enhancements
- Add **I/O handling**.
- Improve **debugging tools** with step-by-step execution tracing.

