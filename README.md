# My CPU Emulator & Assembler

My CPU is a lightweight CPU emulator and assembler written in Rust. It simulates a simple processor with a custom instruction set, basic registers and flags, and a RAM module with dynamic memory allocation. The included assembler lets you write assembly-like programs (with labels, operands, and jump instructions) and convert them into machine code that the CPU can execute.

## Table of Contents

- [Overview](#overview)
- [Features](#features)
- [Project Structure](#project-structure)
- [Getting Started](#getting-started)
  - [Prerequisites](#prerequisites)
  - [Building the Project](#building-the-project)
- [Usage](#usage)
  - [Running the Example](#running-the-example)
  - [Assembler Workflow](#assembler-workflow)
- [CPU Details](#cpu-details)
- [Memory Management](#memory-management)
- [Error Handling](#error-handling)

## Overview

This repository implements:
- **A CPU Emulator:** A simulated CPU that executes a custom instruction set. It features 8 general-purpose registers, an accumulator, a program counter, and flags (Zero, Sign, and Overflow).
- **An Assembler:** A simple assembler that converts assembly instructions into machine code. It supports operands of different types (memory address, register, flag, and immediate), labels, and unresolved jump instructions that are later resolved into absolute addresses.
- **RAM Module:** A RAM abstraction with a segment-list allocator for dynamic memory management. It provides methods to allocate, free, and read/write various data types.

## Features

- **Custom Instruction Set:**  
  - Arithmetic: `Add`, `Sub`, `Mul`, `Mod`, `Div`
  - Logical: `And`, `Or`, `Xor`, `Not`
  - Bitwise: `BitwiseAnd`, `BitwiseOr`, `BitwiseXor`, `BitwiseNot`
  - Shifts: `Shl`, `Shr`
  - Control Flow: Unconditional and conditional jumps (`Jump`, `JumpIf`, `JumpIfNot`, `JumpIfGreater`, `JumpIfLess`, `JumpIfEqual`)
  - Floating-point operations (`FAdd`, `FSub`, `FMul`, `FDiv`) are present as placeholders.

- **Assembler Capabilities:**  
  - Define instructions and operands in a high-level, human-readable form.
  - Use labels for jump instructions.
  - Resolve symbolic addresses to generate final machine code.
  - Output the assembled code as bytes and write it directly to RAM.

- **RAM Management:**  
  - Dynamic allocation using a segment-list allocator.
  - Safe memory operations with overflow checks.
  - Read/write operations for various integer sizes (`u8` through `u128` and their signed counterparts).

- **Debugging Support:**  
  - The CPU maintains an instruction counter and prints state information after each instruction execution (for debugging purposes).

## Project Structure

- **src/cpu.rs**  
  Contains the CPU emulator implementation:
  - Defines the `CPUInstr` enum with all supported instructions.
  - Implements operand types (`MemoryAddress`, `Register`, `Flag`, `Immediate`) and CPU flags.
  - Manages CPU state (registers, accumulator, program counter, and flags) and instruction execution.

- **src/ram.rs**  
  Implements a RAM module with:
  - A segment-list allocator to manage free memory.
  - Functions to allocate/free memory and read/write bytes and integers.

- **src/my_assembler.rs**  
  Provides the assembler functionality:
  - Represents assembly units (resolved instructions and unresolved jumps).
  - Maintains a symbol table for labels.
  - Resolves jumps to generate final machine code.
  - Can write the assembled code into a RAM instance.

- **src/error.rs**  
  (Not shown here, but) defines error types used by the CPU and RAM modules (e.g., `CPUError`, `RAMError`).

- **src/macros.rs**  
  Contains helper macros (such as opcode definitions) used across the project.

- **src/main.rs**  
  An example program demonstrating how to:
  - Use the assembler to build a simple loop.
  - Write the assembled program to RAM.
  - Execute the program on the CPU emulator.

## Getting Started

### Prerequisites

- [Rust (edition 2021)](https://www.rust-lang.org/tools/install)
- [Cargo](https://doc.rust-lang.org/cargo/)

### Building the Project

Clone the repository and build with Cargo:

```bash
git clone https://github.com/ComplexAirport/my-cpu.git
cd my-cpu
cargo build --release
```

## Usage

### Running the Example

The `main.rs` file demonstrates a basic program that:
- Sets up an assembler.
- Defines a simple loop (using labels and jump instructions).
- Writes the machine code to a RAM instance.
- Instantiates the CPU and starts execution.

Run the example with:

```bash
cargo run --release
```

You should see the CPU executing instructions until it reaches a halt condition.

### Assembler Workflow

The assembler allows you to build programs by:
- Adding instructions and their operands:
  ```rust
  let mut assembler = Assembler::new();
  assembler.add_instr(CPUInstr::Set);
  assembler.add_reg(0);
  assembler.add_imm(-1);
  ```
- Defining labels to mark jump destinations:
  ```rust
  assembler.add_label(Label::from("begin"));
  ```
- Adding jump instructions with unresolved labels:
  ```rust
  assembler.add_jump_if_not(Operand::Flag(CPUFlag::Sign), Label::from("begin"));
  assembler.add_jump(Label::from("begin"));
  ```
- Resolving symbols and writing the assembled code to RAM:
  ```rust
  let mut ram = RAM::new(128);
  assembler.write_to_ram(&mut ram).unwrap();
  ```

## CPU Details

- **Registers & Flags:**  
  The CPU contains 8 general-purpose registers, an accumulator register, and supports flags for zero, sign, and overflow conditions.

- **Instruction Cycle:**  
  The CPU fetches an instruction byte from RAM, decodes it into a `CPUInstr`, executes the corresponding operation, and then advances the program counter. This continues until a `Halt` instruction is encountered.

- **Instruction Set:**  
  The supported instructions cover arithmetic, logical, bitwise, shift, and conditional jump operations. Note that floating-point operations are currently placeholders (marked as "todo").

## Memory Management

The RAM module provides:
- **Dynamic Allocation:**  
  A segment list allocator to allocate and free contiguous blocks of memory.
- **Safety Checks:**  
  Overflow-safe arithmetic for address manipulation and bounds checking for read/write operations.
- **Utility Methods:**  
  Methods to allocate, free, and read/write primitive data types (from `u8` to `u128` and signed equivalents).

## Error Handling

Both CPU and RAM operations include detailed error handling:
- **CPUError:**  
  Reports issues like invalid instructions, operand type mismatches, or execution failures.
- **RAMError:**  
  Handles memory allocation errors, out-of-bounds accesses, and invalid read/write operations.
