## Maybe?
- Forbid to `Set` `OperandType::MemoryAddress` and add separate `Stb` (Store byte) and `Stq` (store quad word) instructions?

- Make `read_and_extract_addr()` also allow addresses in registers?

- Forbid to `Set` a flag?

- For shifts (UShl, UShr, IShl, IShr), we do:
`x.overflowing_shl(y as u32)`
without bounds-checking y beyond the cast. In real hardware, the shift amount typically uses only the lower 5 or 6 bits (e.g. y & 0x3F for 64-bit). If y is out of range, you might get shifts that effectively do zero or something else. In our case, we just do a normal Rust conversion—if y is big, it will saturate to some 32-bit number. That can lead to shifting by 400 million bits, which is just 0 in Rust but might set the overflow flag in a “real CPU.” We could add a clamp or mod: `let shift_amount = (y as u32) & 63;  // only take 6 bits`
 
## Pipelines, Caches, Interrupts (If You Want to Go Further)
If your goal is purely an instructional single-cycle CPU model, you’ve done enough. If you ever want to simulate pipelining (with hazards, stalls, bypassing, etc.) or “interrupts” with context switching, you’ll need more infrastructure:
Pipeline: separate “fetch, decode, execute, memory, writeback” steps in your cycle
Interrupts: CPU needs an interrupt vector, interrupt_enable flags, a way to push the PC, etc.