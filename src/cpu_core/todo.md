## New Stack Instructions

We'll introduce instructions to push and pop 8 bytes to/from the stack, as well as function call/return instructions.

**Assumptions**
- We have designated a special register (e.g. `SP_IDX = 7`) to act as the stack pointer (SP).
- The stack grows downward, so pushing data decrements the stack pointer, and popping increments it.

---

### [ ] `Push [source_operand]`
- **Goal:** Store 8 bytes from `source_operand` (which could be a register, an immediate, a memory address, or even a flag if you like) onto the stack.
- **Steps:**
    1. Decode the operand to get its 8-byte value.
    2. Decrement `SP` by 8.
    3. Write the 8 bytes to RAM at `[SP..SP+8]`.

---

### [ ] `Pop [destination_operand]`
- **Goal:** Load 8 bytes from the top of the stack into the given `destination_operand`.
- **Steps:**
    1. Read 8 bytes from RAM at `[SP..SP+8]`.
    2. Increment `SP` by 8.
    3. Write those 8 bytes into the operand (register, memory, flag, etc.).

---

### [ ] `Call [addr_operand]`
- **Goal:** Function‐call mechanic. Save the current `PC` (program counter) on the stack, then jump to `addr_operand`.
- **Steps:**
    1. Push the current `PC`.
    2. Set `PC` to the address decoded from `addr_operand`.

---

### [ ] `Ret`
- **Goal:** Function‐return mechanic. Restore the `PC` by popping from the stack.
- **Steps:**
    1. Pop an 8-byte value from stack.
    2. Set `PC` to that popped address.

---

### [ ] “Push/Pop Multiple” or “Adjust SP”
- **Push/Pop Multiple**
    - Some architectures allow pushing/popping multiple registers at once, e.g. `PushAll R0..R3`.
    - If desired, add instructions to do so in a single operation.
- **Adjust SP**
    - A direct way to reserve space on the stack or release it, e.g. `AddSP <immediate>`.
    - This simply updates the stack pointer by some immediate offset.



## New SetMem, LoadMem instructions
Introduce new SetMem instruction with which we can quickly store values
from registers to 8 memory addresses
- [ ] `SetMem [dest_addr] [source_reg]`

Similarly, introduce new LoadMem instruction with which we can quickly
load 8 bytes from memory into a register
- [ ] `LoadMem [source_addr] [dest_reg]`