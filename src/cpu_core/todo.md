## New Stack Instructions

We'll introduce instructions to push and pop 8 bytes to/from the stack, as well as function call/return instructions.

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
- [x] `SetMem [dest_addr] [source_reg]`

Similarly, introduce new LoadMem instruction with which we can quickly
load 8 bytes from memory into a register
- [x] `LoadMem [source_addr] [dest_reg]`
