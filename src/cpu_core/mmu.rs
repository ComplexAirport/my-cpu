use crate::cpu_core::ram::{RAM, Address};
use crate::cpu_core::error::RAMError;
use crate::cpu_core::typing::{SingleByte, Unsigned64};

// 4-level paging constants \
// These mirror x86-64 style:
// - 9 bits per level
// - 12-bit offset = 4 KB pages

/// 4kb pages = 2^12
const PAGE_OFFSET_BITS: usize = 12;

/// Bitmask for getting page offset. Equal to 0b111111111111
const PAGE_OFFSET_MASK: usize = (1 << PAGE_OFFSET_BITS) - 1;

/// Shifts for for PML4, PDPT, PD, PT
const LEVEL_SHIFT: [usize; 4] = [39, 30, 21, 12];

/// Bitmask for getting a page level value. 9 bits
const LEVEL_MASK:  usize      = 0b111111111;


/// The MMU holds a reference to physical RAM and the base address of the top-level (PML4)
/// page table.
/// - Uses 4KB paging
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MMU {
    pub ram: RAM,

    /// The physical base address of the top-level page table (PML4).
    /// The PTBR (a CPU register) holds the base physical address where that
    /// process’s top-level page table (e.g., the PML4) is stored.
    /// The OS / CPU sets this when switching processes.
    pml4_base: Address
}

impl MMU {
    pub const fn from(ram: RAM, pml4: Address) -> Self {
        Self { ram, pml4_base: pml4 }
    }

    /// Reads a single byte from RAM using a virtual address
    pub fn read_byte(&mut self, virtual_addr: Address) -> Result<SingleByte, RAMError> {
        let phys = self.translate(virtual_addr)?;
        self.ram.read_byte(phys)
    }

    /// Writes a single byte to RAM using a virtual address
    pub fn write_byte(&mut self, value: SingleByte, virtual_addr: Address) -> Result<(), RAMError> {
        let phys = self.translate(virtual_addr)?;
        self.ram.write_byte(value, phys)
    }

    /// Reads `C` bytes from RAM using a virtual address
    pub fn read_bytes<const C: usize>(&mut self, virtual_addr: Address) -> Result<[u8; C], RAMError> {
        let mut out = [0u8; C];
        for i in 0..C {
            let b = self.read_byte(Address(virtual_addr.0 + i))?;
            out[i] = b;
        }
        Ok(out)
    }

    /// Reads `C` bytes to RAM using a virtual address
    pub fn write_bytes(&mut self, data: &[u8], virtual_addr: Address) -> Result<(), RAMError> {
        for (i, val) in data.iter().enumerate() {
            self.write_byte(*val, Address(virtual_addr.0 + i))?;
        }
        Ok(())
    }

    /// Translates a 48-bit virtual address into a physical address using a 4-level page table.
    /// - PML4 (Page Map Level 4) - The highest-level table, points to PDPT entries.
    /// - PDPT (Page Directory Pointer Table) - Points to PD entries.
    /// - PD   (Page Directory) - Points to PT entries.
    /// - PT   (Page Table) - Maps virtual pages to physical page frames.
    /// ```text
    /// |--------------------------------------------------------------|
    /// | 000000000 | 000000000 | 000000000 | 000000000 | 000000000000 |
    /// |    PML4   |    PDPT   |    PD     |    PT     |    Offset    |
    /// |--------------------------------------------------------------|
    /// ```
    ///
    /// So, each page needs 1 Page Table Entry (PTE)
    ///
    /// - For a small 8MiB process, total page table memory is ~28KiB
    /// - For a large 1GiB process, total page table memory is ~4MiB
    pub fn translate(&mut self, virtual_addr: Address) -> Result<Address, RAMError> {
        // 1) Extract the offset and the four indexes (for PML4, PDPT, PD, PT).
        let page_offset = virtual_addr.0 & PAGE_OFFSET_MASK; // bits 11..0
        let mut current_table_base = self.pml4_base; // start at PML4

        // We'll do up to 4 levels of lookup.
        // For each level, read the correct entry from the table, check "present" bit, get next base.
        for level in 0..4 {
            let idx_shift = LEVEL_SHIFT[level];
            let idx = (virtual_addr.0 >> idx_shift) & LEVEL_MASK;

            // Each entry is 8 bytes. The address of the entry in the current table:
            let entry_addr = Address(current_table_base.0 + idx * 8);
            let entry_bytes = self.ram.read_bytes::<8>(entry_addr)?;
            let entry_val = Unsigned64::from_le_bytes(entry_bytes);

            // Check present bit (lowest bit). If it's 0, page-fault.
            if (entry_val & 1) == 0 {
                return Err(RAMError::PageFault(virtual_addr));
            }

            // Next level base is stored in bits [51:12].
            // We just mask out the lower 12 bits, leaving the "frame number" in bits [63:12].
            let next_frame = entry_val & 0xFFFF_FFFF_FFFF_F000;

            // If this is the last level, we have the physical frame of the final page.
            // Otherwise, it's the base address of the next-level table.
            if level < 3 {
                // The next table is stored in that physical frame
                current_table_base = Address(next_frame as usize);
            } else {
                // Final level: combine with offset
                let phys = (next_frame | (page_offset as u64)) as usize;
                return Ok(Address(phys));
            }
        }

        // We should never reach here if we have exactly 4 levels,
        // but if we do, return an error or something.
        Err(RAMError::PageFault(virtual_addr))
    }

    /// Set the top-level page table base address (pml4 base) to a new address
    pub fn set_pml4_base(&mut self, physical_address: Address) {
        self.pml4_base = physical_address
    }

    /// Returns true if a virtual address is valid \
    /// In x86-64 architecture, valid address ranges are:
    /// - 0x0000000000000000 - 0x00007FFFFFFFFFFF (low half)
    /// - 0xFFFF800000000000 - 0xFFFFFFFFFFFFFFFF (high half)
    /// Everything else is considered non-canonical and accessing it should trigger a
    /// general protection fault (#GP). \
    ///
    /// The low half is usually used for user processes, like stack, heap, program code and data,
    /// shared libraries, etc. \
    ///
    /// The high half is used for kernel space, like kernel code, kernel data, kernel stack,
    /// page tables, memory-mapped i/o, etc.
    pub fn is_valid_virtual_addr(&self, virtual_addr: Address) -> bool {
        virtual_addr.0 >= 0x0000000000000000 &&     // Lower half start
            virtual_addr.0 <= 0x00007FFFFFFFFFFF || // Lower half end
            virtual_addr.0 >= 0xFFFF800000000000 && // Higher half start
            virtual_addr.0 <= 0xFFFFFFFFFFFFFFFF    // Higher half end
    }
}
