pub use super::error::RAMError;
pub use super::typing::SingleByte;

/// Stores a RAM address. \
/// For example: `0x00AC20FF`
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct RamAddr(pub usize);

impl RamAddr {
    /// Overflow-safe addition
    pub fn add(&self, rhs: usize) -> Result<Self, RAMError> {
        Ok(Self(
            self.0.checked_add(rhs).ok_or_else(||
                RAMError::AddrAddError(*self, rhs))?
        ))
    }

    /// Overflow-safe subtraction
    pub fn sub(&self, rhs: usize) -> Result<Self, RAMError> {
        Ok(Self(
            self.0.checked_sub(rhs).ok_or_else(||
                RAMError::AddrSubError(*self, rhs))?
        ))
    }

    /// Increment the address (overflow safe)
    pub fn inc(&mut self, rhs: usize) -> Result<(), RAMError> {
        self.0 = self.0.checked_add(rhs)
            .ok_or_else(|| RAMError::AddrAddError(*self, rhs))?;
        Ok(())
    }

    /// Decrement the address (overflow safe)
    pub fn dec(&mut self, rhs: usize) -> Result<(), RAMError> {
        self.0 = self.0.checked_sub(rhs)
            .ok_or_else(|| RAMError::AddrSubError(*self, rhs))?;
        Ok(())
    }

    /// Calculates the absolute value of distance between two RAM addresses
    pub fn distance(&self, rhs: Self) -> usize {
        if rhs.0 > self.0 {
            rhs.0 - self.0
        } else {
            self.0 - rhs.0
        }
    }
}


/// Smallest addressable unit in our `RAM`.
pub type RamUnit = SingleByte;


/// Represents a free memory segment in the RAM.
#[derive(Clone, Debug)]
struct FreeSegment {
    start: RamAddr,
    size: usize,
}

impl FreeSegment {
    pub fn end(&self) -> RamAddr {
        self.start.add(self.size).unwrap()
    }
}



/// RAM with Segment List Allocator
pub struct RAM {
    /// Our actual memory storage.
    pub mem: Box<[RamUnit]>,

    /// List of free segments, sorted by `start` address.
    free_segments: Vec<FreeSegment>,
}


/** `new` method */
impl RAM {
    /// Create a new `RAM` with the entire region free.
    pub fn new(size: usize) -> Self {
        Self {
            mem: vec![0u8; size].into_boxed_slice(),
            // Initially, we have one big free segment spanning the entire memory.
            free_segments: vec![FreeSegment {
                start: RamAddr(0),
                size,
            }],
        }
    }
}


/** RAM methods related to __general__ memory allocating */
impl RAM {
    /// Allocates a contiguous block of `size` bytes **at or after** the specified address
    /// and returns the starting address. In other words, tries to allocate `size` bytes in the
    /// **specified range** - **[`start`; )**
    /// # Errors
    /// - [`RAMError::AllocatingZero`] if tried to allocate 0
    /// - [`RamError:NotEnoughMemory`] if not enough memory for this allocation
    pub fn allocate_at(&mut self, size: usize, start: RamAddr) -> Result<RamAddr, RAMError> {
        if size == 0 {
            // Usually when 0 bytes try to be allocated, it's an error somewhere
            return Err(RAMError::AllocatingZero);
        }

        // Quickly check if the total free size is less than `size`.
        if self.free_size() < size {
            return Err(RAMError::NotEnoughMemory(size, start));
        }

        // Iterate over free segments
        let mut i = 0;
        while i < self.free_segments.len() {
            let seg = &mut self.free_segments[i];
            let seg_start = seg.start;
            let seg_end   = seg.end(); // seg_start + seg.size

            // The earliest point we can allocate in this segment
            let alloc_start = seg_start.max(start);

            // Check if we can fit `size` bytes from `alloc_start`
            // i.e. does [alloc_start, alloc_start + size) fit within [seg_start, seg_end) ?
            if alloc_start.add(size)? <= seg_end {
                // We’ve found a segment that fits the request.
                // Before and after the allocated region, the memory remains free.
                // That means we potentially split into two remainder segments:
                //
                //   [seg_start ... alloc_start)  -- front remainder
                //   [alloc_start ... alloc_start+size) -- allocated area
                //   [alloc_start+size ... seg_end)  -- back remainder
                let front_size = alloc_start.distance(seg_start);
                let back_start = alloc_start.add(size)?;
                let back_size  = seg_end.distance(back_start);
                
                self.free_segments.remove(i);

                // If there is a front remainder, push it.
                if front_size > 0 {
                    self.free_segments.push(FreeSegment {
                        start: seg_start,
                        size: front_size,
                    });
                }

                // If there is a back remainder, push it.
                if back_size > 0 {
                    self.free_segments.push(FreeSegment {
                        start: back_start,
                        size: back_size,
                    });
                }
                
                self.merge_adjacent_segments();

                return Ok(alloc_start);
            }

            // Otherwise, this segment doesn’t have enough capacity at/after `start`.
            i += 1;
        }

        // If we reach here, there was no suitable segment.
        Err(RAMError::NotEnoughMemory(size, start))
    }

    /// Allocates a contiguous block of `size` bytes and returns the starting address.
    /// # Errors
    /// - `RAMError::OutOfMemory(size)` if there's no free segment big enough.
    pub fn allocate(&mut self, size: usize) -> Result<RamAddr, RAMError> {
        // Basically the same as `allocate_at` with `start` = 0
        self.allocate_at(size, RamAddr(0))
    }

    /// Allocate bytes to the memory
    pub fn alloc_bytes<B: AsRef<[SingleByte]>>(&mut self, bytes: B) -> Result<RamAddr, RAMError> {
        let bytes = bytes.as_ref();
        let byte_count = bytes.len();
        let addr = self.allocate(byte_count)?;

        for i in 0..byte_count {
            self.write_byte(RamAddr(addr.0 + i), bytes[i])?;
        }

        Ok(addr)
    }

    /// Frees a previously allocated block of `size` bytes at address `addr`.
    /// # Errors
    /// - `RAMError::InvalidFree(addr, size)` if `[addr .. addr + size)` is out of bounds or invalid.
    pub fn free(&mut self, addr: RamAddr, size: usize) -> Result<(), RAMError> {
        let start = addr;

        if start.0.checked_add(size).unwrap_or(usize::MAX) > self.mem.len() {
            return Err(RAMError::InvalidFree(addr, size));
        }

        let new_segment = FreeSegment { start, size };

        let idx = self
            .free_segments
            .binary_search_by_key(&new_segment.start, |seg| seg.start).unwrap_or_else(|pos| pos);

        self.free_segments.insert(idx, new_segment);
        self.merge_adjacent_segments();
        Ok(())
    }


    /** Private Helpers */
    /// Merge adjacent or overlapping free segments.
    /// We rely on `free_segments` being sorted by `start`.
    fn merge_adjacent_segments(&mut self) {
        if self.free_segments.is_empty() {
            return;
        }

        // We'll merge in a single pass. Because merges can create new merges,
        // we keep going until no more merges occur on that pass.
        let mut i = 0;
        while i < self.free_segments.len() - 1 {
            let curr_start = self.free_segments[i].start;
            let curr_size = self.free_segments[i].size;
            let curr_end = curr_start.add(curr_size).unwrap(); // Cannot panic since it is already in free segments

            let next_start = self.free_segments[i + 1].start;
            let next_size = self.free_segments[i + 1].size;
            let next_end = next_start.add(next_size).unwrap(); // Cannot panic since it is already in free segments

            if next_start <= curr_end {
                // They overlap or are adjacent; merge them
                let merged_start = curr_start.min(next_start);
                let merged_end = curr_end.max(next_end);
                let merged_size = merged_end.0 - merged_start.0;

                self.free_segments[i].start = merged_start;
                self.free_segments[i].size = merged_size;

                // Remove the next segment
                self.free_segments.remove(i + 1);
            } else {
                i += 1;
            }
        }
    }

    /// Write a byte at `addr`, returning an error if out of bounds.
    pub fn write_byte(&mut self, addr: RamAddr, val: SingleByte) -> Result<(), RAMError> {
        if addr.0 < self.mem.len() {
            self.mem[addr.0] = val;
            Ok(())
        } else {
            Err(RAMError::OutOfBounds(addr))
        }
    }
}


/** RAM methods related to general address (segment) inspection/reading */
impl RAM {
    /** Segment Inspection */
    /// Checks if a given range `[addr .. addr + size)` is fully free.
    pub fn is_free(&self, addr: RamAddr, size: usize) -> bool {
        let start = addr;
        let end = start.add(size);
        if end.is_err() { return false; }
        let end = end.unwrap();
        if end.0 > self.mem.len() {
            return false;
        }

        // We only need to see if there's at least one free segment covering `[start, end)`.
        // But a naive approach is to check if we can find a continuous coverage in `free_segments`.
        let mut remaining = size;
        let mut current = start;

        for seg in &self.free_segments {
            if seg.start.add(seg.size).unwrap() < current {
                // Segment is before [current..end)
                continue;
            }
            if seg.start > current {
                // There's a gap between current and seg.start
                return false;
            }

            // If we reached here, seg.start <= current
            let segment_end = seg.start.add(seg.size).unwrap();
            if segment_end >= end {
                // Entire range is covered
                return true;
            }
            // Partial coverage, move current up
            if segment_end > current {
                let covered = segment_end.sub(current.0).unwrap();
                remaining = remaining.saturating_sub(covered.0);
                current = segment_end;
            }
            if remaining == 0 {
                return true;
            }
        }
        false
    }

    /// Returns how many total bytes are free (sum of all `size` in `free_segments`).
    pub fn free_size(&self) -> usize {
        self.free_segments.iter().map(|seg| seg.size).sum()
    }

    /// Returns how many total bytes are allocated (self.mem.len() minus free).
    pub fn used_size(&self) -> usize {
        self.mem.len() - self.free_size()
    }

    /// Returns `true` if `addr` is within our memory bounds.
    pub fn is_valid_addr(&self, addr: RamAddr) -> bool
    {
        addr.0 < self.mem.len()
    }

    /// Get the value at `addr` in RAM, if it is valid.
    pub fn at<T>(&self, addr: T) -> Result<RamUnit, RAMError>
    where
        T: Into<RamAddr>,
    {
        let idx = addr.into();
        if idx.0 < self.mem.len() {
            Ok(self.mem[idx.0])
        } else {
            Err(RAMError::OutOfBounds(idx))
        }
    }

    /// Read the byte at address
    pub fn read_byte(&self, addr: RamAddr) -> Result<RamUnit, RAMError> {
        if addr.0 < self.mem.len() {
            Ok(self.mem[addr.0])
        } else {
            Err(RAMError::OutOfBounds(addr))
        }
    }

    /// Read `N` bytes from the memory and return as an array of `N` elements
    pub fn read_bytes<const N: usize>(&self, start: RamAddr) -> Result<[RamUnit; N], RAMError> {
        if !self.is_free(start, N) {
            let res: [RamUnit; N] = (&self.mem[start.0..start.0 + N])
                .try_into()
                .unwrap();
            Ok(res)
        } else {
            Err(RAMError::InvalidRead(start, N))
        }
    }
}


/** RAM methods related to reading/allocating integers `u8` to `u128` and `i8` to `i128` */
impl RAM {
    /** Unsigned */
    pub fn alloc_u8(&mut self, val: u8) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_u8(&self, start: RamAddr) -> Result<u8, RAMError> {
        Ok(u8::from_le_bytes(self.read_bytes::<1>(start)?))
    }

    pub fn alloc_u16(&mut self, val: u16) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_u16(&self, start: RamAddr) -> Result<u16, RAMError> {
        Ok(u16::from_le_bytes(self.read_bytes::<2>(start)?))
    }

    pub fn alloc_u32(&mut self, val: u32) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_u32(&self, start: RamAddr) -> Result<u32, RAMError> {
        Ok(u32::from_le_bytes(self.read_bytes::<4>(start)?))
    }

    pub fn alloc_u64(&mut self, val: u64) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_u64(&self, start: RamAddr) -> Result<u64, RAMError> {
        Ok(u64::from_le_bytes(self.read_bytes::<8>(start)?))
    }

    pub fn alloc_u128(&mut self, val: u128) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_u128(&self, start: RamAddr) -> Result<u128, RAMError> {
        Ok(u128::from_le_bytes(self.read_bytes::<16>(start)?))
    }

    /** Signed */
    pub fn alloc_i8(&mut self, val: i8) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_i8(&self, start: RamAddr) -> Result<i8, RAMError> {
        Ok(i8::from_le_bytes(self.read_bytes::<1>(start)?))
    }

    pub fn alloc_i16(&mut self, val: i16) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_i16(&self, start: RamAddr) -> Result<i16, RAMError> {
        Ok(i16::from_le_bytes(self.read_bytes::<2>(start)?))
    }

    pub fn alloc_i32(&mut self, val: i32) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_i32(&self, start: RamAddr) -> Result<i32, RAMError> {
        Ok(i32::from_le_bytes(self.read_bytes::<4>(start)?))
    }

    pub fn alloc_i64(&mut self, val: i64) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_i64(&self, start: RamAddr) -> Result<i64, RAMError> {
        Ok(i64::from_le_bytes(self.read_bytes::<8>(start)?))
    }

    pub fn alloc_i128(&mut self, val: i128) -> Result<RamAddr, RAMError> {
        self.alloc_bytes(val.to_le_bytes())
    }

    pub fn read_i128(&self, start: RamAddr) -> Result<i128, RAMError> {
        Ok(i128::from_le_bytes(self.read_bytes::<16>(start)?))
    }
}


/** Conversions & Formatting */
impl<T: Into<usize>> From<T> for RamAddr {
    fn from(value: T) -> Self {
        RamAddr(value.into())
    }
}

impl std::fmt::Debug for RamAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:010x}", self.0)
    }
}
