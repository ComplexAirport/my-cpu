//! This file contains interfaces for our simulated RAM \
//! This includes:
//! - [`RAM`] - Main RAM interface
//! - [`RamAddr`] - Represents RAM addresses

use super::error::RAMError;
use super::typing::SingleByte;


/// Stores a RAM address. \
/// For example: `0x00AC20FF`
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct RamAddr(pub usize);

impl RamAddr {
    /// Overflow-safe addition
    pub fn add(&self, rhs: usize) -> Result<Self, RAMError> {
        Ok(Self(
            self.0.checked_add(rhs).ok_or_else(||
                RAMError::AddressOverflow(*self))?
        ))
    }

    /// Overflow-safe subtraction
    pub fn sub(&self, rhs: usize) -> Result<Self, RAMError> {
        Ok(Self(
            self.0.checked_sub(rhs).ok_or_else(||
                RAMError::AddressOverflow(*self))?
        ))
    }

    /// Increment the address (overflow safe)
    pub fn inc(&mut self, rhs: usize) -> Result<(), RAMError> {
        self.0 = self.0.checked_add(rhs)
            .ok_or_else(|| RAMError::AddressOverflow(*self))?;
        Ok(())
    }

    /// Decrement the address (overflow safe)
    pub fn dec(&mut self, rhs: usize) -> Result<(), RAMError> {
        self.0 = self.0.checked_sub(rhs)
            .ok_or_else(|| RAMError::AddressOverflow(*self))?;
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


/// Represents our simulated RAM interface
pub struct RAM {
    /// Our actual memory storage.
    pub mem: Box<[SingleByte]>,
}

impl RAM {
    pub fn with_size(size: usize) -> Self {
        Self {
            mem: vec![0u8; size].into_boxed_slice(),
        }
    }

    /// Write a single byte to specified RAM address
    pub fn write_byte(&mut self, byte: SingleByte, addr: RamAddr) -> Result<(), RAMError> {
        if self.is_valid_addr(addr) {
            self.mem[addr.0] = byte;
            Ok(())
        } else {
            Err(RAMError::BadWrite(addr))
        }
    }

    /// Write many bytes to specified RAM address
    pub fn write_bytes(&mut self, bytes: &[SingleByte], addr: RamAddr) -> Result<(), RAMError> {
        for (idx, byte) in bytes.iter().enumerate() {
            self.write_byte(*byte, addr.add(idx)?)?;
        }
        Ok(())
    }

    /// Read a single byte from a specified RAM address
    pub fn read_byte(&self, addr: RamAddr) -> Result<SingleByte, RAMError> {
        if self.is_valid_addr(addr) {
            Ok(self.mem[addr.0])
        } else {
            Err(RAMError::BadRead(addr))
        }
    }

    /// Read many bytes from a specified RAM address
    /// `C` represents amount of bytes to read
    pub fn read_bytes<const C: usize>(&self, addr: RamAddr) -> Result<[SingleByte; C], RAMError> {
        let mut result: [SingleByte; C] = [SingleByte::default(); C];
        for idx in 0..C {
            result[idx] = self.read_byte(addr.add(idx)?)?;
        }

        Ok(result)
    }

    /// Checks if an address falls inside our RAM
    pub fn is_valid_addr(&self, addr: RamAddr) -> bool {
        addr.0 < self.size()
    }

    /// Returns the last valid address that falls inside our RAM
    pub fn last_addr(&self) -> RamAddr { RamAddr(self.size() - 1) }

    /// Returns the size of our RAM in bytes
    pub fn size(&self) -> usize { self.mem.len() }
}


/** Conversions & Formatting */
impl std::fmt::Debug for RamAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:010x}", self.0)
    }
}
