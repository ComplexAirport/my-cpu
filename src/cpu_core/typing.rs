//! This file contains Rust wrappers for our CPU data types and
//! helper conversion methods between different data types

/// Represents the Rust wrapper for signed 8-byte integers in our CPU
pub type Signed64 = i64;
/// Represents the Rust wrapper for unsigned 8-byte integers in our CPU
pub type Unsigned64 = u64;
/// Represents the Rust wrapper for floating-point 8-byte numbers in our CPU
pub type Float64 = f64;
/// Represents the Rust wrapper for a single byte in our CPU
pub type SingleByte = u8;

/// Note that both [`RegType`] and [`EightBytes`] have Signed64 value, but the important thing
/// is that they can hold 8 bytes. The bytes may (and are) be reinterpreted as any 8-byte type
/// Represents a holder data type for general-purpose registers (including accumulator) in our CPU
pub type RegType = Signed64;

/// Note that both [`RegType`] and [`EightBytes`] have Signed64 value, but the important thing
/// is that they can hold 8 bytes. The bytes may (and are) be reinterpreted as any 8-byte type
/// Represents a holder data type for general-purpose registers (including accumulator) in our CPU
pub type EightBytes = Signed64;

/// This trait implies that a data type can be
/// - Converted to bytes (little endian)
/// - Constructed from bytes (little endian)
///
///
/// All wrapper data types in our CPU will implement this, so they can always
/// be reinterpreted as other data types. \
/// For example, let's say we want to store a memory address in a general-purpose register. \
/// Maybe the address is `18446744073709551600` (which is [`Unsigned64`]), which has the bytes
/// ```plain
/// [255, 255, 255, 255, 255, 255, 255, 255]
/// ```
/// When we decide to store it in a general-purpose register, its value will become `-1`. \
/// When we try to jump to the address stored in that register, we would need to reinterpret the
/// bytes of `-1` from [`Signed64`] to [`Unsigned64`] to get back the real address value
/// `18446744073709551600`.
pub trait Reinterpret64 {
    /// Returns the value as 8-bytes (little-endian)
    fn to_bytes(&self) -> [u8; 8];

    /// Returns the value as 8-byte (big-endian)
    fn from_bytes(bytes: [u8; 8]) -> Self;

    /// Allows to reinterpret the bytes of underlying data
    /// into as another type \
    /// Refer to [`Reinterpret64`] for more info.
    fn reinterpret<T: Reinterpret64>(&self) -> T { T::from_bytes(self.to_bytes()) }
}

impl Reinterpret64 for Signed64 {
    fn to_bytes(&self) -> [u8; 8] { self.to_le_bytes() }

    fn from_bytes(bytes: [u8; 8]) -> Self { Self::from_le_bytes(bytes) }
}

impl Reinterpret64 for Unsigned64 {
    fn to_bytes(&self) -> [u8; 8] { self.to_le_bytes() }

    fn from_bytes(bytes: [u8; 8]) -> Self { Self::from_le_bytes(bytes) }
}

impl Reinterpret64 for Float64 {
    fn to_bytes(&self) -> [u8; 8] { self.to_le_bytes() }

    fn from_bytes(bytes: [u8; 8]) -> Self { Self::from_le_bytes(bytes) }
}

// Reinterpreting [`SingleByte`] to 8 bytes simply means
// appending 7 `0` bytes to the end of it
// So a byte with value 43 becomes [43, 0, 0, 0, 0, 0, 0, 0]
impl Reinterpret64 for SingleByte {
    fn to_bytes(&self) -> [u8; 8] { [*self, 0, 0, 0, 0, 0, 0, 0] }

    fn from_bytes(bytes: [u8; 8]) -> Self {
        SingleByte::from_le_bytes([bytes[0]]) // Ignore the rest of the bytes
    }
}

// Reinterpreting bool is also necessary in some parts of our CPU code
impl Reinterpret64 for bool {
    fn to_bytes(&self) -> [u8; 8] { [*self as u8, 0, 0, 0, 0, 0, 0, 0] }

    fn from_bytes(bytes: [u8; 8]) -> Self { bytes[0] != 0 }
}


/// This trait implies that
/// - a data type can be checked to be negative, zero, positive, and infinite (with floats)
pub trait SignClassifiable {
    /// Returns `true` if the underlying value is negative, `false` otherwise
    fn is_negative(&self) -> bool;

    /// Returns `true` if the underlying value is positive, `false` otherwise
    fn is_positive(&self) -> bool;

    /// Returns `true` if the underlying value is zero, `false` otherwise
    fn is_zero(&self) -> bool;

    /// Returns `true` if the underlying value is infinite (only floats may be), `false` otherwise
    fn is_infinite(&self) -> bool;
}

impl SignClassifiable for Signed64 {
    fn is_negative(&self) -> bool { Signed64::is_negative(*self) }

    fn is_positive(&self) -> bool { Signed64::is_positive(*self) }

    fn is_zero(&self) -> bool { *self == 0 }

    fn is_infinite(&self) -> bool { false }
}

impl SignClassifiable for Unsigned64 {
    fn is_negative(&self) -> bool { false }

    fn is_positive(&self) -> bool { *self != 0 }

    fn is_zero(&self) -> bool { *self == 0 }

    fn is_infinite(&self) -> bool { false }
}

impl SignClassifiable for Float64 {
    fn is_negative(&self) -> bool { Float64::is_sign_negative(*self) }

    fn is_positive(&self) -> bool { Float64::is_sign_positive(*self) }

    fn is_zero(&self) -> bool { *self == 0f64 }

    fn is_infinite(&self) -> bool { Float64::is_infinite(*self) }
}

impl SignClassifiable for SingleByte {
    fn is_negative(&self) -> bool { false }

    fn is_positive(&self) -> bool { *self != 0 }

    fn is_zero(&self) -> bool { *self == 0 }

    fn is_infinite(&self) -> bool { false }
}

/// This trait implies that
/// - a data type can be converted into bool
pub trait BoolConvertible {
    fn as_bool(&self) -> bool;
}

impl BoolConvertible for Signed64 {
    fn as_bool(&self) -> bool { *self != 0 }
}

impl BoolConvertible for Unsigned64 {
    fn as_bool(&self) -> bool { *self != 0 }
}

impl BoolConvertible for Float64 {
    fn as_bool(&self) -> bool { *self != 0.0 }
}

impl BoolConvertible for SingleByte {
    fn as_bool(&self) -> bool { *self != 0 }
}