/// Macro to define `pub const` values automatically numbered sequentially.
/// This is, for example, used in [`crate::cpu::CPUInstr`],
/// [`crate::cpu::CPUFlag`] and [`crate::cpu::OperandType`]
/// to assign the bytes automatically. \
/// Instead of writing
/// ```rust
/// pub const HALT: u8      = 0;
/// pub const ADD: u8       = 1;
/// pub const SUB: u8       = 2;
/// pub const MUL: u8       = 3;
/// pub const SET: u8       = 4;
/// // ...
/// ```
/// We can write
/// ```rust
/// use my_cpu::define_opcodes;
/// define_opcodes!(
///     HALT,
///     ADD,
///     SUB,
///     MUL,
///     SET,
/// );
/// ```
#[macro_export]
macro_rules! define_opcodes {
    // Entry point: captures all identifier names, starts counting at 0.
    ($($name:ident),* $(,)?) => {
        define_opcodes!(@internal 0; $($name),*);
    };

    // Base case: no more names, just stop.
    (@internal $_count:expr;) => {};

    // Recursive case: define a const for `$first` with the current `$count`,
    // then recurse for the rest with `$count + 1`.
    (@internal $count:expr; $first:ident $(, $rest:ident)*) => {
        pub const $first: u8 = $count;
        define_opcodes!(@internal ($count + 1); $($rest),*);
    };
}
