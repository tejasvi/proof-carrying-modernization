//! The midpoint overflow fix, loop-free.

pub mod v1 {
    /// Average of two `u32`, rounded down; panics when `a + b` overflows.
    pub fn mid(a: u32, b: u32) -> u32 {
        (a + b) / 2
    }
}

pub mod v2 {
    /// PR: never overflows.
    pub fn mid(a: u32, b: u32) -> u32 {
        a / 2 + b / 2 + (a % 2 + b % 2) / 2
    }
}
