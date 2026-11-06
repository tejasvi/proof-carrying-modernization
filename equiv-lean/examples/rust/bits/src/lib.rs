//! Bit-twiddling functions (Rust side of the TypeScript migration demos).

/// FNV-1a, 32 bits, over a byte slice.
pub fn fnv1a32(data: &[u8]) -> u32 {
    let mut h: u32 = 0x811c_9dc5;
    let mut i: usize = 0;
    while i < data.len() {
        h ^= data[i] as u32;
        h = h.wrapping_mul(0x0100_0193);
        i += 1;
    }
    h
}

/// Number of set bits (Kernighan: clear the lowest set bit until zero).
pub fn popcount(x: u32) -> u32 {
    let mut v = x;
    let mut c: u32 = 0;
    while v != 0 {
        v &= v - 1;
        c += 1;
    }
    c
}

/// Number of set bits, branch-free (SWAR).
pub fn popcount_swar(x: u32) -> u32 {
    let mut v = x;
    v = v - ((v >> 1u32) & 0x5555_5555);
    v = (v & 0x3333_3333) + ((v >> 2u32) & 0x3333_3333);
    v = (v + (v >> 4u32)) & 0x0f0f_0f0f;
    v.wrapping_mul(0x0101_0101) >> 24u32
}

/// Reverse the 32 bits of a word.
pub fn reverse_bits(x: u32) -> u32 {
    let mut v = x;
    let mut r: u32 = 0;
    let mut i: u32 = 0;
    while i < 32 {
        r = (r << 1u32) | (v & 1);
        v >>= 1u32;
        i += 1;
    }
    r
}
