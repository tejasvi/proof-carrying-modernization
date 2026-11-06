//! TS <-> Rust demo (equiv-lean): a polynomial hash over bytes in `i32` arithmetic
//! (h = 31 * h + byte, wrapping), against the TypeScript `polyHash` of
//! examples/ts/poly_hash.ts (`Math.imul` and `| 0`).

/// The polynomial hash of `data`, wrapping in `i32`.
pub fn poly_hash(data: &[u8]) -> i32 {
    let mut h: i32 = 0;
    let mut i: usize = 0;
    while i < data.len() {
        h = h.wrapping_mul(31).wrapping_add(data[i] as i32);
        i += 1;
    }
    h
}
