//! A search loop before and after an "early return" refactoring.

pub mod v1 {
    /// Index of the first occurrence of `x` in `v`, or `v.len()`.
    pub fn find(v: &[u32], x: u32) -> usize {
        let mut i: usize = 0;
        while i < v.len() && v[i] != x {
            i += 1;
        }
        i
    }
}

pub mod v2 {
    /// PR: return from inside the loop.
    pub fn find(v: &[u32], x: u32) -> usize {
        let mut i: usize = 0;
        while i < v.len() {
            if v[i] == x {
                return i;
            }
            i += 1;
        }
        v.len()
    }
}
