//! Three versions of the same function, as a PR history: `v1` is the original, `v2` and `v3`
//! are two refactorings of it.  All arithmetic is checked (debug build semantics): `+` on
//! `u32` panics on overflow.

pub mod v1 {
    /// Sum of a slice; panics if the sum overflows `u32`.
    pub fn sum(v: &[u32]) -> u32 {
        let mut s: u32 = 0;
        let mut i: usize = 0;
        while i < v.len() {
            s = s + v[i];
            i = i + 1;
        }
        s
    }
}

pub mod v2 {
    /// PR 1: loop until `i == len`, read the element once, skip zero entries.
    pub fn sum(v: &[u32]) -> u32 {
        let mut s: u32 = 0;
        let mut i: usize = 0;
        while i != v.len() {
            let x = v[i];
            if x != 0 {
                s += x;
            }
            i += 1;
        }
        s
    }
}

pub mod v3 {
    /// PR 2: saturate instead of panicking on overflow.
    pub fn sum(v: &[u32]) -> u32 {
        let mut s: u32 = 0;
        let mut i: usize = 0;
        while i < v.len() {
            s = s.saturating_add(v[i]);
            i = i + 1;
        }
        s
    }
}

pub mod v4 {
    /// PR 3: unrolled by two (the second element of a pair is guarded).
    pub fn sum(v: &[u32]) -> u32 {
        let mut s: u32 = 0;
        let mut i: usize = 0;
        while i < v.len() {
            s = s + v[i];
            i += 1;
            if i < v.len() {
                s = s + v[i];
                i += 1;
            }
        }
        s
    }
}

pub mod v5 {
    /// A caller of the original sum: twice the sum (panics on overflow).
    pub fn double_sum(v: &[u32]) -> u32 {
        crate::v1::sum(v) * 2
    }
}

pub mod v6 {
    /// The same caller after PR 1 (it calls the refactored `v2::sum`).
    pub fn double_sum(v: &[u32]) -> u32 {
        crate::v2::sum(v) * 2
    }
}
