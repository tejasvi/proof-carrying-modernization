//! `Vec` versions of a PR: building a vector and summing it.

pub mod v1 {
    /// The squares `0, 1, 4, …, (n-1)^2`.
    pub fn squares(n: u32) -> Vec<u64> {
        let mut out = Vec::new();
        let mut i: u32 = 0;
        while i < n {
            out.push((i as u64) * (i as u64));
            i += 1;
        }
        out
    }

    /// Sum of a vector, panics on overflow.
    pub fn sum(v: &Vec<u64>) -> u64 {
        let mut s: u64 = 0;
        let mut i: usize = 0;
        while i < v.len() {
            s = s + v[i];
            i += 1;
        }
        s
    }
}

pub mod v2 {
    /// PR: preallocate, and compute the square by repeated addition (i^2 = (i-1)^2 + 2i - 1).
    pub fn squares(n: u32) -> Vec<u64> {
        let mut out = Vec::with_capacity(n as usize);
        let mut i: u32 = 0;
        let mut sq: u64 = 0;
        while i < n {
            out.push(sq);
            sq = sq + 2 * (i as u64) + 1;
            i += 1;
        }
        out
    }
}
