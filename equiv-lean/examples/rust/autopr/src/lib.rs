//! Pull-request refactorings that change the loop variables of the Aeneas translation (their
//! order, or an extra one); `EquivLean/Demo/Aeneas/AutoCouple.lean` proves each pair equivalent
//! with a generated coupling invariant.  All arithmetic is checked (debug build semantics).

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

    /// Whether `x` occurs in `v`.
    pub fn contains(v: &[u32], x: u32) -> bool {
        let mut i: usize = 0;
        while i < v.len() {
            if v[i] == x {
                return true;
            }
            i += 1;
        }
        false
    }

    /// The largest element, 0 for an empty slice; the element is read into a variable declared
    /// before the loop.
    pub fn max(v: &[u32]) -> u32 {
        let mut x: u32 = 0;
        let mut m: u32 = 0;
        let mut i: usize = 0;
        while i < v.len() {
            x = v[i];
            if x > m {
                m = x;
            }
            i += 1;
        }
        m
    }
}

pub mod v2 {
    /// PR: the index declared first, compound assignments, `!=` as the loop condition.
    pub fn sum(v: &[u32]) -> u32 {
        let mut i: usize = 0;
        let mut s: u32 = 0;
        while i != v.len() {
            s += v[i];
            i += 1;
        }
        s
    }

    /// PR: a flag and `break` instead of the early `return`.
    pub fn contains(v: &[u32], x: u32) -> bool {
        let mut found = false;
        let mut i: usize = 0;
        while i < v.len() {
            if v[i] == x {
                found = true;
                break;
            }
            i += 1;
        }
        found
    }

    /// PR: the element variable declared where it is used.
    pub fn max(v: &[u32]) -> u32 {
        let mut m: u32 = 0;
        let mut i: usize = 0;
        while i < v.len() {
            let x = v[i];
            if x > m {
                m = x;
            }
            i += 1;
        }
        m
    }
}
