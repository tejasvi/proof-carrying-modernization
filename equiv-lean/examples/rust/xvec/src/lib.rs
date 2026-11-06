//! Rust side of the C++ -> Rust collections migration demo (Demo/XLang/VecSum.lean):
//! `int vsum(const std::vector<int>& v)` of examples/xlang/vec.cpp, rewritten over `Vec<i32>`.

/// Sum of the elements; `+=` is checked (panics on `i32` overflow, where C++ has UB).
pub fn vsum(v: &Vec<i32>) -> i32 {
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < v.len() {
        s += v[i];
        i += 1;
    }
    s
}
