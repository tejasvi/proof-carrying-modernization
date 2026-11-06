//! Rust side of the C -> Rust struct demo (examples/xlang/point.c).

pub struct Point {
    pub x: i32,
    pub y: i32,
}

/// |x| + |y|; overflow panics (debug semantics, as Aeneas models it).
pub fn manhattan(p: &Point) -> i32 {
    let ax = if p.x < 0 { -p.x } else { p.x };
    let ay = if p.y < 0 { -p.y } else { p.y };
    ax + ay
}
