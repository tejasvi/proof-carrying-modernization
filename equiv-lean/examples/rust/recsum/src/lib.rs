//! Rust rewrite of RECSUM.cob: one output record `(id, running total)` per input record
//! `(id, amount)`, amounts and totals in cents (scale 2).

pub fn recsum(recs: &[(u32, i64)]) -> Vec<(u32, i64)> {
    let mut out = Vec::new();
    let mut total: i64 = 0;
    let mut i = 0;
    while i < recs.len() {
        let (id, amt) = recs[i];
        total += amt;
        out.push((id, total));
        i += 1;
    }
    out
}
