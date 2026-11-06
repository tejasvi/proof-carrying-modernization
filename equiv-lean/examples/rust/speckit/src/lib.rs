//! Test cases for the Rust spec-proof kit: loops over record slices that build output Vecs.

#[derive(Clone, Copy)]
pub struct Rec {
    pub id: u32,
    pub amount: u32,
}

#[derive(Clone, Copy)]
pub struct Line {
    pub key: u32,
    pub val: u32,
}

/// (a) One output line per record.
pub fn map_lines(recs: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut i: usize = 0;
    while i < recs.len() {
        let r = recs[i];
        out.push(Line { key: r.id, val: r.amount });
        i += 1;
    }
    out
}

/// (a') A header line, one line per record, a trailer line.
pub fn framed(recs: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    out.push(Line { key: 0, val: 0 });
    let mut i: usize = 0;
    while i < recs.len() {
        out.push(Line { key: recs[i].id, val: recs[i].amount });
        i += 1;
    }
    out.push(Line { key: 1, val: 1 });
    out
}

/// (b) Lines for the records with a nonzero amount.
pub fn filter_lines(recs: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut i: usize = 0;
    while i < recs.len() {
        let r = recs[i];
        if r.amount != 0 {
            out.push(Line { key: r.id, val: r.amount });
        }
        i += 1;
    }
    out
}

/// (c) The records with a nonzero amount, then a final line with their count.
pub fn count_lines(recs: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut n: u32 = 0;
    let mut i: usize = 0;
    while i < recs.len() {
        let r = recs[i];
        if r.amount != 0 {
            out.push(Line { key: r.id, val: r.amount });
            n += 1;
        }
        i += 1;
    }
    out.push(Line { key: 9, val: n });
    out
}

/// (c') A wrapping running total in a final line.
pub fn total_line(recs: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut total: u32 = 0;
    let mut i: usize = 0;
    while i < recs.len() {
        total = total.wrapping_add(recs[i].amount);
        out.push(Line { key: recs[i].id, val: total });
        i += 1;
    }
    out.push(Line { key: 9, val: total });
    out
}

/// (d) Two outputs: a line per record, and the records with a nonzero amount; and a return code.
pub fn two_outputs(recs: &[Rec]) -> (Vec<Line>, Vec<Rec>, u32) {
    let mut lines: Vec<Line> = Vec::new();
    let mut written: Vec<Rec> = Vec::new();
    let mut i: usize = 0;
    while i < recs.len() {
        let r = recs[i];
        lines.push(Line { key: r.id, val: r.amount });
        if r.amount != 0 {
            written.push(r);
        }
        i += 1;
    }
    (lines, written, 0)
}

/// (e) The amount of the first record of `tbl` with key `key`, or 0 (linear search).
pub fn lookup(tbl: &[Rec], key: u32) -> u32 {
    let mut j: usize = 0;
    while j < tbl.len() {
        if tbl[j].id == key {
            return tbl[j].amount;
        }
        j += 1;
    }
    0
}

/// (e) For each record, its id and the amount found in `tbl` under its id.
pub fn joined(recs: &[Rec], tbl: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut i: usize = 0;
    while i < recs.len() {
        let v = lookup(tbl, recs[i].id);
        out.push(Line { key: recs[i].id, val: v });
        i += 1;
    }
    out
}

/// (f) Two loops in sequence: the lines of `a`, then the lines of `b`.
pub fn two_loops(a: &[Rec], b: &[Rec]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        out.push(Line { key: a[i].id, val: a[i].amount });
        i += 1;
    }
    let mut j: usize = 0;
    while j < b.len() {
        out.push(Line { key: b[j].id, val: b[j].amount });
        j += 1;
    }
    out
}

/// (g) A return code: 4 if some record has a zero amount, else 0; and the lines.
pub fn with_rc(recs: &[Rec]) -> (Vec<Line>, u32) {
    let mut out: Vec<Line> = Vec::new();
    let mut bad: bool = false;
    let mut i: usize = 0;
    while i < recs.len() {
        if recs[i].amount == 0 {
            bad = true;
        } else {
            out.push(Line { key: recs[i].id, val: recs[i].amount });
        }
        i += 1;
    }
    let rc: u32 = if bad { 4 } else { 0 };
    (out, rc)
}

/// (h) A CBACT02C-shaped program: a card record, displayed field by field.
#[derive(Clone, Copy)]
pub struct CardRecord {
    pub card_num: [u8; 16],
    pub card_acct_id: i64,
    pub card_cvv_cd: i64,
    pub filler1: [u8; 59],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub abended: bool,
}

/// The `n` low decimal digits of `v` (0 for a negative `v`), zero-padded, as Latin-1 bytes
/// (`n <= 19`).
pub fn zero_pad(v: i64, n: usize) -> Vec<u8> {
    let x: u64 = if v < 0 { 0 } else { v as u64 };
    let mut p: u64 = 1;
    let mut k: usize = 0;
    while k < n {
        p = p * 10;
        k += 1;
    }
    let mut out: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        p = p / 10;
        let d = (x / p) % 10;
        out.push(b'0' + (d as u8));
        j += 1;
    }
    out
}

/// Appends the bytes of a field.
pub fn push_bytes(line: &mut Vec<u8>, b: &[u8]) {
    let mut j: usize = 0;
    while j < b.len() {
        line.push(b[j]);
        j += 1;
    }
}

/// The display line of a card record: its fields in order.
pub fn card_line(c: &CardRecord) -> Vec<u8> {
    let mut line: Vec<u8> = Vec::new();
    push_bytes(&mut line, &c.card_num);
    let a = zero_pad(c.card_acct_id, 11);
    push_bytes(&mut line, &a);
    let v = zero_pad(c.card_cvv_cd, 3);
    push_bytes(&mut line, &v);
    push_bytes(&mut line, &c.filler1);
    line
}

/// A start line, one line per card record, an end line.
pub fn run(cards: &[CardRecord]) -> Output {
    let mut displays: Vec<Vec<u8>> = Vec::new();
    let mut start: Vec<u8> = Vec::new();
    start.push(b'S');
    start.push(b'T');
    displays.push(start);
    let mut i: usize = 0;
    while i < cards.len() {
        displays.push(card_line(&cards[i]));
        i += 1;
    }
    let mut end: Vec<u8> = Vec::new();
    end.push(b'E');
    end.push(b'N');
    displays.push(end);
    Output { displays, abended: false }
}
