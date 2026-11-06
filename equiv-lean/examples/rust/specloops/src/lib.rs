//! Loop shapes of the Headline A translations, for the Rust spec-proof kit: `for` ranges,
//! counters, a COBOL read loop ended by a flag, and the library calls of display lines.

#[derive(Clone, Copy)]
pub struct Rec {
    pub tag: [u8; 4],
    pub amount: i64,
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub abended: bool,
}

/// `for i in 0..s.len()`: a copy over a range.
pub fn copy_range(s: &[u8]) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    for i in 0..s.len() {
        v.push(s[i]);
    }
    v
}

/// `for _ in 0..n`: `n` spaces (a range up to a bound).
pub fn spaces(n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    for _i in 0..n {
        v.push(b' ');
    }
    v
}

/// `while j < digits && j < 18`: the first `digits` bytes of a buffer (a counter with two bounds).
pub fn take_digits(buf: &[u8; 18], digits: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j < digits && j < 18 {
        out.push(buf[j]);
        j += 1;
    }
    out
}

/// `to_vec` and `extend_from_slice`: a literal label, then a field.
pub fn labelled(b: &[u8; 4]) -> Vec<u8> {
    let mut line = b"ID: ".to_vec();
    line.extend_from_slice(b);
    line
}

/// A COBOL read loop ended by the end-of-file flag: a start line, the tag of each record, an end
/// line; the status of each read decides, and an unexpected status abends.
pub fn listing(recs: &[Rec]) -> Output {
    let mut displays: Vec<Vec<u8>> = Vec::new();
    displays.push(b"START".to_vec());
    let mut pos: usize = 0;
    let mut at_eof = false;
    let mut end_of_file = false;
    while !end_of_file {
        let status: [u8; 2];
        let mut rec: Option<Rec> = None;
        if at_eof {
            status = *b"46";
        } else if pos < recs.len() {
            rec = Some(recs[pos]);
            pos += 1;
            status = *b"00";
        } else {
            at_eof = true;
            status = *b"10";
        }
        if status == *b"10" {
            end_of_file = true;
        } else if status != *b"00" {
            displays.push(b"ERROR".to_vec());
            return Output {
                displays,
                abended: true,
            };
        }
        if !end_of_file {
            if let Some(r) = rec {
                displays.push(r.tag.to_vec());
            }
        }
    }
    displays.push(b"END".to_vec());
    Output {
        displays,
        abended: false,
    }
}
