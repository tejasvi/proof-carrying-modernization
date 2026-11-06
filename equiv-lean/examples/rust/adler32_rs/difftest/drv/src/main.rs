//! Rust side of the adler32 differential test: `examples/rust/adler32_rs` on the cases of
//! `gen_cases.py`.  usage: adler32_drv CASES.  Prints the same lines as `harness.c`:
//! "<index> <kind> <result as 16 hex digits>".

use std::io::{BufWriter, Write};

fn rd8(d: &[u8], pos: &mut usize) -> u8 {
    let v = d[*pos];
    *pos += 1;
    v
}

fn rd32(d: &[u8], pos: &mut usize) -> u32 {
    let v = u32::from_le_bytes(d[*pos..*pos + 4].try_into().unwrap());
    *pos += 4;
    v
}

fn rd64(d: &[u8], pos: &mut usize) -> u64 {
    let v = u64::from_le_bytes(d[*pos..*pos + 8].try_into().unwrap());
    *pos += 8;
    v
}

fn rdbuf<'a>(d: &'a [u8], pos: &mut usize, is_null: u8, len: usize) -> Option<&'a [u8]> {
    if is_null != 0 {
        None
    } else {
        let b = &d[*pos..*pos + len];
        *pos += len;
        Some(b)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert!(args.len() == 2, "usage: adler32_drv CASES");
    let d = std::fs::read(&args[1]).expect("cannot read the case file");
    assert!(d.len() >= 8 && &d[0..4] == b"ADL1", "bad magic");
    let mut pos = 4usize;
    let count = rd32(&d, &mut pos);
    let out = std::io::stdout();
    let mut w = BufWriter::new(out.lock());
    for i in 0..count {
        let kind = rd8(&d, &mut pos);
        let r = match kind {
            0 => {
                let adler = rd64(&d, &mut pos);
                let is_null = rd8(&d, &mut pos);
                let len = rd64(&d, &mut pos) as usize;
                let buf = rdbuf(&d, &mut pos, is_null, len);
                adler32_rs::adler32_z(adler, buf, len)
            }
            1 => {
                let adler = rd64(&d, &mut pos);
                let is_null = rd8(&d, &mut pos);
                let len = rd32(&d, &mut pos);
                let buf = rdbuf(&d, &mut pos, is_null, len as usize);
                adler32_rs::adler32(adler, buf, len)
            }
            2 | 3 => {
                let a1 = rd64(&d, &mut pos);
                let a2 = rd64(&d, &mut pos);
                let l2 = rd64(&d, &mut pos) as i64;
                if kind == 2 {
                    adler32_rs::adler32_combine(a1, a2, l2)
                } else {
                    adler32_rs::adler32_combine64(a1, a2, l2)
                }
            }
            _ => panic!("bad kind {} at case {}", kind, i),
        };
        writeln!(w, "{} {} {:016x}", i, kind, r).unwrap();
    }
    assert!(pos == d.len(), "trailing bytes in the case file");
}
