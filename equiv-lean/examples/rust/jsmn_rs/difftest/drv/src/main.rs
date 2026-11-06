// Differential driver: reads cases (u32 num_tokens, u32 len, len bytes; little endian) and prints, per case,
// jsmn_parse's return value and the first min(max(ret, 0), num_tokens) tokens as type:start:end:size
// (type as the C enum value).
use jsmn_rs::{jsmn_init, jsmn_parse, JsmnTok, JsmnType};
use std::io::Read;

fn code(t: JsmnType) -> i32 {
    match t {
        JsmnType::Undefined => 0,
        JsmnType::Object => 1,
        JsmnType::Array => 2,
        JsmnType::String => 4,
        JsmnType::Primitive => 8,
    }
}

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let mut data = Vec::new();
    std::fs::File::open(path).unwrap().read_to_end(&mut data).unwrap();
    let mut off = 0;
    let rd = |o: usize| u32::from_le_bytes([data[o], data[o + 1], data[o + 2], data[o + 3]]) as usize;
    let mut out = String::new();
    while off + 8 <= data.len() {
        let n = rd(off);
        let len = rd(off + 4);
        let js = &data[off + 8..off + 8 + len];
        off += 8 + len;
        let mut toks = vec![JsmnTok { typ: JsmnType::Undefined, start: 0, end: 0, size: 0 }; n];
        let mut p = jsmn_init();
        let r = jsmn_parse(&mut p, js, &mut toks);
        out.push_str(&format!("{}", r));
        let k = if r < 0 { 0 } else { std::cmp::min(r as usize, n) };
        for t in &toks[..k] {
            out.push_str(&format!(" {}:{}:{}:{}", code(t.typ), t.start, t.end, t.size));
        }
        out.push('\n');
    }
    print!("{}", out);
}
