//! jsmn (zserge/jsmn @ 25647e6, `jsmn.h`), default configuration (neither `JSMN_PARENT_LINKS` nor
//! `JSMN_STRICT`), in safe Rust: written by equiv-lean's agents in an Aeneas-friendly form (no
//! `unsafe`; loops as `while` with state, no `return` inside a loop; the token array as a slice).
//! The source length is `js.len()` and the token capacity `tokens.len()`; positions and the token
//! counter are `usize` (C: `unsigned int`), token fields and `toksuper` are `i32` (C: `int`).
//! Only the mode with a token array (C: `tokens != NULL`) is translated.

/// Not enough tokens were provided.
pub const JSMN_ERROR_NOMEM: i32 = -1;
/// Invalid character inside JSON string.
pub const JSMN_ERROR_INVAL: i32 = -2;
/// The string is not a full JSON packet, more bytes expected.
pub const JSMN_ERROR_PART: i32 = -3;

/// `jsmntype_t` (C values 0, 1, 2, 4, 8).
#[derive(Clone, Copy)]
pub enum JsmnType {
    Undefined,
    Object,
    Array,
    String,
    Primitive,
}

/// `jsmntok_t`.
#[derive(Clone, Copy)]
pub struct JsmnTok {
    pub typ: JsmnType,
    pub start: i32,
    pub end: i32,
    pub size: i32,
}

/// `jsmn_parser`.
pub struct JsmnParser {
    pub pos: usize,
    pub toknext: usize,
    pub toksuper: i32,
}

/// `jsmn_init`.
pub fn jsmn_init() -> JsmnParser {
    JsmnParser { pos: 0, toknext: 0, toksuper: -1 }
}

/// A container token (object or array).
fn is_container(t: JsmnType) -> bool {
    match t {
        JsmnType::Object => true,
        JsmnType::Array => true,
        _ => false,
    }
}

/// `token->type == type` for the type of a closing bracket (`}`: object, `]`: array).
fn type_is(t: JsmnType, object: bool) -> bool {
    match t {
        JsmnType::Object => object,
        JsmnType::Array => !object,
        _ => false,
    }
}

/// `jsmn_alloc_token`: the index of the next free token, or `None` when the array is full.
fn alloc_token(parser: &mut JsmnParser, tokens: &mut [JsmnTok]) -> Option<usize> {
    if parser.toknext >= tokens.len() {
        return None;
    }
    let i = parser.toknext;
    parser.toknext += 1;
    tokens[i].start = -1;
    tokens[i].end = -1;
    tokens[i].size = 0;
    Some(i)
}

/// `jsmn_fill_token`.
fn fill_token(token: &mut JsmnTok, typ: JsmnType, start: i32, end: i32) {
    token.typ = typ;
    token.start = start;
    token.end = end;
    token.size = 0;
}

/// `jsmn_parse_primitive` (non-strict: a primitive ends at `:`, whitespace, `,`, `]`, `}`, the end
/// of the input or a NUL byte).
fn parse_primitive(parser: &mut JsmnParser, js: &[u8], tokens: &mut [JsmnTok]) -> i32 {
    let len = js.len();
    let start = parser.pos;
    let mut found = false;
    let mut inval = false;
    while !found && !inval && parser.pos < len && js[parser.pos] != 0 {
        let c = js[parser.pos];
        if c == b':' || c == b'\t' || c == b'\r' || c == b'\n' || c == b' ' || c == b',' || c == b']'
            || c == b'}'
        {
            found = true;
        } else if c < 32 || c >= 127 {
            inval = true;
        } else {
            parser.pos += 1;
        }
    }
    if inval {
        parser.pos = start;
        return JSMN_ERROR_INVAL;
    }
    match alloc_token(parser, tokens) {
        None => {
            parser.pos = start;
            JSMN_ERROR_NOMEM
        }
        Some(i) => {
            fill_token(&mut tokens[i], JsmnType::Primitive, start as i32, parser.pos as i32);
            parser.pos -= 1;
            0
        }
    }
}

/// A hexadecimal digit `0-9`, `A-F`, `a-f`.
fn is_hex(h: u8) -> bool {
    (h >= 48 && h <= 57) || (h >= 65 && h <= 70) || (h >= 97 && h <= 102)
}

/// One of the escaped symbols `"`, `/`, `\`, `b`, `f`, `r`, `n`, `t`.
fn is_simple_escape(e: u8) -> bool {
    e == b'"' || e == b'/' || e == b'\\' || e == b'b' || e == b'f' || e == b'r' || e == b'n' || e == b't'
}

/// `jsmn_parse_string` (`parser.pos` at the opening quote).
fn parse_string(parser: &mut JsmnParser, js: &[u8], tokens: &mut [JsmnTok]) -> i32 {
    let len = js.len();
    let start = parser.pos;
    parser.pos += 1;
    let mut res = JSMN_ERROR_PART;
    let mut done = false;
    while !done && parser.pos < len && js[parser.pos] != 0 {
        let c = js[parser.pos];
        if c == b'"' {
            match alloc_token(parser, tokens) {
                None => {
                    parser.pos = start;
                    res = JSMN_ERROR_NOMEM;
                }
                Some(i) => {
                    fill_token(&mut tokens[i], JsmnType::String, start as i32 + 1, parser.pos as i32);
                    res = 0;
                }
            }
            done = true;
        } else if c == b'\\' && parser.pos + 1 < len {
            parser.pos += 1;
            let e = js[parser.pos];
            if is_simple_escape(e) {
                parser.pos += 1;
            } else if e == b'u' {
                parser.pos += 1;
                let mut i = 0;
                let mut bad = false;
                while !bad && i < 4 && parser.pos < len && js[parser.pos] != 0 {
                    if is_hex(js[parser.pos]) {
                        parser.pos += 1;
                        i += 1;
                    } else {
                        bad = true;
                    }
                }
                if bad {
                    parser.pos = start;
                    res = JSMN_ERROR_INVAL;
                    done = true;
                }
            } else {
                parser.pos = start;
                res = JSMN_ERROR_INVAL;
                done = true;
            }
        } else {
            parser.pos += 1;
        }
    }
    if !done {
        parser.pos = start;
    }
    res
}

/// The innermost open token (`start != -1`, `end == -1`) at index `i` or below, or `-1`.
fn find_open(tokens: &[JsmnTok], i0: i32) -> i32 {
    let mut i = i0;
    let mut found = false;
    while !found && i >= 0 {
        let t = tokens[i as usize];
        if t.start != -1 && t.end == -1 {
            found = true;
        } else {
            i -= 1;
        }
    }
    i
}

/// The innermost open object or array at index `i` or below, or `-1`.
fn find_open_container(tokens: &[JsmnTok], i0: i32) -> i32 {
    let mut i = i0;
    let mut found = false;
    while !found && i >= 0 {
        let t = tokens[i as usize];
        if is_container(t.typ) && t.start != -1 && t.end == -1 {
            found = true;
        } else {
            i -= 1;
        }
    }
    i
}

/// `jsmn_parse` with a token array: the number of tokens, or `JSMN_ERROR_NOMEM`,
/// `JSMN_ERROR_INVAL`, `JSMN_ERROR_PART`.
pub fn jsmn_parse(parser: &mut JsmnParser, js: &[u8], tokens: &mut [JsmnTok]) -> i32 {
    let len = js.len();
    let mut count = parser.toknext as i32;
    let mut ret = 0;
    let mut stop = false;
    while !stop && parser.pos < len && js[parser.pos] != 0 {
        let c = js[parser.pos];
        if c == b'{' || c == b'[' {
            count += 1;
            match alloc_token(parser, tokens) {
                None => {
                    ret = JSMN_ERROR_NOMEM;
                    stop = true;
                }
                Some(i) => {
                    if parser.toksuper != -1 {
                        tokens[parser.toksuper as usize].size += 1;
                    }
                    tokens[i].typ = if c == b'{' { JsmnType::Object } else { JsmnType::Array };
                    tokens[i].start = parser.pos as i32;
                    parser.toksuper = parser.toknext as i32 - 1;
                }
            }
        } else if c == b'}' || c == b']' {
            let object = c == b'}';
            let i = find_open(tokens, parser.toknext as i32 - 1);
            if i == -1 {
                ret = JSMN_ERROR_INVAL;
                stop = true;
            } else if !type_is(tokens[i as usize].typ, object) {
                ret = JSMN_ERROR_INVAL;
                stop = true;
            } else {
                parser.toksuper = -1;
                tokens[i as usize].end = parser.pos as i32 + 1;
                let j = find_open(tokens, i);
                if j != -1 {
                    parser.toksuper = j;
                }
            }
        } else if c == b'"' {
            let r = parse_string(parser, js, tokens);
            if r < 0 {
                ret = r;
                stop = true;
            } else {
                count += 1;
                if parser.toksuper != -1 {
                    tokens[parser.toksuper as usize].size += 1;
                }
            }
        } else if c == b'\t' || c == b'\r' || c == b'\n' || c == b' ' {
        } else if c == b':' {
            parser.toksuper = parser.toknext as i32 - 1;
        } else if c == b',' {
            if parser.toksuper != -1 && !is_container(tokens[parser.toksuper as usize].typ) {
                let i = find_open_container(tokens, parser.toknext as i32 - 1);
                if i != -1 {
                    parser.toksuper = i;
                }
            }
        } else {
            let r = parse_primitive(parser, js, tokens);
            if r < 0 {
                ret = r;
                stop = true;
            } else {
                count += 1;
                if parser.toksuper != -1 {
                    tokens[parser.toksuper as usize].size += 1;
                }
            }
        }
        if !stop {
            parser.pos += 1;
        }
    }
    if stop {
        return ret;
    }
    if find_open(tokens, parser.toknext as i32 - 1) != -1 {
        return JSMN_ERROR_PART;
    }
    count
}
