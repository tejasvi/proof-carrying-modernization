pub const MAX_REGEXP_OBJECTS: usize = 30;
pub const MAX_CHAR_CLASS_LEN: usize = 40;

const UNUSED: u8 = 0;
const DOT: u8 = 1;
const BEGIN: u8 = 2;
const END: u8 = 3;
const QUESTIONMARK: u8 = 4;
const STAR: u8 = 5;
const PLUS: u8 = 6;
const CHAR: u8 = 7;
const CHAR_CLASS: u8 = 8;
const INV_CHAR_CLASS: u8 = 9;
const DIGIT: u8 = 10;
const NOT_DIGIT: u8 = 11;
const ALPHA: u8 = 12;
const NOT_ALPHA: u8 = 13;
const WHITESPACE: u8 = 14;
const NOT_WHITESPACE: u8 = 15;

#[derive(Clone, Copy)]
pub struct RegexObj {
    pub kind: u8,
    pub ch: u8,
    pub ccl: usize,
}

#[derive(Clone, Copy)]
pub struct Regex {
    pub objs: [RegexObj; 30],
    pub ccl_buf: [u8; 40],
}

/* ---------- byte accessors ---------- */

fn at(s: &[u8], i: usize) -> u8 {
    if i < s.len() {
        s[i]
    } else {
        0
    }
}

fn obj(re: &Regex, i: usize) -> RegexObj {
    if i < MAX_REGEXP_OBJECTS {
        re.objs[i]
    } else {
        RegexObj { kind: UNUSED, ch: 0, ccl: 0 }
    }
}

fn cb(re: &Regex, k: usize) -> u8 {
    if k < MAX_CHAR_CLASS_LEN {
        re.ccl_buf[k]
    } else {
        0
    }
}

/* ---------- ctype (glibc, "C" locale, signed char) ---------- */

fn isdigit(c: u8) -> bool {
    c >= b'0' && c <= b'9'
}

fn isalpha(c: u8) -> bool {
    (c >= b'a' && c <= b'z') || (c >= b'A' && c <= b'Z')
}

fn isspace(c: u8) -> bool {
    c == b' ' || (c >= 9 && c <= 13)
}

fn matchalphanum(c: u8) -> bool {
    c == b'_' || isalpha(c) || isdigit(c)
}

fn ismetachar(c: u8) -> bool {
    c == b's' || c == b'S' || c == b'w' || c == b'W' || c == b'd' || c == b'D'
}

fn matchmetachar(c: u8, s: u8) -> bool {
    match s {
        b'd' => isdigit(c),
        b'D' => !isdigit(c),
        b'w' => matchalphanum(c),
        b'W' => !matchalphanum(c),
        b's' => isspace(c),
        b'S' => !isspace(c),
        _ => c == s,
    }
}

fn matchrange(re: &Regex, c: u8, k: usize) -> bool {
    if c == b'-' {
        return false;
    }
    if k >= MAX_CHAR_CLASS_LEN {
        // str[0] would be 0
        return false;
    }
    let s0 = re.ccl_buf[k];
    if s0 == 0 || s0 == b'-' {
        return false;
    }
    let s1 = cb(re, k + 1);
    if s1 != b'-' {
        return false;
    }
    let s2 = cb(re, k + 2);
    if s2 == 0 {
        return false;
    }
    (c as i8) >= (s0 as i8) && (c as i8) <= (s2 as i8)
}

fn matchcharclass(re: &Regex, c: u8, start: usize) -> bool {
    let mut k = start;
    loop {
        if k >= MAX_CHAR_CLASS_LEN {
            // str[0] reads as 0 here; c is never 0, so no branch matches and the loop ends.
            return false;
        }
        let s0 = re.ccl_buf[k];
        if matchrange(re, c, k) {
            return true;
        } else if s0 == b'\\' {
            k += 1;
            let s = cb(re, k);
            if matchmetachar(c, s) {
                return true;
            } else if c == s && !ismetachar(c) {
                return true;
            }
        } else if c == s0 {
            if c == b'-' {
                let prev = if k == 0 { 0 } else { re.ccl_buf[k - 1] };
                let next = cb(re, k + 1);
                return prev == 0 || next == 0;
            } else {
                return true;
            }
        }
        let x = cb(re, k);
        if x == 0 {
            return false;
        }
        k += 1;
    }
}

fn matchone(re: &Regex, p: RegexObj, c: u8) -> bool {
    let k = p.kind;
    if k == DOT {
        true
    } else if k == CHAR_CLASS {
        matchcharclass(re, c, p.ccl)
    } else if k == INV_CHAR_CLASS {
        !matchcharclass(re, c, p.ccl)
    } else if k == DIGIT {
        isdigit(c)
    } else if k == NOT_DIGIT {
        !isdigit(c)
    } else if k == ALPHA {
        matchalphanum(c)
    } else if k == NOT_ALPHA {
        !matchalphanum(c)
    } else if k == WHITESPACE {
        isspace(c)
    } else if k == NOT_WHITESPACE {
        !isspace(c)
    } else {
        // unsigned char u.ch compared with a signed char
        (p.ch as i32) == ((c as i8) as i32)
    }
}

/* forward scan of matchstar / matchplus (not in the recursion group) */
fn scan_fwd(re: &Regex, p: RegexObj, text: &[u8], ti: usize, ml: i32) -> (usize, i32) {
    let mut t = ti;
    let mut m = ml;
    while t < text.len() && at(text, t) != 0 && matchone(re, p, at(text, t)) {
        t += 1;
        m = m.wrapping_add(1);
    }
    (t, m)
}

/* ---------- recursion group (no loops) ---------- */

fn matchpattern(re: &Regex, pi: usize, text: &[u8], ti: usize, ml: i32) -> (bool, i32) {
    matchpattern_loop(re, pi, text, ti, ml, ml)
}

fn matchpattern_loop(
    re: &Regex,
    pi: usize,
    text: &[u8],
    ti: usize,
    ml: i32,
    pre: i32,
) -> (bool, i32) {
    let p0 = obj(re, pi);
    let p1 = obj(re, pi + 1);
    if p0.kind == UNUSED || p1.kind == QUESTIONMARK {
        return matchquestion(re, p0, pi + 2, text, ti, ml);
    }
    if p1.kind == STAR {
        return matchstar(re, p0, pi + 2, text, ti, ml);
    }
    if p1.kind == PLUS {
        return matchplus(re, p0, pi + 2, text, ti, ml);
    }
    if p0.kind == END && p1.kind == UNUSED {
        return (at(text, ti) == 0, ml);
    }
    let ml2 = ml.wrapping_add(1);
    let c = at(text, ti);
    if c != 0 && matchone(re, p0, c) {
        matchpattern_loop(re, pi + 1, text, ti + 1, ml2, pre)
    } else {
        (false, pre)
    }
}

fn matchquestion(
    re: &Regex,
    p: RegexObj,
    pi: usize,
    text: &[u8],
    ti: usize,
    ml: i32,
) -> (bool, i32) {
    if p.kind == UNUSED {
        return (true, ml);
    }
    let (r, ml1) = matchpattern(re, pi, text, ti, ml);
    if r {
        return (true, ml1);
    }
    let c = at(text, ti);
    if c != 0 && matchone(re, p, c) {
        let (r2, ml2) = matchpattern(re, pi, text, ti + 1, ml1);
        if r2 {
            return (true, ml2.wrapping_add(1));
        }
        return (false, ml2);
    }
    (false, ml1)
}

fn matchstar(
    re: &Regex,
    p: RegexObj,
    pi: usize,
    text: &[u8],
    ti: usize,
    ml: i32,
) -> (bool, i32) {
    let prelen = ml;
    let (t, ml1) = scan_fwd(re, p, text, ti, ml);
    star_back(re, pi, text, t as isize, ti as isize, ml1, prelen)
}

fn star_back(
    re: &Regex,
    pi: usize,
    text: &[u8],
    t: isize,
    pre: isize,
    ml: i32,
    prelen: i32,
) -> (bool, i32) {
    if t < pre || t < 0 {
        return (false, prelen);
    }
    let (r, ml1) = matchpattern(re, pi, text, t as usize, ml);
    if r {
        return (true, ml1);
    }
    star_back(re, pi, text, t - 1, pre, ml1.wrapping_sub(1), prelen)
}

fn matchplus(
    re: &Regex,
    p: RegexObj,
    pi: usize,
    text: &[u8],
    ti: usize,
    ml: i32,
) -> (bool, i32) {
    let (t, ml1) = scan_fwd(re, p, text, ti, ml);
    plus_back(re, pi, text, t, ti, ml1)
}

fn plus_back(
    re: &Regex,
    pi: usize,
    text: &[u8],
    t: usize,
    pre: usize,
    ml: i32,
) -> (bool, i32) {
    if t <= pre {
        return (false, ml);
    }
    let (r, ml1) = matchpattern(re, pi, text, t, ml);
    if r {
        return (true, ml1);
    }
    plus_back(re, pi, text, t - 1, pre, ml1.wrapping_sub(1))
}

/* ---------- public API ---------- */

pub fn re_match(pattern: &[u8], text: &[u8]) -> (i32, i32) {
    let r = re_compile(pattern);
    match &r {
        Some(x) => re_matchp(Some(x), text),
        None => re_matchp(None, text),
    }
}

pub fn re_matchp(pattern: Option<&Regex>, text: &[u8]) -> (i32, i32) {
    match pattern {
        None => (-1, 0),
        Some(re) => {
            if obj(re, 0).kind == BEGIN {
                let (r, ml) = matchpattern(re, 1, text, 0, 0);
                return (if r { 0 } else { -1 }, ml);
            }
            let mut idx: i32 = -1;
            let mut ti: usize = 0;
            let mut ml: i32 = 0;
            loop {
                idx = idx.wrapping_add(1);
                let (r, ml1) = matchpattern(re, 0, text, ti, ml);
                ml = ml1;
                if r {
                    if at(text, ti) == 0 {
                        return (-1, ml);
                    }
                    return (idx, ml);
                }
                if at(text, ti) == 0 {
                    break;
                }
                if ti >= text.len() {
                    break;
                }
                ti += 1;
            }
            (-1, ml)
        }
    }
}

/* copies the characters inside [..]; None = C's `return 0` */
fn compile_class(
    pattern: &[u8],
    i0: usize,
    b0: usize,
    buf: &mut [u8; MAX_CHAR_CLASS_LEN],
) -> Option<(usize, usize)> {
    let mut i = i0;
    let mut b = b0;
    loop {
        if i >= pattern.len() {
            // pattern[++i] would be past the NUL; C never gets here (the NUL stops the scan)
            break;
        }
        i += 1;
        let pc = at(pattern, i);
        if pc == b']' || pc == 0 {
            break;
        }
        if pc == b'\\' {
            if b >= MAX_CHAR_CLASS_LEN - 1 {
                return None;
            }
            if at(pattern, i + 1) == 0 {
                return None;
            }
            buf[b] = pc;
            b += 1;
            i += 1;
        } else if b >= MAX_CHAR_CLASS_LEN {
            return None;
        }
        buf[b] = at(pattern, i);
        b += 1;
    }
    if b >= MAX_CHAR_CLASS_LEN {
        return None;
    }
    buf[b] = 0;
    b += 1;
    Some((i, b))
}

pub fn re_compile(pattern: &[u8]) -> Option<Regex> {
    let mut re = Regex {
        objs: [RegexObj { kind: 0, ch: 0, ccl: 0 }; MAX_REGEXP_OBJECTS],
        ccl_buf: [0u8; MAX_CHAR_CLASS_LEN],
    };
    let mut bufidx: usize = 1;
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < pattern.len() && at(pattern, i) != 0 && j + 1 < MAX_REGEXP_OBJECTS {
        let c = at(pattern, i);
        let mut o = re.objs[j];
        match c {
            b'^' => {
                o.kind = BEGIN;
            }
            b'$' => {
                o.kind = END;
            }
            b'.' => {
                o.kind = DOT;
            }
            b'*' => {
                o.kind = STAR;
            }
            b'+' => {
                o.kind = PLUS;
            }
            b'?' => {
                o.kind = QUESTIONMARK;
            }
            b'\\' => {
                if at(pattern, i + 1) != 0 {
                    i += 1;
                    let e = at(pattern, i);
                    match e {
                        b'd' => {
                            o.kind = DIGIT;
                        }
                        b'D' => {
                            o.kind = NOT_DIGIT;
                        }
                        b'w' => {
                            o.kind = ALPHA;
                        }
                        b'W' => {
                            o.kind = NOT_ALPHA;
                        }
                        b's' => {
                            o.kind = WHITESPACE;
                        }
                        b'S' => {
                            o.kind = NOT_WHITESPACE;
                        }
                        _ => {
                            o.kind = CHAR;
                            o.ch = e;
                        }
                    }
                }
            }
            b'[' => {
                let buf_begin = bufidx;
                if at(pattern, i + 1) == b'^' {
                    o.kind = INV_CHAR_CLASS;
                    i += 1;
                    if at(pattern, i + 1) == 0 {
                        return None;
                    }
                } else {
                    o.kind = CHAR_CLASS;
                }
                match compile_class(pattern, i, bufidx, &mut re.ccl_buf) {
                    None => return None,
                    Some((i2, b2)) => {
                        i = i2;
                        bufidx = b2;
                    }
                }
                o.ccl = buf_begin;
            }
            _ => {
                o.kind = CHAR;
                o.ch = c;
            }
        }
        re.objs[j] = o;
        if at(pattern, i) == 0 {
            return None;
        }
        i += 1;
        j += 1;
    }
    let mut o = re.objs[j];
    o.kind = UNUSED;
    re.objs[j] = o;
    Some(re)
}