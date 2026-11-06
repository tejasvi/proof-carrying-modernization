// Translation of CBSTM03A (with its subroutine CBSTM03B as private helpers).

#[derive(Clone, Copy)]
pub struct TrnxRecord {
    pub trnx_card_num: [u8; 16],
    pub trnx_id: [u8; 16],
    pub trnx_type_cd: [u8; 2],
    pub trnx_cat_cd: i64,
    pub trnx_source: [u8; 10],
    pub trnx_desc: [u8; 100],
    pub trnx_amt: i64,
    pub trnx_merchant_id: i64,
    pub trnx_merchant_name: [u8; 50],
    pub trnx_merchant_city: [u8; 50],
    pub trnx_merchant_zip: [u8; 10],
    pub trnx_orig_ts: [u8; 26],
    pub trnx_proc_ts: [u8; 26],
    pub filler1: [u8; 20],
}

#[derive(Clone, Copy)]
pub struct CardXrefRecord {
    pub xref_card_num: [u8; 16],
    pub xref_cust_id: i64,
    pub xref_acct_id: i64,
    pub filler1: [u8; 14],
}

#[derive(Clone, Copy)]
pub struct CustomerRecord {
    pub cust_id: i64,
    pub cust_first_name: [u8; 25],
    pub cust_middle_name: [u8; 25],
    pub cust_last_name: [u8; 25],
    pub cust_addr_line_1: [u8; 50],
    pub cust_addr_line_2: [u8; 50],
    pub cust_addr_line_3: [u8; 50],
    pub cust_addr_state_cd: [u8; 2],
    pub cust_addr_country_cd: [u8; 3],
    pub cust_addr_zip: [u8; 10],
    pub cust_phone_num_1: [u8; 15],
    pub cust_phone_num_2: [u8; 15],
    pub cust_ssn: i64,
    pub cust_govt_issued_id: [u8; 20],
    pub cust_dob_yyyymmdd: [u8; 10],
    pub cust_eft_account_id: [u8; 10],
    pub cust_pri_card_holder_ind: [u8; 1],
    pub cust_fico_credit_score: i64,
    pub filler1: [u8; 168],
}

#[derive(Clone, Copy)]
pub struct AccountRecord {
    pub acct_id: i64,
    pub acct_active_status: [u8; 1],
    pub acct_curr_bal: i64,
    pub acct_credit_limit: i64,
    pub acct_cash_credit_limit: i64,
    pub acct_open_date: [u8; 10],
    pub acct_expiraion_date: [u8; 10],
    pub acct_reissue_date: [u8; 10],
    pub acct_curr_cyc_credit: i64,
    pub acct_curr_cyc_debit: i64,
    pub acct_addr_zip: [u8; 10],
    pub acct_group_id: [u8; 10],
    pub filler1: [u8; 178],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub stmt_file_writes: Vec<Vec<u8>>,
    pub html_file_writes: Vec<Vec<u8>>,
    pub abended: bool,
}

struct Ctx {
    displays: Vec<Vec<u8>>,
    stmt: Vec<Vec<u8>>,
    html: Vec<Vec<u8>>,
    abended: bool,
    // CBSTM03B state
    trnx_pos: usize,
    trnx_eof: bool,
    trnx_status: [u8; 2],
    xref_pos: usize,
    xref_eof: bool,
    xref_status: [u8; 2],
    cust_status: [u8; 2],
    acct_status: [u8; 2],
    // WS-M03B-AREA
    m_dd: [u8; 8],
    m_oper: u8,
    m_rc: [u8; 2],
    m_key: [u8; 25],
    m_key_ln: i64,
    m_fldt: [u8; 1000],
}

struct St {
    name: [u8; 75],
    add1: [u8; 50],
    add2: [u8; 50],
    add3: [u8; 80],
    acct_id: [u8; 20],
    curr_bal: [u8; 13],
    fico: [u8; 20],
    tranid: [u8; 16],
    trandt: [u8; 49],
    tranamt: [u8; 13],
    total_tramt: [u8; 13],
}

// sparse model of WS-TRNX-TABLE / WS-TRN-TBL-CNTR storage (flat byte log)
struct Mem {
    offs: Vec<i64>,
    starts: Vec<usize>,
    lens: Vec<usize>,
    bytes: Vec<u8>,
}

const CARD_SZ: i64 = 3356;
const TRAN_SZ: i64 = 334;
const TABLE_SZ: i64 = 171156;
const CNTR_BASE: i64 = 171160;

// EBCDIC (CP037) byte -> Latin-1 code point
const EBC2LAT: [u8; 256] = [
    0x00, 0x01, 0x02, 0x03, 0x9C, 0x09, 0x86, 0x7F, 0x97, 0x8D, 0x8E, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
    0x10, 0x11, 0x12, 0x13, 0x9D, 0x85, 0x08, 0x87, 0x18, 0x19, 0x92, 0x8F, 0x1C, 0x1D, 0x1E, 0x1F,
    0x80, 0x81, 0x82, 0x83, 0x84, 0x0A, 0x17, 0x1B, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x05, 0x06, 0x07,
    0x90, 0x91, 0x16, 0x93, 0x94, 0x95, 0x96, 0x04, 0x98, 0x99, 0x9A, 0x9B, 0x14, 0x15, 0x9E, 0x1A,
    0x20, 0xA0, 0xE2, 0xE4, 0xE0, 0xE1, 0xE3, 0xE5, 0xE7, 0xF1, 0xA2, 0x2E, 0x3C, 0x28, 0x2B, 0x7C,
    0x26, 0xE9, 0xEA, 0xEB, 0xE8, 0xED, 0xEE, 0xEF, 0xEC, 0xDF, 0x21, 0x24, 0x2A, 0x29, 0x3B, 0xAC,
    0x2D, 0x2F, 0xC2, 0xC4, 0xC0, 0xC1, 0xC3, 0xC5, 0xC7, 0xD1, 0xA6, 0x2C, 0x25, 0x5F, 0x3E, 0x3F,
    0xF8, 0xC9, 0xCA, 0xCB, 0xC8, 0xCD, 0xCE, 0xCF, 0xCC, 0x60, 0x3A, 0x23, 0x40, 0x27, 0x3D, 0x22,
    0xD8, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xAB, 0xBB, 0xF0, 0xFD, 0xFE, 0xB1,
    0xB0, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0xAA, 0xBA, 0xE6, 0xB8, 0xC6, 0xA4,
    0xB5, 0x7E, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0xA1, 0xBF, 0xD0, 0xDD, 0xDE, 0xAE,
    0x5E, 0xA3, 0xA5, 0xB7, 0xA9, 0xA7, 0xB6, 0xBC, 0xBD, 0xBE, 0x5B, 0x5D, 0xAF, 0xA8, 0xB4, 0xD7,
    0x7B, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0xAD, 0xF4, 0xF6, 0xF2, 0xF3, 0xF5,
    0x7D, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0xB9, 0xFB, 0xFC, 0xF9, 0xFA, 0xFF,
    0x5C, 0xF7, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0xB2, 0xD4, 0xD6, 0xD2, 0xD3, 0xD5,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0xB3, 0xDB, 0xDC, 0xD9, 0xDA, 0x9F,
];

const L01: &[u8] = b"<!DOCTYPE html>";
const L02: &[u8] = b"<html lang=\"en\">";
const L03: &[u8] = b"<head>";
const L04: &[u8] = b"<meta charset=\"utf-8\">";
const L05: &[u8] = b"<title>HTML Table Layout</title>";
const L06: &[u8] = b"</head>";
const L07: &[u8] = b"<body style=\"margin:0px;\">";
const L08: &[u8] =
    b"<table  align=\"center\" frame=\"box\" style=\"width:70%; font:12px Segoe UI,sans-serif;\">";
const LTRS: &[u8] = b"<tr>";
const LTRE: &[u8] = b"</tr>";
const LTDE: &[u8] = b"</td>";
const L10: &[u8] = b"<td colspan=\"3\" style=\"padding:0px 5px;background-color:#1d1d96b3;\">";
const L15: &[u8] = b"<td colspan=\"3\" style=\"padding:0px 5px;background-color:#FFAF33;\">";
const L16: &[u8] = b"<p style=\"font-size:16px\">Bank of XYZ</p>";
const L17: &[u8] = b"<p>410 Terry Ave N</p>";
const L18: &[u8] = b"<p>Seattle WA 99999</p>";
const L22_35: &[u8] = b"<td colspan=\"3\" style=\"padding:0px 5px;background-color:#f2f2f2;\">";
const L30_42: &[u8] =
    b"<td colspan=\"3\" style=\"padding:0px 5px;background-color:#33FFD1; text-align:center;\">";
const L31: &[u8] = b"<p style=\"font-size:16px\">Basic Details</p>";
const L43: &[u8] = b"<p style=\"font-size:16px\">Transaction Summary</p>";
const L47: &[u8] =
    b"<td style=\"width:25%; padding:0px 5px; background-color:#33FF5E; text-align:left;\">";
const L48: &[u8] = b"<p style=\"font-size:16px\">Tran ID</p>";
const L50: &[u8] =
    b"<td style=\"width:55%; padding:0px 5px; background-color:#33FF5E; text-align:left;\">";
const L51: &[u8] = b"<p style=\"font-size:16px\">Tran Details</p>";
const L53: &[u8] =
    b"<td style=\"width:20%; padding:0px 5px; background-color:#33FF5E; text-align:right;\">";
const L54: &[u8] = b"<p style=\"font-size:16px\">Amount</p>";
const L58: &[u8] =
    b"<td style=\"width:25%; padding:0px 5px; background-color:#f2f2f2; text-align:left;\">";
const L61: &[u8] =
    b"<td style=\"width:55%; padding:0px 5px; background-color:#f2f2f2; text-align:left;\">";
const L64: &[u8] =
    b"<td style=\"width:20%; padding:0px 5px; background-color:#f2f2f2; text-align:right;\">";
const L75: &[u8] = b"<h3>End of Statement</h3>";
const L78: &[u8] = b"</table>";
const L79: &[u8] = b"</body>";
const L80: &[u8] = b"</html>";

// ---------------------------------------------------------------- helpers

fn vb(s: &[u8]) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
    }
    v
}

fn app(v: &mut Vec<u8>, s: &[u8]) {
    let mut i = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
    }
}

fn eq_bytes(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut res = true;
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            res = false;
        }
        i += 1;
    }
    res
}

// Latin-1 -> EBCDIC (CP037) collating table
fn lat2ebc_table() -> [u8; 256] {
    let mut t = [0u8; 256];
    let mut e: usize = 0;
    while e < 256 {
        let l = EBC2LAT[e] as usize;
        t[l] = e as u8;
        e += 1;
    }
    t
}

// alphanumeric comparison a > b in the EBCDIC collating sequence
fn gt_bytes(a: &[u8], b: &[u8], tbl: &[u8; 256]) -> bool {
    let mut res = false;
    let mut decided = false;
    let mut i = 0;
    while !decided && i < a.len() && i < b.len() {
        let x = tbl[a[i] as usize];
        let y = tbl[b[i] as usize];
        if x > y {
            res = true;
            decided = true;
        } else if x < y {
            res = false;
            decided = true;
        }
        i += 1;
    }
    res
}

// copy src into dst at off, padding to len with spaces (truncate if longer)
fn put(dst: &mut [u8], off: usize, len: usize, src: &[u8]) {
    let mut i = 0;
    while i < len {
        if off + i < dst.len() {
            dst[off + i] = if i < src.len() { src[i] } else { b' ' };
        }
        i += 1;
    }
}

fn fill(dst: &mut [u8], off: usize, len: usize, ch: u8) {
    let mut i = 0;
    while i < len {
        if off + i < dst.len() {
            dst[off + i] = ch;
        }
        i += 1;
    }
}

// unsigned zoned display digits
fn put_unum(dst: &mut [u8], off: usize, n: usize, v: i64) {
    let mut m: u64 = if v < 0 { (-(v as i128)) as u64 } else { v as u64 };
    let mut i = n;
    while i > 0 {
        i -= 1;
        if off + i < dst.len() {
            dst[off + i] = b'0' + (m % 10) as u8;
        }
        m = m / 10;
    }
}

// signed zoned display digits, sign overpunched in the last digit
fn put_snum(dst: &mut [u8], off: usize, n: usize, v: i64) {
    put_unum(dst, off, n, v);
    if n > 0 && off + n - 1 < dst.len() {
        let d = dst[off + n - 1] - b'0';
        if v < 0 {
            dst[off + n - 1] = if d == 0 { b'}' } else { b'J' + d - 1 };
        } else {
            dst[off + n - 1] = if d == 0 { b'{' } else { b'A' + d - 1 };
        }
    }
}

// STRING ... DELIMITED BY delim (empty = SIZE)
fn str_part(dst: &mut [u8], ptr: &mut usize, src: &[u8], delim: &[u8]) {
    let mut n = src.len();
    if delim.len() > 0 && delim.len() <= src.len() {
        let mut i = 0;
        let mut found = false;
        while !found && i + delim.len() <= src.len() {
            let mut m = true;
            let mut j = 0;
            while j < delim.len() {
                if src[i + j] != delim[j] {
                    m = false;
                }
                j += 1;
            }
            if m {
                found = true;
                n = i;
            } else {
                i += 1;
            }
        }
    }
    let mut k = 0;
    while k < n && *ptr < dst.len() {
        dst[*ptr] = src[k];
        *ptr += 1;
        k += 1;
    }
}

// decode a zoned decimal field (sign overpunched in the last byte)
fn zoned(b: &[u8]) -> i64 {
    let mut v: i64 = 0;
    let mut neg = false;
    let n = b.len();
    let mut i = 0;
    while i < n {
        let c = b[i];
        let d: i64;
        if c >= b'0' && c <= b'9' {
            d = (c - b'0') as i64;
        } else if i + 1 == n && c == b'{' {
            d = 0;
        } else if i + 1 == n && c >= b'A' && c <= b'I' {
            d = (c - b'A') as i64 + 1;
        } else if i + 1 == n && c == b'}' {
            d = 0;
            neg = true;
        } else if i + 1 == n && c >= b'J' && c <= b'R' {
            d = (c - b'J') as i64 + 1;
            neg = true;
        } else if i + 1 == n && c >= b'p' && c <= b'y' {
            d = (c - b'p') as i64;
            neg = true;
        } else {
            d = ((c & 0x0F) as i64) % 10;
        }
        v = v * 10 + d;
        i += 1;
    }
    if neg {
        -v
    } else {
        v
    }
}

fn digits11(v: i64) -> [u8; 11] {
    let mut m = if v < 0 { -v } else { v };
    m = m % 100_000_000_000;
    let mut d = [b'0'; 11];
    let mut i: usize = 11;
    while i > 0 {
        i -= 1;
        d[i] = b'0' + (m % 10) as u8;
        m = m / 10;
    }
    d
}

// PIC 9(9).99-
fn fmt_9_99(v: i64) -> [u8; 13] {
    let d = digits11(v);
    let mut o = [b' '; 13];
    let mut i = 0;
    while i < 9 {
        o[i] = d[i];
        i += 1;
    }
    o[9] = b'.';
    o[10] = d[9];
    o[11] = d[10];
    o[12] = if v < 0 { b'-' } else { b' ' };
    o
}

// PIC Z(9).99-
fn fmt_z_99(v: i64) -> [u8; 13] {
    let d = digits11(v);
    let mut o = [b' '; 13];
    let mut sig = false;
    let mut i = 0;
    while i < 9 {
        if d[i] != b'0' {
            sig = true;
        }
        o[i] = if sig { d[i] } else { b' ' };
        i += 1;
    }
    o[9] = b'.';
    o[10] = d[9];
    o[11] = d[10];
    o[12] = if v < 0 { b'-' } else { b' ' };
    o
}

fn add1(x: i64) -> i64 {
    (x + 1) % 10000
}

fn add_trunc11(a: i64, b: i64) -> i64 {
    let s = a + b;
    let m = (if s < 0 { -s } else { s }) % 100_000_000_000;
    if s < 0 {
        -m
    } else {
        m
    }
}

// ---------------------------------------------------------------- record images

fn ser_trnx(r: &TrnxRecord) -> [u8; 350] {
    let mut b = [b' '; 350];
    put(&mut b, 0, 16, &r.trnx_card_num);
    put(&mut b, 16, 16, &r.trnx_id);
    put(&mut b, 32, 2, &r.trnx_type_cd);
    put_unum(&mut b, 34, 4, r.trnx_cat_cd);
    put(&mut b, 38, 10, &r.trnx_source);
    put(&mut b, 48, 100, &r.trnx_desc);
    put_snum(&mut b, 148, 11, r.trnx_amt);
    put_unum(&mut b, 159, 9, r.trnx_merchant_id);
    put(&mut b, 168, 50, &r.trnx_merchant_name);
    put(&mut b, 218, 50, &r.trnx_merchant_city);
    put(&mut b, 268, 10, &r.trnx_merchant_zip);
    put(&mut b, 278, 26, &r.trnx_orig_ts);
    put(&mut b, 304, 26, &r.trnx_proc_ts);
    put(&mut b, 330, 20, &r.filler1);
    b
}

fn ser_xref(r: &CardXrefRecord) -> [u8; 50] {
    let mut b = [b' '; 50];
    put(&mut b, 0, 16, &r.xref_card_num);
    put_unum(&mut b, 16, 9, r.xref_cust_id);
    put_unum(&mut b, 25, 11, r.xref_acct_id);
    put(&mut b, 36, 14, &r.filler1);
    b
}

fn ser_cust(r: &CustomerRecord) -> [u8; 500] {
    let mut b = [b' '; 500];
    put_unum(&mut b, 0, 9, r.cust_id);
    put(&mut b, 9, 25, &r.cust_first_name);
    put(&mut b, 34, 25, &r.cust_middle_name);
    put(&mut b, 59, 25, &r.cust_last_name);
    put(&mut b, 84, 50, &r.cust_addr_line_1);
    put(&mut b, 134, 50, &r.cust_addr_line_2);
    put(&mut b, 184, 50, &r.cust_addr_line_3);
    put(&mut b, 234, 2, &r.cust_addr_state_cd);
    put(&mut b, 236, 3, &r.cust_addr_country_cd);
    put(&mut b, 239, 10, &r.cust_addr_zip);
    put(&mut b, 249, 15, &r.cust_phone_num_1);
    put(&mut b, 264, 15, &r.cust_phone_num_2);
    put_unum(&mut b, 279, 9, r.cust_ssn);
    put(&mut b, 288, 20, &r.cust_govt_issued_id);
    put(&mut b, 308, 10, &r.cust_dob_yyyymmdd);
    put(&mut b, 318, 10, &r.cust_eft_account_id);
    put(&mut b, 328, 1, &r.cust_pri_card_holder_ind);
    put_unum(&mut b, 329, 3, r.cust_fico_credit_score);
    put(&mut b, 332, 168, &r.filler1);
    b
}

fn ser_acct(r: &AccountRecord) -> [u8; 300] {
    let mut b = [b' '; 300];
    put_unum(&mut b, 0, 11, r.acct_id);
    put(&mut b, 11, 1, &r.acct_active_status);
    put_snum(&mut b, 12, 12, r.acct_curr_bal);
    put_snum(&mut b, 24, 12, r.acct_credit_limit);
    put_snum(&mut b, 36, 12, r.acct_cash_credit_limit);
    put(&mut b, 48, 10, &r.acct_open_date);
    put(&mut b, 58, 10, &r.acct_expiraion_date);
    put(&mut b, 68, 10, &r.acct_reissue_date);
    put_snum(&mut b, 78, 12, r.acct_curr_cyc_credit);
    put_snum(&mut b, 90, 12, r.acct_curr_cyc_debit);
    put(&mut b, 102, 10, &r.acct_addr_zip);
    put(&mut b, 112, 10, &r.acct_group_id);
    put(&mut b, 122, 178, &r.filler1);
    b
}

// ---------------------------------------------------------------- sparse table memory

fn mem_default(p: i64) -> u8 {
    if p >= 0 && p < TABLE_SZ {
        b' '
    } else {
        0
    }
}

fn mem_write(mem: &mut Mem, off: i64, src: &[u8]) {
    mem.offs.push(off);
    mem.starts.push(mem.bytes.len());
    mem.lens.push(src.len());
    let mut i = 0;
    while i < src.len() {
        mem.bytes.push(src[i]);
        i += 1;
    }
}

fn mem_get(mem: &Mem, off: i64, dst: &mut [u8]) {
    let dl = dst.len() as i64;
    let mut i = 0;
    while i < dst.len() {
        dst[i] = mem_default(off + i as i64);
        i += 1;
    }
    let mut w = 0;
    while w < mem.offs.len() {
        let o = mem.offs[w];
        let start = mem.starts[w];
        let n = mem.lens[w] as i64;
        let mut s = if o > off { o } else { off };
        let e1 = o + n;
        let e2 = off + dl;
        let e = if e1 < e2 { e1 } else { e2 };
        while s < e {
            let src_idx = start + (s - o) as usize;
            let dst_idx = (s - off) as usize;
            let byte = mem.bytes[src_idx];
            dst[dst_idx] = byte;
            s += 1;
        }
        w += 1;
    }
}

fn card_off(c: i64) -> i64 {
    (c - 1) * CARD_SZ
}

fn tran_off(c: i64, t: i64) -> i64 {
    (c - 1) * CARD_SZ + 16 + (t - 1) * TRAN_SZ
}

fn trct_off(c: i64) -> i64 {
    CNTR_BASE + (c - 1) * 2
}

fn write_trct(mem: &mut Mem, c: i64, v: i64) {
    let u = v & 0xFFFF;
    let b = [((u >> 8) & 0xFF) as u8, (u & 0xFF) as u8];
    mem_write(mem, trct_off(c), &b);
}

fn read_trct(mem: &Mem, c: i64) -> i64 {
    let mut b = [0u8; 2];
    mem_get(mem, trct_off(c), &mut b);
    let u = (b[0] as i64) * 256 + b[1] as i64;
    if u >= 32768 {
        u - 65536
    } else {
        u
    }
}

// ---------------------------------------------------------------- CBSTM03B

fn call_m03b(
    c: &mut Ctx,
    trnx: &[TrnxRecord],
    xref: &[CardXrefRecord],
    cust: &[CustomerRecord],
    acct: &[AccountRecord],
) {
    if eq_bytes(&c.m_dd, b"TRNXFILE") {
        if c.m_oper == b'O' {
            c.trnx_status = *b"00";
            c.trnx_pos = 0;
            c.trnx_eof = false;
        } else if c.m_oper == b'R' {
            if c.trnx_eof {
                c.trnx_status = *b"46";
            } else if c.trnx_pos < trnx.len() {
                let r = trnx[c.trnx_pos];
                let img = ser_trnx(&r);
                c.m_fldt = [b' '; 1000];
                put(&mut c.m_fldt, 0, 350, &img);
                c.trnx_pos += 1;
                c.trnx_status = *b"00";
            } else {
                c.trnx_eof = true;
                c.trnx_status = *b"10";
            }
        } else if c.m_oper == b'C' {
            c.trnx_status = *b"00";
        }
        c.m_rc = c.trnx_status;
    } else if eq_bytes(&c.m_dd, b"XREFFILE") {
        if c.m_oper == b'O' {
            c.xref_status = *b"00";
            c.xref_pos = 0;
            c.xref_eof = false;
        } else if c.m_oper == b'R' {
            if c.xref_eof {
                c.xref_status = *b"46";
            } else if c.xref_pos < xref.len() {
                let r = xref[c.xref_pos];
                let img = ser_xref(&r);
                c.m_fldt = [b' '; 1000];
                put(&mut c.m_fldt, 0, 50, &img);
                c.xref_pos += 1;
                c.xref_status = *b"00";
            } else {
                c.xref_eof = true;
                c.xref_status = *b"10";
            }
        } else if c.m_oper == b'C' {
            c.xref_status = *b"00";
        }
        c.m_rc = c.xref_status;
    } else if eq_bytes(&c.m_dd, b"CUSTFILE") {
        if c.m_oper == b'O' {
            c.cust_status = *b"00";
        } else if c.m_oper == b'K' {
            let mut ln = c.m_key_ln;
            if ln < 0 {
                ln = 0;
            }
            if ln > 25 {
                ln = 25;
            }
            let lnu = ln as usize;
            let mut key = [b' '; 9];
            let mut i = 0;
            while i < 9 && i < lnu {
                key[i] = c.m_key[i];
                i += 1;
            }
            let mut found = false;
            let mut j = 0;
            while !found && j < cust.len() {
                let r = cust[j];
                let mut rk = [b'0'; 9];
                put_unum(&mut rk, 0, 9, r.cust_id);
                if eq_bytes(&rk, &key) {
                    found = true;
                    let img = ser_cust(&r);
                    c.m_fldt = [b' '; 1000];
                    put(&mut c.m_fldt, 0, 500, &img);
                }
                j += 1;
            }
            c.cust_status = if found { *b"00" } else { *b"23" };
        } else if c.m_oper == b'C' {
            c.cust_status = *b"00";
        }
        c.m_rc = c.cust_status;
    } else if eq_bytes(&c.m_dd, b"ACCTFILE") {
        if c.m_oper == b'O' {
            c.acct_status = *b"00";
        } else if c.m_oper == b'K' {
            let mut ln = c.m_key_ln;
            if ln < 0 {
                ln = 0;
            }
            if ln > 25 {
                ln = 25;
            }
            let lnu = ln as usize;
            // alphanumeric -> PIC 9(11): right-justified, zero filled
            let mut key = [b'0'; 11];
            let mut i = 0;
            while i < 11 && i < lnu {
                key[10 - i] = c.m_key[lnu - 1 - i];
                i += 1;
            }
            let kv = zoned(&key);
            let mut found = false;
            let mut j = 0;
            while !found && j < acct.len() {
                let r = acct[j];
                let rk = digits11(r.acct_id);
                if zoned(&rk) == kv {
                    found = true;
                    let img = ser_acct(&r);
                    c.m_fldt = [b' '; 1000];
                    put(&mut c.m_fldt, 0, 300, &img);
                }
                j += 1;
            }
            c.acct_status = if found { *b"00" } else { *b"23" };
        } else if c.m_oper == b'C' {
            c.acct_status = *b"00";
        }
        c.m_rc = c.acct_status;
    }
}

// ---------------------------------------------------------------- output helpers

fn sw(c: &mut Ctx, line: &[u8; 80]) {
    c.stmt.push(vb(line));
}

fn hw(c: &mut Ctx, lit: &[u8]) {
    let mut r = [b' '; 100];
    put(&mut r, 0, 100, lit);
    c.html.push(vb(&r));
}

fn rc_ok(c: &Ctx) -> bool {
    eq_bytes(&c.m_rc, b"00") || eq_bytes(&c.m_rc, b"04")
}

fn err_abend(c: &mut Ctx, msg: &[u8]) {
    c.displays.push(vb(msg));
    let mut d: Vec<u8> = Vec::new();
    app(&mut d, b"RETURN CODE: ");
    app(&mut d, &c.m_rc);
    c.displays.push(d);
    c.displays.push(vb(b"ABENDING PROGRAM"));
    c.abended = true;
}

fn set_dd(c: &mut Ctx, dd: &[u8]) {
    put(&mut c.m_dd, 0, 8, dd);
}

fn finish(c: Ctx) -> Output {
    Output {
        displays: c.displays,
        stmt_file_writes: c.stmt,
        html_file_writes: c.html,
        abended: c.abended,
    }
}

fn st_line(n: u32, st: &St) -> [u8; 80] {
    let mut l = [b' '; 80];
    match n {
        0 => {
            fill(&mut l, 0, 31, b'*');
            put(&mut l, 31, 18, b"START OF STATEMENT");
            fill(&mut l, 49, 31, b'*');
        }
        1 => {
            put(&mut l, 0, 75, &st.name);
        }
        2 => {
            put(&mut l, 0, 50, &st.add1);
        }
        3 => {
            put(&mut l, 0, 50, &st.add2);
        }
        4 => {
            put(&mut l, 0, 80, &st.add3);
        }
        5 => {
            fill(&mut l, 0, 80, b'-');
        }
        6 => {
            put(&mut l, 33, 14, b"Basic Details");
        }
        7 => {
            put(&mut l, 0, 20, b"Account ID         :");
            put(&mut l, 20, 20, &st.acct_id);
        }
        8 => {
            put(&mut l, 0, 20, b"Current Balance    :");
            put(&mut l, 20, 13, &st.curr_bal);
        }
        9 => {
            put(&mut l, 0, 20, b"FICO Score         :");
            put(&mut l, 20, 20, &st.fico);
        }
        10 => {
            fill(&mut l, 0, 80, b'-');
        }
        11 => {
            put(&mut l, 30, 20, b"TRANSACTION SUMMARY ");
        }
        12 => {
            fill(&mut l, 0, 80, b'-');
        }
        13 => {
            put(&mut l, 0, 16, b"Tran ID         ");
            put(&mut l, 16, 51, b"Tran Details    ");
            put(&mut l, 67, 13, b"  Tran Amount");
        }
        14 => {
            put(&mut l, 0, 16, &st.tranid);
            l[16] = b' ';
            put(&mut l, 17, 49, &st.trandt);
            l[66] = b'$';
            put(&mut l, 67, 13, &st.tranamt);
        }
        140 => {
            put(&mut l, 0, 10, b"Total EXP:");
            l[66] = b'$';
            put(&mut l, 67, 13, &st.total_tramt);
        }
        _ => {
            fill(&mut l, 0, 32, b'*');
            put(&mut l, 32, 16, b"END OF STATEMENT");
            fill(&mut l, 48, 32, b'*');
        }
    }
    l
}

// ---------------------------------------------------------------- paragraphs

fn html_header(c: &mut Ctx, acct: &[u8; 300]) {
    hw(c, L01);
    hw(c, L02);
    hw(c, L03);
    hw(c, L04);
    hw(c, L05);
    hw(c, L06);
    hw(c, L07);
    hw(c, L08);
    hw(c, LTRS);
    hw(c, L10);
    let mut l11 = [b' '; 59];
    put(&mut l11, 0, 34, b"<h3>Statement for Account Number: ");
    put(&mut l11, 34, 20, &acct[0..11]);
    put(&mut l11, 54, 5, b"</h3>");
    hw(c, &l11);
    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, LTRS);
    hw(c, L15);
    hw(c, L16);
    hw(c, L17);
    hw(c, L18);
    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, LTRS);
    hw(c, L22_35);
}

fn html_p_line(c: &mut Ctx, pre: &[u8], data: &[u8], delim: &[u8], add_two: bool) {
    let mut r = [b' '; 100];
    let mut p: usize = 0;
    str_part(&mut r, &mut p, pre, b"*");
    str_part(&mut r, &mut p, data, delim);
    if add_two {
        str_part(&mut r, &mut p, b"  ", b"");
    }
    str_part(&mut r, &mut p, b"</p>", b"*");
    c.html.push(vb(&r));
}

fn html_nmadbs(c: &mut Ctx, st: &St) {
    let mut l23 = [b' '; 50];
    put(&mut l23, 0, 50, &st.name);
    html_p_line(c, b"<p style=\"font-size:16px\">", &l23, b"  ", true);
    html_p_line(c, b"<p>", &st.add1, b"  ", true);
    html_p_line(c, b"<p>", &st.add2, b"  ", true);
    html_p_line(c, b"<p>", &st.add3, b"  ", true);

    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, LTRS);
    hw(c, L30_42);
    hw(c, L31);
    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, LTRS);
    hw(c, L22_35);

    html_p_line(c, b"<p>Account ID         : ", &st.acct_id, b"*", false);
    html_p_line(c, b"<p>Current Balance    : ", &st.curr_bal, b"*", false);
    html_p_line(c, b"<p>FICO Score         : ", &st.fico, b"*", false);
    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, LTRS);
    hw(c, L30_42);
    hw(c, L43);
    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, LTRS);
    hw(c, L47);
    hw(c, L48);
    hw(c, LTDE);
    hw(c, L50);
    hw(c, L51);
    hw(c, LTDE);
    hw(c, L53);
    hw(c, L54);
    hw(c, LTDE);
    hw(c, LTRE);
}

fn create_statement(c: &mut Ctx, st: &mut St, cust: &[u8; 500], acct: &[u8; 300]) {
    // INITIALIZE STATEMENT-LINES (non-FILLER items only)
    st.name = [b' '; 75];
    st.add1 = [b' '; 50];
    st.add2 = [b' '; 50];
    st.add3 = [b' '; 80];
    st.acct_id = [b' '; 20];
    st.curr_bal = fmt_9_99(0);
    st.fico = [b' '; 20];
    st.tranid = [b' '; 16];
    st.trandt = [b' '; 49];
    st.tranamt = fmt_z_99(0);
    st.total_tramt = fmt_z_99(0);

    let l0 = st_line(0, st);
    sw(c, &l0);
    html_header(c, acct);

    let mut p: usize = 0;
    str_part(&mut st.name, &mut p, &cust[9..34], b" ");
    str_part(&mut st.name, &mut p, b" ", b"");
    str_part(&mut st.name, &mut p, &cust[34..59], b" ");
    str_part(&mut st.name, &mut p, b" ", b"");
    str_part(&mut st.name, &mut p, &cust[59..84], b" ");
    str_part(&mut st.name, &mut p, b" ", b"");

    put(&mut st.add1, 0, 50, &cust[84..134]);
    put(&mut st.add2, 0, 50, &cust[134..184]);

    p = 0;
    str_part(&mut st.add3, &mut p, &cust[184..234], b" ");
    str_part(&mut st.add3, &mut p, b" ", b"");
    str_part(&mut st.add3, &mut p, &cust[234..236], b" ");
    str_part(&mut st.add3, &mut p, b" ", b"");
    str_part(&mut st.add3, &mut p, &cust[236..239], b" ");
    str_part(&mut st.add3, &mut p, b" ", b"");
    str_part(&mut st.add3, &mut p, &cust[239..249], b" ");
    str_part(&mut st.add3, &mut p, b" ", b"");

    put(&mut st.acct_id, 0, 20, &acct[0..11]);
    st.curr_bal = fmt_9_99(zoned(&acct[12..24]));
    put(&mut st.fico, 0, 20, &cust[329..332]);
    html_nmadbs(c, st);

    let order: [u32; 15] = [1, 2, 3, 4, 5, 6, 5, 7, 8, 9, 10, 11, 12, 13, 12];
    let mut i: usize = 0;
    while i < 15 {
        let l = st_line(order[i], st);
        sw(c, &l);
        i += 1;
    }
}

fn write_trans(c: &mut Ctx, st: &mut St, trnx: &[u8; 350]) {
    put(&mut st.tranid, 0, 16, &trnx[16..32]);
    put(&mut st.trandt, 0, 49, &trnx[48..148]);
    st.tranamt = fmt_z_99(zoned(&trnx[148..159]));
    let l = st_line(14, st);
    sw(c, &l);

    hw(c, LTRS);
    hw(c, L58);
    html_p_line(c, b"<p>", &st.tranid, b"*", false);
    hw(c, LTDE);
    hw(c, L61);
    html_p_line(c, b"<p>", &st.trandt, b"*", false);
    hw(c, LTDE);
    hw(c, L64);
    html_p_line(c, b"<p>", &st.tranamt, b"*", false);
    hw(c, LTDE);
    hw(c, LTRE);
}

// 4000-TRNXFILE-GET
fn trnx_get(
    c: &mut Ctx,
    st: &mut St,
    mem: &Mem,
    cr_cnt: i64,
    xref_rec: &[u8; 50],
    trnx_rec: &mut [u8; 350],
    tbl: &[u8; 256],
) {
    let mut total: i64 = 0;
    let mut xref_card = [b' '; 16];
    put(&mut xref_card, 0, 16, &xref_rec[0..16]);
    let mut cr_jmp: i64 = 1;
    let mut done = false;
    while !done {
        if cr_jmp > cr_cnt {
            done = true;
        } else {
            let mut wcard = [b' '; 16];
            mem_get(mem, card_off(cr_jmp), &mut wcard);
            if gt_bytes(&wcard, &xref_card, tbl) {
                done = true;
            } else {
                if eq_bytes(&xref_card, &wcard) {
                    put(trnx_rec, 0, 16, &wcard);
                    let mut tr_jmp: i64 = 1;
                    let mut tdone = false;
                    while !tdone {
                        if tr_jmp > read_trct(mem, cr_jmp) {
                            tdone = true;
                        } else {
                            let mut tid = [b' '; 16];
                            mem_get(mem, tran_off(cr_jmp, tr_jmp), &mut tid);
                            let mut rest = [b' '; 318];
                            mem_get(mem, tran_off(cr_jmp, tr_jmp) + 16, &mut rest);
                            put(trnx_rec, 16, 16, &tid);
                            put(trnx_rec, 32, 318, &rest);
                            write_trans(c, st, trnx_rec);
                            total = add_trunc11(total, zoned(&trnx_rec[148..159]));
                            tr_jmp = add1(tr_jmp);
                        }
                    }
                }
                cr_jmp = add1(cr_jmp);
            }
        }
    }
    let ws_trn_amt = total;
    st.total_tramt = fmt_z_99(ws_trn_amt);
    let l12 = st_line(12, st);
    sw(c, &l12);
    let l14a = st_line(140, st);
    sw(c, &l14a);
    let l15 = st_line(15, st);
    sw(c, &l15);

    hw(c, LTRS);
    hw(c, L10);
    hw(c, L75);
    hw(c, LTDE);
    hw(c, LTRE);
    hw(c, L78);
    hw(c, L79);
    hw(c, L80);
}

fn open_file(
    c: &mut Ctx,
    dd: &[u8],
    msg: &[u8],
    trnx: &[TrnxRecord],
    xref: &[CardXrefRecord],
    cust: &[CustomerRecord],
    acct: &[AccountRecord],
) -> bool {
    set_dd(c, dd);
    c.m_oper = b'O';
    c.m_rc = *b"00";
    call_m03b(c, trnx, xref, cust, acct);
    if !rc_ok(c) {
        err_abend(c, msg);
        false
    } else {
        true
    }
}

fn close_file(
    c: &mut Ctx,
    dd: &[u8],
    msg: &[u8],
    trnx: &[TrnxRecord],
    xref: &[CardXrefRecord],
    cust: &[CustomerRecord],
    acct: &[AccountRecord],
) -> bool {
    set_dd(c, dd);
    c.m_oper = b'C';
    c.m_rc = *b"00";
    call_m03b(c, trnx, xref, cust, acct);
    if !rc_ok(c) {
        err_abend(c, msg);
        false
    } else {
        true
    }
}

// ---------------------------------------------------------------- entry point

pub fn run(
    trnx_file: &[TrnxRecord],
    xref_file: &[CardXrefRecord],
    cust_file: &[CustomerRecord],
    acct_file: &[AccountRecord],
) -> Output {
    let tbl = lat2ebc_table();
    let mut c = Ctx {
        displays: Vec::new(),
        stmt: Vec::new(),
        html: Vec::new(),
        abended: false,
        trnx_pos: 0,
        trnx_eof: false,
        trnx_status: [b' '; 2],
        xref_pos: 0,
        xref_eof: false,
        xref_status: [b' '; 2],
        cust_status: [b' '; 2],
        acct_status: [b' '; 2],
        m_dd: [b' '; 8],
        m_oper: b' ',
        m_rc: [b' '; 2],
        m_key: [b' '; 25],
        m_key_ln: 0,
        m_fldt: [b' '; 1000],
    };

    // OPEN OUTPUT STMT-FILE HTML-FILE; INITIALIZE tables (sparse, defaults implied)
    let mut mem = Mem {
        offs: Vec::new(),
        starts: Vec::new(),
        lens: Vec::new(),
        bytes: Vec::new(),
    };

    let mut st = St {
        name: [b' '; 75],
        add1: [b' '; 50],
        add2: [b' '; 50],
        add3: [b' '; 80],
        acct_id: [b' '; 20],
        curr_bal: [b' '; 13],
        fico: [b' '; 20],
        tranid: [b' '; 16],
        trandt: [b' '; 49],
        tranamt: [b' '; 13],
        total_tramt: [b' '; 13],
    };

    // 8100-TRNXFILE-OPEN
    if !open_file(
        &mut c,
        b"TRNXFILE",
        b"ERROR OPENING TRNXFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }
    c.m_oper = b'R';
    c.m_fldt = [b' '; 1000];
    call_m03b(&mut c, trnx_file, xref_file, cust_file, acct_file);
    if !rc_ok(&c) {
        err_abend(&mut c, b"ERROR READING TRNXFILE");
        return finish(c);
    }
    let mut trnx_rec = [b' '; 350];
    put(&mut trnx_rec, 0, 350, &c.m_fldt[0..350]);
    let mut save_card = [b' '; 16];
    put(&mut save_card, 0, 16, &trnx_rec[0..16]);
    let mut cr_cnt: i64 = 1;
    let mut tr_cnt: i64 = 0;

    // 8500-READTRNX-READ
    let mut reading = true;
    let mut ok = true;
    while reading {
        if eq_bytes(&save_card, &trnx_rec[0..16]) {
            tr_cnt = add1(tr_cnt);
        } else {
            write_trct(&mut mem, cr_cnt, tr_cnt);
            cr_cnt = add1(cr_cnt);
            tr_cnt = 1;
        }
        mem_write(&mut mem, card_off(cr_cnt), &trnx_rec[0..16]);
        mem_write(&mut mem, tran_off(cr_cnt, tr_cnt), &trnx_rec[16..32]);
        mem_write(&mut mem, tran_off(cr_cnt, tr_cnt) + 16, &trnx_rec[32..350]);
        put(&mut save_card, 0, 16, &trnx_rec[0..16]);

        set_dd(&mut c, b"TRNXFILE");
        c.m_oper = b'R';
        c.m_fldt = [b' '; 1000];
        call_m03b(&mut c, trnx_file, xref_file, cust_file, acct_file);
        if eq_bytes(&c.m_rc, b"00") {
            put(&mut trnx_rec, 0, 350, &c.m_fldt[0..350]);
        } else if eq_bytes(&c.m_rc, b"10") {
            reading = false;
        } else {
            err_abend(&mut c, b"ERROR READING TRNXFILE");
            ok = false;
            reading = false;
        }
    }
    if !ok {
        return finish(c);
    }
    // 8599-EXIT
    write_trct(&mut mem, cr_cnt, tr_cnt);

    // 8200 / 8300 / 8400
    if !open_file(
        &mut c,
        b"XREFFILE",
        b"ERROR OPENING XREFFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }
    if !open_file(
        &mut c,
        b"CUSTFILE",
        b"ERROR OPENING CUSTFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }
    if !open_file(
        &mut c,
        b"ACCTFILE",
        b"ERROR OPENING ACCTFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }

    // 1000-MAINLINE
    let mut eof: u8 = b'N';
    let mut xref_rec = [b' '; 50];
    let mut cust_rec = [b' '; 500];
    let mut acct_rec = [b' '; 300];
    while ok && eof != b'Y' {
        if eof == b'N' {
            // 1000-XREFFILE-GET-NEXT
            set_dd(&mut c, b"XREFFILE");
            c.m_oper = b'R';
            c.m_rc = *b"00";
            c.m_fldt = [b' '; 1000];
            call_m03b(&mut c, trnx_file, xref_file, cust_file, acct_file);
            if eq_bytes(&c.m_rc, b"00") {
            } else if eq_bytes(&c.m_rc, b"10") {
                eof = b'Y';
            } else {
                err_abend(&mut c, b"ERROR READING XREFFILE");
                ok = false;
            }
            if ok {
                put(&mut xref_rec, 0, 50, &c.m_fldt[0..50]);
            }

            if ok && eof == b'N' {
                // 2000-CUSTFILE-GET
                set_dd(&mut c, b"CUSTFILE");
                c.m_oper = b'K';
                c.m_key = [b' '; 25];
                put(&mut c.m_key, 0, 9, &xref_rec[16..25]);
                c.m_key_ln = 9;
                c.m_rc = *b"00";
                c.m_fldt = [b' '; 1000];
                call_m03b(&mut c, trnx_file, xref_file, cust_file, acct_file);
                if !eq_bytes(&c.m_rc, b"00") {
                    err_abend(&mut c, b"ERROR READING CUSTFILE");
                    ok = false;
                }
                if ok {
                    put(&mut cust_rec, 0, 500, &c.m_fldt[0..500]);

                    // 3000-ACCTFILE-GET
                    set_dd(&mut c, b"ACCTFILE");
                    c.m_oper = b'K';
                    c.m_key = [b' '; 25];
                    put(&mut c.m_key, 0, 11, &xref_rec[25..36]);
                    c.m_key_ln = 11;
                    c.m_rc = *b"00";
                    c.m_fldt = [b' '; 1000];
                    call_m03b(&mut c, trnx_file, xref_file, cust_file, acct_file);
                    if !eq_bytes(&c.m_rc, b"00") {
                        err_abend(&mut c, b"ERROR READING ACCTFILE");
                        ok = false;
                    }
                }
                if ok {
                    put(&mut acct_rec, 0, 300, &c.m_fldt[0..300]);

                    // 5000-CREATE-STATEMENT
                    create_statement(&mut c, &mut st, &cust_rec, &acct_rec);

                    // 4000-TRNXFILE-GET
                    trnx_get(&mut c, &mut st, &mem, cr_cnt, &xref_rec, &mut trnx_rec, &tbl);
                }
            }
        }
    }
    if !ok {
        return finish(c);
    }

    if !close_file(
        &mut c,
        b"TRNXFILE",
        b"ERROR CLOSING TRNXFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }
    if !close_file(
        &mut c,
        b"XREFFILE",
        b"ERROR CLOSING XREFFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }
    if !close_file(
        &mut c,
        b"CUSTFILE",
        b"ERROR CLOSING CUSTFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }
    if !close_file(
        &mut c,
        b"ACCTFILE",
        b"ERROR CLOSING ACCTFILE",
        trnx_file,
        xref_file,
        cust_file,
        acct_file,
    ) {
        return finish(c);
    }

    finish(c)
}