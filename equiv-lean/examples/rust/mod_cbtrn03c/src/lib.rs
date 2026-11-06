#[derive(Clone, Copy)]
pub struct TranRecord {
    pub tran_id: [u8; 16],
    pub tran_type_cd: [u8; 2],
    pub tran_cat_cd: i64,
    pub tran_source: [u8; 10],
    pub tran_desc: [u8; 100],
    pub tran_amt: i64,
    pub tran_merchant_id: i64,
    pub tran_merchant_name: [u8; 50],
    pub tran_merchant_city: [u8; 50],
    pub tran_merchant_zip: [u8; 10],
    pub tran_card_num: [u8; 16],
    pub tran_orig_ts: [u8; 26],
    pub tran_proc_ts: [u8; 26],
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
pub struct TranTypeRecord {
    pub tran_type: [u8; 2],
    pub tran_type_desc: [u8; 50],
    pub filler1: [u8; 8],
}

#[derive(Clone, Copy)]
pub struct TranCatRecord {
    pub tran_type_cd: [u8; 2],
    pub tran_cat_cd: i64,
    pub tran_cat_type_desc: [u8; 50],
    pub filler1: [u8; 4],
}

#[derive(Clone, Copy)]
pub struct WsDateparmRecord {
    pub ws_start_date: [u8; 10],
    pub filler1: [u8; 1],
    pub ws_end_date: [u8; 10],
}

#[derive(Clone, Copy)]
pub struct FdReptfileRec {
    pub fd_reptfile_rec: [u8; 133],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub report_file_writes: Vec<FdReptfileRec>,
    pub abended: bool,
}

struct St {
    displays: Vec<Vec<u8>>,
    writes: Vec<FdReptfileRec>,
    line_counter: i64,
    page_total: i64,
    account_total: i64,
    grand_total: i64,
    rept_start_date: [u8; 10],
    rept_end_date: [u8; 10],
}

// CP037: EBCDIC code -> character code point
const CP037: [u8; 256] = [
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

fn ebcdic_weight(b: u8) -> usize {
    let mut i: usize = 0;
    while i < 256 {
        if CP037[i] == b {
            return i;
        }
        i += 1;
    }
    b as usize
}

// returns -1, 0, 1 comparing a and b (equal length) in EBCDIC collating sequence
fn cmp_ebcdic(a: &[u8], b: &[u8]) -> i32 {
    let mut i: usize = 0;
    while i < a.len() && i < b.len() {
        let wa = ebcdic_weight(a[i]);
        let wb = ebcdic_weight(b[i]);
        if wa < wb {
            return -1;
        }
        if wa > wb {
            return 1;
        }
        i += 1;
    }
    0
}

fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn push_bytes(out: &mut Vec<u8>, s: &[u8]) {
    let mut i: usize = 0;
    while i < s.len() {
        out.push(s[i]);
        i += 1;
    }
}

fn push_padded(out: &mut Vec<u8>, s: &[u8], width: usize) {
    let mut i: usize = 0;
    while i < width {
        if i < s.len() {
            out.push(s[i]);
        } else {
            out.push(b' ');
        }
        i += 1;
    }
}

fn push_fill(out: &mut Vec<u8>, c: u8, width: usize) {
    let mut i: usize = 0;
    while i < width {
        out.push(c);
        i += 1;
    }
}

fn push_digits(out: &mut Vec<u8>, v: i64, width: usize) {
    let mut mag: u64 = if v < 0 { (-v) as u64 } else { v as u64 };
    let mut buf = [b'0'; 20];
    let mut i: usize = 0;
    while i < width {
        buf[width - 1 - i] = b'0' + (mag % 10) as u8;
        mag /= 10;
        i += 1;
    }
    let mut j: usize = 0;
    while j < width {
        out.push(buf[j]);
        j += 1;
    }
}

fn push_zoned_signed(out: &mut Vec<u8>, v: i64, width: usize) {
    push_digits(out, v, width);
    let n = out.len();
    let d = out[n - 1] - b'0';
    out[n - 1] = if v < 0 {
        if d == 0 {
            b'}'
        } else {
            b'J' + d - 1
        }
    } else if d == 0 {
        b'{'
    } else {
        b'A' + d - 1
    };
}

// [+|-]ZZZ,ZZZ,ZZZ.ZZ
fn edit_amount(v: i64, plus: bool) -> [u8; 15] {
    let mut out = [b' '; 15];
    let mag_full: u64 = if v < 0 { (-v) as u64 } else { v as u64 };
    let mag = mag_full % 100_000_000_000;
    if mag == 0 {
        return out;
    }
    out[0] = if v < 0 {
        b'-'
    } else if plus {
        b'+'
    } else {
        b' '
    };
    let int_part = mag / 100;
    let frac = mag % 100;
    let mut digits = [0u8; 9];
    let mut t = int_part;
    let mut i: usize = 0;
    while i < 9 {
        digits[8 - i] = (t % 10) as u8;
        t /= 10;
        i += 1;
    }
    let pattern: &[u8; 11] = b"ZZZ,ZZZ,ZZZ";
    let mut suppress = true;
    let mut k: usize = 0;
    let mut p: usize = 0;
    while p < 11 {
        if pattern[p] == b',' {
            out[1 + p] = if suppress { b' ' } else { b',' };
        } else {
            let d = digits[k];
            k += 1;
            if suppress && d == 0 {
                out[1 + p] = b' ';
            } else {
                suppress = false;
                out[1 + p] = b'0' + d;
            }
        }
        p += 1;
    }
    out[12] = b'.';
    out[13] = b'0' + (frac / 10) as u8;
    out[14] = b'0' + (frac % 10) as u8;
    out
}

fn to133(v: &[u8]) -> [u8; 133] {
    let mut r = [b' '; 133];
    let mut i: usize = 0;
    while i < 133 && i < v.len() {
        r[i] = v[i];
        i += 1;
    }
    r
}

fn trunc11(x: i64) -> i64 {
    x % 100_000_000_000
}

fn inc_counter(st: &mut St) {
    st.line_counter = (st.line_counter + 1) % 1_000_000_000;
}

fn write_rec(st: &mut St, rec: [u8; 133]) {
    st.writes.push(FdReptfileRec { fd_reptfile_rec: rec });
}

fn header2() -> [u8; 133] {
    [b'-'; 133]
}

fn write_page_totals(st: &mut St) {
    let mut v = Vec::new();
    push_padded(&mut v, b"Page Total", 11);
    push_fill(&mut v, b'.', 86);
    let e = edit_amount(st.page_total, true);
    push_bytes(&mut v, &e);
    write_rec(st, to133(&v));
    st.grand_total = trunc11(st.grand_total + st.page_total);
    st.page_total = 0;
    inc_counter(st);
    write_rec(st, header2());
    inc_counter(st);
}

fn write_account_totals(st: &mut St) {
    let mut v = Vec::new();
    push_padded(&mut v, b"Account Total", 13);
    push_fill(&mut v, b'.', 84);
    let e = edit_amount(st.account_total, true);
    push_bytes(&mut v, &e);
    write_rec(st, to133(&v));
    st.account_total = 0;
    inc_counter(st);
    write_rec(st, header2());
    inc_counter(st);
}

fn write_grand_totals(st: &mut St) {
    let mut v = Vec::new();
    push_padded(&mut v, b"Grand Total", 11);
    push_fill(&mut v, b'.', 86);
    let e = edit_amount(st.grand_total, true);
    push_bytes(&mut v, &e);
    write_rec(st, to133(&v));
}

fn write_headers(st: &mut St) {
    let mut v = Vec::new();
    push_padded(&mut v, b"DALYREPT", 38);
    push_padded(&mut v, b"Daily Transaction Report", 41);
    push_padded(&mut v, b"Date Range: ", 12);
    let sd = st.rept_start_date;
    let ed = st.rept_end_date;
    push_bytes(&mut v, &sd);
    push_bytes(&mut v, b" to ");
    push_bytes(&mut v, &ed);
    write_rec(st, to133(&v));
    inc_counter(st);

    write_rec(st, [b' '; 133]);
    inc_counter(st);

    let mut h = Vec::new();
    push_padded(&mut h, b"Transaction ID", 17);
    push_padded(&mut h, b"Account ID", 12);
    push_padded(&mut h, b"Transaction Type", 19);
    push_padded(&mut h, b"Tran Category", 35);
    push_padded(&mut h, b"Tran Source", 14);
    push_padded(&mut h, b" ", 1);
    push_padded(&mut h, b"        Amount", 16);
    write_rec(st, to133(&h));
    inc_counter(st);

    write_rec(st, header2());
    inc_counter(st);
}

fn write_detail(
    st: &mut St,
    tran: &TranRecord,
    xref: &CardXrefRecord,
    ttype: &TranTypeRecord,
    tcat: &TranCatRecord,
) {
    let mut v = Vec::new();
    push_bytes(&mut v, &tran.tran_id);
    v.push(b' ');
    push_digits(&mut v, xref.xref_acct_id, 11);
    v.push(b' ');
    push_bytes(&mut v, &tran.tran_type_cd);
    v.push(b'-');
    push_padded(&mut v, &ttype.tran_type_desc[0..15], 15);
    v.push(b' ');
    push_digits(&mut v, tran.tran_cat_cd, 4);
    v.push(b'-');
    push_padded(&mut v, &tcat.tran_cat_type_desc[0..29], 29);
    v.push(b' ');
    push_bytes(&mut v, &tran.tran_source);
    push_fill(&mut v, b' ', 4);
    let e = edit_amount(tran.tran_amt, false);
    push_bytes(&mut v, &e);
    push_fill(&mut v, b' ', 2);
    write_rec(st, to133(&v));
    inc_counter(st);
}

fn write_transaction_report(
    st: &mut St,
    first_time: &mut bool,
    dates: &WsDateparmRecord,
    tran: &TranRecord,
    xref: &CardXrefRecord,
    ttype: &TranTypeRecord,
    tcat: &TranCatRecord,
) {
    if *first_time {
        *first_time = false;
        st.rept_start_date = dates.ws_start_date;
        st.rept_end_date = dates.ws_end_date;
        write_headers(st);
    }
    if st.line_counter % 20 == 0 {
        write_page_totals(st);
        write_headers(st);
    }
    st.page_total = trunc11(st.page_total + tran.tran_amt);
    st.account_total = trunc11(st.account_total + tran.tran_amt);
    write_detail(st, tran, xref, ttype, tcat);
}

fn tran_record_bytes(t: &TranRecord) -> Vec<u8> {
    let mut v = Vec::new();
    push_bytes(&mut v, &t.tran_id);
    push_bytes(&mut v, &t.tran_type_cd);
    push_digits(&mut v, t.tran_cat_cd, 4);
    push_bytes(&mut v, &t.tran_source);
    push_bytes(&mut v, &t.tran_desc);
    push_zoned_signed(&mut v, t.tran_amt, 11);
    push_digits(&mut v, t.tran_merchant_id, 9);
    push_bytes(&mut v, &t.tran_merchant_name);
    push_bytes(&mut v, &t.tran_merchant_city);
    push_bytes(&mut v, &t.tran_merchant_zip);
    push_bytes(&mut v, &t.tran_card_num);
    push_bytes(&mut v, &t.tran_orig_ts);
    push_bytes(&mut v, &t.tran_proc_ts);
    push_bytes(&mut v, &t.filler1);
    v
}

fn abend_status23(st: &mut St) {
    let mut d = Vec::new();
    push_bytes(&mut d, b"FILE STATUS IS: NNNN0023");
    st.displays.push(d);
    let mut a = Vec::new();
    push_bytes(&mut a, b"ABENDING PROGRAM");
    st.displays.push(a);
}

fn finish(st: St, abended: bool) -> Output {
    Output {
        displays: st.displays,
        report_file_writes: st.writes,
        abended,
    }
}

pub fn run(
    transact_file: &[TranRecord],
    xref_file: &[CardXrefRecord],
    trantype_file: &[TranTypeRecord],
    trancatg_file: &[TranCatRecord],
    date_parms_file: &[WsDateparmRecord],
) -> Output {
    let mut st = St {
        displays: Vec::new(),
        writes: Vec::new(),
        line_counter: 0,
        page_total: 0,
        account_total: 0,
        grand_total: 0,
        rept_start_date: [b' '; 10],
        rept_end_date: [b' '; 10],
    };

    let mut tran = TranRecord {
        tran_id: [b' '; 16],
        tran_type_cd: [b' '; 2],
        tran_cat_cd: 0,
        tran_source: [b' '; 10],
        tran_desc: [b' '; 100],
        tran_amt: 0,
        tran_merchant_id: 0,
        tran_merchant_name: [b' '; 50],
        tran_merchant_city: [b' '; 50],
        tran_merchant_zip: [b' '; 10],
        tran_card_num: [b' '; 16],
        tran_orig_ts: [b' '; 26],
        tran_proc_ts: [b' '; 26],
        filler1: [b' '; 20],
    };
    let mut xref = CardXrefRecord {
        xref_card_num: [b' '; 16],
        xref_cust_id: 0,
        xref_acct_id: 0,
        filler1: [b' '; 14],
    };
    let mut ttype = TranTypeRecord {
        tran_type: [b' '; 2],
        tran_type_desc: [b' '; 50],
        filler1: [b' '; 8],
    };
    let mut tcat = TranCatRecord {
        tran_type_cd: [b' '; 2],
        tran_cat_cd: 0,
        tran_cat_type_desc: [b' '; 50],
        filler1: [b' '; 4],
    };
    let mut dates = WsDateparmRecord {
        ws_start_date: [b' '; 10],
        filler1: [b' '; 1],
        ws_end_date: [b' '; 10],
    };

    let mut first_time = true;
    let mut curr_card: [u8; 16] = [b' '; 16];
    let mut end_of_file = false;
    let mut tran_idx: usize = 0;

    let mut s = Vec::new();
    push_bytes(&mut s, b"START OF EXECUTION OF PROGRAM CBTRN03C");
    st.displays.push(s);

    // 0550-DATEPARM-READ
    if date_parms_file.len() > 0 {
        dates = date_parms_file[0];
        let mut d = Vec::new();
        push_bytes(&mut d, b"Reporting from ");
        push_bytes(&mut d, &dates.ws_start_date);
        push_bytes(&mut d, b" to ");
        push_bytes(&mut d, &dates.ws_end_date);
        st.displays.push(d);
    } else {
        end_of_file = true;
    }

    while !end_of_file {
        // 1000-TRANFILE-GET-NEXT
        if tran_idx < transact_file.len() {
            tran = transact_file[tran_idx];
            tran_idx += 1;
        } else {
            end_of_file = true;
        }

        let ts = &tran.tran_proc_ts[0..10];
        let in_range = cmp_ebcdic(ts, &dates.ws_start_date) >= 0
            && cmp_ebcdic(ts, &dates.ws_end_date) <= 0;
        if !in_range {
            // NEXT SENTENCE: leaves the inline PERFORM
            break;
        }

        if !end_of_file {
            st.displays.push(tran_record_bytes(&tran));
            if !bytes_eq(&curr_card, &tran.tran_card_num) {
                if !first_time {
                    write_account_totals(&mut st);
                }
                curr_card = tran.tran_card_num;
                let key = tran.tran_card_num;
                let mut found = false;
                let mut i: usize = 0;
                while i < xref_file.len() {
                    if bytes_eq(&xref_file[i].xref_card_num, &key) {
                        xref = xref_file[i];
                        found = true;
                        break;
                    }
                    i += 1;
                }
                if !found {
                    let mut d = Vec::new();
                    push_bytes(&mut d, b"INVALID CARD NUMBER : ");
                    push_bytes(&mut d, &key);
                    st.displays.push(d);
                    abend_status23(&mut st);
                    return finish(st, true);
                }
            }

            let tkey = tran.tran_type_cd;
            let mut found = false;
            let mut i: usize = 0;
            while i < trantype_file.len() {
                if bytes_eq(&trantype_file[i].tran_type, &tkey) {
                    ttype = trantype_file[i];
                    found = true;
                    break;
                }
                i += 1;
            }
            if !found {
                let mut d = Vec::new();
                push_bytes(&mut d, b"INVALID TRANSACTION TYPE : ");
                push_bytes(&mut d, &tkey);
                st.displays.push(d);
                abend_status23(&mut st);
                return finish(st, true);
            }

            let ckey_type = tran.tran_type_cd;
            let ckey_cat = tran.tran_cat_cd;
            let mut found = false;
            let mut i: usize = 0;
            while i < trancatg_file.len() {
                if bytes_eq(&trancatg_file[i].tran_type_cd, &ckey_type)
                    && trancatg_file[i].tran_cat_cd == ckey_cat
                {
                    tcat = trancatg_file[i];
                    found = true;
                    break;
                }
                i += 1;
            }
            if !found {
                let mut d = Vec::new();
                push_bytes(&mut d, b"INVALID TRAN CATG KEY : ");
                push_bytes(&mut d, &ckey_type);
                push_digits(&mut d, ckey_cat, 4);
                st.displays.push(d);
                abend_status23(&mut st);
                return finish(st, true);
            }

            write_transaction_report(
                &mut st,
                &mut first_time,
                &dates,
                &tran,
                &xref,
                &ttype,
                &tcat,
            );
        } else {
            let mut d = Vec::new();
            push_bytes(&mut d, b"TRAN-AMT ");
            push_zoned_signed(&mut d, tran.tran_amt, 11);
            st.displays.push(d);
            let mut d2 = Vec::new();
            push_bytes(&mut d2, b"WS-PAGE-TOTAL");
            push_zoned_signed(&mut d2, st.page_total, 11);
            st.displays.push(d2);
            st.page_total = trunc11(st.page_total + tran.tran_amt);
            st.account_total = trunc11(st.account_total + tran.tran_amt);
            write_page_totals(&mut st);
            write_grand_totals(&mut st);
        }
    }

    let mut e = Vec::new();
    push_bytes(&mut e, b"END OF EXECUTION OF PROGRAM CBTRN03C");
    st.displays.push(e);

    finish(st, false)
}