// Translation of CardDemo batch program CBTRN02C (post daily transactions).

#[derive(Clone, Copy)]
pub struct DalytranRecord {
    pub dalytran_id: [u8; 16],
    pub dalytran_type_cd: [u8; 2],
    pub dalytran_cat_cd: i64,
    pub dalytran_source: [u8; 10],
    pub dalytran_desc: [u8; 100],
    pub dalytran_amt: i64,
    pub dalytran_merchant_id: i64,
    pub dalytran_merchant_name: [u8; 50],
    pub dalytran_merchant_city: [u8; 50],
    pub dalytran_merchant_zip: [u8; 10],
    pub dalytran_card_num: [u8; 16],
    pub dalytran_orig_ts: [u8; 26],
    pub dalytran_proc_ts: [u8; 26],
    pub filler1: [u8; 20],
}

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

#[derive(Clone, Copy)]
pub struct TranCatBalRecord {
    pub trancat_acct_id: i64,
    pub trancat_type_cd: [u8; 2],
    pub trancat_cd: i64,
    pub tran_cat_bal: i64,
    pub filler1: [u8; 22],
}

#[derive(Clone, Copy)]
pub struct RejectRecord {
    pub reject_tran_data: [u8; 350],
    pub validation_trailer: [u8; 80],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub transact_file_writes: Vec<TranRecord>,
    pub dalyrejs_file_writes: Vec<RejectRecord>,
    pub account_file_rewrites: Vec<AccountRecord>,
    pub tcatbal_file_writes: Vec<TranCatBalRecord>,
    pub tcatbal_file_rewrites: Vec<TranCatBalRecord>,
    pub return_code: i64,
    pub abended: bool,
}

const P9: i64 = 1_000_000_000;
const P11: i64 = 100_000_000_000;
const P12: i64 = 1_000_000_000_000;

// CP037: EBCDIC byte -> Latin-1 code point.
const EBC_DEC: [u8; 256] = [
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

// Latin-1 code point -> EBCDIC byte (CP037).
fn ebcdic(b: u8) -> u8 {
    let mut e: usize = 0;
    while e < 256 {
        if EBC_DEC[e] == b {
            return e as u8;
        }
        e += 1;
    }
    0
}

fn push_bytes(v: &mut Vec<u8>, s: &[u8]) {
    let mut i = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
    }
}

fn lit(s: &[u8]) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    push_bytes(&mut v, s);
    v
}

fn abs_u64(val: i64) -> u64 {
    if val < 0 {
        ((val + 1) * -1) as u64 + 1
    } else {
        val as u64
    }
}

// Unsigned display digits of |val| truncated to len digits.
fn digits(val: i64, len: usize) -> Vec<u8> {
    let mut m = abs_u64(val);
    let mut buf = [b'0'; 20];
    let mut k = 0;
    while k < len {
        buf[len - 1 - k] = b'0' + (m % 10) as u8;
        m /= 10;
        k += 1;
    }
    let mut v: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < len {
        v.push(buf[i]);
        i += 1;
    }
    v
}

// Signed zoned decimal with trailing overpunch sign.
fn signed_digits(val: i64, len: usize) -> Vec<u8> {
    let mut d = digits(val, len);
    let pos: [u8; 10] = *b"{ABCDEFGHI";
    let neg: [u8; 10] = *b"}JKLMNOPQR";
    let last = (d[len - 1] - b'0') as usize;
    if val < 0 {
        d[len - 1] = neg[last];
    } else {
        d[len - 1] = pos[last];
    }
    d
}

fn put(buf: &mut [u8], pos: usize, src: &[u8]) -> usize {
    let mut i = 0;
    while i < src.len() {
        buf[pos + i] = src[i];
        i += 1;
    }
    pos + src.len()
}

fn same(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

// a(1:n) >= b(1:n) as alphanumeric comparison (EBCDIC collating sequence)
fn ge_prefix(a: &[u8], b: &[u8], n: usize) -> bool {
    let mut i = 0;
    while i < n {
        let x = ebcdic(a[i]);
        let y = ebcdic(b[i]);
        if x > y {
            return true;
        }
        if x < y {
            return false;
        }
        i += 1;
    }
    true
}

fn alpha76(s: &[u8]) -> [u8; 76] {
    let mut r = [b' '; 76];
    let mut i = 0;
    while i < s.len() && i < 76 {
        r[i] = s[i];
        i += 1;
    }
    r
}

fn encode_dalytran(r: &DalytranRecord) -> [u8; 350] {
    let mut b = [b' '; 350];
    let mut p = 0usize;
    p = put(&mut b, p, &r.dalytran_id);
    p = put(&mut b, p, &r.dalytran_type_cd);
    p = put(&mut b, p, &digits(r.dalytran_cat_cd, 4));
    p = put(&mut b, p, &r.dalytran_source);
    p = put(&mut b, p, &r.dalytran_desc);
    p = put(&mut b, p, &signed_digits(r.dalytran_amt, 11));
    p = put(&mut b, p, &digits(r.dalytran_merchant_id, 9));
    p = put(&mut b, p, &r.dalytran_merchant_name);
    p = put(&mut b, p, &r.dalytran_merchant_city);
    p = put(&mut b, p, &r.dalytran_merchant_zip);
    p = put(&mut b, p, &r.dalytran_card_num);
    p = put(&mut b, p, &r.dalytran_orig_ts);
    p = put(&mut b, p, &r.dalytran_proc_ts);
    put(&mut b, p, &r.filler1);
    b
}

fn display_io_status(out: &mut Output, st: [u8; 2]) {
    let numeric = st[0] >= b'0' && st[0] <= b'9' && st[1] >= b'0' && st[1] <= b'9';
    let mut line = lit(b"FILE STATUS IS: NNNN");
    if !numeric || st[0] == b'9' {
        line.push(st[0]);
        let v = (ebcdic(st[1]) as i64) % 1000;
        push_bytes(&mut line, &digits(v, 3));
    } else {
        line.push(b'0');
        line.push(b'0');
        line.push(st[0]);
        line.push(st[1]);
    }
    out.displays.push(line);
}

fn abend(out: &mut Output) {
    out.displays.push(lit(b"ABENDING PROGRAM"));
    out.abended = true;
}

fn blank_dalytran() -> DalytranRecord {
    DalytranRecord {
        dalytran_id: [b' '; 16],
        dalytran_type_cd: [b' '; 2],
        dalytran_cat_cd: 0,
        dalytran_source: [b' '; 10],
        dalytran_desc: [b' '; 100],
        dalytran_amt: 0,
        dalytran_merchant_id: 0,
        dalytran_merchant_name: [b' '; 50],
        dalytran_merchant_city: [b' '; 50],
        dalytran_merchant_zip: [b' '; 10],
        dalytran_card_num: [b' '; 16],
        dalytran_orig_ts: [b' '; 26],
        dalytran_proc_ts: [b' '; 26],
        filler1: [b' '; 20],
    }
}

fn blank_tran() -> TranRecord {
    TranRecord {
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
    }
}

fn blank_xref() -> CardXrefRecord {
    CardXrefRecord {
        xref_card_num: [b' '; 16],
        xref_cust_id: 0,
        xref_acct_id: 0,
        filler1: [b' '; 14],
    }
}

fn blank_account() -> AccountRecord {
    AccountRecord {
        acct_id: 0,
        acct_active_status: [b' '; 1],
        acct_curr_bal: 0,
        acct_credit_limit: 0,
        acct_cash_credit_limit: 0,
        acct_open_date: [b' '; 10],
        acct_expiraion_date: [b' '; 10],
        acct_reissue_date: [b' '; 10],
        acct_curr_cyc_credit: 0,
        acct_curr_cyc_debit: 0,
        acct_addr_zip: [b' '; 10],
        acct_group_id: [b' '; 10],
        filler1: [b' '; 178],
    }
}

fn blank_tcatbal() -> TranCatBalRecord {
    TranCatBalRecord {
        trancat_acct_id: 0,
        trancat_type_cd: [b' '; 2],
        trancat_cd: 0,
        tran_cat_bal: 0,
        filler1: [b' '; 22],
    }
}

fn db2_timestamp(clock: &[u8; 21]) -> [u8; 26] {
    let mut ts = [b' '; 26];
    ts[0] = clock[0];
    ts[1] = clock[1];
    ts[2] = clock[2];
    ts[3] = clock[3];
    ts[4] = b'-';
    ts[5] = clock[4];
    ts[6] = clock[5];
    ts[7] = b'-';
    ts[8] = clock[6];
    ts[9] = clock[7];
    ts[10] = b'-';
    ts[11] = clock[8];
    ts[12] = clock[9];
    ts[13] = b'.';
    ts[14] = clock[10];
    ts[15] = clock[11];
    ts[16] = b'.';
    ts[17] = clock[12];
    ts[18] = clock[13];
    ts[19] = b'.';
    ts[20] = clock[14];
    ts[21] = clock[15];
    ts[22] = b'0';
    ts[23] = b'0';
    ts[24] = b'0';
    ts[25] = b'0';
    ts
}

pub fn run(
    dalytran_file: &[DalytranRecord],
    xref_file: &[CardXrefRecord],
    account_file: &[AccountRecord],
    tcatbal_file: &[TranCatBalRecord],
    clock: &[u8; 21],
) -> Output {
    let mut out = Output {
        displays: Vec::new(),
        transact_file_writes: Vec::new(),
        dalyrejs_file_writes: Vec::new(),
        account_file_rewrites: Vec::new(),
        tcatbal_file_writes: Vec::new(),
        tcatbal_file_rewrites: Vec::new(),
        return_code: 0,
        abended: false,
    };

    let mut accounts: Vec<AccountRecord> = Vec::new();
    let mut i = 0;
    while i < account_file.len() {
        accounts.push(account_file[i]);
        i += 1;
    }
    let mut tcatbals: Vec<TranCatBalRecord> = Vec::new();
    i = 0;
    while i < tcatbal_file.len() {
        tcatbals.push(tcatbal_file[i]);
        i += 1;
    }

    out.displays.push(lit(b"START OF EXECUTION OF PROGRAM CBTRN02C"));

    let mut dalytran_record = blank_dalytran();
    let mut card_xref_record = blank_xref();
    let mut account_record = blank_account();
    let mut tran_cat_bal_record = blank_tcatbal();
    let mut tran_record = blank_tran();

    let mut rd_pos: usize = 0;
    let mut end_of_file = false;
    let mut tx_count: i64 = 0;
    let mut rej_count: i64 = 0;
    let mut fail_reason: i64;
    let mut fail_desc: [u8; 76];

    while !end_of_file {
        if rd_pos < dalytran_file.len() {
            dalytran_record = dalytran_file[rd_pos];
            rd_pos += 1;
        } else {
            end_of_file = true;
            continue;
        }

        tx_count = (tx_count + 1) % P9;
        fail_reason = 0;
        fail_desc = [b' '; 76];

        // 1500-A-LOOKUP-XREF
        let mut xfound = false;
        let mut k = 0;
        while k < xref_file.len() {
            if same(&xref_file[k].xref_card_num, &dalytran_record.dalytran_card_num) {
                card_xref_record = xref_file[k];
                xfound = true;
                break;
            }
            k += 1;
        }
        if !xfound {
            fail_reason = 100;
            fail_desc = alpha76(b"INVALID CARD NUMBER FOUND");
        }

        if fail_reason == 0 {
            // 1500-B-LOOKUP-ACCT
            let key = card_xref_record.xref_acct_id;
            let mut afound = false;
            k = 0;
            while k < accounts.len() {
                if accounts[k].acct_id == key {
                    account_record = accounts[k];
                    afound = true;
                    break;
                }
                k += 1;
            }
            if !afound {
                fail_reason = 101;
                fail_desc = alpha76(b"ACCOUNT RECORD NOT FOUND");
            } else {
                let temp_bal = (account_record.acct_curr_cyc_credit
                    - account_record.acct_curr_cyc_debit
                    + dalytran_record.dalytran_amt)
                    % P11;
                if !(account_record.acct_credit_limit >= temp_bal) {
                    fail_reason = 102;
                    fail_desc = alpha76(b"OVERLIMIT TRANSACTION");
                }
                if !ge_prefix(
                    &account_record.acct_expiraion_date,
                    &dalytran_record.dalytran_orig_ts,
                    10,
                ) {
                    fail_reason = 103;
                    fail_desc = alpha76(b"TRANSACTION RECEIVED AFTER ACCT EXPIRATION");
                }
            }
        }

        if fail_reason == 0 {
            // 2000-POST-TRANSACTION
            tran_record.tran_id = dalytran_record.dalytran_id;
            tran_record.tran_type_cd = dalytran_record.dalytran_type_cd;
            tran_record.tran_cat_cd = dalytran_record.dalytran_cat_cd;
            tran_record.tran_source = dalytran_record.dalytran_source;
            tran_record.tran_desc = dalytran_record.dalytran_desc;
            tran_record.tran_amt = dalytran_record.dalytran_amt;
            tran_record.tran_merchant_id = dalytran_record.dalytran_merchant_id;
            tran_record.tran_merchant_name = dalytran_record.dalytran_merchant_name;
            tran_record.tran_merchant_city = dalytran_record.dalytran_merchant_city;
            tran_record.tran_merchant_zip = dalytran_record.dalytran_merchant_zip;
            tran_record.tran_card_num = dalytran_record.dalytran_card_num;
            tran_record.tran_orig_ts = dalytran_record.dalytran_orig_ts;
            tran_record.tran_proc_ts = db2_timestamp(clock);

            // 2700-UPDATE-TCATBAL
            let key_acct = card_xref_record.xref_acct_id;
            let key_type = dalytran_record.dalytran_type_cd;
            let key_cd = dalytran_record.dalytran_cat_cd;
            let mut create = false;
            let mut tfound = false;
            k = 0;
            while k < tcatbals.len() {
                let e = tcatbals[k];
                if e.trancat_acct_id == key_acct
                    && same(&e.trancat_type_cd, &key_type)
                    && e.trancat_cd == key_cd
                {
                    tran_cat_bal_record = e;
                    tfound = true;
                    break;
                }
                k += 1;
            }
            if !tfound {
                let mut line = lit(b"TCATBAL record not found for key : ");
                push_bytes(&mut line, &digits(key_acct, 11));
                push_bytes(&mut line, &key_type);
                push_bytes(&mut line, &digits(key_cd, 4));
                push_bytes(&mut line, b".. Creating.");
                out.displays.push(line);
                create = true;
            }

            if create {
                // 2700-A-CREATE-TCATBAL-REC (INITIALIZE leaves FILLER unchanged)
                tran_cat_bal_record.trancat_acct_id = 0;
                tran_cat_bal_record.trancat_type_cd = [b' '; 2];
                tran_cat_bal_record.trancat_cd = 0;
                tran_cat_bal_record.tran_cat_bal = 0;
                tran_cat_bal_record.trancat_acct_id = card_xref_record.xref_acct_id;
                tran_cat_bal_record.trancat_type_cd = dalytran_record.dalytran_type_cd;
                tran_cat_bal_record.trancat_cd = dalytran_record.dalytran_cat_cd;
                tran_cat_bal_record.tran_cat_bal =
                    (tran_cat_bal_record.tran_cat_bal + dalytran_record.dalytran_amt) % P11;
                let mut dup = false;
                k = 0;
                while k < tcatbals.len() {
                    let e = tcatbals[k];
                    if e.trancat_acct_id == tran_cat_bal_record.trancat_acct_id
                        && same(&e.trancat_type_cd, &tran_cat_bal_record.trancat_type_cd)
                        && e.trancat_cd == tran_cat_bal_record.trancat_cd
                    {
                        dup = true;
                        break;
                    }
                    k += 1;
                }
                if dup {
                    out.displays
                        .push(lit(b"ERROR WRITING TRANSACTION BALANCE FILE"));
                    display_io_status(&mut out, [b'2', b'2']);
                    abend(&mut out);
                    return out;
                }
                tcatbals.push(tran_cat_bal_record);
                out.tcatbal_file_writes.push(tran_cat_bal_record);
            } else {
                // 2700-B-UPDATE-TCATBAL-REC
                tran_cat_bal_record.tran_cat_bal =
                    (tran_cat_bal_record.tran_cat_bal + dalytran_record.dalytran_amt) % P11;
                let mut idx: usize = 0;
                let mut found = false;
                k = 0;
                while k < tcatbals.len() {
                    let e = tcatbals[k];
                    if e.trancat_acct_id == tran_cat_bal_record.trancat_acct_id
                        && same(&e.trancat_type_cd, &tran_cat_bal_record.trancat_type_cd)
                        && e.trancat_cd == tran_cat_bal_record.trancat_cd
                    {
                        idx = k;
                        found = true;
                        break;
                    }
                    k += 1;
                }
                if !found {
                    out.displays
                        .push(lit(b"ERROR REWRITING TRANSACTION BALANCE FILE"));
                    display_io_status(&mut out, [b'2', b'3']);
                    abend(&mut out);
                    return out;
                }
                tcatbals[idx] = tran_cat_bal_record;
                out.tcatbal_file_rewrites.push(tran_cat_bal_record);
            }

            // 2800-UPDATE-ACCOUNT-REC
            account_record.acct_curr_bal =
                (account_record.acct_curr_bal + dalytran_record.dalytran_amt) % P12;
            if dalytran_record.dalytran_amt >= 0 {
                account_record.acct_curr_cyc_credit =
                    (account_record.acct_curr_cyc_credit + dalytran_record.dalytran_amt) % P12;
            } else {
                account_record.acct_curr_cyc_debit =
                    (account_record.acct_curr_cyc_debit + dalytran_record.dalytran_amt) % P12;
            }
            let mut aidx: usize = 0;
            let mut afound2 = false;
            k = 0;
            while k < accounts.len() {
                if accounts[k].acct_id == account_record.acct_id {
                    aidx = k;
                    afound2 = true;
                    break;
                }
                k += 1;
            }
            if afound2 {
                accounts[aidx] = account_record;
                out.account_file_rewrites.push(account_record);
            } else {
                fail_reason = 109;
                fail_desc = alpha76(b"ACCOUNT RECORD NOT FOUND");
            }
            let _ = fail_reason;
            let _ = fail_desc;

            // 2900-WRITE-TRANSACTION-FILE
            let mut tdup = false;
            k = 0;
            while k < out.transact_file_writes.len() {
                if same(&out.transact_file_writes[k].tran_id, &tran_record.tran_id) {
                    tdup = true;
                    break;
                }
                k += 1;
            }
            if tdup {
                out.displays.push(lit(b"ERROR WRITING TO TRANSACTION FILE"));
                display_io_status(&mut out, [b'2', b'2']);
                abend(&mut out);
                return out;
            }
            out.transact_file_writes.push(tran_record);
        } else {
            rej_count = (rej_count + 1) % P9;
            // 2500-WRITE-REJECT-REC
            let mut trailer = [b' '; 80];
            let mut p = put(&mut trailer, 0, &digits(fail_reason, 4));
            p = put(&mut trailer, p, &fail_desc);
            let _ = p;
            let rec = RejectRecord {
                reject_tran_data: encode_dalytran(&dalytran_record),
                validation_trailer: trailer,
            };
            out.dalyrejs_file_writes.push(rec);
        }
    }

    let mut line = lit(b"TRANSACTIONS PROCESSED :");
    push_bytes(&mut line, &digits(tx_count, 9));
    out.displays.push(line);
    let mut line2 = lit(b"TRANSACTIONS REJECTED  :");
    push_bytes(&mut line2, &digits(rej_count, 9));
    out.displays.push(line2);
    if rej_count > 0 {
        out.return_code = 4;
    }
    out.displays.push(lit(b"END OF EXECUTION OF PROGRAM CBTRN02C"));
    out
}