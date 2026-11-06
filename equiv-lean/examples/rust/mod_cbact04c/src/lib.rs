#[derive(Clone, Copy)]
pub struct TranCatBalRecord {
    pub trancat_acct_id: i64,
    pub trancat_type_cd: [u8; 2],
    pub trancat_cd: i64,
    pub tran_cat_bal: i64,
    pub filler1: [u8; 22],
}

#[derive(Clone, Copy)]
pub struct CardXrefRecord {
    pub xref_card_num: [u8; 16],
    pub xref_cust_id: i64,
    pub xref_acct_id: i64,
    pub filler1: [u8; 14],
}

#[derive(Clone, Copy)]
pub struct DisGroupRecord {
    pub dis_acct_group_id: [u8; 10],
    pub dis_tran_type_cd: [u8; 2],
    pub dis_tran_cat_cd: i64,
    pub dis_int_rate: i64,
    pub filler1: [u8; 28],
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
pub struct ExternalParms {
    pub parm_length: i64,
    pub parm_date: [u8; 10],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub transact_file_writes: Vec<TranRecord>,
    pub account_file_rewrites: Vec<AccountRecord>,
    pub abended: bool,
}

struct State {
    accounts: Vec<AccountRecord>,
    tran_cat_bal_record: TranCatBalRecord,
    card_xref_record: CardXrefRecord,
    dis_group_record: DisGroupRecord,
    account_record: AccountRecord,
    tran_record: TranRecord,
    last_acct_set: bool,
    last_acct: i64,
    first_time: bool,
    total_int: i64,
    tranid_suffix: i64,
}

fn to_vec(s: &[u8]) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
    }
    v
}

fn push_bytes(v: &mut Vec<u8>, s: &[u8]) {
    let mut i: usize = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
    }
}

fn eq10(a: &[u8; 10], b: &[u8; 10]) -> bool {
    let mut eq = true;
    let mut i: usize = 0;
    while i < 10 {
        if a[i] != b[i] {
            eq = false;
        }
        i += 1;
    }
    eq
}

fn eq2(a: &[u8; 2], b: &[u8; 2]) -> bool {
    a[0] == b[0] && a[1] == b[1]
}

// ---------------------------------------------------------------- texts

fn m_start() -> Vec<u8> {
    let a = [
        b'S', b'T', b'A', b'R', b'T', b' ', b'O', b'F', b' ', b'E', b'X', b'E', b'C', b'U',
        b'T', b'I', b'O', b'N', b' ', b'O', b'F', b' ', b'P', b'R', b'O', b'G', b'R', b'A',
        b'M', b' ', b'C', b'B', b'A', b'C', b'T', b'0', b'4', b'C',
    ];
    to_vec(&a)
}

fn m_end() -> Vec<u8> {
    let a = [
        b'E', b'N', b'D', b' ', b'O', b'F', b' ', b'E', b'X', b'E', b'C', b'U', b'T', b'I',
        b'O', b'N', b' ', b'O', b'F', b' ', b'P', b'R', b'O', b'G', b'R', b'A', b'M', b' ',
        b'C', b'B', b'A', b'C', b'T', b'0', b'4', b'C',
    ];
    to_vec(&a)
}

fn m_abending() -> Vec<u8> {
    let a = [
        b'A', b'B', b'E', b'N', b'D', b'I', b'N', b'G', b' ', b'P', b'R', b'O', b'G', b'R',
        b'A', b'M',
    ];
    to_vec(&a)
}

fn m_file_status() -> Vec<u8> {
    let a = [
        b'F', b'I', b'L', b'E', b' ', b'S', b'T', b'A', b'T', b'U', b'S', b' ', b'I', b'S',
        b':', b' ', b'N', b'N', b'N', b'N',
    ];
    to_vec(&a)
}

fn m_err_rewrite_acct() -> Vec<u8> {
    let a = [
        b'E', b'R', b'R', b'O', b'R', b' ', b'R', b'E', b'-', b'W', b'R', b'I', b'T', b'I',
        b'N', b'G', b' ', b'A', b'C', b'C', b'O', b'U', b'N', b'T', b' ', b'F', b'I', b'L',
        b'E',
    ];
    to_vec(&a)
}

fn m_acct_not_found() -> Vec<u8> {
    let a = [
        b'A', b'C', b'C', b'O', b'U', b'N', b'T', b' ', b'N', b'O', b'T', b' ', b'F', b'O',
        b'U', b'N', b'D', b':', b' ',
    ];
    to_vec(&a)
}

fn m_err_read_acct() -> Vec<u8> {
    let a = [
        b'E', b'R', b'R', b'O', b'R', b' ', b'R', b'E', b'A', b'D', b'I', b'N', b'G', b' ',
        b'A', b'C', b'C', b'O', b'U', b'N', b'T', b' ', b'F', b'I', b'L', b'E',
    ];
    to_vec(&a)
}

fn m_err_read_xref() -> Vec<u8> {
    let a = [
        b'E', b'R', b'R', b'O', b'R', b' ', b'R', b'E', b'A', b'D', b'I', b'N', b'G', b' ',
        b'X', b'R', b'E', b'F', b' ', b'F', b'I', b'L', b'E',
    ];
    to_vec(&a)
}

fn m_disc_missing() -> Vec<u8> {
    let a = [
        b'D', b'I', b'S', b'C', b'L', b'O', b'S', b'U', b'R', b'E', b' ', b'G', b'R', b'O',
        b'U', b'P', b' ', b'R', b'E', b'C', b'O', b'R', b'D', b' ', b'M', b'I', b'S', b'S',
        b'I', b'N', b'G',
    ];
    to_vec(&a)
}

fn m_try_default() -> Vec<u8> {
    let a = [
        b'T', b'R', b'Y', b' ', b'W', b'I', b'T', b'H', b' ', b'D', b'E', b'F', b'A', b'U',
        b'L', b'T', b' ', b'G', b'R', b'O', b'U', b'P', b' ', b'C', b'O', b'D', b'E',
    ];
    to_vec(&a)
}

fn m_err_default_disc() -> Vec<u8> {
    let a = [
        b'E', b'R', b'R', b'O', b'R', b' ', b'R', b'E', b'A', b'D', b'I', b'N', b'G', b' ',
        b'D', b'E', b'F', b'A', b'U', b'L', b'T', b' ', b'D', b'I', b'S', b'C', b'L', b'O',
        b'S', b'U', b'R', b'E', b' ', b'G', b'R', b'O', b'U', b'P',
    ];
    to_vec(&a)
}

// ---------------------------------------------------------------- numbers

fn abs_u64(val: i64) -> u64 {
    if val < 0 {
        ((-(val + 1)) as u64) + 1
    } else {
        val as u64
    }
}

fn pow10(n: u32) -> i64 {
    let mut p: i64 = 1;
    let mut i: u32 = 0;
    while i < n {
        p = p * 10;
        i += 1;
    }
    p
}

// High-order truncation to n digits, sign kept.
fn trunc_digits(val: i64, n: u32) -> i64 {
    val % pow10(n)
}

// Unsigned zoned display digits (n digits).
fn digits_of(val: i64, n: usize) -> Vec<u8> {
    let mut a = abs_u64(val);
    let mut tmp: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        tmp.push(b'0' + (a % 10) as u8);
        a = a / 10;
        i += 1;
    }
    let mut v: Vec<u8> = Vec::new();
    let mut j: usize = n;
    while j > 0 {
        j -= 1;
        v.push(tmp[j]);
    }
    v
}

fn push_digits(v: &mut Vec<u8>, val: i64, n: usize) {
    let d = digits_of(val, n);
    let mut i: usize = 0;
    while i < d.len() {
        v.push(d[i]);
        i += 1;
    }
}

// Signed zoned display with trailing overpunch sign.
fn push_signed(v: &mut Vec<u8>, val: i64, n: usize) {
    let d = digits_of(val, n);
    let neg = val < 0;
    let mut i: usize = 0;
    while i < n {
        if i + 1 == n {
            let dg = d[i] - b'0';
            let c = if neg {
                if dg == 0 {
                    b'}'
                } else {
                    b'J' + dg - 1
                }
            } else if dg == 0 {
                b'{'
            } else {
                b'A' + dg - 1
            };
            v.push(c);
        } else {
            v.push(d[i]);
        }
        i += 1;
    }
}

fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

fn status_line(s0: u8, s1: u8) -> Vec<u8> {
    let mut v = m_file_status();
    let numeric = is_digit(s0) && is_digit(s1);
    if !numeric || s0 == b'9' {
        v.push(s0);
        let n = (s1 as i64) % 1000;
        push_digits(&mut v, n, 3);
    } else {
        v.push(b'0');
        v.push(b'0');
        v.push(s0);
        v.push(s1);
    }
    v
}

fn abend(out: &mut Output, msg: Vec<u8>, s0: u8, s1: u8) {
    out.displays.push(msg);
    out.displays.push(status_line(s0, s1));
    out.displays.push(m_abending());
    out.abended = true;
}

fn display_tcat(r: &TranCatBalRecord) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    push_digits(&mut v, r.trancat_acct_id, 11);
    push_bytes(&mut v, &r.trancat_type_cd);
    push_digits(&mut v, r.trancat_cd, 4);
    push_signed(&mut v, r.tran_cat_bal, 11);
    push_bytes(&mut v, &r.filler1);
    v
}

// ---------------------------------------------------------------- lookups
// Each returns the index of the first match, or the length when not found.

fn find_account(accounts: &Vec<AccountRecord>, id: i64) -> usize {
    let n = accounts.len();
    let mut result: usize = n;
    let mut i: usize = 0;
    while i < n {
        let r = accounts[i];
        if result == n {
            if r.acct_id == id {
                result = i;
            }
        }
        i += 1;
    }
    result
}

fn find_xref(xref_file: &[CardXrefRecord], acct_id: i64) -> usize {
    let n = xref_file.len();
    let mut result: usize = n;
    let mut i: usize = 0;
    while i < n {
        let r = xref_file[i];
        if result == n {
            if r.xref_acct_id == acct_id {
                result = i;
            }
        }
        i += 1;
    }
    result
}

fn find_disc(
    discgrp_file: &[DisGroupRecord],
    group: &[u8; 10],
    typ: &[u8; 2],
    cat: i64,
) -> usize {
    let n = discgrp_file.len();
    let mut result: usize = n;
    let mut i: usize = 0;
    while i < n {
        let r = discgrp_file[i];
        if result == n {
            let g = r.dis_acct_group_id;
            let t = r.dis_tran_type_cd;
            if eq10(&g, group) {
                if eq2(&t, typ) {
                    if r.dis_tran_cat_cd == cat {
                        result = i;
                    }
                }
            }
        }
        i += 1;
    }
    result
}

// ---------------------------------------------------------------- paragraphs

// 1050-UPDATE-ACCOUNT. Returns false if the program abended.
fn update_account(st: &mut State, out: &mut Output) -> bool {
    let mut a = st.account_record;
    a.acct_curr_bal = trunc_digits(a.acct_curr_bal + st.total_int, 12);
    a.acct_curr_cyc_credit = 0;
    a.acct_curr_cyc_debit = 0;
    st.account_record = a;
    let idx = find_account(&st.accounts, a.acct_id);
    if idx < st.accounts.len() {
        st.accounts[idx] = a;
        out.account_file_rewrites.push(a);
        true
    } else {
        abend(out, m_err_rewrite_acct(), b'2', b'3');
        false
    }
}

fn make_timestamp(clock: &[u8; 21]) -> [u8; 26] {
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

// 1300-B-WRITE-TX record construction.
fn build_tran(
    prev: TranRecord,
    parm_date: &[u8; 10],
    suffix: i64,
    acct_id: i64,
    monthly_int: i64,
    card_num: [u8; 16],
    clock: &[u8; 21],
) -> TranRecord {
    let mut t = prev;
    let mut tid = [b' '; 16];
    let mut p: usize = 0;
    while p < 10 {
        tid[p] = parm_date[p];
        p += 1;
    }
    let sd = digits_of(suffix, 6);
    let mut q: usize = 0;
    while q < 6 {
        tid[10 + q] = sd[q];
        q += 1;
    }
    t.tran_id = tid;
    t.tran_type_cd = [b'0', b'1'];
    t.tran_cat_cd = 5;
    t.tran_source = [b'S', b'y', b's', b't', b'e', b'm', b' ', b' ', b' ', b' '];
    let prefix = [
        b'I', b'n', b't', b'.', b' ', b'f', b'o', b'r', b' ', b'a', b'/', b'c', b' ',
    ];
    let mut desc = t.tran_desc;
    let mut x: usize = 0;
    while x < 13 {
        desc[x] = prefix[x];
        x += 1;
    }
    let ad = digits_of(acct_id, 11);
    let mut y: usize = 0;
    while y < 11 {
        desc[13 + y] = ad[y];
        y += 1;
    }
    t.tran_desc = desc;
    t.tran_amt = monthly_int;
    t.tran_merchant_id = 0;
    t.tran_merchant_name = [b' '; 50];
    t.tran_merchant_city = [b' '; 50];
    t.tran_merchant_zip = [b' '; 10];
    t.tran_card_num = card_num;
    let ts = make_timestamp(clock);
    t.tran_orig_ts = ts;
    t.tran_proc_ts = ts;
    t
}

// Processing of one TCATBAL record. Returns false if the program abended.
fn process_record(
    st: &mut State,
    xref_file: &[CardXrefRecord],
    discgrp_file: &[DisGroupRecord],
    parms: &ExternalParms,
    clock: &[u8; 21],
    out: &mut Output,
) -> bool {
    let rec = st.tran_cat_bal_record;
    out.displays.push(display_tcat(&rec));
    if !st.last_acct_set || rec.trancat_acct_id != st.last_acct {
        if st.first_time {
            st.first_time = false;
        } else {
            if !update_account(st, out) {
                return false;
            }
        }
        st.total_int = 0;
        st.last_acct = rec.trancat_acct_id;
        st.last_acct_set = true;
        // 1100-GET-ACCT-DATA
        let fd_acct_id = rec.trancat_acct_id;
        let idx = find_account(&st.accounts, fd_acct_id);
        if idx >= st.accounts.len() {
            let mut v = m_acct_not_found();
            push_digits(&mut v, fd_acct_id, 11);
            out.displays.push(v);
            abend(out, m_err_read_acct(), b'2', b'3');
            return false;
        }
        st.account_record = st.accounts[idx];
        // 1110-GET-XREF-DATA
        let fd_xref_acct_id = rec.trancat_acct_id;
        let xidx = find_xref(xref_file, fd_xref_acct_id);
        if xidx >= xref_file.len() {
            let mut v = m_acct_not_found();
            push_digits(&mut v, fd_xref_acct_id, 11);
            out.displays.push(v);
            abend(out, m_err_read_xref(), b'2', b'3');
            return false;
        }
        st.card_xref_record = xref_file[xidx];
    }
    // 1200-GET-INTEREST-RATE
    let group = st.account_record.acct_group_id;
    let typ = rec.trancat_type_cd;
    let cat = rec.trancat_cd;
    let didx = find_disc(discgrp_file, &group, &typ, cat);
    if didx < discgrp_file.len() {
        st.dis_group_record = discgrp_file[didx];
    } else {
        out.displays.push(m_disc_missing());
        out.displays.push(m_try_default());
        let def = [b'D', b'E', b'F', b'A', b'U', b'L', b'T', b' ', b' ', b' '];
        // 1200-A-GET-DEFAULT-INT-RATE
        let didx2 = find_disc(discgrp_file, &def, &typ, cat);
        if didx2 >= discgrp_file.len() {
            abend(out, m_err_default_disc(), b'2', b'3');
            return false;
        }
        st.dis_group_record = discgrp_file[didx2];
    }
    if st.dis_group_record.dis_int_rate != 0 {
        // 1300-COMPUTE-INTEREST
        let monthly_int = trunc_digits(
            (rec.tran_cat_bal * st.dis_group_record.dis_int_rate) / 120000,
            11,
        );
        st.total_int = trunc_digits(st.total_int + monthly_int, 11);
        // 1300-B-WRITE-TX
        st.tranid_suffix = (st.tranid_suffix + 1) % 1000000;
        let t = build_tran(
            st.tran_record,
            &parms.parm_date,
            st.tranid_suffix,
            st.account_record.acct_id,
            monthly_int,
            st.card_xref_record.xref_card_num,
            clock,
        );
        st.tran_record = t;
        out.transact_file_writes.push(t);
        // 1400-COMPUTE-FEES: not implemented
    }
    true
}

pub fn run(
    tcatbal_file: &[TranCatBalRecord],
    xref_file: &[CardXrefRecord],
    account_file: &[AccountRecord],
    discgrp_file: &[DisGroupRecord],
    external_parms: &ExternalParms,
    clock: &[u8; 21],
) -> Output {
    let mut out = Output {
        displays: Vec::new(),
        transact_file_writes: Vec::new(),
        account_file_rewrites: Vec::new(),
        abended: false,
    };

    let mut accounts: Vec<AccountRecord> = Vec::new();
    let mut k: usize = 0;
    while k < account_file.len() {
        accounts.push(account_file[k]);
        k += 1;
    }

    let mut st = State {
        accounts: accounts,
        tran_cat_bal_record: TranCatBalRecord {
            trancat_acct_id: 0,
            trancat_type_cd: [b' '; 2],
            trancat_cd: 0,
            tran_cat_bal: 0,
            filler1: [b' '; 22],
        },
        card_xref_record: CardXrefRecord {
            xref_card_num: [b' '; 16],
            xref_cust_id: 0,
            xref_acct_id: 0,
            filler1: [b' '; 14],
        },
        dis_group_record: DisGroupRecord {
            dis_acct_group_id: [b' '; 10],
            dis_tran_type_cd: [b' '; 2],
            dis_tran_cat_cd: 0,
            dis_int_rate: 0,
            filler1: [b' '; 28],
        },
        account_record: AccountRecord {
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
        },
        tran_record: TranRecord {
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
        },
        last_acct_set: false,
        last_acct: 0,
        first_time: true,
        total_int: 0,
        tranid_suffix: 0,
    };

    out.displays.push(m_start());
    // All OPENs succeed.

    let mut end_of_file = false;
    let mut stop = false;
    let mut pos: usize = 0;
    while !end_of_file && !stop {
        // 1000-TCATBALF-GET-NEXT
        if pos < tcatbal_file.len() {
            st.tran_cat_bal_record = tcatbal_file[pos];
            pos += 1;
            if !process_record(
                &mut st,
                xref_file,
                discgrp_file,
                external_parms,
                clock,
                &mut out,
            ) {
                stop = true;
            }
        } else {
            end_of_file = true;
        }
    }

    if !stop {
        // All CLOSEs succeed.
        out.displays.push(m_end());
    }
    out
}