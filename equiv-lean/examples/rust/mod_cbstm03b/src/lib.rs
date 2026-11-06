#[derive(Clone, Copy)]
pub struct FdTrnxfileRec {
    pub fd_trnx_card: [u8; 16],
    pub fd_trnx_id: [u8; 16],
    pub fd_acct_data: [u8; 318],
}

#[derive(Clone, Copy)]
pub struct FdXreffileRec {
    pub fd_xref_card_num: [u8; 16],
    pub fd_xref_data: [u8; 34],
}

#[derive(Clone, Copy)]
pub struct FdCustfileRec {
    pub fd_cust_id: [u8; 9],
    pub fd_cust_data: [u8; 491],
}

#[derive(Clone, Copy)]
pub struct FdAcctfileRec {
    pub fd_acct_id: i64,
    pub fd_acct_data: [u8; 289],
}

#[derive(Clone, Copy)]
pub struct LkM03bArea {
    pub lk_m03b_dd: [u8; 8],
    pub lk_m03b_oper: [u8; 1],
    pub lk_m03b_rc: [u8; 2],
    pub lk_m03b_key: [u8; 25],
    pub lk_m03b_key_ln: i64,
    pub lk_m03b_fldt: [u8; 1000],
}

pub struct TrnxFile {
    pub open: bool,
    pub recs: Vec<FdTrnxfileRec>,
    pub pos: usize,
    pub eof: bool,
}

pub struct XrefFile {
    pub open: bool,
    pub recs: Vec<FdXreffileRec>,
    pub pos: usize,
    pub eof: bool,
}

pub struct CustFile {
    pub open: bool,
    pub recs: Vec<FdCustfileRec>,
    pub pos: usize,
    pub eof: bool,
}

pub struct AcctFile {
    pub open: bool,
    pub recs: Vec<FdAcctfileRec>,
    pub pos: usize,
    pub eof: bool,
}

pub struct State {
    pub trnx_file: TrnxFile,
    pub xref_file: XrefFile,
    pub cust_file: CustFile,
    pub acct_file: AcctFile,
    pub fd_trnxfile_rec: FdTrnxfileRec,
    pub fd_xreffile_rec: FdXreffileRec,
    pub fd_custfile_rec: FdCustfileRec,
    pub fd_acctfile_rec: FdAcctfileRec,
    pub trnxfile_status: [u8; 2],
    pub xreffile_status: [u8; 2],
    pub custfile_status: [u8; 2],
    pub acctfile_status: [u8; 2],
}

const ACCT_MOD: i64 = 100_000_000_000;
const NO_ERR: u8 = 255;

fn fmt_status(c: u8) -> [u8; 2] {
    [b'0' + (c / 10) % 10, b'0' + c % 10]
}

fn open_err_code(err: Option<u8>) -> u8 {
    match err {
        Some(c) => c,
        None => NO_ERR,
    }
}

fn eq8(a: [u8; 8], b: [u8; 8]) -> bool {
    let mut eq = true;
    let mut i: usize = 0;
    while i < 8 {
        if a[i] != b[i] {
            eq = false;
        }
        i += 1;
    }
    eq
}

fn eq9(a: [u8; 9], b: [u8; 9]) -> bool {
    let mut eq = true;
    let mut i: usize = 0;
    while i < 9 {
        if a[i] != b[i] {
            eq = false;
        }
        i += 1;
    }
    eq
}

/// Display form of LK-M03B-KEY-LN (PIC S9(4)), sign overpunched in the last digit.
fn key_ln_display(v: i64) -> [u8; 4] {
    let neg = v < 0;
    let mut a = if neg { 0 - v } else { v };
    a = a % 10000;
    let mut out = [b'0'; 4];
    let mut i: usize = 4;
    while i > 0 {
        i -= 1;
        out[i] = b'0' + (a % 10) as u8;
        a = a / 10;
    }
    let d = out[3] - b'0';
    if neg {
        if d == 0 {
            out[3] = b'}';
        } else {
            out[3] = b'J' + (d - 1);
        }
    } else {
        if d == 0 {
            out[3] = b'{';
        } else {
            out[3] = b'A' + (d - 1);
        }
    }
    out
}

/// Byte at offset i starting from LK-M03B-KEY in the linkage area.
fn key_byte(area: &LkM03bArea, i: usize) -> u8 {
    if i < 25 {
        area.lk_m03b_key[i]
    } else if i < 29 {
        let d = key_ln_display(area.lk_m03b_key_ln);
        d[i - 25]
    } else if i < 1029 {
        area.lk_m03b_fldt[i - 29]
    } else {
        b' '
    }
}

/// MOVE LK-M03B-KEY (1:LK-M03B-KEY-LN) TO FD-CUST-ID
fn cust_key(area: &LkM03bArea) -> [u8; 9] {
    let k = area.lk_m03b_key_ln as usize;
    let mut id = [b' '; 9];
    let mut j: usize = 0;
    while j < 9 {
        if j < k {
            id[j] = key_byte(area, j);
        }
        j += 1;
    }
    id
}

/// MOVE LK-M03B-KEY (1:LK-M03B-KEY-LN) TO FD-ACCT-ID
fn acct_key(area: &LkM03bArea) -> i64 {
    let k = area.lk_m03b_key_ln as usize;
    let start = if k > 11 { k - 11 } else { 0 };
    let mut val: i64 = 0;
    let mut i = start;
    while i < k {
        let b = key_byte(area, i);
        let d = (b & 0x0F) as i64;
        val = (val * 10 + d) % ACCT_MOD;
        i += 1;
    }
    val
}

fn cust_id_at(recs: &Vec<FdCustfileRec>, i: usize) -> [u8; 9] {
    recs[i].fd_cust_id
}

fn acct_id_at(recs: &Vec<FdAcctfileRec>, i: usize) -> i64 {
    recs[i].fd_acct_id
}

/// Returns index of first match, or recs.len() if none.
fn find_cust(recs: &Vec<FdCustfileRec>, id: [u8; 9]) -> usize {
    let n = recs.len();
    let mut idx: usize = n;
    let mut i: usize = 0;
    while i < n {
        if idx == n {
            let k = cust_id_at(recs, i);
            if eq9(k, id) {
                idx = i;
            }
        }
        i += 1;
    }
    idx
}

/// Returns index of first match, or recs.len() if none.
fn find_acct(recs: &Vec<FdAcctfileRec>, key: i64) -> usize {
    let n = recs.len();
    let mut idx: usize = n;
    let mut i: usize = 0;
    while i < n {
        if idx == n {
            let k = acct_id_at(recs, i);
            if k == key {
                idx = i;
            }
        }
        i += 1;
    }
    idx
}

fn trnx_image(r: &FdTrnxfileRec) -> [u8; 1000] {
    let mut out = [b' '; 1000];
    let mut i: usize = 0;
    while i < 16 {
        out[i] = r.fd_trnx_card[i];
        i += 1;
    }
    i = 0;
    while i < 16 {
        out[16 + i] = r.fd_trnx_id[i];
        i += 1;
    }
    i = 0;
    while i < 318 {
        out[32 + i] = r.fd_acct_data[i];
        i += 1;
    }
    out
}

fn xref_image(r: &FdXreffileRec) -> [u8; 1000] {
    let mut out = [b' '; 1000];
    let mut i: usize = 0;
    while i < 16 {
        out[i] = r.fd_xref_card_num[i];
        i += 1;
    }
    i = 0;
    while i < 34 {
        out[16 + i] = r.fd_xref_data[i];
        i += 1;
    }
    out
}

fn cust_image(r: &FdCustfileRec) -> [u8; 1000] {
    let mut out = [b' '; 1000];
    let mut i: usize = 0;
    while i < 9 {
        out[i] = r.fd_cust_id[i];
        i += 1;
    }
    i = 0;
    while i < 491 {
        out[9 + i] = r.fd_cust_data[i];
        i += 1;
    }
    out
}

fn acct_image(r: &FdAcctfileRec) -> [u8; 1000] {
    let mut out = [b' '; 1000];
    let mut v = r.fd_acct_id % ACCT_MOD;
    if v < 0 {
        v = 0 - v;
    }
    let mut i: usize = 11;
    while i > 0 {
        i -= 1;
        out[i] = b'0' + (v % 10) as u8;
        v = v / 10;
    }
    i = 0;
    while i < 289 {
        out[11 + i] = r.fd_acct_data[i];
        i += 1;
    }
    out
}

fn trnx_proc(err_code: u8, st: &mut State, area: &mut LkM03bArea) {
    let op = area.lk_m03b_oper[0];
    if op == b'O' {
        let mut s: [u8; 2] = *b"00";
        if st.trnx_file.open {
            s = *b"41";
        } else if err_code != NO_ERR {
            s = fmt_status(err_code);
        } else {
            st.trnx_file.open = true;
            st.trnx_file.pos = 0;
            st.trnx_file.eof = false;
        }
        st.trnxfile_status = s;
    } else if op == b'R' {
        let mut s: [u8; 2] = *b"00";
        if !st.trnx_file.open {
            s = *b"47";
        } else if st.trnx_file.eof {
            s = *b"46";
        } else if st.trnx_file.pos >= st.trnx_file.recs.len() {
            st.trnx_file.eof = true;
            s = *b"10";
        } else {
            let r = st.trnx_file.recs[st.trnx_file.pos];
            st.trnx_file.pos += 1;
            st.fd_trnxfile_rec = r;
            area.lk_m03b_fldt = trnx_image(&r);
        }
        st.trnxfile_status = s;
    } else if op == b'C' {
        let mut s: [u8; 2] = *b"00";
        if !st.trnx_file.open {
            s = *b"42";
        } else {
            st.trnx_file.open = false;
        }
        st.trnxfile_status = s;
    }
    area.lk_m03b_rc = st.trnxfile_status;
}

fn xref_proc(err_code: u8, st: &mut State, area: &mut LkM03bArea) {
    let op = area.lk_m03b_oper[0];
    if op == b'O' {
        let mut s: [u8; 2] = *b"00";
        if st.xref_file.open {
            s = *b"41";
        } else if err_code != NO_ERR {
            s = fmt_status(err_code);
        } else {
            st.xref_file.open = true;
            st.xref_file.pos = 0;
            st.xref_file.eof = false;
        }
        st.xreffile_status = s;
    } else if op == b'R' {
        let mut s: [u8; 2] = *b"00";
        if !st.xref_file.open {
            s = *b"47";
        } else if st.xref_file.eof {
            s = *b"46";
        } else if st.xref_file.pos >= st.xref_file.recs.len() {
            st.xref_file.eof = true;
            s = *b"10";
        } else {
            let r = st.xref_file.recs[st.xref_file.pos];
            st.xref_file.pos += 1;
            st.fd_xreffile_rec = r;
            area.lk_m03b_fldt = xref_image(&r);
        }
        st.xreffile_status = s;
    } else if op == b'C' {
        let mut s: [u8; 2] = *b"00";
        if !st.xref_file.open {
            s = *b"42";
        } else {
            st.xref_file.open = false;
        }
        st.xreffile_status = s;
    }
    area.lk_m03b_rc = st.xreffile_status;
}

fn cust_proc(err_code: u8, st: &mut State, area: &mut LkM03bArea) {
    let op = area.lk_m03b_oper[0];
    if op == b'O' {
        let mut s: [u8; 2] = *b"00";
        if st.cust_file.open {
            s = *b"41";
        } else if err_code != NO_ERR {
            s = fmt_status(err_code);
        } else {
            st.cust_file.open = true;
            st.cust_file.pos = 0;
            st.cust_file.eof = false;
        }
        st.custfile_status = s;
    } else if op == b'K' {
        let id = cust_key(area);
        st.fd_custfile_rec.fd_cust_id = id;
        let mut s: [u8; 2] = *b"00";
        if !st.cust_file.open {
            s = *b"47";
        } else {
            let n = st.cust_file.recs.len();
            let idx = find_cust(&st.cust_file.recs, id);
            if idx >= n {
                s = *b"23";
            } else {
                let r = st.cust_file.recs[idx];
                st.cust_file.pos = idx + 1;
                st.cust_file.eof = false;
                st.fd_custfile_rec = r;
                area.lk_m03b_fldt = cust_image(&r);
            }
        }
        st.custfile_status = s;
    } else if op == b'C' {
        let mut s: [u8; 2] = *b"00";
        if !st.cust_file.open {
            s = *b"42";
        } else {
            st.cust_file.open = false;
        }
        st.custfile_status = s;
    }
    area.lk_m03b_rc = st.custfile_status;
}

fn acct_proc(err_code: u8, st: &mut State, area: &mut LkM03bArea) {
    let op = area.lk_m03b_oper[0];
    if op == b'O' {
        let mut s: [u8; 2] = *b"00";
        if st.acct_file.open {
            s = *b"41";
        } else if err_code != NO_ERR {
            s = fmt_status(err_code);
        } else {
            st.acct_file.open = true;
            st.acct_file.pos = 0;
            st.acct_file.eof = false;
        }
        st.acctfile_status = s;
    } else if op == b'K' {
        let val = acct_key(area);
        st.fd_acctfile_rec.fd_acct_id = val;
        let mut s: [u8; 2] = *b"00";
        if !st.acct_file.open {
            s = *b"47";
        } else {
            let n = st.acct_file.recs.len();
            let idx = find_acct(&st.acct_file.recs, val);
            if idx >= n {
                s = *b"23";
            } else {
                let r = st.acct_file.recs[idx];
                st.acct_file.pos = idx + 1;
                st.acct_file.eof = false;
                st.fd_acctfile_rec = r;
                area.lk_m03b_fldt = acct_image(&r);
            }
        }
        st.acctfile_status = s;
    } else if op == b'C' {
        let mut s: [u8; 2] = *b"00";
        if !st.acct_file.open {
            s = *b"42";
        } else {
            st.acct_file.open = false;
        }
        st.acctfile_status = s;
    }
    area.lk_m03b_rc = st.acctfile_status;
}

pub fn call(open_errors: &[Option<u8>; 4], st: &mut State, area: &mut LkM03bArea) {
    let dd = area.lk_m03b_dd;
    let trnx: [u8; 8] = [b'T', b'R', b'N', b'X', b'F', b'I', b'L', b'E'];
    let xref: [u8; 8] = [b'X', b'R', b'E', b'F', b'F', b'I', b'L', b'E'];
    let cust: [u8; 8] = [b'C', b'U', b'S', b'T', b'F', b'I', b'L', b'E'];
    let acct: [u8; 8] = [b'A', b'C', b'C', b'T', b'F', b'I', b'L', b'E'];
    if eq8(dd, trnx) {
        let e: Option<u8> = open_errors[0];
        let c = open_err_code(e);
        trnx_proc(c, st, area);
    } else if eq8(dd, xref) {
        let e: Option<u8> = open_errors[1];
        let c = open_err_code(e);
        xref_proc(c, st, area);
    } else if eq8(dd, cust) {
        let e: Option<u8> = open_errors[2];
        let c = open_err_code(e);
        cust_proc(c, st, area);
    } else if eq8(dd, acct) {
        let e: Option<u8> = open_errors[3];
        let c = open_err_code(e);
        acct_proc(c, st, area);
    }
}