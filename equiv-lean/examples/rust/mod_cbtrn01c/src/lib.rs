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
pub struct FdCustfileRec {
    pub fd_cust_id: i64,
    pub fd_cust_data: [u8; 491],
}

#[derive(Clone, Copy)]
pub struct CardXrefRecord {
    pub xref_card_num: [u8; 16],
    pub xref_cust_id: i64,
    pub xref_acct_id: i64,
    pub filler1: [u8; 14],
}

#[derive(Clone, Copy)]
pub struct FdCardfileRec {
    pub fd_card_num: [u8; 16],
    pub fd_card_data: [u8; 134],
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
pub struct FdTranfileRec {
    pub fd_trans_id: [u8; 16],
    pub fd_acct_data: [u8; 334],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub abended: bool,
}

fn init_dalytran() -> DalytranRecord {
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

fn init_xref() -> CardXrefRecord {
    CardXrefRecord {
        xref_card_num: [b' '; 16],
        xref_cust_id: 0,
        xref_acct_id: 0,
        filler1: [b' '; 14],
    }
}

fn init_account() -> AccountRecord {
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

fn push_bytes(out: &mut Vec<u8>, s: &[u8]) {
    let mut i = 0usize;
    while i < s.len() {
        out.push(s[i]);
        i += 1;
    }
}

fn abs_u64(v: i64) -> u64 {
    if v < 0 {
        ((v + 1) * -1) as u64 + 1
    } else {
        v as u64
    }
}

fn digits_of(v: i64, n: usize) -> [u8; 18] {
    let mut d = [b'0'; 18];
    let mut x = abs_u64(v);
    let mut i = n;
    while i > 0 {
        d[i - 1] = b'0' + (x % 10) as u8;
        x /= 10;
        i -= 1;
    }
    d
}

fn push_unsigned(out: &mut Vec<u8>, v: i64, n: usize) {
    let d = digits_of(v, n);
    let mut i = 0usize;
    while i < n {
        out.push(d[i]);
        i += 1;
    }
}

fn push_signed_overpunch(out: &mut Vec<u8>, v: i64, n: usize) {
    let d = digits_of(v, n);
    let mut i = 0usize;
    while i + 1 < n {
        out.push(d[i]);
        i += 1;
    }
    let last = d[n - 1] - b'0';
    let c = if v >= 0 {
        if last == 0 {
            b'{'
        } else {
            b'A' + last - 1
        }
    } else {
        if last == 0 {
            b'}'
        } else {
            b'J' + last - 1
        }
    };
    out.push(c);
}

fn dalytran_bytes(r: &DalytranRecord) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    push_bytes(&mut v, &r.dalytran_id);
    push_bytes(&mut v, &r.dalytran_type_cd);
    push_unsigned(&mut v, r.dalytran_cat_cd, 4);
    push_bytes(&mut v, &r.dalytran_source);
    push_bytes(&mut v, &r.dalytran_desc);
    push_signed_overpunch(&mut v, r.dalytran_amt, 11);
    push_unsigned(&mut v, r.dalytran_merchant_id, 9);
    push_bytes(&mut v, &r.dalytran_merchant_name);
    push_bytes(&mut v, &r.dalytran_merchant_city);
    push_bytes(&mut v, &r.dalytran_merchant_zip);
    push_bytes(&mut v, &r.dalytran_card_num);
    push_bytes(&mut v, &r.dalytran_orig_ts);
    push_bytes(&mut v, &r.dalytran_proc_ts);
    push_bytes(&mut v, &r.filler1);
    v
}

fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

fn io_status_line(s1: u8, s2: u8) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    push_bytes(&mut v, b"FILE STATUS IS: NNNN");
    if !(is_digit(s1) && is_digit(s2)) || s1 == b'9' {
        v.push(s1);
        push_unsigned(&mut v, (s2 as i64) % 1000, 3);
    } else {
        push_bytes(&mut v, b"00");
        v.push(s1);
        v.push(s2);
    }
    v
}

fn bytes_eq16(a: &[u8; 16], b: &[u8; 16]) -> bool {
    let mut i = 0usize;
    while i < 16 {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn run(
    dalytran_file: &[DalytranRecord],
    customer_file: &[FdCustfileRec],
    xref_file: &[CardXrefRecord],
    card_file: &[FdCardfileRec],
    account_file: &[AccountRecord],
    transact_file: &[FdTranfileRec],
) -> Output {
    let _ = customer_file;
    let _ = card_file;
    let _ = transact_file;

    let mut out = Output {
        displays: Vec::new(),
        abended: false,
    };

    out.displays
        .push(b"START OF EXECUTION OF PROGRAM CBTRN01C".to_vec());
    // All OPENs succeed (status '00').

    let mut dal = init_dalytran();
    let mut xref = init_xref();
    let mut acct = init_account();
    let mut eof_flag: u8 = b'N';
    let mut pos: usize = 0;
    let mut eof_hit = false;

    while eof_flag != b'Y' {
        if eof_flag == b'N' {
            // 1000-DALYTRAN-GET-NEXT
            let s1: u8;
            let s2: u8;
            if pos < dalytran_file.len() {
                dal = dalytran_file[pos];
                pos += 1;
                s1 = b'0';
                s2 = b'0';
            } else if !eof_hit {
                eof_hit = true;
                s1 = b'1';
                s2 = b'0';
            } else {
                s1 = b'4';
                s2 = b'6';
            }
            let appl: i64 = if s1 == b'0' && s2 == b'0' {
                0
            } else if s1 == b'1' && s2 == b'0' {
                16
            } else {
                12
            };
            if appl == 0 {
            } else if appl == 16 {
                eof_flag = b'Y';
            } else {
                out.displays
                    .push(b"ERROR READING DAILY TRANSACTION FILE".to_vec());
                out.displays.push(io_status_line(s1, s2));
                out.displays.push(b"ABENDING PROGRAM".to_vec());
                out.abended = true;
                return out;
            }

            if eof_flag == b'N' {
                out.displays.push(dalytran_bytes(&dal));
            }

            let mut xref_status: i64 = 0;
            xref.xref_card_num = dal.dalytran_card_num;
            // 2000-LOOKUP-XREF
            let key = xref.xref_card_num;
            let mut found = false;
            let mut i = 0usize;
            while i < xref_file.len() {
                if bytes_eq16(&xref_file[i].xref_card_num, &key) {
                    xref = xref_file[i];
                    found = true;
                    break;
                }
                i += 1;
            }
            if !found {
                out.displays
                    .push(b"INVALID CARD NUMBER FOR XREF".to_vec());
                xref_status = 4;
            } else {
                out.displays.push(b"SUCCESSFUL READ OF XREF".to_vec());
                let mut l1: Vec<u8> = Vec::new();
                push_bytes(&mut l1, b"CARD NUMBER: ");
                push_bytes(&mut l1, &xref.xref_card_num);
                out.displays.push(l1);
                let mut l2: Vec<u8> = Vec::new();
                push_bytes(&mut l2, b"ACCOUNT ID : ");
                push_unsigned(&mut l2, xref.xref_acct_id, 11);
                out.displays.push(l2);
                let mut l3: Vec<u8> = Vec::new();
                push_bytes(&mut l3, b"CUSTOMER ID: ");
                push_unsigned(&mut l3, xref.xref_cust_id, 9);
                out.displays.push(l3);
            }

            if xref_status == 0 {
                let mut acct_status: i64 = 0;
                acct.acct_id = (abs_u64(xref.xref_acct_id) % 100_000_000_000u64) as i64;
                // 3000-READ-ACCOUNT
                let akey = acct.acct_id;
                let mut afound = false;
                let mut j = 0usize;
                while j < account_file.len() {
                    if account_file[j].acct_id == akey {
                        acct = account_file[j];
                        afound = true;
                        break;
                    }
                    j += 1;
                }
                if !afound {
                    out.displays
                        .push(b"INVALID ACCOUNT NUMBER FOUND".to_vec());
                    acct_status = 4;
                } else {
                    out.displays
                        .push(b"SUCCESSFUL READ OF ACCOUNT FILE".to_vec());
                }
                if acct_status != 0 {
                    let mut l: Vec<u8> = Vec::new();
                    push_bytes(&mut l, b"ACCOUNT ");
                    push_unsigned(&mut l, acct.acct_id, 11);
                    push_bytes(&mut l, b" NOT FOUND");
                    out.displays.push(l);
                }
            } else {
                let mut l: Vec<u8> = Vec::new();
                push_bytes(&mut l, b"CARD NUMBER ");
                push_bytes(&mut l, &dal.dalytran_card_num);
                push_bytes(
                    &mut l,
                    b" COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-",
                );
                push_bytes(&mut l, &dal.dalytran_id);
                out.displays.push(l);
            }
        }
    }

    // All CLOSEs succeed (status '00').
    out.displays
        .push(b"END OF EXECUTION OF PROGRAM CBTRN01C".to_vec());
    out
}