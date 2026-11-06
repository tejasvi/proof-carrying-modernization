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
pub struct OutAcctRec {
    pub out_acct_id: i64,
    pub out_acct_active_status: [u8; 1],
    pub out_acct_curr_bal: i64,
    pub out_acct_credit_limit: i64,
    pub out_acct_cash_credit_limit: i64,
    pub out_acct_open_date: [u8; 10],
    pub out_acct_expiraion_date: [u8; 10],
    pub out_acct_reissue_date: [u8; 10],
    pub out_acct_curr_cyc_credit: i64,
    pub out_acct_curr_cyc_debit: i64,
    pub out_acct_group_id: [u8; 10],
}

#[derive(Clone, Copy)]
pub struct ArrArrayRec {
    pub arr_acct_id: i64,
    pub arr_acct_curr_bal: [i64; 5],
    pub arr_acct_curr_cyc_debit: [i64; 5],
    pub arr_filler: [u8; 4],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub out_file_writes: Vec<OutAcctRec>,
    pub arry_file_writes: Vec<ArrArrayRec>,
    pub vbrc_file_writes: Vec<Vec<u8>>,
    pub abended: bool,
}

fn push_bytes(out: &mut Vec<u8>, s: &[u8]) {
    let mut i = 0;
    while i < s.len() {
        out.push(s[i]);
        i += 1;
    }
}

fn lit(s: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    push_bytes(&mut v, s);
    v
}

fn overpunch(d: u8, neg: bool) -> u8 {
    if neg {
        if d == 0 {
            b'}'
        } else {
            b'J' + d - 1
        }
    } else if d == 0 {
        b'{'
    } else {
        b'A' + d - 1
    }
}

fn magnitude(v: i64) -> u64 {
    if v < 0 {
        ((-(v + 1)) as u64) + 1
    } else {
        v as u64
    }
}

/// Zoned decimal display form; signed items get the sign overpunched in the last digit.
fn push_zoned(out: &mut Vec<u8>, v: i64, digits: usize, signed: bool) {
    let neg = v < 0;
    let mut m: u64 = magnitude(v);
    let mut buf = [b'0'; 20];
    let mut i = digits;
    while i > 0 {
        i -= 1;
        buf[i] = b'0' + (m % 10) as u8;
        m /= 10;
    }
    if signed && digits > 0 {
        let d = buf[digits - 1] - b'0';
        buf[digits - 1] = overpunch(d, neg);
    }
    let mut k = 0;
    while k < digits {
        out.push(buf[k]);
        k += 1;
    }
}

fn set_err_msg(rec: &mut [u8; 80]) {
    let msg = b"INVALID INPUT";
    let mut i = 0;
    while i < 38 {
        let c = if i < 13 { msg[i] } else { b' ' };
        rec[42 + i] = c;
        i += 1;
    }
}

/// COBDATFT: date formatting routine operating on the CODATECN-REC layout:
/// type(0) inp-date(1..21) outtype(21) out-date(22..42) error-msg(42..80)
fn cobdatft(rec: &mut [u8; 80]) {
    let intype = rec[0];
    let outtype = rec[21];
    let mut mode: u8 = 0;
    if intype == b'1' {
        if rec[5] != b'-' && outtype != b'2' {
            mode = 1;
        }
    } else if intype == b'2' {
        if outtype != b'1' {
            mode = 2;
        }
    }
    if mode == 1 {
        rec[22] = rec[1];
        rec[23] = rec[2];
        rec[24] = rec[3];
        rec[25] = rec[4];
        rec[26] = b'-';
        rec[27] = rec[5];
        rec[28] = rec[6];
        rec[29] = b'-';
        rec[30] = rec[7];
        rec[31] = rec[8];
    } else if mode == 2 {
        rec[22] = rec[1];
        rec[23] = rec[2];
        rec[24] = rec[3];
        rec[25] = rec[4];
        rec[26] = rec[6];
        rec[27] = rec[7];
        rec[28] = rec[9];
        rec[29] = rec[10];
    } else {
        set_err_msg(rec);
    }
}

fn set_inp_date(rec: &mut [u8; 80], d: &[u8; 10]) {
    let mut i = 0;
    while i < 20 {
        let c = if i < 10 { d[i] } else { b' ' };
        rec[1 + i] = c;
        i += 1;
    }
}

fn get_out_date(rec: &[u8; 80]) -> [u8; 10] {
    let mut r = [b' '; 10];
    let mut j = 0;
    while j < 10 {
        r[j] = rec[22 + j];
        j += 1;
    }
    r
}

fn push_first4(out: &mut Vec<u8>, s: &[u8; 10]) {
    let mut k = 0;
    while k < 4 {
        out.push(s[k]);
        k += 1;
    }
}

fn labeled_num(label: &[u8], v: i64, digits: usize, signed: bool) -> Vec<u8> {
    let mut d = lit(label);
    push_zoned(&mut d, v, digits, signed);
    d
}

fn labeled_x(label: &[u8], x: &[u8]) -> Vec<u8> {
    let mut d = lit(label);
    push_bytes(&mut d, x);
    d
}

pub fn run(acctfile_file: &[AccountRecord]) -> Output {
    let mut displays: Vec<Vec<u8>> = Vec::new();
    let mut out_file_writes: Vec<OutAcctRec> = Vec::new();
    let mut arry_file_writes: Vec<ArrArrayRec> = Vec::new();
    let mut vbrc_file_writes: Vec<Vec<u8>> = Vec::new();

    displays.push(lit(b"START OF EXECUTION OF PROGRAM CBACT01C"));

    let mut out_rec = OutAcctRec {
        out_acct_id: 0,
        out_acct_active_status: [b' '; 1],
        out_acct_curr_bal: 0,
        out_acct_credit_limit: 0,
        out_acct_cash_credit_limit: 0,
        out_acct_open_date: [b' '; 10],
        out_acct_expiraion_date: [b' '; 10],
        out_acct_reissue_date: [b' '; 10],
        out_acct_curr_cyc_credit: 0,
        out_acct_curr_cyc_debit: 0,
        out_acct_group_id: [b' '; 10],
    };
    let mut codatecn: [u8; 80] = [b' '; 80];

    let mut end_of_file = false;
    let mut idx: usize = 0;

    while !end_of_file {
        if idx < acctfile_file.len() {
            let acct = acctfile_file[idx];
            idx += 1;

            // 1100-DISPLAY-ACCT-RECORD
            displays.push(labeled_num(b"ACCT-ID                 :", acct.acct_id, 11, false));
            displays.push(labeled_x(b"ACCT-ACTIVE-STATUS      :", &acct.acct_active_status));
            displays.push(labeled_num(b"ACCT-CURR-BAL           :", acct.acct_curr_bal, 12, true));
            displays.push(labeled_num(b"ACCT-CREDIT-LIMIT       :", acct.acct_credit_limit, 12, true));
            displays.push(labeled_num(
                b"ACCT-CASH-CREDIT-LIMIT  :",
                acct.acct_cash_credit_limit,
                12,
                true,
            ));
            displays.push(labeled_x(b"ACCT-OPEN-DATE          :", &acct.acct_open_date));
            displays.push(labeled_x(b"ACCT-EXPIRAION-DATE     :", &acct.acct_expiraion_date));
            displays.push(labeled_x(b"ACCT-REISSUE-DATE       :", &acct.acct_reissue_date));
            displays.push(labeled_num(
                b"ACCT-CURR-CYC-CREDIT    :",
                acct.acct_curr_cyc_credit,
                12,
                true,
            ));
            displays.push(labeled_num(
                b"ACCT-CURR-CYC-DEBIT     :",
                acct.acct_curr_cyc_debit,
                12,
                true,
            ));
            displays.push(labeled_x(b"ACCT-GROUP-ID           :", &acct.acct_group_id));
            displays.push(lit(b"-------------------------------------------------"));

            // 1300-POPUL-ACCT-RECORD
            out_rec.out_acct_id = acct.acct_id;
            out_rec.out_acct_active_status = acct.acct_active_status;
            out_rec.out_acct_curr_bal = acct.acct_curr_bal;
            out_rec.out_acct_credit_limit = acct.acct_credit_limit;
            out_rec.out_acct_cash_credit_limit = acct.acct_cash_credit_limit;
            out_rec.out_acct_open_date = acct.acct_open_date;
            out_rec.out_acct_expiraion_date = acct.acct_expiraion_date;
            set_inp_date(&mut codatecn, &acct.acct_reissue_date);
            let ws_reissue: [u8; 10] = acct.acct_reissue_date;
            codatecn[0] = b'2';
            codatecn[21] = b'2';
            cobdatft(&mut codatecn);
            out_rec.out_acct_reissue_date = get_out_date(&codatecn);
            out_rec.out_acct_curr_cyc_credit = acct.acct_curr_cyc_credit;
            if acct.acct_curr_cyc_debit == 0 {
                out_rec.out_acct_curr_cyc_debit = 252500;
            }
            out_rec.out_acct_group_id = acct.acct_group_id;

            // 1350-WRITE-ACCT-RECORD
            out_file_writes.push(out_rec);

            // INITIALIZE ARR-ARRAY-REC + 1400-POPUL-ARRAY-RECORD
            let mut bal: [i64; 5] = [0; 5];
            let mut deb: [i64; 5] = [0; 5];
            bal[0] = acct.acct_curr_bal;
            deb[0] = 100500;
            bal[1] = acct.acct_curr_bal;
            deb[1] = 152500;
            bal[2] = -102500;
            deb[2] = -250000;
            let arr_rec = ArrArrayRec {
                arr_acct_id: acct.acct_id,
                arr_acct_curr_bal: bal,
                arr_acct_curr_cyc_debit: deb,
                arr_filler: [b' '; 4],
            };

            // 1450-WRITE-ARRY-RECORD
            arry_file_writes.push(arr_rec);

            // 1500-POPUL-VBRC-RECORD
            let mut vbrc1: Vec<u8> = Vec::new();
            push_zoned(&mut vbrc1, acct.acct_id, 11, false);
            vbrc1.push(acct.acct_active_status[0]);

            let mut vbrc2: Vec<u8> = Vec::new();
            push_zoned(&mut vbrc2, acct.acct_id, 11, false);
            push_zoned(&mut vbrc2, acct.acct_curr_bal, 12, true);
            push_zoned(&mut vbrc2, acct.acct_credit_limit, 12, true);
            push_first4(&mut vbrc2, &ws_reissue);

            let mut d1 = lit(b"VBRC-REC1:");
            push_bytes(&mut d1, &vbrc1);
            displays.push(d1);
            let mut d2 = lit(b"VBRC-REC2:");
            push_bytes(&mut d2, &vbrc2);
            displays.push(d2);

            // 1550-WRITE-VB1-RECORD (length 12)
            vbrc_file_writes.push(vbrc1);
            // 1575-WRITE-VB2-RECORD (length 39)
            vbrc_file_writes.push(vbrc2);

            // DISPLAY ACCOUNT-RECORD
            let mut d = Vec::new();
            push_zoned(&mut d, acct.acct_id, 11, false);
            push_bytes(&mut d, &acct.acct_active_status);
            push_zoned(&mut d, acct.acct_curr_bal, 12, true);
            push_zoned(&mut d, acct.acct_credit_limit, 12, true);
            push_zoned(&mut d, acct.acct_cash_credit_limit, 12, true);
            push_bytes(&mut d, &acct.acct_open_date);
            push_bytes(&mut d, &acct.acct_expiraion_date);
            push_bytes(&mut d, &acct.acct_reissue_date);
            push_zoned(&mut d, acct.acct_curr_cyc_credit, 12, true);
            push_zoned(&mut d, acct.acct_curr_cyc_debit, 12, true);
            push_bytes(&mut d, &acct.acct_addr_zip);
            push_bytes(&mut d, &acct.acct_group_id);
            push_bytes(&mut d, &acct.filler1);
            displays.push(d);
        } else {
            end_of_file = true;
        }
    }

    displays.push(lit(b"END OF EXECUTION OF PROGRAM CBACT01C"));

    Output {
        displays,
        out_file_writes,
        arry_file_writes,
        vbrc_file_writes,
        abended: false,
    }
}