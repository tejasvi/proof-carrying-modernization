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
    pub cust_dob_yyyy_mm_dd: [u8; 10],
    pub cust_eft_account_id: [u8; 10],
    pub cust_pri_card_holder_ind: [u8; 1],
    pub cust_fico_credit_score: i64,
    pub filler1: [u8; 168],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub abended: bool,
}

fn push_bytes(out: &mut Vec<u8>, b: &[u8]) {
    let mut i = 0;
    while i < b.len() {
        out.push(b[i]);
        i += 1;
    }
}

fn magnitude(v: i64) -> u64 {
    if v < 0 {
        ((-(v + 1)) as u64) + 1
    } else {
        v as u64
    }
}

// Unsigned zoned decimal display of `digits` digits (magnitude, truncated on the left).
fn push_unsigned(out: &mut Vec<u8>, v: i64, digits: usize) {
    let mut u = magnitude(v);
    let mut buf: [u8; 20] = [b'0'; 20];
    let mut i = 0;
    while i < digits {
        buf[digits - 1 - i] = b'0' + (u % 10) as u8;
        u /= 10;
        i += 1;
    }
    let mut j = 0;
    while j < digits {
        out.push(buf[j]);
        j += 1;
    }
}

fn customer_display(r: &CustomerRecord) -> Vec<u8> {
    let mut d: Vec<u8> = Vec::new();
    push_unsigned(&mut d, r.cust_id, 9);
    push_bytes(&mut d, &r.cust_first_name);
    push_bytes(&mut d, &r.cust_middle_name);
    push_bytes(&mut d, &r.cust_last_name);
    push_bytes(&mut d, &r.cust_addr_line_1);
    push_bytes(&mut d, &r.cust_addr_line_2);
    push_bytes(&mut d, &r.cust_addr_line_3);
    push_bytes(&mut d, &r.cust_addr_state_cd);
    push_bytes(&mut d, &r.cust_addr_country_cd);
    push_bytes(&mut d, &r.cust_addr_zip);
    push_bytes(&mut d, &r.cust_phone_num_1);
    push_bytes(&mut d, &r.cust_phone_num_2);
    push_unsigned(&mut d, r.cust_ssn, 9);
    push_bytes(&mut d, &r.cust_govt_issued_id);
    push_bytes(&mut d, &r.cust_dob_yyyy_mm_dd);
    push_bytes(&mut d, &r.cust_eft_account_id);
    push_bytes(&mut d, &r.cust_pri_card_holder_ind);
    push_unsigned(&mut d, r.cust_fico_credit_score, 3);
    push_bytes(&mut d, &r.filler1);
    d
}

fn lit(s: &[u8]) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    push_bytes(&mut v, s);
    v
}

fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

fn z_display_io_status(displays: &mut Vec<Vec<u8>>, io_status: [u8; 2]) {
    let mut st04: [u8; 4] = [b'0'; 4];
    if !(is_digit(io_status[0]) && is_digit(io_status[1])) || io_status[0] == b'9' {
        st04[0] = io_status[0];
        let bin: u64 = io_status[1] as u64;
        let v = bin % 1000;
        st04[1] = b'0' + ((v / 100) % 10) as u8;
        st04[2] = b'0' + ((v / 10) % 10) as u8;
        st04[3] = b'0' + (v % 10) as u8;
    } else {
        st04[0] = b'0';
        st04[1] = b'0';
        st04[2] = io_status[0];
        st04[3] = io_status[1];
    }
    let mut d = lit(b"FILE STATUS IS: NNNN");
    push_bytes(&mut d, &st04);
    displays.push(d);
}

fn z_abend_program(displays: &mut Vec<Vec<u8>>) {
    displays.push(lit(b"ABENDING PROGRAM"));
}

pub fn run(custfile_file: &[CustomerRecord]) -> Output {
    let mut displays: Vec<Vec<u8>> = Vec::new();
    displays.push(lit(b"START OF EXECUTION OF PROGRAM CBCUS01C"));

    // 0000-CUSTFILE-OPEN: OPEN succeeds with status '00'.
    let mut pos: usize = 0;
    let mut at_eof = false;
    let mut end_of_file: u8 = b'N';

    while end_of_file != b'Y' {
        if end_of_file == b'N' {
            // 1000-CUSTFILE-GET-NEXT
            let status: [u8; 2];
            let mut rec: Option<CustomerRecord> = None;
            if at_eof {
                status = [b'4', b'6'];
            } else if pos < custfile_file.len() {
                rec = Some(custfile_file[pos]);
                pos += 1;
                status = [b'0', b'0'];
            } else {
                at_eof = true;
                status = [b'1', b'0'];
            }
            let appl_result: i64;
            if status[0] == b'0' && status[1] == b'0' {
                appl_result = 0;
                if let Some(r) = rec {
                    displays.push(customer_display(&r));
                }
            } else if status[0] == b'1' && status[1] == b'0' {
                appl_result = 16;
            } else {
                appl_result = 12;
            }
            if appl_result == 0 {
                // continue
            } else if appl_result == 16 {
                end_of_file = b'Y';
            } else {
                displays.push(lit(b"ERROR READING CUSTOMER FILE"));
                z_display_io_status(&mut displays, status);
                z_abend_program(&mut displays);
                return Output {
                    displays,
                    abended: true,
                };
            }
            if end_of_file == b'N' {
                if let Some(r) = rec {
                    displays.push(customer_display(&r));
                }
            }
        }
    }

    // 9000-CUSTFILE-CLOSE: CLOSE succeeds with status '00'.

    displays.push(lit(b"END OF EXECUTION OF PROGRAM CBCUS01C"));
    Output {
        displays,
        abended: false,
    }
}