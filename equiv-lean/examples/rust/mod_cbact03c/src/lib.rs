#[derive(Clone, Copy)]
pub struct CardXrefRecord {
    pub xref_card_num: [u8; 16],
    pub xref_cust_id: i64,
    pub xref_acct_id: i64,
    pub filler1: [u8; 14],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub abended: bool,
}

const DIGITS: [u8; 10] = *b"0123456789";

fn push_bytes(dst: &mut Vec<u8>, src: &[u8]) {
    let mut i = 0;
    while i < src.len() {
        dst.push(src[i]);
        i += 1;
    }
}

fn push_unsigned(dst: &mut Vec<u8>, value: i64, digits: usize) {
    // Unsigned display numeric: magnitude, truncated to the field's digits.
    let mut v: i64 = if value < 0 { -value } else { value };
    let mut buf: [u8; 20] = [b'0'; 20];
    let mut pos = digits;
    while pos > 0 {
        pos -= 1;
        let d = (v % 10) as usize;
        buf[pos] = DIGITS[d];
        v = v / 10;
    }
    let mut i = 0;
    while i < digits {
        dst.push(buf[i]);
        i += 1;
    }
}

fn record_bytes(r: &CardXrefRecord) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    push_bytes(&mut out, &r.xref_card_num);
    push_unsigned(&mut out, r.xref_cust_id, 9);
    push_unsigned(&mut out, r.xref_acct_id, 11);
    push_bytes(&mut out, &r.filler1);
    out
}

fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

fn display_io_status(displays: &mut Vec<Vec<u8>>, stat1: u8, stat2: u8) {
    let mut line: Vec<u8> = Vec::new();
    push_bytes(&mut line, b"FILE STATUS IS: NNNN");
    if !(is_digit(stat1) && is_digit(stat2)) || stat1 == b'9' {
        line.push(stat1);
        let v = stat2 as i64;
        push_unsigned(&mut line, v, 3);
    } else {
        line.push(b'0');
        line.push(b'0');
        line.push(stat1);
        line.push(stat2);
    }
    displays.push(line);
}

fn abend(displays: &mut Vec<Vec<u8>>) {
    let mut line: Vec<u8> = Vec::new();
    push_bytes(&mut line, b"ABENDING PROGRAM");
    displays.push(line);
}

pub fn run(xreffile_file: &[CardXrefRecord]) -> Output {
    let mut displays: Vec<Vec<u8>> = Vec::new();

    let mut line: Vec<u8> = Vec::new();
    push_bytes(&mut line, b"START OF EXECUTION OF PROGRAM CBACT03C");
    displays.push(line);

    // OPEN INPUT succeeds (status '00').
    let mut card_xref_record = CardXrefRecord {
        xref_card_num: [b' '; 16],
        xref_cust_id: 0,
        xref_acct_id: 0,
        filler1: [b' '; 14],
    };
    let mut end_of_file = false;
    let mut pos: usize = 0;
    let mut eof_reached = false;

    while !end_of_file {
        // 1000-XREFFILE-GET-NEXT
        let stat1: u8;
        let stat2: u8;
        if eof_reached {
            stat1 = b'4';
            stat2 = b'6';
        } else if pos < xreffile_file.len() {
            card_xref_record = xreffile_file[pos];
            pos += 1;
            stat1 = b'0';
            stat2 = b'0';
        } else {
            eof_reached = true;
            stat1 = b'1';
            stat2 = b'0';
        }
        let appl_result: i64;
        if stat1 == b'0' && stat2 == b'0' {
            appl_result = 0;
            displays.push(record_bytes(&card_xref_record));
        } else if stat1 == b'1' && stat2 == b'0' {
            appl_result = 16;
        } else {
            appl_result = 12;
        }
        if appl_result == 0 {
            // continue
        } else if appl_result == 16 {
            end_of_file = true;
        } else {
            let mut l: Vec<u8> = Vec::new();
            push_bytes(&mut l, b"ERROR READING XREFFILE");
            displays.push(l);
            display_io_status(&mut displays, stat1, stat2);
            abend(&mut displays);
            return Output {
                displays,
                abended: true,
            };
        }
        if !end_of_file {
            displays.push(record_bytes(&card_xref_record));
        }
    }

    // CLOSE succeeds (status '00').

    let mut line2: Vec<u8> = Vec::new();
    push_bytes(&mut line2, b"END OF EXECUTION OF PROGRAM CBACT03C");
    displays.push(line2);

    Output {
        displays,
        abended: false,
    }
}