#[derive(Clone, Copy)]
pub struct CardRecord {
    pub card_num: [u8; 16],
    pub card_acct_id: i64,
    pub card_cvv_cd: i64,
    pub card_embossed_name: [u8; 50],
    pub card_expiraion_date: [u8; 10],
    pub card_active_status: [u8; 1],
    pub filler1: [u8; 59],
}

pub struct Output {
    pub displays: Vec<Vec<u8>>,
    pub abended: bool,
}

fn push_bytes(dst: &mut Vec<u8>, src: &[u8]) {
    let mut i = 0;
    while i < src.len() {
        dst.push(src[i]);
        i += 1;
    }
}

/// Unsigned zoned-decimal display of `digits` digits (PIC 9(n)).
fn push_unsigned(dst: &mut Vec<u8>, value: i64, digits: usize) {
    let mut v: u64 = if value < 0 {
        (0i64 - (value as i128) as i64) as u64
    } else {
        value as u64
    };
    let mut buf: [u8; 18] = [b'0'; 18];
    let mut i = 0;
    while i < digits && i < 18 {
        buf[digits - 1 - i] = b'0' + (v % 10) as u8;
        v /= 10;
        i += 1;
    }
    let mut j = 0;
    while j < digits && j < 18 {
        dst.push(buf[j]);
        j += 1;
    }
}

fn card_record_display(r: &CardRecord) -> Vec<u8> {
    let mut line: Vec<u8> = Vec::new();
    push_bytes(&mut line, &r.card_num);
    push_unsigned(&mut line, r.card_acct_id, 11);
    push_unsigned(&mut line, r.card_cvv_cd, 3);
    push_bytes(&mut line, &r.card_embossed_name);
    push_bytes(&mut line, &r.card_expiraion_date);
    push_bytes(&mut line, &r.card_active_status);
    push_bytes(&mut line, &r.filler1);
    line
}

fn display_io_status(displays: &mut Vec<Vec<u8>>, status: [u8; 2]) {
    let stat1 = status[0];
    let stat2 = status[1];
    let numeric = stat1 >= b'0' && stat1 <= b'9' && stat2 >= b'0' && stat2 <= b'9';
    let mut line: Vec<u8> = Vec::new();
    push_bytes(&mut line, b"FILE STATUS IS: NNNN");
    if !numeric || stat1 == b'9' {
        line.push(stat1);
        push_unsigned(&mut line, stat2 as i64, 3);
    } else {
        line.push(b'0');
        line.push(b'0');
        line.push(stat1);
        line.push(stat2);
    }
    displays.push(line);
}

fn abend(displays: &mut Vec<Vec<u8>>) {
    displays.push(b"ABENDING PROGRAM".to_vec());
}

pub fn run(cardfile_file: &[CardRecord]) -> Output {
    let mut displays: Vec<Vec<u8>> = Vec::new();
    displays.push(b"START OF EXECUTION OF PROGRAM CBACT02C".to_vec());

    // OPEN INPUT always succeeds with status '00'.
    let mut pos: usize = 0;
    let mut at_eof = false;
    let mut end_of_file = false;

    while !end_of_file {
        // 1000-CARDFILE-GET-NEXT
        let status: [u8; 2];
        let mut rec_opt: Option<CardRecord> = None;
        if at_eof {
            status = [b'4', b'6'];
        } else if pos < cardfile_file.len() {
            rec_opt = Some(cardfile_file[pos]);
            pos += 1;
            status = [b'0', b'0'];
        } else {
            at_eof = true;
            status = [b'1', b'0'];
        }
        let appl_result: i64 = if status[0] == b'0' && status[1] == b'0' {
            0
        } else if status[0] == b'1' && status[1] == b'0' {
            16
        } else {
            12
        };
        if appl_result == 0 {
            // continue
        } else if appl_result == 16 {
            end_of_file = true;
        } else {
            displays.push(b"ERROR READING CARDFILE".to_vec());
            display_io_status(&mut displays, status);
            abend(&mut displays);
            return Output {
                displays,
                abended: true,
            };
        }
        if !end_of_file {
            if let Some(r) = rec_opt {
                displays.push(card_record_display(&r));
            }
        }
    }

    // CLOSE always succeeds with status '00'.
    displays.push(b"END OF EXECUTION OF PROGRAM CBACT02C".to_vec());

    Output {
        displays,
        abended: false,
    }
}