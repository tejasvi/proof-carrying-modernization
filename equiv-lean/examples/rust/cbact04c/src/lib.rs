//! Rust port of CardDemo's CBACT04C (monthly interest on category balances), for the COBOL → Rust
//! proof against coblean's all-input theorem `cbact04c_all` (translated to Lean by Charon and
//! Aeneas).
//!
//! The files of the COBOL program are arguments and results, as a data-access layer would
//! provide them: the category-balance records in file order (TCATBAL), the account and
//! disclosure-group records, looked up by key like the keyed READs (ACCTDAT, DISCGRP), and as
//! results the rewritten accounts in REWRITE order and the number of interest transactions
//! written (TRANSACT).  Amounts are in cents and rates in hundredths of a percent, as in the
//! `PIC S9(n)V99` fields; the truncation of an ADD or COMPUTE into a smaller field is explicit
//! (`S9(9)V99`: remainder modulo 10^11, `S9(10)V99`: modulo 10^12).  `/` and `%` on `i64`
//! truncate toward zero, as COBOL does here; all arithmetic is checked (an overflow panics).
//! The alphanumeric keys are integers: the group id (`PIC X(10)`) is the big-endian value of
//! its ten EBCDIC bytes, the transaction type code (`PIC X(02)`) that of its two bytes.
//!
//! Like the COBOL program, the interest of the last account in the file is never posted: the
//! `ELSE PERFORM 1050-UPDATE-ACCOUNT` branch of the main loop is dead (CardDemo issue #64).

/// TRAN-CAT-BAL-RECORD.
pub struct Cat {
    pub acct_id: i64,
    pub type_cd: u16,
    pub cat_cd: i32,
    pub bal: i64,
}

/// ACCOUNT-RECORD: the fields the program reads or changes.  A keyed READ copies the record
/// (`READ ACCOUNT-FILE INTO ACCOUNT-RECORD`).
#[derive(Clone, Copy)]
pub struct Account {
    pub id: i64,
    pub bal: i64,
    pub cyc_credit: i64,
    pub cyc_debit: i64,
    pub group_id: u128,
}

/// DIS-GROUP-RECORD.
pub struct Disc {
    pub group_id: u128,
    pub type_cd: u16,
    pub cat_cd: i32,
    pub rate: i64,
}

/// The group id `'DEFAULT'` (padded with spaces to ten EBCDIC bytes).
const DEFAULT_GROUP: u128 = 0xC4C5_C6C1_E4D3_E340_4040;

/// 1100-GET-ACCT-DATA: the account record with this key (`None`: INVALID KEY).
fn read_account(accounts: &[Account], id: i64) -> Option<Account> {
    let mut i = 0;
    while i < accounts.len() {
        if accounts[i].id == id {
            return Some(accounts[i]);
        }
        i += 1;
    }
    None
}

/// The rate of the disclosure-group record with this key (`None`: INVALID KEY).
fn find_rate(discs: &[Disc], group_id: u128, type_cd: u16, cat_cd: i32) -> Option<i64> {
    let mut i = 0;
    while i < discs.len() {
        let d = &discs[i];
        if d.group_id == group_id && d.type_cd == type_cd && d.cat_cd == cat_cd {
            return Some(d.rate);
        }
        i += 1;
    }
    None
}

/// 1200-GET-INTEREST-RATE, with 1200-A-GET-DEFAULT-INT-RATE when the key is not found.
fn read_rate(discs: &[Disc], group_id: u128, type_cd: u16, cat_cd: i32) -> i64 {
    match find_rate(discs, group_id, type_cd, cat_cd) {
        Some(rate) => rate,
        None => find_rate(discs, DEFAULT_GROUP, type_cd, cat_cd).expect("no disclosure group record"),
    }
}

/// 1050-UPDATE-ACCOUNT: post the interest, zero the cycle credit and debit.
fn post(a: Account, total_int: i64) -> Account {
    Account {
        id: a.id,
        bal: (a.bal + total_int) % 1_000_000_000_000,
        cyc_credit: 0,
        cyc_debit: 0,
        group_id: a.group_id,
    }
}

/// The main loop of the PROCEDURE DIVISION: the REWRITEs, in order, and the number of
/// transactions written.
pub fn run(cats: &[Cat], accounts: &[Account], discs: &[Disc]) -> (Vec<Account>, u32) {
    let mut rewrites = Vec::new();
    let mut transactions: u32 = 0;
    let mut first_time = true;
    let mut last_acct: i64 = 0;
    let mut total_int: i64 = 0;
    let mut acct: Option<Account> = None;
    let mut i = 0;
    while i < cats.len() {
        let c = &cats[i];
        // WS-LAST-ACCT-NUM holds spaces until the first record: no account id equals it
        if first_time || c.acct_id != last_acct {
            if !first_time {
                rewrites.push(post(acct.unwrap(), total_int));
            } else {
                first_time = false;
            }
            total_int = 0;
            last_acct = c.acct_id;
            acct = read_account(accounts, c.acct_id);
        }
        let a = acct.expect("account not found");
        let rate = read_rate(discs, a.group_id, c.type_cd, c.cat_cd);
        if rate != 0 {
            // 1300-COMPUTE-INTEREST and 1300-B-WRITE-TX
            let monthly = c.bal * rate / 120_000 % 100_000_000_000;
            total_int = (total_int + monthly) % 100_000_000_000;
            transactions += 1;
        }
        i += 1;
    }
    (rewrites, transactions)
}
