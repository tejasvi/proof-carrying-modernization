//! Rust rewrite of ACCTINT.cob with scaled integers: balance and interest in cents (scale 2),
//! rate in units of 1e-5, daily rate in units of 1e-8, intermediates in i128.

/// `None` balance: the balance field holds LOW-VALUES.
pub fn accrue(acct_type: char, balance: Option<i64>, rate: i64, days: u16) -> (i64, i64, char) {
    let bal = balance.unwrap_or(0);
    if days == 0 || (acct_type != 'S' && acct_type != 'C') {
        return (bal, 0, 'Z');
    }
    let daily = div_half_up(rate as i128 * 1000, 365);
    let interest = div_half_up(bal as i128 * daily * days as i128, 100_000_000);
    if interest.abs() >= 100_000_000_000 {          // does not fit S9(9)V99
        return (bal, 0, 'E');
    }
    let new_bal = bal as i128 + interest;
    if new_bal.abs() >= 10_000_000_000_000 {        // does not fit S9(11)V99
        return (bal, interest as i64, 'E');
    }
    (new_bal as i64, interest as i64, 'K')
}

/// `n / d` rounded half away from zero (`d > 0`).
fn div_half_up(n: i128, d: i128) -> i128 {
    if n >= 0 { (2 * n + d) / (2 * d) } else { -((2 * -n + d) / (2 * d)) }
}
