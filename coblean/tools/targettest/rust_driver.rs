// Reads `type balance|null rate days` lines and prints `balance interest status`.
#[path = "../../examples/acctint/acctint.rs"]
mod acctint;
use acctint::accrue;

fn main() {
    use std::io::BufRead;
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.trim().split(' ').collect();
        let t = f[0].chars().next().unwrap();
        let bal = if f[1] == "null" { None } else { Some(f[1].parse::<i64>().unwrap()) };
        let rate: i64 = f[2].parse().unwrap();
        let days: u16 = f[3].parse().unwrap();
        let (b, i, s) = accrue(t, bal, rate, days);
        println!("{} {} {}", b, i, s);
    }
}
