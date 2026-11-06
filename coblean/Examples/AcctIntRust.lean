/-
# ACCTINT: COBOL program ≡ Rust rewrite (scaled integers, `i128` intermediates)

`AcctIntRust.accrue` transcribes `examples/acctint/acctint.rs` over the Rust model: `i64`
values are `Int64`, `i128` intermediates are `Int`s with debug-build overflow panics
(`Rust.mul128`, …), `/` truncates toward zero.  The theorem also shows that the Rust code never
panics on valid records: every `i128` overflow check is decided by the ranges of the inputs.
-/
import Examples.AcctInt
open Cobol

namespace AcctIntRust
open Rust

/-- `fn div_half_up(n: i128, d: i128) -> i128`. -/
def divHalfUp (n d : Int) : Except Panic Int :=
  if 0 ≤ n then do
    let a ← mul128 2 n
    let b ← add128 a d
    let c ← mul128 2 d
    div128 b c
  else do
    let a ← neg128 n
    let a ← mul128 2 a
    let b ← add128 a d
    let c ← mul128 2 d
    let q ← div128 b c
    neg128 q

/-- `pub fn accrue(acct_type: char, balance: Option<i64>, rate: i64, days: u16)`. -/
def accrue (type : Char) (balance : Option Int64) (rate : Int64) (days : UInt16) :
    Except Panic (Int64 × Int64 × Char) := do
  let bal := balance.getD 0
  if days = 0 ∨ (type ≠ 'S' ∧ type ≠ 'C') then return (bal, 0, 'Z')
  let r ← mul128 rate.toInt 1000
  let daily ← divHalfUp r 365
  let p ← mul128 bal.toInt daily
  let p ← mul128 p days.toNat
  let interest ← divHalfUp p 100000000
  let ia ← abs128 interest
  if ia ≥ 100000000000 then return (bal, 0, 'E')
  let nb ← add128 bal.toInt interest
  let na ← abs128 nb
  if na ≥ 10000000000000 then return (bal, Int64.ofInt interest, 'E')
  return (Int64.ofInt nb, Int64.ofInt interest, 'K')

end AcctIntRust

/-- The observation of the Rust result (status as its CP037 byte). -/
def rustObs : Except Rust.Panic (Int64 × Int64 × Char) → Option (Int × Int × List UInt8)
  | .ok (b, i, s) => (Codepage.cp037Byte s).map fun x => (b.toInt, i.toInt, [x])
  | .error _ => none

open AcctInt in
/-- **ACCTINT ≡ acctint.rs.** -/
theorem acctint_rust_equiv (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int64)
    (days : UInt16)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal.toInt)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.toInt)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.toNat : Int)) :
    cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) =
      rustObs (AcctIntRust.accrue (Codepage.cp037Char ty) (some bal) rate days) := by
  cobol_ranges
  have hz : ¬ m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0] := by
    intro h; cobol_sym [h] at hbal
  have := daily_rate_eq rate.toInt
  cobol_equiv [cobolObs, rustObs, hm, hty, hbal, hrate, hdays, hz,
    AcctIntRust.accrue, AcctIntRust.divHalfUp, Rust.divRound_halfUp_idiom]

#print axioms acctint_rust_equiv
