/-
# ACCTINT: COBOL program ≡ Java rewrite

`examples/acctint/ACCTINT.cob` (+ copybook `ACCTREC.cpy`) is loaded from its surface IR
(`acctint.ir.json`, what an extractor emits).  `AcctIntJava.accrue` is a line-by-line
transcription of `examples/acctint/AcctInt.java` over the `Java.BigDecimal` model.

The theorem says: for every storage whose account record holds valid data (any bytes
elsewhere), running the COBOL program and running the Java method give the same new
balance, interest and status (the status as the CP037 byte the COBOL program stores).
-/
import Cobol
open Cobol

cobol_program AcctInt from "../examples/acctint/acctint.ir.json"

namespace AcctIntJava
open Java

structure Result where
  balance : BigDecimal
  interest : BigDecimal
  status : Char

def ZERO2 : BigDecimal := BigDecimal.valueOf 0 2

/-- `AcctInt.accrue` (`balance = none` for a balance field holding LOW-VALUES). -/
def accrue (type : Char) (balance : Option BigDecimal) (rate : BigDecimal) (days : Int32) :
    Except ArithmeticException Result :=
  let bal := balance.getD ZERO2
  if days = 0 ∨ (type ≠ 'S' ∧ type ≠ 'C') then .ok ⟨bal, ZERO2, 'Z'⟩ else
  match rate.divide (BigDecimal.valueOf 365) 8 RoundingMode.HALF_UP with
  | .error e => .error e
  | .ok daily =>
    match ((bal.multiply daily).multiply (BigDecimal.valueOf days.toInt)).setScale 2
        RoundingMode.HALF_UP with
    | .error e => .error e
    | .ok interest =>
      if interest.abs.compareTo (BigDecimal.valueOf 1000000000) ≥ 0 then .ok ⟨bal, ZERO2, 'E'⟩
      else
        let newBal := bal.add interest
        if newBal.abs.compareTo (BigDecimal.valueOf 100000000000) ≥ 0 then
          .ok ⟨bal, interest, 'E'⟩
        else .ok ⟨newBal, interest, 'K'⟩

end AcctIntJava

/-! ## Observations

`AcctInt.ACCT_BALANCE : FieldDesc`, `AcctInt.ACCT_BALANCE.fmt : NumFmt`, … are defined by
`cobol_program` from the data division (offset, length, PICTURE / USAGE). -/

open AcctInt in
/-- What the COBOL run produces: new balance, interest (both scale 2) and status byte. -/
def cobolObs (r : Sem.Res) : Option (Int × Int × List UInt8) :=
  if r.1 = .stop .goback then
    match decodeNum {} ACCT_BALANCE.fmt (r.2.mem.field ACCT_BALANCE),
          decodeNum {} WS_INTEREST.fmt (r.2.mem.field WS_INTEREST) with
    | some b, some i => some (b, i, r.2.mem.field WS_STATUS)
    | _, _ => none
  else none

/-- The same observation of the Java result. -/
def javaObs : Except Java.ArithmeticException AcctIntJava.Result → Option (Int × Int × List UInt8)
  | .ok res => (Codepage.cp037Byte res.status).map fun b =>
      (res.balance.valueAt 2, res.interest.valueAt 2, [b])
  | .error _ => none

/-- The daily rate.  COBOL computes `ACCT-RATE / 365` to 9 decimal places (IBM intermediate
rule: `dmax = 8`, plus one place for `ROUNDED`), truncating, then rounds to the 8 places of
`WS-DAILY-RATE`; Java rounds the exact quotient to 8 places with `HALF_UP`.  These agree
(rounding half away from zero only looks at the first dropped digit).  (That the result fits
`WS-DAILY-RATE` is found automatically, from the range of `rate`.) -/
theorem daily_rate_eq (rate : Int) :
    divRound .nearestAwayFromZero (divRound .truncation (rate * 10000) 365) 10 =
      divRound .nearestAwayFromZero (rate * 1000) 365 := by
  cobol_arith

open AcctInt in
/-- **ACCTINT ≡ AcctInt.accrue.**  Any storage whose account record holds a type byte, a valid
balance, rate and day count: the COBOL program and the Java method agree on the new balance,
the interest and the status. -/
theorem acctint_equiv (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int) (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) :
    cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) =
      javaObs (AcctIntJava.accrue (Codepage.cp037Char ty) (some (.valueOf bal 2))
        (.valueOf rate 5) days) := by
  cobol_ranges
  -- a valid packed balance is never LOW-VALUES (the program tests `ACCT-BAL-RAW`)
  have hz : ¬ m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0] := by
    intro h; cobol_sym [h] at hbal
  -- the arithmetic fact: COBOL's two roundings of the daily rate = Java's one
  have := daily_rate_eq rate
  cobol_equiv [cobolObs, javaObs, hm, hty, hbal, hrate, hdays, hz,
    AcctIntJava.accrue, AcctIntJava.ZERO2]

open AcctInt in
/-- The LOW-VALUES case: the program zeroes the balance, the Java method gets `null`. -/
theorem acctint_equiv_lowvalues (m : Mem) (hm : m.size = 33) (ty : UInt8) (rate : Int)
    (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hraw : m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0])
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) :
    cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) =
      javaObs (AcctIntJava.accrue (Codepage.cp037Char ty) none (.valueOf rate 5) days) := by
  cobol_ranges
  have := daily_rate_eq rate
  cobol_equiv [cobolObs, javaObs, hm, hty, hraw, hrate, hdays, AcctIntJava.accrue,
    AcctIntJava.ZERO2]

#print axioms acctint_equiv
#print axioms acctint_equiv_lowvalues
