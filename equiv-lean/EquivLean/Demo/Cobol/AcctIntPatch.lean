import Cobol
import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Cobol.Obs
import EquivLean.Bridge.Cobol.Tactic

/-!
# A same-language COBOL patch: `COMPUTE … ROUNDED = A / B` ↦ `DIVIDE A BY B GIVING … ROUNDED`

`examples/cobol/acctint2/ACCTINT2.cob` is ACCTINT with one statement changed:

    COMPUTE WS-DAILY-RATE ROUNDED = ACCT-RATE / 365.          (old)
    DIVIDE ACCT-RATE BY 365 GIVING WS-DAILY-RATE ROUNDED.     (new)

The two are not the same computation: `COMPUTE` evaluates the quotient with IBM's
intermediate precision (9 places, truncated) and then rounds into `WS-DAILY-RATE`;
`DIVIDE … GIVING … ROUNDED` rounds the exact quotient once.  `acctint_patch` proves that on
every storage holding a valid account record the patch is behaviour-preserving: both programs
are safe, end with the same signal and output, and leave the same bytes in the balance,
interest, daily-rate and status fields (`CobolEquivOn`, `ObsEq`).  The arithmetic fact is
`daily_rate_eq` (half-up rounding looks at the first dropped digit only).

Both programs are loaded with `cobol_program` from their surface IR (`acctint2.ir.json` is the
extractor output for ACCTINT2: the `compute` node of `acctint.ir.json` replaced by a `divide`
node, `examples/cobol/acctint2/mk_acctint2.py`).  The proof is `equiv_cobol`: evaluate both
runs symbolically, compare with `cobol_grind`.
-/

open Cobol

cobol_program AcctIntOld from "../../../examples/cobol/acctint/acctint.ir.json"
cobol_program AcctIntNew from "../../../examples/cobol/acctint2/acctint2.ir.json"

namespace EquivLean.Demo.AcctIntPatch

open EquivLean.Cobol

/-- Storage holding a valid account record (the inputs on which the patch must not change
behaviour). -/
def ValidRec (m : Mem) : Prop :=
  m.size = 33 ∧ (∃ ty : UInt8, m.field AcctIntOld.ACCT_TYPE = [ty]) ∧
    (∃ bal : Int,
      decodeNum {} AcctIntOld.ACCT_BALANCE.fmt (m.field AcctIntOld.ACCT_BALANCE) = some bal) ∧
    (∃ rate : Int, decodeNum {} AcctIntOld.ACCT_RATE.fmt (m.field AcctIntOld.ACCT_RATE) = some rate) ∧
    (∃ days : Int, decodeNum {} AcctIntOld.ACCT_DAYS.fmt (m.field AcctIntOld.ACCT_DAYS) = some days)

/-- The observed fields: new balance, interest, daily rate and status byte. -/
abbrev obsFields : List FieldDesc :=
  [AcctIntOld.ACCT_BALANCE, AcctIntOld.WS_INTEREST, AcctIntOld.WS_DAILY_RATE, AcctIntOld.WS_STATUS]

/-- COBOL's two roundings of the daily rate equal one half-up rounding of the exact quotient. -/
theorem daily_rate_eq (rate : Int) :
    Cobol.divRound .nearestAwayFromZero (Cobol.divRound .truncation (rate * 10000) 365) 10 =
      Cobol.divRound .nearestAwayFromZero (rate * 1000) 365 := by
  cobol_arith

/-- **The patch changes nothing on valid records.** -/
theorem acctint_patch :
    CobolEquivOn (fun m => ¬ ValidRec m) obsFields AcctIntOld AcctIntNew {} 20 [] := by
  intro m hm
  simp only [Classical.not_not] at hm
  obtain ⟨hsize, ⟨ty, hty⟩, ⟨bal, hbal⟩, ⟨rate, hrate⟩, ⟨days, hdays⟩⟩ := hm
  cobol_ranges
  have hz : ¬ m.field AcctIntOld.ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0] := by
    intro h; cobol_sym [h] at hbal
  have := daily_rate_eq rate
  equiv_cobol [hsize, hty, hbal, hrate, hdays, hz]

end EquivLean.Demo.AcctIntPatch

#print axioms EquivLean.Demo.AcctIntPatch.acctint_patch
