import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH3

/-!
# CBTRN02C → Java: `db2Timestamp`, `reasonDesc`

`db2Timestamp(clock)`: `YYYY-MM-DD-HH.MM.SS.HH0000` from the first 16 characters of the clock
reading.  `reasonDesc(reason)`: the description of a reject reason.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The description `reasonDesc` returns for reason `k` (100 … 103). -/
def descJ (k : Int) : JStr :=
  if k = 100 then JStr.ofString "INVALID CARD NUMBER FOUND"
  else if k = 101 then JStr.ofString "ACCOUNT RECORD NOT FOUND"
  else if k = 102 then JStr.ofString "OVERLIMIT TRANSACTION"
  else JStr.ofString "TRANSACTION RECEIVED AFTER ACCT EXPIRATION"

abbrev reasonDescRef : MethodRef := Gen.Cbtrn02c.«reasonDesc(int)».ref

def reasonDescSpec : Spec := Spec.of
  (fun args _ => ∃ k : I32, args = [.int k] ∧ (k = 100#32 ∨ k = 101#32 ∨ k = 102#32 ∨ k = 103#32))
  (fun args σ r σ' => ∀ k : I32, args = [.int k] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (descJ k.toInt)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem reasonDesc_vc :
    MethodVC Gen.prog (fun _ => none) 0 reasonDescRef reasonDescSpec [] 20 := by
  jverify [reasonDescSpec, Grows, descJ]


end EquivLean.Modernize.Cbtrn02c.Java
