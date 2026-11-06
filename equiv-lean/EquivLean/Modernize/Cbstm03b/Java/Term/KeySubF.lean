import EquivLean.Modernize.Cbstm03b.Java.HKeySub

/-!
# CBSTM03B → Java: `keySub` with a fresh result (for termination)

`keySubSpecT`: on an area whose key field is a 25-character string and whose key length is small, `keySub` returns
a new string (`substring` allocates) of at most 25 characters.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

/-- `keySub(area)` for termination: a new string of at most 25 characters. -/
def keySubSpecT : Spec := Spec.of
  (fun args σ => ∃ q skey fs key kl, args = [.ref q] ∧ σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fs) ∧
     Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKey") = some (.ref skey) ∧ σ.heap skey = some (.str key) ∧
     key.length = 25 ∧ Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)) ∧
     -10000 < kl ∧ kl < 10000)
  (fun _ σ r σ' => ∃ x s, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str s) ∧ s.length ≤ 25 ∧
     Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem keySubT_vc : MethodVC Gen.prog (fun _ => none) 0 keySubRef keySubSpecT [] 60 := by
  jverify [keySubSpecT, Grows]
  all_goals (rw [long_to_int_small (by omega) (by omega)] at *; omega)

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.keySubT_vc
