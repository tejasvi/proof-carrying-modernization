import EquivLean.Modernize.Cbstm03b.Java.Base

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

/-- After the loop's length call (statement 15): the builder holds the text padded to its length `k` (local
`$i1`). Locals: `i0` 0, `$i1` 1, `$r1` 2, `$r0` 3. -/
def fitInv : Invariants := [(15, fun args σ0 fr σ => ∀ sv n, args = [sv, .int n] →
  ∃ sb sr k, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int k) ∧ fr.get 2 = some (.ref sb) ∧
    fr.get 3 = some (.ref sr) ∧ σ.heap sr = some (.str (argText σ0 sv)) ∧
    (argText σ0 sv).length < n.toInt.toNat ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr (argText σ0 sv) k.toInt.toNat)) ∧
    0 ≤ k.toInt ∧ (argText σ0 sv).length ≤ k.toInt.toNat ∧ k.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.hypHeapFacts true in
theorem fit_vc : MethodVC Gen.prog (fun _ => none) 0 fitRef fitSpec fitInv 60 := by
  jverify [ite_nat_ne, fitSpec, fitInv, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.fit_vc
