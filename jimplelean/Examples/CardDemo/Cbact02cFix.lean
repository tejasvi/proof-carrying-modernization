/-
  Examples/CardDemo/Cbact02cFix.lean

  `Cbact02c.fix(String, int)`: the first `n` characters of `s` (`""` for `null`), padded with
  spaces to `n`. One loop invariant (statement 7, the loop head). The contract is stated with
  the argument's text `argText σ sv` (a function of the argument), so that the precondition, the
  invariant and the postcondition talk about the same string.
-/
import Examples.CardDemo.Cbact02cProg

open Jimple

namespace Examples.CardDemo

abbrev fixRef : MethodRef := CB.Cbact02c.«fix(java.lang.String,int)».ref

def fixSpec : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 7): the builder holds the first `i` characters. -/
def fixInv : Invariants := [(7, fun args σ0 fr σ => ∀ sv n, args = [sv, .int n] →
  ∃ sb sr i, fr.get 0 = some (.int n) ∧ fr.get 2 = some (.int i) ∧ fr.get 3 = some (.ref sb) ∧
    fr.get 5 = some (.ref sr) ∧ σ.heap sr = some (.str (argText σ0 sv)) ∧
    (argText σ0 sv).length < 2147483648 ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr (argText σ0 sv) i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem fix_vc : MethodVC CB.prog (fun _ => none) 0 fixRef fixSpec fixInv 60 := by
  jverify [ite_nat_ne, fixSpec, fixInv, StrOk, argText, Grows, fixStr]

end Examples.CardDemo

#print axioms Examples.CardDemo.fix_vc
