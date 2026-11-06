import EquivLean.Modernize.Cbstm03b.Java.HStatus2
import EquivLean.Modernize.Cbstm03b.Java.HFit

/-!
# CBSTM03B → Java: `status2` and `fit` with fresh results

The contracts `trnxProc` and `xrefProc` are verified against: `status2SpecF` and `fitSpecF` add to `status2Spec`
and `fitSpec` that the returned string is a new object (for `fit`: or the argument itself).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

def status2SpecF : Spec := Spec.of
  (fun args _ => ∃ c : I32, args = [.int c] ∧ 0 ≤ c.toInt ∧ c.toInt < 100)
  (fun args σ r σ' => ∀ c : I32, args = [.int c] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (stChars c.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def fitSpecF : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ (σ.next ≤ x ∨ sv = .ref x) ∧
       σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def seqCalleesF : Contracts := [(status2Sig, status2SpecF), (fitSig, fitSpecF)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem status2F_vc : MethodVC Gen.prog (fun _ => none) 0 status2Ref status2SpecF [] 40 := by
  jverify [status2SpecF, stChars, Grows, status2_hi, status2_lo]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.hypHeapFacts true in
theorem fitF_vc : MethodVC Gen.prog (fun _ => none) 0 fitRef fitSpecF fitInv 60 := by
  jverify [ite_nat_ne, fitSpecF, fitInv, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.status2F_vc
#print axioms EquivLean.Modernize.Cbstm03b.Java.fitF_vc
