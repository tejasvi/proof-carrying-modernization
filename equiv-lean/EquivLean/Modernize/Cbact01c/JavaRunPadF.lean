import EquivLean.Modernize.Cbact01c.JavaRunConcat

/-!
# CBACT01C → Java: `spaces` and `pad` return new strings

The contracts of `Helpers` with the result a new object (`σ.next ≤ x`): the strings the record
methods store in the records they write are newer than the `Result` lists.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec

namespace EquivLean.Modernize.Cbact01c.Java

def spacesSpecF : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr [] n.toInt.toNat)) ∧ σ.next ≤ x ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vcF : MethodVC Gen.prog (fun _ => none) 0 spacesRef spacesSpecF spacesInv 60 := by
  jverify [spacesSpecF, spacesInv, Grows, fixStr]

def padSpecF : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       σ.next ≤ x ∧ Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pad_vcF : MethodVC Gen.prog (fun _ => none) 0 padRef padSpecF padInv 60 := by
  jverify [padSpecF, padInv, StrOk, argText, Grows, fixStr]

end EquivLean.Modernize.Cbact01c.Java

