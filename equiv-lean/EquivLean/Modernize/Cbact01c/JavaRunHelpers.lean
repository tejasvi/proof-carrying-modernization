import EquivLean.Modernize.Cbact01c.JavaRunProg

/-!
# CBACT01C → Java: the helpers `spaces` and `pad`

One loop invariant each (the loop heads, statements 4 and 9).
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec

namespace EquivLean.Modernize.Cbact01c.Java

abbrev spacesRef : MethodRef := Gen.Cbact01c.«spaces(int)».ref

def spacesSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr [] n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def spacesInv : Invariants := [(4, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr [] i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv 60 := by
  jverify [spacesSpec, spacesInv, Grows, fixStr]

abbrev padRef : MethodRef := Gen.Cbact01c.«pad(java.lang.String,int)».ref

def padSpec : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 9): the builder holds the first `i` characters; local 1 is the
length of the argument's text. Locals: `i0` 0, `$i2` 1, `i3` 2, `$r1` 3, `r0` 5. -/
def padInv : Invariants := [(9, fun args σ0 fr σ => ∀ sv n, args = [sv, .int n] →
  ∃ sb i len, fr.get 0 = some (.int n) ∧ fr.get 2 = some (.int i) ∧ fr.get 3 = some (.ref sb) ∧
    fr.get 5 = some sv ∧ fr.get 1 = some (.int len) ∧ len.toInt = (argText σ0 sv).length ∧
    (argText σ0 sv).length < 2147483648 ∧
    (sv = .null ∨ ∃ x, sv = .ref x ∧ σ.heap x = some (.str (argText σ0 sv))) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr (argText σ0 sv) i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pad_vc : MethodVC Gen.prog (fun _ => none) 0 padRef padSpec padInv 60 := by
  jverify [padSpec, padInv, StrOk, argText, Grows, fixStr]

end EquivLean.Modernize.Cbact01c.Java

