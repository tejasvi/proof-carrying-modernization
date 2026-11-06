import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: `spaces`, `fit`, `padNum`

`spaces(n)`: `n` spaces. `fit(s, n)`: the first `n` characters of `s`, padded with spaces.
`padNum(v, n)`: the last `n` decimal digits of `|v|`, zero-padded.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ### `spaces` -/

abbrev spacesRef : MethodRef := Gen.Cbtrn02c.«spaces(int)».ref

def spacesSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ n.toInt < 2147483647)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (spJ n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- At the loop head (statement 4): the builder holds `i` spaces. -/
def spacesInv : Invariants := [(4, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (spJ i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv 60 := by
  jverify [spacesSpec, spacesInv, Grows, spJ_succ, valueOfArg_char]

/-! ### `fit` -/

abbrev fitRef : MethodRef := Gen.Cbtrn02c.«fit(java.lang.String,int)».ref

def fitSpec : Spec := Spec.of
  (fun args σ => ∃ (s : Addr) (cs : JStr) (n : I32), args = [.ref s, .int n] ∧
     σ.heap s = some (.str cs) ∧ cs.length < 2147483648 ∧ 0 ≤ n.toInt ∧ n.toInt < 2147483647)
  (fun args σ r σ' => ∀ (s : Addr) (cs : JStr) (n : I32), args = [.ref s, .int n] →
     σ.heap s = some (.str cs) →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fitJ cs n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- At the loop head (statement 5): the builder holds the first `i` characters. -/
def fitInv : Invariants := [(5, fun args σ0 fr σ => ∀ (s : Addr) (cs : JStr) (n : I32),
  args = [.ref s, .int n] → σ0.heap s = some (.str cs) →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 2 = some (.int i) ∧ fr.get 3 = some (.ref sb) ∧
    fr.get 5 = some (.ref s) ∧ σ.heap s = some (.str cs) ∧ cs.length < 2147483648 ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fitJ cs i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fit_vc : MethodVC Gen.prog (fun _ => none) 0 fitRef fitSpec fitInv 60 := by
  jverify [fitSpec, fitInv, Grows, fitJ_zero, valueOfArg_char, jchar_rt]
  all_goals first
    | exact (fitJ_succ_ge _ _ (by omega)).symm
    | exact (fitJ_succ_lt _ _ _ (List.getElem?_eq_getElem _)).symm

end EquivLean.Modernize.Cbtrn02c.Java
