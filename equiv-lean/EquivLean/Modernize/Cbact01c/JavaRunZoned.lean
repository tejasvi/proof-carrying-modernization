import EquivLean.Modernize.Cbact01c.JavaRunZLemmas

/-!
# CBACT01C → Java: the helper `zoned(v, n, signed)`

Two loops: `div = 10^(n-1)` (statement 15), then the digits from the left (statement 22), the
last one overpunched with the sign when `signed`.
Locals: `l0` 0 (`|v|`), `$l3` 1, `l14` 2 (`div`), `$c12` 3, `i1` 5 (`n`), `i5` 6, `i15` 8 (`i`),
`$r0` 9, `z0` 11 (`signed`), `$z2` 12 (`neg`), `$z3` 13.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

abbrev zonedRef : MethodRef := Gen.Cbact01c.«zoned(long,int,boolean)».ref

def zonedSpec : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n z : I32), args = [.long v, .int n, .int z] ∧
     v.toInt.natAbs < 10 ^ 18 ∧ 1 ≤ n.toInt ∧ n.toInt ≤ 18)
  (fun args σ r σ' => ∀ (v : I64) (n z : I32), args = [.long v, .int n, .int z] →
     ∃ x, r = some (.ref x) ∧
       σ'.heap x = some (.str (zonedJ v.toInt n.toInt.toNat (decide (z ≠ 0)))) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def zonedInv : Invariants :=
  [(15, fun args σ0 fr σ => ∀ (v : I64) (n z : I32), args = [.long v, .int n, .int z] →
     ∃ (a d : I64) (i : I32), fr.get 0 = some (.long a) ∧ fr.get 2 = some (.long d) ∧
       fr.get 8 = some (.int i) ∧ fr.get 5 = some (.int n) ∧ fr.get 11 = some (.int z) ∧
       fr.get 12 = some (.int (ngOf v)) ∧ a.toNat = v.toInt.natAbs ∧ 0 ≤ a.toInt ∧
       1 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ d.toNat = 10 ^ (i.toInt.toNat - 1) ∧
       d.toNat < 10 ^ 18 ∧ σ = σ0),
   (22, fun args σ0 fr σ => ∀ (v : I64) (n z : I32), args = [.long v, .int n, .int z] →
     ∃ (a d : I64) (i : I32) (sb : Addr), fr.get 0 = some (.long a) ∧ fr.get 2 = some (.long d) ∧
       fr.get 8 = some (.int i) ∧ fr.get 5 = some (.int n) ∧ fr.get 11 = some (.int z) ∧
       fr.get 12 = some (.int (ngOf v)) ∧ a.toNat = v.toInt.natAbs ∧ 0 ≤ a.toInt ∧
       0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ 0 ≤ d.toInt ∧
       (i.toInt < n.toInt → d.toNat = 10 ^ (n.toInt.toNat - 1 - i.toInt.toNat)) ∧
       fr.get 9 = some (.ref sb) ∧
       σ.heap sb = some (.builder "java.lang.StringBuilder"
         (zonedPre v.toInt.natAbs n.toInt.toNat (decide (z ≠ 0)) (decide (v.toInt < 0)) i.toInt.toNat)) ∧
       σ0.next ≤ sb ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zoned_vc : MethodVC Gen.prog (fun _ => none) 0 zonedRef zonedSpec zonedInv 80 := by
  jverify [zonedSpec, zonedInv, Grows, zonedJ, zonedPre, zch, digitJ, overpunch, ngOf, toInt_digit,
    digit_eq_zero, char48, char74, char65, sdiv10_toNat_of_nonneg, sdiv10_nonneg, mul10_toNat,
    pow10_pred_mul, pow10_div10, pow10_lt18, abs_neg_toNat, abs_neg_nonneg, abs_toNat]
  all_goals zoned_close

end EquivLean.Modernize.Cbact01c.Java

