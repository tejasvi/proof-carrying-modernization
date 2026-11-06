import EquivLean.Modernize.Cbtrn01c.JavaRunLib

/-!
# CBTRN01C → Java: the helpers `spaces` and `digits`

`spaces(n)`: `n` spaces. `digits(v, n)`: the last `n` decimal digits of `|v|`, zero-padded
(`v > Long.MIN_VALUE`). One loop invariant each.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

/-! ### `spaces` -/

abbrev spacesRef : MethodRef := Gen.Cbtrn01c.«spaces(int)».ref

def spacesSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ n.toInt < 2147483647)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (spJ n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn01c" = σ.initOf "Cbtrn01c")

/-- At the loop head (statement 4): the builder holds `i` spaces. -/
def spacesInv : Invariants := [(4, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (spJ i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn01c" = σ0.initOf "Cbtrn01c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv 60 := by
  jverify [spacesSpec, spacesInv, Grows, spJ_succ, valueOfArg_char]

/-! ### `digits` -/

abbrev digitsRef : MethodRef := Gen.Cbtrn01c.«digits(long,int)».ref

def digitsSpec : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 0 ≤ n.toInt ∧ n.toInt < 2147483647)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadJ v.toInt.natAbs n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn01c" = σ.initOf "Cbtrn01c")

/-- At the loop head (statement 8): positions `i+1 …` of the array hold the digits written so
    far, and the rest of the number is `l`. -/
def digitsInv : Invariants := [(8, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i l xs, fr.get 4 = some (.int i) ∧ fr.get 1 = some (.long l) ∧ fr.get 6 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    0 ≤ l.toInt ∧ -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    zpadJ v.toInt.natAbs n.toInt.toNat =
      zpadJ l.toNat (i.toInt + 1).toNat ++ Native.charsOf (xs.drop (i.toInt + 1).toNat) ∧
    σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn01c" = σ0.initOf "Cbtrn01c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem digits_vc : MethodVC Gen.prog (fun _ => none) 0 digitsRef digitsSpec digitsInv 80 := by
  jverify [digitsSpec, digitsInv, Grows, zpadJ, digitJ, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char2, drop_set_self, cmp_zero_nonneg_iff, pos_toNat, negNat, toNat_add_one_of_neg,
    charsOf_cons_int, charsOf_replicate_drop, int_add_neg_one_add_one]

end EquivLean.Modernize.Cbtrn01c.Java
