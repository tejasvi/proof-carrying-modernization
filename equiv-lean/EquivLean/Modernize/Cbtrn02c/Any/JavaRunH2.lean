import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH1

/-!
# CBTRN02C → Java: `padNum`

`padNum(v, n)`: the digits of `|v|`, least significant first, into `rev` (`revD`), then `rev`
reversed: the last `n` decimal digits of `|v|`, zero-padded (`zpadJ`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev padNumRef : MethodRef := Gen.Cbtrn02c.«padNum(long,int)».ref

def padNumSpec : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 0 ≤ n.toInt ∧ n.toInt < 2147483647)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadJ v.toInt.natAbs n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- Statement 9 (first loop): `rev` holds the last `i` digits of `|v|`, least significant first;
`a = |v| / 10^i`.  Statement 21 (second loop): `sb` holds `rev` from index `i + 1` on, reversed. -/
def padNumInv : Invariants :=
  [(9, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
    ∃ rev i a, fr.get 0 = some (.long a) ∧ fr.get 4 = some (.int n) ∧ fr.get 6 = some (.int i) ∧
      fr.get 7 = some (.ref rev) ∧
      σ.heap rev = some (.builder "java.lang.StringBuilder" (revD v.toInt.natAbs i.toInt.toNat)) ∧
      0 ≤ a.toInt ∧ a.toNat = v.toInt.natAbs / 10 ^ i.toInt.toNat ∧
      0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ rev ∧ Grows σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"),
   (21, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
    ∃ rev sb i, fr.get 4 = some (.int i) ∧ fr.get 7 = some (.ref rev) ∧ fr.get 8 = some (.ref sb) ∧
      σ.heap rev = some (.builder "java.lang.StringBuilder" (revD v.toInt.natAbs n.toInt.toNat)) ∧
      σ.heap sb = some (.builder "java.lang.StringBuilder"
        ((revD v.toInt.natAbs n.toInt.toNat).drop (i.toInt + 1).toNat).reverse) ∧
      -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧ rev ≠ sb ∧ σ0.next ≤ rev ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem padNum_vc : MethodVC Gen.prog (fun _ => none) 0 padNumRef padNumSpec padNumInv 60 := by
  jverify [padNumSpec, padNumInv, Grows, valueOfArg_char, jchar_rt, digit_char3,
    sdiv10_toNat_of_nonneg, sdiv10_nonneg, cmp_zero_nonneg_iff, revD_reverse, revD_length]
  all_goals first
    | exact (revD_succ _ _).symm
    | (rw [Nat.pow_succ, Nat.div_div_eq_div_mul])
    | (rw [toNat_add_one_of_neg _ (by omega) (by omega), List.drop_zero, revD_reverse])
    | (rw [List.getElem?_eq_none_iff, revD_length] at hd; omega)
    | ((try rw [int_add_neg_one_add_one]); exact rev_drop_step _ _ _ hd)

end EquivLean.Modernize.Cbtrn02c.Java
