import EquivLean.Modernize.Cbstm03a.Java.Term2.Defs

/-!
# CBSTM03A → Java, termination: machine-arithmetic facts

`toInt`/`toNat` of the `int`/`long` values `memWrite` and `memRead` compute, on their ranges.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

theorem bmod32_self' {x : Int} (h1 : -2147483648 ≤ x) (h2 : x < 2147483648) : x.bmod (2 ^ 32) = x := by
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.cast_ofNat]
  split <;> omega

theorem bmod64_self' {x : Int} (h1 : -9223372036854775808 ≤ x) (h2 : x < 9223372036854775808) :
    x.bmod (2 ^ 64) = x := by
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.cast_ofNat]
  split <;> omega

theorem toNat_ofNat32 {k : Nat} (h : k < 4294967296) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat]; omega

theorem toNat_ofNat64 {k : Nat} (h : k < 18446744073709551616) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat]; omega

theorem toInt_of_toNat_lt {n : Nat} (x : BitVec n) (h : 2 * x.toNat < 2 ^ n) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; exact ite_eq_left_of_eq_true _ _ (eq_true h)

theorem toInt_ofNat32 {k : Nat} (h : k < 2147483648) : (BitVec.ofNat 32 k).toInt = k := by
  rw [toInt_of_toNat_lt _ (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega)]

theorem toNat_of_toInt_nonneg64 (x : I64) (h : 0 ≤ x.toInt) : (x.toNat : Int) = x.toInt := by
  have hx := x.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  simp only [Nat.reducePow] at *
  split <;> split at h <;> omega

theorem toLong_toInt (x : I32) : (JInt.toLong x).toInt = x.toInt := by
  unfold JInt.toLong
  rw [BitVec.toInt_signExtend]
  have := BitVec.toInt_lt (x := x)
  have := BitVec.le_toInt (x := x)
  simp only [show min 64 32 = 32 from rfl]
  exact bmod32_self' (by omega) (by omega)

theorem toInt_add64 (x y : I64) (h1 : -9223372036854775808 ≤ x.toInt + y.toInt)
    (h2 : x.toInt + y.toInt < 9223372036854775808) : (x + y).toInt = x.toInt + y.toInt := by
  rw [BitVec.toInt_add]; exact bmod64_self' h1 h2

theorem toInt_neg64 (x : I64) (h1 : -9223372036854775808 < x.toInt) : (-x).toInt = -x.toInt := by
  rw [BitVec.toInt_neg]
  have := BitVec.toInt_lt (x := x)
  exact bmod64_self' (by simp at *; omega) (by simp at *; omega)

theorem l2i_toInt (x : I64) (h1 : -2147483648 ≤ x.toInt) (h2 : x.toInt < 2147483648) :
    (JLong.toInt x).toInt = x.toInt := by
  have hx := x.isLt
  have e1 : (JLong.toInt x).toNat = x.toNat % 4294967296 := by
    simp [JLong.toInt, BitVec.toNat_setWidth]
  rw [BitVec.toInt_eq_toNat_cond x] at h1 h2 ⊢
  rw [BitVec.toInt_eq_toNat_cond (JLong.toInt x), e1]
  simp only [Nat.reducePow] at *
  split <;> split <;> split at h1 <;> split at h2 <;> omega

theorem toInt_sub64 (x y : I64) (h1 : -9223372036854775808 ≤ x.toInt - y.toInt)
    (h2 : x.toInt - y.toInt < 9223372036854775808) : (x - y).toInt = x.toInt - y.toInt := by
  rw [BitVec.toInt_sub]; exact bmod64_self' h1 h2

theorem toInt_ofNat64 {k : Nat} (h : k < 9223372036854775808) : (BitVec.ofNat 64 k).toInt = k := by
  rw [toInt_of_toNat_lt _ (by rw [toNat_ofNat64 (by omega)]; omega), toNat_ofNat64 (by omega)]

end EquivLean.Modernize.Cbstm03a.Java.Term2
