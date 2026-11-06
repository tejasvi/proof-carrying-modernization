import EquivLean.Demo.Thrift.Java.Rv32P

/-!
# Thrift → Java (T4): zigzag, i32 and i64, both directions

`intToZigZag(n) = (n << 1) ^ (n >> 31)`, `zigzagToInt(n) = (n >>> 1) ^ -(n & 1)`, and the `long`
versions with 63 and `1L`. (E) the encoder gives `zigzag n`; (D) the decoder gives `unzigzag u` for
every pattern `u` (it is total: no input is malformed), so on `zigzag n` it gives `n`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## Bits -/

theorem sshr_last {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0
    by_cases hm : x.getLsbD (w - 1) <;> simp [hm, hi, show ¬ w ≤ 0 by omega, show w - 1 + 0 < w by omega]
  · have h1 : ¬ (w - 1 + i < w) := by omega
    by_cases hm : x.getLsbD (w - 1) <;> simp [hm, hi, h1, show ¬ w ≤ i by omega]

theorem toNat_fill {w : Nat} (b : Bool) :
    (if b then BitVec.allOnes w else 0#w).toNat = if b then 2 ^ w - 1 else 0 := by
  cases b <;> simp [BitVec.toNat_allOnes]

theorem msb_iff_toInt_neg {w : Nat} (hw : 0 < w) (x : BitVec w) : x.msb = true ↔ x.toInt < 0 := by
  rw [BitVec.toInt_neg_iff, BitVec.msb_eq_decide]
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  simp only [decide_eq_true_eq]
  omega

theorem zz_toNat {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((x <<< 1) ^^^ x.sshiftRight (w - 1)).toNat =
      (x.toNat * 2 % 2 ^ w) ^^^ (if x.toInt < 0 then 2 ^ w - 1 else 0) := by
  rw [BitVec.toNat_xor, sshr_last hw, toNat_fill, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  by_cases h : x.toInt < 0
  · rw [if_pos ((msb_iff_toInt_neg hw x).mpr h), if_pos h]
  · have : x.msb = false := by
      cases hm : x.msb
      · rfl
      · exact absurd ((msb_iff_toInt_neg hw x).mp hm) h
    rw [this, if_neg h]
    rfl

theorem neg_and_one_toNat {w : Nat} (hw : 0 < w) (u : BitVec w) :
    (-(u &&& 1#w)).toNat = if u.toNat % 2 = 0 then 0 else 2 ^ w - 1 := by
  have h1 : (u &&& 1#w).toNat = u.toNat % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega)),
      show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_neg, h1]
  have hp : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw
    simpa using this
  by_cases h : u.toNat % 2 = 0
  · rw [h, if_pos rfl, Nat.sub_zero, Nat.mod_self]
  · have h' : u.toNat % 2 = 1 := by omega
    rw [h', if_neg (by omega), Nat.mod_eq_of_lt (by omega)]

theorem uzz_toNat {w : Nat} (hw : 0 < w) (u : BitVec w) :
    ((u >>> 1) ^^^ -(u &&& 1#w)).toNat = (u.toNat / 2) ^^^ (if u.toNat % 2 = 0 then 0 else 2 ^ w - 1) := by
  rw [BitVec.toNat_xor, neg_and_one_toNat hw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.pow_one]

/-! ## The 32-bit results on values -/

theorem toU64_toInt (x : I64) : Spec.toU 64 x.toInt = x.toNat := by
  have hx := x.isLt
  have hc := BitVec.toInt_eq_toNat_cond x
  have key : ((Spec.toU 64 x.toInt : Nat) : Int) = (x.toNat : Int) := by
    by_cases h : 2 * x.toNat < 2 ^ 64
    · rw [if_pos h] at hc
      rw [Spec.toU_of_nonneg (by rw [hc]; omega) (by rw [hc]; simp; omega), hc]
    · rw [if_neg h] at hc
      rw [Spec.toU_of_neg (by rw [hc]; simp at h ⊢; omega) (by rw [hc]; simp; omega), hc]
      simp
  exact_mod_cast key

theorem inI32_toInt (x : I32) : Spec.InI32 x.toInt := by
  have := BitVec.toInt_lt (x := x)
  have := BitVec.le_toInt (x := x)
  unfold Spec.InI32
  constructor <;> simp_all <;> omega

theorem inI64_toInt (x : I64) : Spec.InI64 x.toInt := by
  have := BitVec.toInt_lt (x := x)
  have := BitVec.le_toInt (x := x)
  unfold Spec.InI64
  constructor <;> simp_all <;> omega

/-- (E) `intToZigZag`: `(n << 1) ^ (n >> 31)` is `zigzag n`. -/
theorem zz32_val (n : I32) :
    (JInt.shl n 1#32 ^^^ JInt.shr n 31#32).toNat = Spec.zigzag n.toInt := by
  simp only [JInt.shl, JInt.shr, show (1#32 : I32).toNat % 32 = 1 from rfl,
    show (31#32 : I32).toNat % 32 = 31 from rfl]
  rw [show (31 : Nat) = 32 - 1 from rfl, zz_toNat (by decide), Spec.zigzag_xor32 (inI32_toInt n),
    toU32_toInt]

/-- (E) `longToZigzag`: `(l << 1) ^ (l >> 63)` is `zigzag l`. -/
theorem zz64_val (n : I64) :
    (JLong.shl n 1#32 ^^^ JLong.shr n 63#32).toNat = Spec.zigzag n.toInt := by
  simp only [JLong.shl, JLong.shr, show (1#32 : I32).toNat % 64 = 1 from rfl,
    show (63#32 : I32).toNat % 64 = 63 from rfl]
  rw [show (63 : Nat) = 64 - 1 from rfl, zz_toNat (by decide), Spec.zigzag_xor64 (inI64_toInt n),
    toU64_toInt]

/-- (D) `zigzagToInt`: `(n >>> 1) ^ -(n & 1)` is `unzigzag n`, for every pattern `n`. -/
theorem uzz32_val (u : I32) :
    (JInt.ushr u 1#32 ^^^ -(u &&& 1#32)).toInt = Spec.unzigzag u.toNat := by
  have h1 : JInt.ushr u 1#32 = u >>> 1 := rfl
  rw [h1, BitVec.toInt_eq_toNat_bmod, uzz_toNat (by decide), ← Spec.unzigzag_xor32 u.isLt]
  exact Spec.toS_toU32 (Spec.unzigzag_range32 u.isLt)

/-- (D) `zigzagToLong`: `(n >>> 1) ^ -(n & 1L)` is `unzigzag n`, for every pattern `n`. -/
theorem uzz64_val (u : I64) :
    (JLong.ushr u 1#32 ^^^ -(u &&& 1#64)).toInt = Spec.unzigzag u.toNat := by
  have h1 : JLong.ushr u 1#32 = u >>> 1 := rfl
  rw [h1, BitVec.toInt_eq_toNat_bmod, uzz_toNat (by decide), ← Spec.unzigzag_xor64 u.isLt]
  exact Spec.toS_toU64 (Spec.unzigzag_range64 u.isLt)

end EquivLean.Demo.Thrift.Java
