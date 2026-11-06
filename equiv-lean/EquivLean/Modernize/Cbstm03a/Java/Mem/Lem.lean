import EquivLean.Modernize.Cbstm03a.Java.Iface2

/-!
# CBSTM03A → Java, table memory: machine-arithmetic facts

`toNat`/`toInt` of the `int`/`long` operations the slot helpers use, on non-negative operands.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

theorem msb_false_of_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) : x.msb = false := by
  have hx := x.isLt
  rw [BitVec.toInt_eq_msb_cond] at h
  cases hm : x.msb
  · rfl
  · rw [hm] at h
    simp only [if_true] at h
    omega

theorem toInt_eq_toNat_of_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) : x.toInt = x.toNat := by
  have hm := msb_false_of_nonneg x h
  rw [BitVec.toInt_eq_msb_cond, hm]
  simp

theorem toInt_toNat_of_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) : x.toInt.toNat = x.toNat := by
  rw [toInt_eq_toNat_of_nonneg x h]
  simp

theorem toInt_eq_toNat_of_lt {n : Nat} (x : BitVec n) (h : 2 * x.toNat < 2 ^ n) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond, if_pos h]

theorem sdiv_toNat_of_nonneg {n : Nat} (x y : BitVec n) (hx : 0 ≤ x.toInt) (hy : y.msb = false) :
    (x.sdiv y).toNat = x.toNat / y.toNat := by
  rw [BitVec.sdiv_eq, msb_false_of_nonneg x hx, hy]
  simp [BitVec.toNat_udiv]

theorem srem_toNat_of_nonneg {n : Nat} (x y : BitVec n) (hx : 0 ≤ x.toInt) (hy : y.msb = false) :
    (x.srem y).toNat = x.toNat % y.toNat := by
  rw [BitVec.srem_eq, msb_false_of_nonneg x hx, hy]
  simp [BitVec.toNat_umod]

theorem bmod32_self {x : Int} (h1 : -2147483648 ≤ x) (h2 : x < 2147483648) : x.bmod (2 ^ 32) = x := by
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.cast_ofNat]
  split <;> omega

theorem bmod64_self {x : Int} (h1 : -9223372036854775808 ≤ x) (h2 : x < 9223372036854775808) :
    x.bmod (2 ^ 64) = x := by
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.cast_ofNat]
  split <;> omega

theorem signExtend_toNat_of_nonneg (x : BitVec 32) (h : 0 ≤ x.toInt) : (x.signExtend 64).toNat = x.toNat := by
  have h1 : (x.signExtend 64).toInt = x.toInt := by
    rw [BitVec.toInt_signExtend]
    have := BitVec.toInt_lt (x := x)
    have := BitVec.le_toInt (x := x)
    simp only [show min 64 32 = 32 from rfl]
    exact bmod32_self (by omega) (by omega)
  have h2 : 0 ≤ (x.signExtend 64).toInt := by omega
  have e1 := toInt_eq_toNat_of_nonneg _ h2
  have e2 := toInt_eq_toNat_of_nonneg _ h
  omega

theorem l2i_toNat (x : BitVec 64) : (JLong.toInt x).toNat = x.toNat % 2 ^ 32 := by
  simp [JLong.toInt, BitVec.toNat_setWidth]

theorem i2l_toNat_of_nonneg (x : BitVec 32) (h : 0 ≤ x.toInt) : (JInt.toLong x).toNat = x.toNat :=
  signExtend_toNat_of_nonneg x h

/-- `getTrct`/`setTrct`: the index `(int) (cr - 1)` for `1 ≤ cr ≤ 51`. -/
theorem l2i_sub_one_toInt (cr : BitVec 64) (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt ≤ 51) :
    (JLong.toInt (cr - 1#64)).toInt = cr.toInt - 1 := by
  have hc := cr.isLt
  have e0 := toInt_eq_toNat_of_nonneg cr (by omega)
  have e1 : (cr - 1#64).toNat = cr.toNat - 1 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have e2 : (JLong.toInt (cr - 1#64)).toNat = cr.toNat - 1 := by rw [l2i_toNat, e1]; omega
  rw [toInt_eq_toNat_of_lt _ (by rw [e2]; omega), e2]
  omega

theorem l2i_sub_one_toNat (cr : BitVec 64) (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt ≤ 51) :
    (JLong.toInt (cr - 1#64)).toNat = cr.toInt.toNat - 1 := by
  have e := l2i_sub_one_toInt cr h1 h2
  have e0 := toInt_eq_toNat_of_nonneg cr (by omega)
  have hc := BitVec.toInt_eq_toNat_cond (JLong.toInt (cr - 1#64))
  have hl := (JLong.toInt (cr - 1#64)).isLt
  split at hc <;> omega

theorem l2i_zero_toInt : (JLong.toInt 0#64).toInt = 0 := by decide
theorem l2i_fifty_toInt : (JLong.toInt 50#64).toInt = 50 := by decide

/-- `slotLen`/`slotStart`: the test `idx % 11 == 0` for `idx ≥ 0`. -/
theorem srem11_eq_zero_iff (w : BitVec 32) (h : 0 ≤ w.toInt) : w.srem 11#32 = 0#32 ↔ w.toInt.toNat % 11 = 0 := by
  rw [toInt_toNat_of_nonneg w h, ← BitVec.toNat_inj, srem_toNat_of_nonneg w _ h (by decide)]
  simp

theorem toNat_lt_of_nonneg32 (w : BitVec 32) (h : 0 ≤ w.toInt) : w.toNat < 2147483648 := by
  have := msb_false_of_nonneg w h
  rw [BitVec.msb_eq_false_iff_two_mul_lt] at this
  omega

theorem sdiv11_toNat (w : BitVec 32) (h : 0 ≤ w.toInt) : (JInt.toLong (w.sdiv 11#32)).toNat = w.toNat / 11 := by
  have hd : (w.sdiv 11#32).toNat = w.toNat / 11 := by rw [sdiv_toNat_of_nonneg w _ h (by decide)]; rfl
  have hl := toNat_lt_of_nonneg32 w h
  have h0 : 0 ≤ (w.sdiv 11#32).toInt := by
    rw [toInt_eq_toNat_of_lt _ (by rw [hd]; omega)]; omega
  rw [i2l_toNat_of_nonneg _ h0, hd]

theorem srem11_sub1_toNat (w : BitVec 32) (h : 0 ≤ w.toInt) (hc : ¬ w.toNat % 11 = 0) :
    (JInt.toLong (w.srem 11#32 - 1#32)).toNat = w.toNat % 11 - 1 := by
  have hr : (w.srem 11#32).toNat = w.toNat % 11 := by rw [srem_toNat_of_nonneg w _ h (by decide)]; rfl
  have hs : (w.srem 11#32 - 1#32).toNat = w.toNat % 11 - 1 := by
    rw [BitVec.toNat_sub, hr]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have h0 : 0 ≤ (w.srem 11#32 - 1#32).toInt := by
    rw [toInt_eq_toNat_of_lt _ (by rw [hs]; omega)]; omega
  rw [i2l_toNat_of_nonneg _ h0, hs]

theorem slotStart_eq0 (w : I32) (h : 0 ≤ BitVec.toInt w) :
    JInt.toLong (BitVec.sdiv w 11#32) * 3356#64 = BitVec.ofNat 64 ((BitVec.toInt w).toNat / 11) * 3356#64 := by
  have hl := toNat_lt_of_nonneg32 w h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_mul, sdiv11_toNat w h, toInt_toNat_of_nonneg w h]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem slotStart_eq1 (w : I32) (h : 0 ≤ BitVec.toInt w) (hc : ¬(BitVec.toInt w).toNat % 11 = 0) :
    JInt.toLong (BitVec.sdiv w 11#32) * 3356#64 + 16#64 + JInt.toLong (BitVec.srem w 11#32 - 1#32) * 334#64 =
      BitVec.ofNat 64 ((BitVec.toInt w).toNat / 11 * 3356 + (16 + ((BitVec.toInt w).toNat % 11 - 1) * 334)) := by
  have hl := toNat_lt_of_nonneg32 w h
  rw [toInt_toNat_of_nonneg w h] at hc ⊢
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, sdiv11_toNat w h,
    srem11_sub1_toNat w h hc]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem l2i_srem3356_toInt (w : I64) (h : 0 ≤ w.toInt) :
    (JLong.toInt (BitVec.srem w 3356#64)).toInt = ((w.toNat % 3356 : Nat) : Int) := by
  have hr : (w.srem 3356#64).toNat = w.toNat % 3356 := by rw [srem_toNat_of_nonneg w _ h (by decide)]; rfl
  have hl : (JLong.toInt (w.srem 3356#64)).toNat = w.toNat % 3356 := by rw [l2i_toNat, hr]; omega
  rw [toInt_eq_toNat_of_lt _ (by rw [hl]; omega), hl]

theorem slotIndex_eq0 (w : I64) (h0 : 0 ≤ BitVec.toInt w) (h1 : BitVec.toInt w < 171156) :
    JLong.toInt (BitVec.sdiv w 3356#64) * 11#32 = BitVec.ofNat 32 (BitVec.toNat w / 3356) * 11#32 := by
  have e0 := toInt_eq_toNat_of_nonneg w h0
  have hd : (w.sdiv 3356#64).toNat = w.toNat / 3356 := by rw [sdiv_toNat_of_nonneg w _ h0 (by decide)]; rfl
  have hl1 : (JLong.toInt (w.sdiv 3356#64)).toNat = w.toNat / 3356 := by rw [l2i_toNat, hd]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_mul, hl1]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem slotIndex_eq1 (w : I64) (h0 : 0 ≤ BitVec.toInt w) (h1 : BitVec.toInt w < 171156)
    (hc : ¬BitVec.toNat w % 3356 < 16) :
    JLong.toInt (BitVec.sdiv w 3356#64) * 11#32 +
        (1#32 + BitVec.sdiv (JLong.toInt (BitVec.srem w 3356#64) - 16#32) 334#32) =
      BitVec.ofNat 32 (BitVec.toNat w / 3356 * 11 + (1 + (BitVec.toNat w % 3356 - 16) / 334)) := by
  have e0 := toInt_eq_toNat_of_nonneg w h0
  have hd : (w.sdiv 3356#64).toNat = w.toNat / 3356 := by rw [sdiv_toNat_of_nonneg w _ h0 (by decide)]; rfl
  have hr : (w.srem 3356#64).toNat = w.toNat % 3356 := by rw [srem_toNat_of_nonneg w _ h0 (by decide)]; rfl
  have hl1 : (JLong.toInt (w.sdiv 3356#64)).toNat = w.toNat / 3356 := by rw [l2i_toNat, hd]; omega
  have hl2 : (JLong.toInt (w.srem 3356#64)).toNat = w.toNat % 3356 := by rw [l2i_toNat, hr]; omega
  have hs : (JLong.toInt (w.srem 3356#64) - 16#32).toNat = w.toNat % 3356 - 16 := by
    rw [BitVec.toNat_sub, hl2]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have hs0 : 0 ≤ (JLong.toInt (w.srem 3356#64) - 16#32).toInt := by
    rw [toInt_eq_toNat_of_lt _ (by rw [hs]; omega)]; omega
  have hq : (BitVec.sdiv (JLong.toInt (w.srem 3356#64) - 16#32) 334#32).toNat = (w.toNat % 3356 - 16) / 334 := by
    rw [sdiv_toNat_of_nonneg _ _ hs0 (by decide), hs]; rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, hl1, hq]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

end EquivLean.Modernize.Cbstm03a.Java.Mem
