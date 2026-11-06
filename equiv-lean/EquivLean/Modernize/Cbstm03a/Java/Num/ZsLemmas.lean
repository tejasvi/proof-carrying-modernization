import EquivLean.Modernize.Cbstm03a.Java.Num.NumLemmas

/-! # `zs`'s last character and text -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (zpadStr digitChar zpadStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem zpadStr_getElem?_last (c k j : Nat) (h : j + 1 = k) : (zpadStr c k)[j]? = some (digitChar (c % 10)) := by
  subst h
  simp [zpadStr, List.getElem?_append_right, zpadStr_length]

/-- `(int) z.charAt(n - 1) - '0'`. -/
theorem dz (d : Nat) (hd : d < 10) : BitVec.setWidth 32 (digitChar d) - 48#32 = BitVec.ofNat 32 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [digitChar, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem dz_zero (d : Nat) (hd : d < 10) : BitVec.setWidth 32 (digitChar d) - 48#32 = 0#32 ↔ d = 0 := by
  rw [dz d hd]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
    omega
  · rintro rfl
    rfl

theorem ovp_close_pos0 (v : Int) (hv : 0 ≤ v)
    (h : BitVec.setWidth 32 (digitChar (v.natAbs % 10)) - 48#32 = 0#32) :
    (123#16 : JChar) = ovpChar (decide (v < 0)) (v.natAbs % 10) := by
  rw [(dz_zero _ (Nat.mod_lt _ (by decide))).1 h]
  simp [ovpChar, show ¬ v < 0 by omega]

theorem ovp_close_neg0 (v : Int) (hv : ¬ 0 ≤ v)
    (h : BitVec.setWidth 32 (digitChar (v.natAbs % 10)) - 48#32 = 0#32) :
    (125#16 : JChar) = ovpChar (decide (v < 0)) (v.natAbs % 10) := by
  rw [(dz_zero _ (Nat.mod_lt _ (by decide))).1 h]
  simp [ovpChar, show v < 0 by omega]

theorem ovp_close_pos (v : Int) (hv : 0 ≤ v)
    (h : ¬ BitVec.setWidth 32 (digitChar (v.natAbs % 10)) - 48#32 = 0#32) :
    BitVec.setWidth 16 (JInt.toChar (65#32 + (BitVec.setWidth 32 (digitChar (v.natAbs % 10)) - 48#32) - 1#32)) =
      ovpChar (decide (v < 0)) (v.natAbs % 10) := by
  have hd : v.natAbs % 10 < 10 := Nat.mod_lt _ (by decide)
  have h0 : v.natAbs % 10 ≠ 0 := fun e => h ((dz_zero _ hd).2 e)
  rw [dz _ hd]
  simp only [ovpChar, show decide (v < 0) = false by simp; omega, Bool.false_eq_true, if_false, if_neg h0]
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.reducePow]
  omega

theorem ovp_close_neg (v : Int) (hv : ¬ 0 ≤ v)
    (h : ¬ BitVec.setWidth 32 (digitChar (v.natAbs % 10)) - 48#32 = 0#32) :
    BitVec.setWidth 16 (JInt.toChar (74#32 + (BitVec.setWidth 32 (digitChar (v.natAbs % 10)) - 48#32) - 1#32)) =
      ovpChar (decide (v < 0)) (v.natAbs % 10) := by
  have hd : v.natAbs % 10 < 10 := Nat.mod_lt _ (by decide)
  have h0 : v.natAbs % 10 ≠ 0 := fun e => h ((dz_zero _ hd).2 e)
  rw [dz _ hd]
  simp only [ovpChar, show decide (v < 0) = true by simp; omega, if_true, if_neg h0]
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.reducePow]
  omega

/-- `z.substring(0, n - 1) + last`. -/
theorem zs_close (v : Int) (k : Nat) (hk : 1 ≤ k) (hk' : k < 4294967296) (c : JChar)
    (hc : c = ovpChar (decide (v < 0)) (v.natAbs % 10)) :
    List.take ((4294967295 + k) % 4294967296) (zpadStr v.natAbs k) ++ [c] = zsStr v k := by
  subst hc
  have e : (4294967295 + k) % 4294967296 = k - 1 := by omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [e, zsStr]
  simp [zpadStr, zpadStr_length]

end EquivLean.Modernize.Cbstm03a.Java
