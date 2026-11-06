import EquivLean.Demo.Gen.Jimple.Thrift

/-!
# Thrift → Java (T4): bit facts of Java's `byte` and `int` operations

Proved bit by bit (`BitVec.eq_of_getLsbD_eq`), without `bv_decide` (whose certificates add
native axioms).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem setWidth8_signExtend32 (y : BitVec 8) : (y.signExtend 32).setWidth 8 = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 32 by omega]

theorem toByte_setWidth8 (x : I32) : (JInt.toByte x).setWidth 8 = x.setWidth 8 := by
  simp only [JInt.toByte]
  exact setWidth8_signExtend32 _

theorem toByte_toByte (x : I32) : JInt.toByte (JInt.toByte x) = JInt.toByte x := by
  show ((JInt.toByte x).setWidth 8).signExtend 32 = JInt.toByte x
  rw [toByte_setWidth8]
  rfl

theorem mask_bits : ∀ i, i < 32 → (4294967168#32).getLsbD i = decide (7 ≤ i) := by decide

theorem and_mask_eq (x : I32) : x &&& 4294967168#32 = (x >>> 7) <<< 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, mask_bits i hi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : 7 ≤ i
  · have e : 7 + (i - 7) = i := by omega
    simp [h, hi, e, show ¬ i < 7 by omega]
  · simp [h, show i < 7 by omega]

/-- `n & ~0x7F == 0`: the value fits in 7 bits. -/
theorem and_m128_eq_zero (x : I32) : (x &&& 4294967168#32 = 0#32) ↔ x.toNat < 128 := by
  rw [and_mask_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight] at this
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat] at this
    have hx := x.isLt
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega

theorem ushr7_toNat (x : I32) : (JInt.ushr x 7#32).toNat = x.toNat / 128 := by
  simp only [JInt.ushr]
  rw [BitVec.toNat_ushiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem and127_toNat (x : I32) : (x &&& 127#32).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (127#32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem cont_eq (x : I32) : x &&& 127#32 ||| 128#32 = (x &&& 127#32) + 128#32 := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  rw [BitVec.and_assoc, show (127#32 &&& 128#32 : I32) = 0#32 by decide, BitVec.and_zero]

theorem cont_toNat (x : I32) : (x &&& 127#32 ||| 128#32).toNat = x.toNat % 128 + 128 := by
  rw [cont_eq, BitVec.toNat_add, and127_toNat]
  have : x.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  simp only [show (128#32).toNat = 128 from rfl]
  omega

end EquivLean.Demo.Thrift.Java
