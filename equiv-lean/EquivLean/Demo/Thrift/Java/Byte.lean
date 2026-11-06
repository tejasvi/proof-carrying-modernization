import EquivLean.Demo.Thrift.Java.Tr

/-!
# Thrift → Java (T4): a Java `byte` read from the wire

A byte `u` read by `readByte()` or from the buffer is the sign-extended `int`
`BitVec.signExtend 32 u.toBitVec` (`jbyte u`). Its 7-bit group (`b & 0x7F`) and its high bit
(`(short) b & 0x80`), bit by bit (no `bv_decide`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem getLsbD_sx (u : UInt8) (i : Nat) :
    (BitVec.signExtend 32 u.toBitVec).getLsbD i =
      (decide (i < 32) && if i < 8 then u.toNat.testBit i else u.toNat.testBit 7) := by
  rw [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
  rfl

theorem bits127 : ∀ i, i < 32 → (127#32).getLsbD i = decide (i < 7) := by decide
theorem bits128 : ∀ i, i < 32 → (128#32).getLsbD i = decide (i = 7) := by decide

/-- The 7-bit group of a byte. -/
theorem sx_and127 (u : UInt8) :
    BitVec.signExtend 32 u.toBitVec &&& 127#32 = BitVec.ofNat 32 (u.toNat % 128) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, getLsbD_sx, bits127 i hi, BitVec.getLsbD_ofNat,
    show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_mod_two_pow]
  by_cases h7 : i < 7
  · simp [hi, h7, show i < 8 by omega]
  · simp [h7]

theorem sx_and127_toNat (u : UInt8) :
    (BitVec.signExtend 32 u.toBitVec &&& 127#32).toNat = u.toNat % 128 := by
  rw [sx_and127, BitVec.toNat_ofNat]
  have : u.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  omega

/-- The high bit of a byte. -/
theorem sx_and128 (u : UInt8) :
    BitVec.signExtend 32 u.toBitVec &&& 128#32 = if 128 ≤ u.toNat then 128#32 else 0#32 := by
  have hu := u.toNat_lt
  have key : u.toNat.testBit 7 = decide (128 ≤ u.toNat) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases h : 128 ≤ u.toNat
    · have : u.toNat / 2 ^ 7 = 1 := by omega
      simp [this, h]
    · have : u.toNat / 2 ^ 7 = 0 := by omega
      simp [this, h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, getLsbD_sx, bits128 i hi]
  by_cases h7 : i = 7
  · subst h7
    by_cases h : 128 ≤ u.toNat
    · rw [if_pos h, bits128 7 (by decide)]; simp [key, h]
    · rw [if_neg h]; simp [key, h]
  · have : ∀ x : I32, x = 128#32 ∨ x = 0#32 → x.getLsbD i = false := by
      rintro x (rfl | rfl)
      · rw [bits128 i hi]; simp [h7]
      · simp
    rw [this _ (by split <;> simp)]
    simp [h7]

/-- A byte's `(short)` cast keeps it. -/
theorem toShort_sx (u : UInt8) :
    JInt.toShort (BitVec.signExtend 32 u.toBitVec) = BitVec.signExtend 32 u.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [JInt.toShort]
  rw [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth, getLsbD_sx, getLsbD_sx]
  by_cases h8 : i < 8
  · simp [hi, h8, show i < 16 by omega]
  · by_cases h16 : i < 16
    · simp [hi, h8, h16]
    · simp [hi, h8, h16]

/-- A value below 128 is its own `(byte)` cast. -/
theorem toByte_ofNat_lt {n : Nat} (h : n < 128) : JInt.toByte (BitVec.ofNat 32 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [JInt.toByte]
  rw [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  have h7 : n.testBit 7 = false := Nat.testBit_lt_two_pow (show n < 2 ^ 7 by omega)
  by_cases h8 : i < 8
  · simp [hi, h8]
  · have h2 : 2 ^ 7 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have : n.testBit i = false := Nat.testBit_lt_two_pow (show n < 2 ^ i by omega)
    simp [hi, h8, h7, this]

end EquivLean.Demo.Thrift.Java
