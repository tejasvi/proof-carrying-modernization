import CIR

/-!
# Thrift, C++ side: bit and byte facts of the compact protocol's integer code

`n & ~0x7F`, `(n & 0x7F) | 0x80` on a `uint32_t`, and a byte through `(int8_t)` then `(uint8_t)`, as cirlean
evaluates them (`bitwise` through `BitVec`, `wrap`).
-/

open CIR

namespace EquivLean.Demo.Thrift.Cpp

/-- `a &&& 0xFFFFFF80` for a 32-bit `a`: its bits above the low 7. -/
theorem nat_and_mask7 {a : Nat} (ha : a < 2 ^ 32) : a &&& 4294967168 = 2 ^ 7 * (a / 2 ^ 7) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (4294967168 : Nat) = 2 ^ 7 * (2 ^ 25 - 1) by decide, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h7 : i ≥ 7
  · rw [Nat.sub_add_cancel h7]
    by_cases h32 : i - 7 < 25
    · simp [h7, h32]
    · have : a.testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h7]

theorem nat_and_mask7_eq_zero {a : Nat} (ha : a < 2 ^ 32) : a &&& 4294967168 = 0 ↔ a < 128 := by
  rw [nat_and_mask7 ha]; constructor
  · intro h; have : a / 2 ^ 7 = 0 := by omega
    have := Nat.div_add_mod a (2 ^ 7); simp only [Nat.reducePow] at *; omega
  · intro h; have : a / 2 ^ 7 = 0 := Nat.div_eq_of_lt (by simpa using h); rw [this]

theorem ofInt_toNat_32 {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 32) : (BitVec.ofInt 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_ofInt]; omega

/-- `n & ~0x7F == 0` on a `uint32_t`. -/
theorem bitwise_mask7_eq_zero {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 4294967295) :
    bitwise false 32 (fun x1 x2 => x1 &&& x2) x 4294967168 = 0 ↔ x < 128 := by
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_and, ofInt_toNat_32 h0 (by omega),
    show (BitVec.ofInt 32 4294967168).toNat = 4294967168 by decide]
  rw [show ((x.toNat &&& 4294967168 : Nat) : Int) = 0 ↔ x.toNat &&& 4294967168 = 0 by omega,
    nat_and_mask7_eq_zero (by omega)]
  omega

/-- `(n & 0x7F) | 0x80` on a `uint32_t`. -/
theorem bitwise_low7_or {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 4294967295) :
    bitwise false 32 (fun x1 x2 => x1 ||| x2) (bitwise false 32 (fun x1 x2 => x1 &&& x2) x 127) 128 =
      x % 128 + 128 := by
  have ha : bitwise false 32 (fun x1 x2 => x1 &&& x2) x 127 = x % 128 := by
    unfold bitwise
    simp only [Bool.false_eq_true, ite_false, BitVec.toNat_and, ofInt_toNat_32 h0 (by omega),
      show (BitVec.ofInt 32 127).toNat = 127 by decide]
    rw [show (127 : Nat) = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
  rw [ha]
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_or, ofInt_toNat_32 (by omega : (0:Int) ≤ x % 128) (by omega),
    show (BitVec.ofInt 32 128).toNat = 128 by decide]
  rw [show (128 : Nat) = 2 ^ 7 by decide, Nat.or_two_pow_eq_add_of_lt (by omega)]; omega

/-- `a &&& 0xFFFFFFFFFFFFFF80` for a 64-bit `a`: its bits above the low 7. -/
theorem nat_and_mask7_64 {a : Nat} (ha : a < 2 ^ 64) :
    a &&& 18446744073709551488 = 2 ^ 7 * (a / 2 ^ 7) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (18446744073709551488 : Nat) = 2 ^ 7 * (2 ^ 57 - 1) by decide,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h7 : i ≥ 7
  · rw [Nat.sub_add_cancel h7]
    by_cases h64 : i - 7 < 57
    · simp [h7, h64]
    · have : a.testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h7]

theorem nat_and_mask7_64_eq_zero {a : Nat} (ha : a < 2 ^ 64) : a &&& 18446744073709551488 = 0 ↔ a < 128 := by
  rw [nat_and_mask7_64 ha]; constructor
  · intro h; have : a / 2 ^ 7 = 0 := by omega
    have := Nat.div_add_mod a (2 ^ 7); simp only [Nat.reducePow] at *; omega
  · intro h; have : a / 2 ^ 7 = 0 := Nat.div_eq_of_lt (by simpa using h); rw [this]

theorem ofInt_toNat_64 {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : (BitVec.ofInt 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_ofInt]; omega

/-- `n & ~0x7FL == 0` on a `uint64_t`. -/
theorem bitwise_mask7_eq_zero64 {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 18446744073709551615) :
    bitwise false 64 (fun x1 x2 => x1 &&& x2) x 18446744073709551488 = 0 ↔ x < 128 := by
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_and, ofInt_toNat_64 h0 (by omega),
    show (BitVec.ofInt 64 18446744073709551488).toNat = 18446744073709551488 by decide]
  rw [show ((x.toNat &&& 18446744073709551488 : Nat) : Int) = 0 ↔ x.toNat &&& 18446744073709551488 = 0 by omega,
    nat_and_mask7_64_eq_zero (by omega)]
  omega

/-- `(n & 0x7F) | 0x80` on a `uint64_t`. -/
theorem bitwise_low7_or64 {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 18446744073709551615) :
    bitwise false 64 (fun x1 x2 => x1 ||| x2) (bitwise false 64 (fun x1 x2 => x1 &&& x2) x 127) 128 =
      x % 128 + 128 := by
  have ha : bitwise false 64 (fun x1 x2 => x1 &&& x2) x 127 = x % 128 := by
    unfold bitwise
    simp only [Bool.false_eq_true, ite_false, BitVec.toNat_and, ofInt_toNat_64 h0 (by omega),
      show (BitVec.ofInt 64 127).toNat = 127 by decide]
    rw [show (127 : Nat) = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
  rw [ha]
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_or, ofInt_toNat_64 (by omega : (0:Int) ≤ x % 128) (by omega),
    show (BitVec.ofInt 64 128).toNat = 128 by decide]
  rw [show (128 : Nat) = 2 ^ 7 by decide, Nat.or_two_pow_eq_add_of_lt (by omega)]; omega

/-- A `uint8_t` cast: the value mod 256. -/
theorem wrap_u8 (y : Int) : wrap false 8 y = y % 256 := by
  simp only [wrap, Bool.false_and, Bool.false_eq_true, ite_false]; rfl

/-- A byte through `(int8_t)` then `(uint8_t)`: the value mod 256. -/
theorem wrap_u8_s8 (x : Int) : wrap false 8 (wrap true 8 x) = x % 256 := by
  rw [wrap_u8]
  simp only [wrap, Bool.true_and]
  split <;> omega

end EquivLean.Demo.Thrift.Cpp
