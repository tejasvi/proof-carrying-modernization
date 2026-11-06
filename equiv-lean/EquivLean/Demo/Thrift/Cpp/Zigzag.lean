import EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

/-!
# Thrift, C++ side: zigzag, both directions, i32 and i64

`i32ToZigzag_E` / `i64ToZigzag_E`: `TCompactProtocolT<TTransport>::i32ToZigzag(n)` (`i64ToZigzag`) returns the zigzag of
every `int32_t` (`int64_t`) `n`; `zigzagToI32_D` / `zigzagToI64_D`: `zigzagToI32(z)` (`zigzagToI64`) returns the inverse
zigzag of every `uint32_t` (`uint64_t`) `z`, which undoes zigzag (`unzigzag_zigzag`).  No input is malformed: every
`z` decodes.  The functions are straight-line code; the arithmetic is `zigzag32_bits` and its kin.
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

theorem bitwise_xor_zero {w : Nat} {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ w) :
    bitwise false w (fun x1 x2 => x1 ^^^ x2) a 0 = a := by
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_xor, BitVec.toNat_ofInt]
  have h2 : (0 : Int) % (2 ^ w : Nat) = 0 := by simp
  rw [h2]
  simp only [Int.toNat_zero, Nat.xor_zero]
  rw [Int.emod_eq_of_lt h0 (by exact_mod_cast h1)]
  omega

theorem two_pow_int_cast (w : Nat) : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl

theorem bitwise_xor_ones {w : Nat} {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ w) :
    bitwise false w (fun x1 x2 => x1 ^^^ x2) a (2 ^ w - 1) = 2 ^ w - 1 - a := by
  have hp1 := Nat.one_le_two_pow (n := w)
  have hpc := two_pow_int_cast w
  unfold bitwise
  have hall : BitVec.ofInt w (2 ^ w - 1) = BitVec.allOnes w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  dsimp only
  rw [hall, BitVec.xor_allOnes]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_not, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt h0 (by omega)]
  omega

theorem bitwise_and_one {w : Nat} {z : Int} (hw : 1 ≤ w) (h0 : 0 ≤ z) (h1 : z < 2 ^ w) :
    bitwise false w (fun x1 x2 => x1 &&& x2) z 1 = z % 2 := by
  have hpc := two_pow_int_cast w
  have h2 : 2 ≤ 2 ^ w := Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hw)
  unfold bitwise
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_and, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt h0 (by omega), Int.emod_eq_of_lt (by decide) (by omega),
    show Int.toNat 1 = 1 from rfl, Nat.and_one_is_mod]
  omega

/-- Zigzag (`(n << 1) ^ (n >> 31)`), as a natural number. -/
def zigzag (n : Int) : Nat := if 0 ≤ n then (2 * n).toNat else (-2 * n - 1).toNat
/-- Its inverse (`(n >> 1) ^ -(n & 1)`). -/
def unzigzag (z : Int) : Int := if z % 2 = 0 then z / 2 else -(z / 2) - 1

theorem unzigzag_zigzag (n : Int) : unzigzag (zigzag n) = n := by
  unfold zigzag unzigzag; split <;> split <;> omega

theorem zigzag32_bits {n : Int} (h0 : -2147483648 ≤ n) (h1 : n ≤ 2147483647) :
    bitwise false 32 (fun x1 x2 => x1 ^^^ x2) (wrap false 32 (wrap false 32 n * 2))
      (wrap false 32 (n / 2147483648)) = (zigzag n : Int) := by
  simp only [wrap, Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases hn : 0 ≤ n
  · rw [show n / 2147483648 = 0 by omega, show (0 : Int) % 2 ^ 32 = 0 by decide,
      show n % 2 ^ 32 * 2 % 2 ^ 32 = 2 * n by omega, bitwise_xor_zero (by omega) (by omega)]
    unfold zigzag; rw [ite_eq_left hn]; omega
  · rw [show n / 2147483648 = -1 by omega, show (-1 : Int) % 2 ^ 32 = 2 ^ 32 - 1 by decide,
      show n % 2 ^ 32 * 2 % 2 ^ 32 = 2 * n + 2 ^ 32 by omega, bitwise_xor_ones (by omega) (by omega)]
    unfold zigzag; rw [ite_eq_right hn]; omega

theorem unzigzag32_bits {z : Int} (h0 : 0 ≤ z) (h1 : z ≤ 4294967295) :
    wrap true 32 (bitwise false 32 (fun x1 x2 => x1 ^^^ x2) (z / 2)
      (wrap false 32 (0 - wrap true 32 (bitwise false 32 (fun x1 x2 => x1 &&& x2) z 1)))) = unzigzag z := by
  rw [bitwise_and_one (by decide) h0 (by omega)]
  have hm : wrap true 32 (z % 2) = z % 2 := by simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  rw [hm]
  unfold unzigzag
  by_cases hz : z % 2 = 0
  · rw [hz, show wrap false 32 (0 - 0) = 0 by decide, bitwise_xor_zero (by omega) (by omega), ite_eq_left rfl]
    simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  · rw [show z % 2 = 1 by omega, show wrap false 32 (0 - 1) = 2 ^ 32 - 1 by decide,
      bitwise_xor_ones (by omega) (by omega), ite_eq_right (by omega)]
    simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

theorem zigzag64_bits {n : Int} (h0 : -9223372036854775808 ≤ n) (h1 : n ≤ 9223372036854775807) :
    bitwise false 64 (fun x1 x2 => x1 ^^^ x2) (wrap false 64 (wrap false 64 n * 2))
      (wrap false 64 (n / 9223372036854775808)) = (zigzag n : Int) := by
  simp only [wrap, Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases hn : 0 ≤ n
  · rw [show n / 9223372036854775808 = 0 by omega, show (0 : Int) % 2 ^ 64 = 0 by decide,
      show n % 2 ^ 64 * 2 % 2 ^ 64 = 2 * n by omega, bitwise_xor_zero (by omega) (by omega)]
    unfold zigzag; rw [ite_eq_left hn]; omega
  · rw [show n / 9223372036854775808 = -1 by omega, show (-1 : Int) % 2 ^ 64 = 2 ^ 64 - 1 by decide,
      show n % 2 ^ 64 * 2 % 2 ^ 64 = 2 * n + 2 ^ 64 by omega, bitwise_xor_ones (by omega) (by omega)]
    unfold zigzag; rw [ite_eq_right hn]; omega

theorem unzigzag64_bits {z : Int} (h0 : 0 ≤ z) (h1 : z ≤ 18446744073709551615) :
    wrap true 64 (bitwise false 64 (fun x1 x2 => x1 ^^^ x2) (z / 2)
      (wrap false 64 (0 - wrap true 64 (bitwise false 64 (fun x1 x2 => x1 &&& x2) z 1)))) = unzigzag z := by
  rw [bitwise_and_one (by decide) h0 (by omega)]
  have hm : wrap true 64 (z % 2) = z % 2 := by simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  rw [hm]
  unfold unzigzag
  by_cases hz : z % 2 = 0
  · rw [hz, show wrap false 64 (0 - 0) = 0 by decide, bitwise_xor_zero (by omega) (by omega), ite_eq_left rfl]
    simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  · rw [show z % 2 = 1 by omega, show wrap false 64 (0 - 1) = 2 ^ 64 - 1 by decide,
      bitwise_xor_ones (by omega) (by omega), ite_eq_right (by omega)]
    simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

def symI32ToZigzag : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE11i32ToZigzagEi"
def symZigzagToI32 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE11zigzagToI32Ej"
def symI64ToZigzag : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE11i64ToZigzagEl"
def symZigzagToI64 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE11zigzagToI64Em"

/-- `i32ToZigzag(n)`: the zigzag of every `int32_t n`. -/
theorem i32ToZigzag_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symI32ToZigzag = some fn_apache_thrift_protocol_TCompactProtocolT_i32ToZigzag)
    (m : Mem) (this : Ptr) (n : Int) (hn : -2147483648 ≤ n ∧ n ≤ 2147483647) :
    Returns ctx symI32ToZigzag [.ptr this, .int n] m
      (fun r m' => r = some (.int (zigzag n)) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  exact zigzag32_bits hn.1 hn.2

/-- `zigzagToI32(z)`: the inverse zigzag of every `uint32_t z`. -/
theorem zigzagToI32_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symZigzagToI32 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI32)
    (m : Mem) (this : Ptr) (z : Int) (hz : 0 ≤ z ∧ z ≤ 4294967295) :
    Returns ctx symZigzagToI32 [.ptr this, .int z] m
      (fun r m' => r = some (.int (unzigzag z)) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_a : bitwise false 32 (fun x1 x2 => x1 &&& x2) z 1 = z % 2 := bitwise_and_one (by decide) hz.1 (by omega)
  have cirH_m : wrap true 32 (z % 2) = z % 2 := by
    simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals (try (cir_strip_mdata; omega))
  rw [← cirH_m, ← cirH_a]; exact unzigzag32_bits hz.1 hz.2

/-- `i64ToZigzag(n)`: the zigzag of every `int64_t n`. -/
theorem i64ToZigzag_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symI64ToZigzag = some fn_apache_thrift_protocol_TCompactProtocolT_i64ToZigzag)
    (m : Mem) (this : Ptr) (n : Int) (hn : -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807) :
    Returns ctx symI64ToZigzag [.ptr this, .int n] m
      (fun r m' => r = some (.int (zigzag n)) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  exact zigzag64_bits hn.1 hn.2

/-- `zigzagToI64(z)`: the inverse zigzag of every `uint64_t z`. -/
theorem zigzagToI64_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symZigzagToI64 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI64)
    (m : Mem) (this : Ptr) (z : Int) (hz : 0 ≤ z ∧ z ≤ 18446744073709551615) :
    Returns ctx symZigzagToI64 [.ptr this, .int z] m
      (fun r m' => r = some (.int (unzigzag z)) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_a : bitwise false 64 (fun x1 x2 => x1 &&& x2) z 1 = z % 2 := bitwise_and_one (by decide) hz.1 (by omega)
  have cirH_m : wrap true 64 (z % 2) = z % 2 := by
    simp only [wrap, Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals (try (cir_strip_mdata; omega))
  rw [← cirH_m, ← cirH_a]; exact unzigzag64_bits hz.1 hz.2

end EquivLean.Demo.Thrift.Cpp
