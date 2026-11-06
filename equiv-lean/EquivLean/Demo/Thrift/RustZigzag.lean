import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact__zigzag_to_i32
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact__zigzag_to_i64
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_zigzag___impl_varint_rs__zigzag__Zigzag_u16__for_i16___zigzag
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_zigzag___impl_varint_rs__zigzag__Zigzag_u32__for_i32___zigzag
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_zigzag___impl_varint_rs__zigzag__Zigzag_u64__for_i64___zigzag
import EquivLean.Demo.Thrift.RustContracts
import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Bridge.Aeneas.SpecAuto

/-!
# Thrift (T4), Rust side: zigzag in both directions

* encoder: varint-rs's `Zigzag::zigzag` for `i16`/`i32`/`i64`, `(n << 1) ^ (n >> (bits - 1))`, under the library
  contract `ShiftContract` (its shifts are std's opaque `Shl`/`Shr` for `&iN`);
* decoder: Thrift's `zigzag_to_i32` / `zigzag_to_i64` (compact.rs:449-457), `((n >> 1) as iN) ^ 0.wrapping_sub((n & 1)
  as iN)`, with no contract.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-! ## Zigzag (varint-rs) -/

/-- The zigzag value of an integer: `2v` for `v ≥ 0`, `-2v - 1` below. -/
def zz (v : Int) : Nat := if 0 ≤ v then (2 * v).toNat else (-2 * v - 1).toNat

theorem sshiftRight_msb_false {w : Nat} (x : BitVec (w + 1)) (hm : x.msb = false) :
    x.sshiftRight w = 0#(w + 1) := by
  rw [BitVec.sshiftRight_eq_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  have hlt := BitVec.msb_eq_false_iff_two_mul_lt.1 hm
  rw [Nat.pow_succ] at hlt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.div_eq_of_lt (by omega)]

theorem sshiftRight_msb_true {w : Nat} (x : BitVec (w + 1)) (hm : x.msb = true) :
    x.sshiftRight w = BitVec.allOnes (w + 1) := by
  rw [BitVec.sshiftRight_eq_of_msb_true hm]
  apply BitVec.eq_of_toNat_eq
  have hge : ¬ 2 * x.toNat < 2 ^ (w + 1) := fun h => by
    have := BitVec.msb_eq_false_iff_two_mul_lt.2 h
    rw [hm] at this
    exact absurd this (by decide)
  have hx := x.isLt
  rw [Nat.pow_succ] at hge hx
  rw [BitVec.toNat_not, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_not,
    BitVec.toNat_allOnes, Nat.pow_succ, Nat.div_eq_of_lt (by omega)]
  omega

/-- varint-rs's zigzag `(n << 1) ^ (n >> (w - 1))` on `w + 1` bits is the zigzag value. -/
theorem zigzag_bv {w : Nat} (x : BitVec (w + 1)) :
    ((x <<< 1) ^^^ x.sshiftRight w).toNat = zz x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hx := x.isLt
  have hP : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hm : x.msb = false
  · have hlt := BitVec.msb_eq_false_iff_two_mul_lt.1 hm
    rw [sshiftRight_msb_false x hm, BitVec.xor_zero, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      ite_eq_left hlt, pow_one]
    simp only [zz]
    rw [hP] at hlt hx ⊢
    have hmod : x.toNat * 2 % (2 * 2 ^ w) = x.toNat * 2 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    split_ifs <;> omega
  · have hm' : x.msb = true := by simpa using hm
    have hge : ¬ 2 * x.toNat < 2 ^ (w + 1) := fun h => hm (BitVec.msb_eq_false_iff_two_mul_lt.2 h)
    rw [sshiftRight_msb_true x hm', BitVec.xor_allOnes, BitVec.toNat_not, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, ite_eq_right hge, pow_one]
    simp only [zz]
    rw [hP] at hge hx ⊢
    have hmod : x.toNat * 2 % (2 * 2 ^ w) = x.toNat * 2 - 2 * 2 ^ w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    split_ifs <;> omega

theorem zigzag_bv16 (x : BitVec 16) : ((x <<< 1) ^^^ x.sshiftRight 15).toNat = zz x.toInt :=
  zigzag_bv (w := 15) x

theorem zigzag16_eq (hSh : ShiftContract) (x : I16) :
    I16.Insts.Varint_rsZigzagZigzagU16.zigzag x = ok ⟨(x.bv <<< 1) ^^^ x.bv.sshiftRight 15⟩ := by
  unfold I16.Insts.Varint_rsZigzagZigzagU16.zigzag
  rw [hSh.shl16 x 1#i32 (by decide) (by decide), hSh.shr16 x 15#i32 (by decide) (by decide)]
  simp [lift, IScalar.hcast]

theorem zigzag32_eq (hSh : ShiftContract) (x : I32) :
    I32.Insts.Varint_rsZigzagZigzagU32.zigzag x = ok ⟨(x.bv <<< 1) ^^^ x.bv.sshiftRight 31⟩ := by
  unfold I32.Insts.Varint_rsZigzagZigzagU32.zigzag
  rw [hSh.shl32 x 1#i32 (by decide) (by decide), hSh.shr32 x 31#i32 (by decide) (by decide)]
  simp [lift, IScalar.hcast]

theorem zigzag64_eq (hSh : ShiftContract) (x : I64) :
    I64.Insts.Varint_rsZigzagZigzagU64.zigzag x = ok ⟨(x.bv <<< 1) ^^^ x.bv.sshiftRight 63⟩ := by
  unfold I64.Insts.Varint_rsZigzagZigzagU64.zigzag
  rw [hSh.shl64 x 1#i32 (by decide) (by decide), hSh.shr64 x 63#i32 (by decide) (by decide)]
  simp [lift, IScalar.hcast]

/-- (E, zigzag) varint-rs's `i32` zigzag is the zigzag value. -/
theorem zigzag32_val (hSh : ShiftContract) (x : I32) :
    ∃ u : U32, I32.Insts.Varint_rsZigzagZigzagU32.zigzag x = ok u ∧ u.val = zz x.val :=
  ⟨_, zigzag32_eq hSh x, zigzag_bv (w := 31) x.bv⟩

/-- (E, zigzag) varint-rs's `i64` zigzag is the zigzag value. -/
theorem zigzag64_val (hSh : ShiftContract) (x : I64) :
    ∃ u : U64, I64.Insts.Varint_rsZigzagZigzagU64.zigzag x = ok u ∧ u.val = zz x.val :=
  ⟨_, zigzag64_eq hSh x, zigzag_bv (w := 63) x.bv⟩

/-! ## The decoder -/

/-- The integer of a zigzag value: `n / 2` for even `n`, `-(n / 2) - 1` for odd `n`. -/
def unzz (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int) - 1

theorem unzz_zz (v : Int) : unzz (zz v) = v := by
  unfold unzz zz
  split_ifs <;> omega

/-- Thrift's `zigzag_to_iN` on `w + 1` bits is the integer of the zigzag value. -/
theorem unzigzag_bv {w : Nat} (n : BitVec (w + 1)) :
    ((n >>> 1) ^^^ -(n &&& 1#(w + 1))).toInt = unzz n.toNat := by
  have hn := n.isLt
  have hP : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hsh : (n >>> 1).toNat = n.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toInt_eq_toNat_cond]
  unfold unzz
  by_cases he : n.toNat % 2 = 0
  · have hand : n &&& 1#(w + 1) = 0#(w + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and]
      simp [Nat.and_one_is_mod, he]
    rw [hand, BitVec.neg_zero, BitVec.xor_zero, hsh, ite_eq_left he]
    rw [hP] at hn ⊢
    rw [ite_eq_left (by omega)]
  · have ho : n.toNat % 2 = 1 := by omega
    have hand : n &&& 1#(w + 1) = 1#(w + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and]
      have h1 : 1 % 2 ^ (w + 1) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
      simp [Nat.and_one_is_mod, ho, h1]
    rw [hand, BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes, BitVec.toNat_not, hsh, ite_eq_right he]
    rw [hP] at hn ⊢
    rw [ite_eq_right (by omega)]
    omega

theorem u32_shr1 (n : U32) : n >>> (1#i32) = ok ⟨n.bv >>> 1⟩ := by
  show UScalar.shiftRight_IScalar n 1#i32 = _
  simp [UScalar.shiftRight_IScalar, UScalar.shiftRight]

theorem u64_shr1 (n : U64) : n >>> (1#i32) = ok ⟨n.bv >>> 1⟩ := by
  show UScalar.shiftRight_IScalar n 1#i32 = _
  simp [UScalar.shiftRight_IScalar, UScalar.shiftRight]

/-- (D, zigzag) `zigzag_to_i32 n` is the integer of the zigzag value `n`, for every `u32`. -/
theorem zigzag_to_i32_val (n : U32) :
    ∃ x : I32, protocol.compact.zigzag_to_i32 n = ok x ∧ x.val = unzz n.val := by
  refine ⟨⟨(n.bv >>> 1) ^^^ -(n.bv &&& 1#32)⟩, ?_, unzigzag_bv (w := 31) n.bv⟩
  unfold protocol.compact.zigzag_to_i32
  simp [lift, UScalar.hcast, core.num.I32.wrapping_sub, IScalar.wrapping_sub, u32_shr1]
  rfl

/-- (D, zigzag) `zigzag_to_i64 n` is the integer of the zigzag value `n`, for every `u64`. -/
theorem zigzag_to_i64_val (n : U64) :
    ∃ x : I64, protocol.compact.zigzag_to_i64 n = ok x ∧ x.val = unzz n.val := by
  refine ⟨⟨(n.bv >>> 1) ^^^ -(n.bv &&& 1#64)⟩, ?_, unzigzag_bv (w := 63) n.bv⟩
  unfold protocol.compact.zigzag_to_i64
  simp [lift, UScalar.hcast, core.num.I64.wrapping_sub, IScalar.wrapping_sub, u64_shr1]
  rfl

/-- (D, zigzag i32) The decoder inverts the encoder: `zigzag_to_i32 (zigzag x) = x` for every `i32`. -/
theorem zigzag32_roundtrip (hSh : ShiftContract) (x : I32) :
    ∃ u : U32, I32.Insts.Varint_rsZigzagZigzagU32.zigzag x = ok u ∧ protocol.compact.zigzag_to_i32 u = ok x := by
  obtain ⟨u, hu, huv⟩ := zigzag32_val hSh x
  obtain ⟨y, hy, hyv⟩ := zigzag_to_i32_val u
  refine ⟨u, hu, ?_⟩
  rw [hy, show y = x from IScalar.eq_of_val_eq (by rw [hyv, huv, unzz_zz])]

/-- (D, zigzag i64) `zigzag_to_i64 (zigzag x) = x` for every `i64`. -/
theorem zigzag64_roundtrip (hSh : ShiftContract) (x : I64) :
    ∃ u : U64, I64.Insts.Varint_rsZigzagZigzagU64.zigzag x = ok u ∧ protocol.compact.zigzag_to_i64 u = ok x := by
  obtain ⟨u, hu, huv⟩ := zigzag64_val hSh x
  obtain ⟨y, hy, hyv⟩ := zigzag_to_i64_val u
  refine ⟨u, hu, ?_⟩
  rw [hy, show y = x from IScalar.eq_of_val_eq (by rw [hyv, huv, unzz_zz])]

end EquivLean.Demo.Thrift.Rust
