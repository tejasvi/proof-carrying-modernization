import EquivLean.Demo.Thrift.Spec
import EquivLean.Demo.Thrift.Cpp.Bits

open CIR

/-!
# Thrift, C++ side: the state of a varint read

`RV bs rest x r val`: `readVarint64`'s loop after `r` bytes of `bs`, against the spec's reader
`Spec.readVarint 10 bs = some (x, rest)`: the bytes read so far had the high bit set, `val` is their value,
and the spec's reader on the bytes not read yet gives `x` as `val + 128^r * v'`.  The read of byte `r` either
ends the varint (`rv_exit`) or keeps the state (`rv_step`, at most 9 such bytes).
-/

namespace EquivLean.Demo.Thrift.Cpp

theorem readVarint_nil (k : Nat) : Spec.readVarint k [] = none := by cases k <;> rfl

def RV (bs rest : Spec.Bytes) (x r val : Nat) : Prop :=
  val < 128 ^ r ∧ ∃ v', Spec.readVarint (10 - r) (bs.drop r) = some (v', rest) ∧ x = val + 128 ^ r * v'

theorem rv_start {bs rest : Spec.Bytes} {x : Nat} (h : Spec.readVarint 10 bs = some (x, rest)) :
    RV bs rest x 0 0 :=
  ⟨by decide, x, by simpa using h, by simp⟩

theorem rv_lt {bs rest : Spec.Bytes} {x r val : Nat} (h : RV bs rest x r val) : r < bs.length ∧ r < 10 := by
  obtain ⟨-, v', hr, -⟩ := h
  refine ⟨Nat.lt_of_not_le fun hle => ?_, Nat.lt_of_not_le fun hle => ?_⟩
  · rw [List.drop_eq_nil_of_le hle, readVarint_nil] at hr; cases hr
  · rw [show 10 - r = 0 by omega] at hr; cases hr

/-- The byte at `r` of the source `bs` (as the numbers the C++ memory holds). -/
theorem rv_byte {bs : Spec.Bytes} {r : Nat} (h : r < bs.length) :
    (bs.map UInt8.toNat).getD r 0 = bs[r].toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]; rfl

theorem rv_byte_lt (bs : Spec.Bytes) (r : Nat) : (bs.map UInt8.toNat).getD r 0 < 256 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bs[r]? with
  | none => decide
  | some b => exact b.toNat_lt

theorem rv_exit {bs rest : Spec.Bytes} {x r val : Nat} (h : RV bs rest x r val)
    (hb : (bs.map UInt8.toNat).getD r 0 < 128) :
    x = val + 128 ^ r * (bs.map UInt8.toNat).getD r 0 ∧ rest = bs.drop (r + 1) := by
  obtain ⟨hl, hr10⟩ := rv_lt h
  obtain ⟨-, v', hr, hx⟩ := h
  rw [rv_byte hl] at hb ⊢
  rw [List.drop_eq_getElem_cons hl, show 10 - r = (9 - r) + 1 by omega] at hr
  simp only [Spec.readVarint, ite_eq_left hb, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨hx, rfl⟩

theorem rv_step {bs rest : Spec.Bytes} {x r val : Nat} (h : RV bs rest x r val)
    (hb : ¬ (bs.map UInt8.toNat).getD r 0 < 128) :
    r ≤ 8 ∧ RV bs rest x (r + 1) (val + (bs.map UInt8.toNat).getD r 0 % 128 * 128 ^ r) := by
  obtain ⟨hl, hr10⟩ := rv_lt h
  obtain ⟨hv, v', hr, hx⟩ := h
  rw [rv_byte hl] at hb ⊢
  rw [List.drop_eq_getElem_cons hl, show 10 - r = (9 - r) + 1 by omega] at hr
  simp only [Spec.readVarint, ite_eq_right hb] at hr
  rcases hr' : Spec.readVarint (9 - r) (bs.drop (r + 1)) with _ | ⟨v'', r''⟩
  · rw [hr'] at hr; cases hr
  rw [hr', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have h9 : r ≤ 8 := Nat.le_of_not_lt fun h9 => by
    rw [show 9 - r = 0 by omega] at hr'; cases hr'
  refine ⟨h9, ?_, v'', by rw [show 10 - (r + 1) = 9 - r by omega]; exact hr', ?_⟩
  · have : bs[r].toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    rw [Nat.pow_succ]
    have := Nat.mul_le_mul_right (128 ^ r) (show bs[r].toNat % 128 + 1 ≤ 128 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · rw [hx]; dsimp only
    rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm (128 ^ r) (bs[r].toNat % 128), Nat.mul_assoc (128 ^ r) 128 v'']
    omega

theorem rv_head (bs : Spec.Bytes) (r : Nat) :
    ((bs.drop r).map UInt8.toNat).headD 0 = (bs.map UInt8.toNat).getD r 0 := by
  rw [List.map_drop, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

theorem rv_tail (bs : Spec.Bytes) (r : Nat) :
    ((bs.drop r).map UInt8.toNat).tail = (bs.drop (r + 1)).map UInt8.toNat := by
  rw [List.map_drop, List.map_drop, List.tail_drop]

theorem rv_ne_nil {bs : Spec.Bytes} {r : Nat} (h : r < bs.length) : (bs.drop r).map UInt8.toNat ≠ [] := by
  simp; omega

/-- The bytes a read of `r + 1` bytes leaves, as numbers. -/
theorem rv_drop (bs : Spec.Bytes) (n : Nat) : (bs.map UInt8.toNat).drop n = (bs.drop n).map UInt8.toNat :=
  (List.map_drop ..).symm

/-- The number of bytes read: what the source loses. -/
theorem rv_len {bs : Spec.Bytes} {r : Nat} (hl : r < bs.length) : bs.length - (bs.drop (r + 1)).length = r + 1 := by
  rw [List.length_drop]; omega

theorem nat_and_128 : ∀ a, a < 256 → a &&& 128 = 128 * (a / 128) := by
  set_option maxRecDepth 100000 in decide

/-- `(int)byte & 0x7F` for a byte. -/
theorem bitwise_and127_s32 {x : Int} (h0 : 0 ≤ x) (h1 : x < 256) :
    bitwise true 32 (fun x1 x2 => x1 &&& x2) x 127 = x % 128 := by
  unfold bitwise
  simp only [ite_true]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_and, ofInt_toNat_32 h0 (by omega),
    show (BitVec.ofInt 32 127).toNat = 127 by decide, show (127 : Nat) = 2 ^ 7 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  split <;> omega

/-- `(int)byte & 0x80` for a byte. -/
theorem bitwise_and128_s32 {x : Int} (h0 : 0 ≤ x) (h1 : x < 256) :
    bitwise true 32 (fun x1 x2 => x1 &&& x2) x 128 = if x < 128 then 0 else 128 := by
  unfold bitwise
  simp only [ite_true]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_and, ofInt_toNat_32 h0 (by omega),
    show (BitVec.ofInt 32 128).toNat = 128 by decide, nat_and_128 _ (by omega)]
  split <;> split <;> omega

theorem nat_or_shl {val k t : Nat} (hv : val < 2 ^ k) (hk : k ≤ 63) :
    val ||| t * 2 ^ k % 2 ^ 64 = (val + t * 2 ^ k) % 2 ^ 64 := by
  have e64 : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [e64, Nat.mul_mod_mul_right]
  have hor : val ||| t % 2 ^ (64 - k) * 2 ^ k = val + t % 2 ^ (64 - k) * 2 ^ k := by
    rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hv, Nat.add_comm]
  rw [hor]
  have hq : t % 2 ^ (64 - k) < 2 ^ (64 - k) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have key : val + t * 2 ^ k =
      (val + t % 2 ^ (64 - k) * 2 ^ k) + t / 2 ^ (64 - k) * (2 ^ (64 - k) * 2 ^ k) := by
    have ht := Nat.div_add_mod t (2 ^ (64 - k))
    generalize 2 ^ (64 - k) = Q at ht hq ⊢
    generalize 2 ^ k = P
    generalize t / Q = q at ht ⊢
    generalize t % Q = s at ht hq ⊢
    subst ht
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm Q q P, Nat.mul_comm Q P, ← Nat.mul_assoc q P Q,
      Nat.mul_comm (q * P) Q]
    omega
  have hlt : val + t % 2 ^ (64 - k) * 2 ^ k < 2 ^ (64 - k) * 2 ^ k :=
    calc val + t % 2 ^ (64 - k) * 2 ^ k < 2 ^ k + t % 2 ^ (64 - k) * 2 ^ k := by omega
      _ = (t % 2 ^ (64 - k) + 1) * 2 ^ k := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      _ ≤ 2 ^ (64 - k) * 2 ^ k := Nat.mul_le_mul_right _ hq
  rw [key, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- `val | ((uint64_t)t << 7r)` as cirlean evaluates it, for `val < 2^(7r)`, `r ≤ 9`: the sum modulo `2^64`. -/
theorem or_shl7 {val r t : Nat} (hv : val < 2 ^ (7 * r)) (hr : r ≤ 9) :
    bitwise false 64 (fun x1 x2 => x1 ||| x2) (val : Int) (wrap false 64 ((t : Int) * 2 ^ (7 * (r : Int)).toNat)) =
      (((val + t * 2 ^ (7 * r)) % 2 ^ 64 : Nat) : Int) := by
  rw [show (7 * (r : Int)).toNat = 7 * r by omega]
  have hv64 : val < 2 ^ 64 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
  unfold bitwise wrap
  simp only [Bool.false_eq_true, ite_false, Bool.false_and, BitVec.toNat_or, BitVec.toNat_ofInt]
  rw [show ((t : Int) * 2 ^ (7 * r)) = ((t * 2 ^ (7 * r) : Nat) : Int) by push_cast; rfl]
  have e1 : ((val : Int) % ((2 ^ 64 : Nat) : Int)).toNat = val := by omega
  have e2 : (((t * 2 ^ (7 * r) : Nat) : Int) % 2 ^ 64 % ((2 ^ 64 : Nat) : Int)).toNat = t * 2 ^ (7 * r) % 2 ^ 64 := by
    omega
  rw [e1, e2, nat_or_shl hv (by omega)]

theorem wrap_s64_mod (n : Nat) : wrap true 64 (((n % 2 ^ 64 : Nat) : Int)) = wrap true 64 (n : Int) := by
  unfold wrap
  have : ((n % 2 ^ 64 : Nat) : Int) % 2 ^ 64 = (n : Int) % 2 ^ 64 := by omega
  rw [this]

theorem readVarint_len : ∀ (k : Nat) (bs : Spec.Bytes) (x : Nat) (rest : Spec.Bytes),
    Spec.readVarint k bs = some (x, rest) → rest.length < bs.length ∧ bs.length ≤ rest.length + k
  | 0, _, _, _, h => by cases h
  | _ + 1, [], _, _, h => by cases h
  | k + 1, b :: bs, x, rest, h => by
    simp only [Spec.readVarint] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
    · rcases h' : Spec.readVarint k bs with _ | ⟨x', r'⟩
      · rw [h'] at h; cases h
      · rw [h', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := readVarint_len k bs x' r' h'
        simp; omega

theorem wrap32_wrap64 (y : Int) : wrap true 32 (wrap true 64 y) = wrap true 32 y := by
  unfold wrap
  simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]
  split <;> split <;> split <;> omega

end EquivLean.Demo.Thrift.Cpp
