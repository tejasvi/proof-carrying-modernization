import EquivLean.Demo.Thrift.Java.Rb
import EquivLean.Demo.Thrift.Java.Vacc
import EquivLean.Demo.Thrift.Java.Byte

/-!
# Thrift → Java (T4): the varint readers' loop facts

`acc32 bs i`: the value of the first `i` groups of `bs`. `FastFacts`/`SlowFacts`: the facts of the
two loops of `readVarint32` about the source, folded during the symbolic execution. The lemmas
connect them with `Spec.readVarint`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The value of the first `i` groups of `bs` (kept folded during the symbolic execution). -/
def acc32 (bs : Bytes) (i : Nat) : Nat := vacc (bs.take i)

/-- The fast loop's facts about the buffer: it holds the next `bufLen` bytes, the first `i` have
the high bit, the next one is `u`. -/
def FastFacts (R : TRep) (σ0 : State) (t : Addr) (arr : List Value) (i : Nat) (u : UInt8) : Prop :=
  5 ≤ R.bufLen σ0 t ∧ R.bufPos σ0 t + (R.bufLen σ0 t).toNat ≤ arr.length ∧
  (arr.drop (R.bufPos σ0 t)).take (R.bufLen σ0 t).toNat =
    ((R.src σ0 t).take (R.bufLen σ0 t).toNat).map jbyte ∧
  (R.bufLen σ0 t).toNat ≤ (R.src σ0 t).length ∧ R.bufPos σ0 t + (R.bufLen σ0 t).toNat < 2147483648 ∧
  (∀ c ∈ (R.src σ0 t).take i, 128 ≤ c.toNat) ∧ (R.src σ0 t)[i]? = some u

/-- The slow loop's facts: `k` bytes, all with the high bit, read from the source. -/
def SlowFacts (R : TRep) (σ0 σ : State) (t : Addr) (k : Nat) : Prop :=
  k ≤ (R.src σ0 t).length ∧ (∀ c ∈ (R.src σ0 t).take k, 128 ≤ c.toNat) ∧
  R.src σ t = (R.src σ0 t).drop k ∧ R.sink σ t = R.sink σ0 t

attribute [irreducible] acc32 FastFacts SlowFacts

theorem acc32_zero (bs : Bytes) : acc32 bs 0 = 0 := by
  unfold acc32; simp [vacc]

theorem take_succ_of_get {bs : Bytes} {k : Nat} {u : UInt8} (h : bs[k]? = some u) :
    bs.take (k + 1) = bs.take k ++ [u] := by
  rw [List.take_succ, h]; rfl

theorem length_take_of_get {bs : Bytes} {k : Nat} {u : UInt8} (h : bs[k]? = some u) :
    (bs.take k).length = k := by
  have : k < bs.length := by
    rcases Nat.lt_or_ge k bs.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h
      cases h
  rw [List.length_take]; omega

theorem acc32_succ {bs : Bytes} {k : Nat} {u : UInt8} (h : bs[k]? = some u) :
    acc32 bs (k + 1) = acc32 bs k + 128 ^ k * (u.toNat % 128) := by
  unfold acc32
  rw [take_succ_of_get h, vacc_append, length_take_of_get h]
  simp [vacc]

theorem acc32_lt (bs : Bytes) (k : Nat) : acc32 bs k < 128 ^ k := by
  unfold acc32
  have h1 := vacc_lt (bs.take k)
  have h2 : (bs.take k).length ≤ k := List.length_take_le _ _
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)

/-- The varint ends at byte `k` (`u < 128`): its value and the rest. -/
theorem readVarint_at {bs : Bytes} {k : Nat} {u : UInt8} (hk : k ≤ 4)
    (hc : ∀ c ∈ bs.take k, 128 ≤ c.toNat) (h : bs[k]? = some u) (hu : u.toNat < 128) :
    Spec.readVarint 5 bs = some (acc32 bs k + 128 ^ k * u.toNat, bs.drop (k + 1)) := by
  have hlen := length_take_of_get h
  have hdrop : bs.drop k = u :: bs.drop (k + 1) := by
    rw [List.drop_eq_getElem?_toList_append, h]
    simp
  have e : bs.take k ++ (u :: bs.drop (k + 1)) = bs := by
    rw [← hdrop, List.take_append_drop]
  have key : Spec.readVarint ((bs.take k).length + (4 - k + 1)) (bs.take k ++ (u :: bs.drop (k + 1))) =
      some (vacc (bs.take k) + 128 ^ (bs.take k).length * u.toNat, bs.drop (k + 1)) := by
    rw [readVarint_prefix _ _ _ hc]
    simp only [Spec.readVarint, if_pos hu, Option.map_some]
  rw [e, hlen, show k + (4 - k + 1) = 5 by omega] at key
  unfold acc32
  exact key

/-- Five bytes with the high bit: overlong. -/
theorem overlong_of {bs : Bytes} (h5 : 5 ≤ bs.length) (hc : ∀ c ∈ bs.take 5, 128 ≤ c.toNat) :
    Spec.VarintOverlong 5 bs := ⟨h5, hc⟩

/-- The source ended after `k < 5` bytes with the high bit: truncated. -/
theorem truncated_of {bs : Bytes} {k : Nat} (hk : k ≤ 4) (hc : ∀ c ∈ bs.take k, 128 ≤ c.toNat)
    (he : bs.drop k = []) : Spec.VarintTruncated 5 bs := by
  have hl : bs.length ≤ k := List.drop_eq_nil_iff.mp he
  refine ⟨by omega, fun b hb => hc b ?_⟩
  rw [List.take_of_length_le hl]
  exact hb

/-- OR-ing the next group into the accumulated value adds it. -/
theorem or_acc32 (bs : Bytes) {k : Nat} (hk : k ≤ 4) (g : I32) :
    BitVec.ofNat 32 (acc32 bs k) ||| (g <<< (7 * k)) =
      BitVec.ofNat 32 (acc32 bs k + 128 ^ k * g.toNat) := by
  have h1 : acc32 bs k < 2 ^ (7 * k) := by
    rw [Nat.pow_mul]; exact acc32_lt bs k
  rw [or_shl_eq_add h1 (by omega), Nat.pow_mul]

end EquivLean.Demo.Thrift.Java
