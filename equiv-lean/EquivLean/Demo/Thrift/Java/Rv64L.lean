import EquivLean.Demo.Thrift.Java.Rv64D

/-!
# Thrift → Java (T4): the 64-bit facts of `readVarint64()`
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem toLong_and127 (u : UInt8) :
    JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32) = BitVec.ofNat 64 (u.toNat % 128) := by
  rw [sx_and127]
  simp only [JInt.toLong]
  apply BitVec.eq_of_toNat_eq
  have h : u.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  have hm : (BitVec.ofNat 32 (u.toNat % 128)).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u.toNat % 128 < 2 ^ 32)]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    have : 2 ^ (32 - 1) = 2147483648 := rfl
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

theorem shl64_ofNat (x : I64) {s : Nat} (hs : s < 64) : JLong.shl x (BitVec.ofNat 32 s) = x <<< s := by
  simp only [JLong.shl, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 32), Nat.mod_eq_of_lt hs]

theorem ofNat64_getLsbD_high {a i s : Nat} (ha : a < 2 ^ s) (hi : s ≤ i) :
    (BitVec.ofNat 64 a).getLsbD i = false := by
  rw [BitVec.getLsbD_ofNat]
  have : a.testBit i = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hi))
  simp [this]

theorem or_shl_eq_add64 {a s : Nat} {g : I64} (ha : a < 2 ^ s) (hs : s < 64) :
    BitVec.ofNat 64 a ||| (g <<< s) = BitVec.ofNat 64 (a + 2 ^ s * g.toNat) := by
  have hand : BitVec.ofNat 64 a &&& (g <<< s) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    by_cases h : s ≤ i
    · rw [ofNat64_getLsbD_high ha h]; simp
    · simp [show i < s by omega]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_comm (2 ^ s) g.toNat]

theorem or_acc64 (bs : Bytes) {k : Nat} (hk : k ≤ 9) (g : I64) :
    BitVec.ofNat 64 (acc32 bs k) ||| (g <<< (7 * k)) =
      BitVec.ofNat 64 (acc32 bs k + 128 ^ k * g.toNat) := by
  have h1 : acc32 bs k < 2 ^ (7 * k) := by
    rw [Nat.pow_mul]; exact acc32_lt bs k
  rw [or_shl_eq_add64 h1 (by omega), Nat.pow_mul]

theorem acc_or64 (bs : Bytes) {k : Nat} (hk : k ≤ 9) (u : UInt8) :
    BitVec.ofNat 64 (acc32 bs k) |||
        JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 64 (acc32 bs k + 128 ^ k * (u.toNat % 128)) := by
  rw [shl64_ofNat _ (by omega), or_acc64 bs hk, toLong_and127, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show u.toNat % 128 < 2 ^ 64 from
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem acc_step64 (bs : Bytes) {k : Nat} (hk : k ≤ 9) {u : UInt8} (h : bs[k]? = some u) :
    BitVec.ofNat 64 (acc32 bs k) |||
        JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 64 (acc32 bs (k + 1)) := by
  rw [acc_or64 bs hk, acc32_succ h]

theorem acc_last64 (bs : Bytes) {k : Nat} (hk : k ≤ 9) {u : UInt8} (hu : u.toNat < 128) :
    BitVec.ofNat 64 (acc32 bs k) |||
        JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 64 (acc32 bs k + 128 ^ k * u.toNat) := by
  rw [acc_or64 bs hk, Nat.mod_eq_of_lt hu]

/-- The varint ends at byte `k < 10`: its value and the rest. -/
theorem readVarint_at10 {bs : Bytes} {k : Nat} {u : UInt8} (hk : k ≤ 9)
    (hc : ∀ c ∈ bs.take k, 128 ≤ c.toNat) (h : bs[k]? = some u) (hu : u.toNat < 128) :
    Spec.readVarint 10 bs = some (acc32 bs k + 128 ^ k * u.toNat, bs.drop (k + 1)) := by
  have hlen := length_take_of_get h
  have hdrop : bs.drop k = u :: bs.drop (k + 1) := by
    rw [List.drop_eq_getElem?_toList_append, h]
    simp
  have e : bs.take k ++ (u :: bs.drop (k + 1)) = bs := by
    rw [← hdrop, List.take_append_drop]
  have key : Spec.readVarint ((bs.take k).length + (9 - k + 1)) (bs.take k ++ (u :: bs.drop (k + 1))) =
      some (vacc (bs.take k) + 128 ^ (bs.take k).length * u.toNat, bs.drop (k + 1)) := by
    rw [readVarint_prefix _ _ _ hc]
    simp only [Spec.readVarint, if_pos hu, Option.map_some]
  rw [e, hlen, show k + (9 - k + 1) = 10 by omega] at key
  unfold acc32
  exact key

theorem rv64_overlong {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} (hCP : CPAtH P R σ p t tmp)
    (hov : Spec.VarintOverlong 10 (R.src σ t)) (he : σ'.heap e = some (.plain tpeCls fs)) :
    rv64E P R [.ref p] σ e σ' := by
  unfold rv64E
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' (CPAtH.elim hCP)
  exact Or.inl ⟨hov, fs, he⟩

theorem rv64_truncated {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} (hCP : CPAtH P R σ p t tmp)
    (htr : Spec.VarintTruncated 10 (R.src σ t)) (he : σ'.heap e = some (.plain ttExcCls fs)) :
    rv64E P R [.ref p] σ e σ' := by
  unfold rv64E
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' (CPAtH.elim hCP)
  exact Or.inr ⟨htr, fs, he⟩

theorem rv64_normal {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr} {v : Nat} {rest : Bytes}
    {r : Value} (hCP : CPAtH P R σ p t tmp) (hrd : Spec.readVarint 10 (R.src σ t) = some (v, rest))
    (hr : r = .long (BitVec.ofNat 64 v)) (hsrc : R.src σ' t = rest) (hsink : R.sink σ' t = R.sink σ t)
    (hCP' : CPAt P R σ' p t tmp) (hpf : PFrame R σ σ' t tmp) : rv64N P R [.ref p] σ (some r) σ' := by
  unfold rv64N
  intro p' t' tmp' hargs hCP0
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP0 (CPAtH.elim hCP)
  exact ⟨v, rest, hrd, by rw [hr], hsrc, hsink, hCP', hpf⟩

theorem slow_ret64 {R : TRep} {σ0 σ1 σ' : State} {t : Addr} {k : Nat} {u : UInt8}
    (hk10 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hsrc1 : R.src σ1 t = u :: R.src σ' t)
    (hsink' : R.sink σ' t = R.sink σ1 t) (hlow : u.toNat < 128) :
    Spec.readVarint 10 (R.src σ0 t) = some (acc32 (R.src σ0 t) k + 128 ^ k * u.toNat, R.src σ' t) ∧
      BitVec.ofNat 64 (acc32 (R.src σ0 t) k) |||
          JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
        BitVec.ofNat 64 (acc32 (R.src σ0 t) k + 128 ^ k * u.toNat) ∧
      R.sink σ' t = R.sink σ0 t := by
  obtain ⟨hget, -, hs', hsk', hc⟩ := slow_next hsf hsrc1 hsink'
  refine ⟨?_, acc_last64 _ (by omega) hlow, hsk'⟩
  rw [readVarint_at10 (by omega) hc hget hlow, hs']

theorem slow_cont64 {R : TRep} {σ0 σ1 σ' : State} {t : Addr} {k : Nat} {u : UInt8}
    (hk10 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hsrc1 : R.src σ1 t = u :: R.src σ' t)
    (hsink' : R.sink σ' t = R.sink σ1 t) (hhigh : 128 ≤ u.toNat) :
    BitVec.ofNat 64 (acc32 (R.src σ0 t) k) |||
        JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 64 (acc32 (R.src σ0 t) (k + 1)) ∧ SlowFacts R σ0 σ' t (k + 1) := by
  obtain ⟨hget, hlt, hs', hsk', hc⟩ := slow_next hsf hsrc1 hsink'
  refine ⟨acc_step64 _ (by omega) hget, ?_⟩
  unfold SlowFacts
  exact ⟨hlt, take_succ_high hget hc hhigh, hs', hsk'⟩

end EquivLean.Demo.Thrift.Java
