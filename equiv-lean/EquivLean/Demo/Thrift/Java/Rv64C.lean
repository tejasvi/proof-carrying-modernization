import EquivLean.Demo.Thrift.Java.Rv64L

/-!
# Thrift → Java (T4): the closers of `readVarint64()`'s verification conditions

As for `readVarint32()` (`Rv32C`), with 10 bytes and a `long` accumulator.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem truncated10_of {bs : Bytes} {k : Nat} (hk : k ≤ 9) (hc : ∀ c ∈ bs.take k, 128 ≤ c.toNat)
    (he : bs.drop k = []) : Spec.VarintTruncated 10 bs := by
  have hl : bs.length ≤ k := List.drop_eq_nil_iff.mp he
  refine ⟨by omega, fun b hb => hc b ?_⟩
  rw [List.take_of_length_le hl]
  exact hb

/-! ## The thirteen verification conditions -/

/-- (1) Entry, fewer than 5 bytes in the buffer: the slow loop's head with `k = 0`. -/
theorem rv64_g1 {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (h : CPAtH P R σ p t tmp) :
    ∃ k, k ≤ 10 ∧ (0#32 : I32) = BitVec.ofNat 32 k ∧ (0#32 : I32) = BitVec.ofNat 32 (7 * k) ∧
      (0#64 : I64) = BitVec.ofNat 64 (acc32 (R.src σ t) k) ∧ SlowFacts R σ σ t k ∧
      CPAtRH R σ p t tmp :=
  ⟨0, by omega, rfl, rfl, by rw [acc32_zero], slowFacts_zero R σ t, cpAtRH_of_cpAtH h⟩

/-- (2) Entry, at least 5 bytes in the buffer: the fast loop's head with `i = 0`. -/
theorem rv64_g2 {R : TRep} {σ : State} {t : Addr} {arr : List Value} {u : UInt8} {rest : Bytes}
    (hcond : ¬R.bufLen σ t < 10)
    (hlen : R.bufPos σ t + (R.bufLen σ t).toNat ≤ arr.length)
    (hbuf : List.take (R.bufLen σ t).toNat (List.drop (R.bufPos σ t) arr) =
      List.take (R.bufLen σ t).toNat (List.map jbyte (R.src σ t)))
    (hsl : R.bufLen σ t ≤ ((R.src σ t).length : Int))
    (hb : R.bufPos σ t + (R.bufLen σ t).toNat < 2147483648)
    (hsrc : R.src σ t = u :: rest)
    (hp : R.bufPos σ t < arr.length)
    (hel : arr[R.bufPos σ t]'hp = Value.int (BitVec.signExtend 32 u.toBitVec)) :
    ∃ x, x ≤ 9 ∧ (0#32 : I32) = BitVec.ofNat 32 x ∧ (0#32 : I32) = BitVec.ofNat 32 (7 * x) ∧
      (0#64 : I64) = BitVec.ofNat 64 (acc32 (u :: rest) x) ∧
      R.bufPos σ t + x < arr.length ∧ R.bufPos σ t + 9 < 2147483648 ∧
      ∃ x_1, arr[R.bufPos σ t + x]? = some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        (∃ h, arr[R.bufPos σ t + x]'h = Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        FastFacts10 R σ t arr x x_1 := by
  have h5 : 10 ≤ R.bufLen σ t := by omega
  refine ⟨0, by omega, rfl, rfl, by rw [acc32_zero], by omega, by omega, u, ?_, ⟨by omega, ?_⟩, ?_⟩
  · rw [Nat.add_zero, List.getElem?_eq_getElem hp, hel]
  · simp only [Nat.add_zero]; exact hel
  · unfold FastFacts10
    refine ⟨h5, hlen, by rw [hbuf, List.map_take], by omega, hb, by simp, by rw [hsrc]; rfl⟩

/-- (3) Fast loop, a continuation byte, fewer than 5 so far: the head with `i + 1`. -/
theorem rv64_g3 {R : TRep} {σ : State} {t : Addr} {arr : List Value} {i : Nat} {u : UInt8}
    (hi : i ≤ 9) (hhigh : JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hc : (i : Int) + 1 < 10) (hff : FastFacts10 R σ t arr i u) :
    ∃ x, x ≤ 9 ∧ BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 x ∧
      BitVec.ofNat 32 (7 * i) + 7#32 = BitVec.ofNat 32 (7 * x) ∧
      BitVec.ofNat 64 (acc32 (R.src σ t) i) |||
          JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * i)) =
        BitVec.ofNat 64 (acc32 (R.src σ t) x) ∧
      R.bufPos σ t + x < arr.length ∧
      ∃ x_1, arr[R.bufPos σ t + x]? = some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        (∃ h, arr[R.bufPos σ t + x]'h = Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        FastFacts10 R σ t arr x x_1 := by
  unfold FastFacts10 at hff
  obtain ⟨h5, hlen, hbuf, hsl, hb, hcs, hu⟩ := hff
  have hs : i + 1 < (R.src σ t).length := by omega
  have hel := buf_elem hbuf (show i + 1 < (R.bufLen σ t).toNat by omega) hs
  have hlt : R.bufPos σ t + (i + 1) < arr.length := by omega
  refine ⟨i + 1, by omega, ofNat_succ32 i, ofNat_add7 i, acc_step64 _ hi hu, hlt,
    (R.src σ t)[i + 1]'hs, hel, ⟨hlt, ?_⟩, ?_⟩
  · have h2 := hel
    rw [List.getElem?_eq_getElem hlt] at h2
    exact Option.some.inj h2
  · unfold FastFacts10
    exact ⟨h5, hlen, hbuf, hsl, hb, take_succ_high hu hcs ((highbit_iff u).mp hhigh),
      List.getElem?_eq_getElem hs⟩

/-- (4) Fast loop, a fifth continuation byte: overlong. -/
theorem rv64_g4 {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr} {arr : List Value} {i : Nat}
    {u : UInt8} {fs : List (FieldKey × Value)}
    (hCP : CPAtH P R σ p t tmp) (hi : i ≤ 9)
    (hhigh : JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hc : ¬ (i : Int) + 1 < 10) (hff : FastFacts10 R σ t arr i u)
    (he : σ'.heap σ.next = some (.plain tpeCls fs)) : rv64E P R [.ref p] σ σ.next σ' := by
  apply rv64_overlong hCP _ he
  unfold FastFacts10 at hff
  obtain ⟨h5, -, -, hsl, -, hcs, hu⟩ := hff
  have hi4 : i = 9 := by omega
  subst hi4
  exact ⟨by omega, take_succ_high hu hcs ((highbit_iff u).mp hhigh)⟩

/-- (5) Fast loop, the last byte: `consumeBuffer(i + 1)`'s precondition. -/
theorem rv64_g5 {R : TRep} {σ : State} {t : Addr} {arr : List Value} {i : Nat} {u : UInt8}
    (hi : i ≤ 9) (hinv : R.inv σ t) (hff : FastFacts10 R σ t arr i u) :
    ∃ t' n, (t = t' ∧ BitVec.ofNat 32 i + 1#32 = n) ∧ R.inv σ t' ∧ 0 ≤ BitVec.toInt n ∧
      BitVec.toInt n ≤ R.bufLen σ t' := by
  unfold FastFacts10 at hff
  obtain ⟨h5, -⟩ := hff
  have ht : (BitVec.ofNat 32 i + 1#32).toInt = (i : Int) + 1 := by
    rw [ofNat_succ32, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    split <;> omega
  exact ⟨t, _, ⟨rfl, rfl⟩, hinv, by rw [ht]; omega, by rw [ht]; omega⟩

/-- (6) Fast loop, the last byte: the value and the rest. -/
theorem rv64_g6 {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr} {arr : List Value} {i : Nat}
    {u : UInt8} {c : ClassName} {fst w : List (FieldKey × Value)}
    (hi : i ≤ 9) (hCP : CPAtH P R σ p t tmp) (hff : FastFacts10 R σ t arr i u)
    (hlow : ¬JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hinv' : R.inv σ' t) (hsrc : R.src σ' t = List.drop (i + 1) (R.src σ t))
    (hsink : R.sink σ' t = R.sink σ t)
    (hnext : σ'.next = σ.next) (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics)
    (hfr : ∀ a, ¬a = t → σ'.heap a = σ.heap a) (hown : ∀ a, R.owns σ' t a ↔ R.owns σ t a)
    (ht : σ.heap t = some (.plain c fst)) (ht' : σ'.heap t = some (.plain c w)) :
    rv64N P R [.ref p] σ (some (.long (BitVec.ofNat 64 (acc32 (R.src σ t) i) |||
      JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * i))))) σ' := by
  have hu128 : u.toNat < 128 := by
    have := mt (highbit_iff u).mpr hlow
    omega
  unfold FastFacts10 at hff
  obtain ⟨-, -, -, -, -, hcs, hu⟩ := hff
  have hR : CPAtR R σ' p t tmp :=
    cpAtR_after_consume (cpAtR_of_cpAt (CPAtH.elim hCP)) hinv' hfr hown
  exact rv64_normal hCP (readVarint_at10 hi hcs hu hu128) (by rw [acc_last64 _ hi hu128]) hsrc hsink
    (cpAt_of_R hCP ht hR ht')
    ⟨Nat.le_of_eq hnext.symm, hin, hst, fun a _ hat _ _ => hfr a hat⟩

/-- (7) Slow loop, 5 continuation bytes read: overlong. -/
theorem rv64_g7 {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {k : Nat}
    {fs : List (FieldKey × Value)}
    (hCP : CPAtH P R σ0 p t tmp) (hk : k ≤ 10) (hsf : SlowFacts R σ0 σ t k) (hc : 10 ≤ (k : Int))
    (he : σ'.heap σ.next = some (.plain tpeCls fs)) : rv64E P R [.ref p] σ0 σ.next σ' := by
  apply rv64_overlong hCP _ he
  unfold SlowFacts at hsf
  obtain ⟨hl, hcs, -⟩ := hsf
  have hk5 : k = 10 := by omega
  subst hk5
  exact ⟨hl, hcs⟩

/-- (11) Slow loop, `readAll` threw (end of input): truncated. -/
theorem rv64_g11 {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp e : Addr} {k : Nat}
    {fs : List (FieldKey × Value)}
    (hCP : CPAtH P R σ0 p t tmp) (hk5 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ t k)
    (hlen : (R.src σ t).length < (1#32 : I32).toNat)
    (he : σ'.heap e = some (.plain ttExcCls fs)) : rv64E P R [.ref p] σ0 e σ' := by
  apply rv64_truncated hCP _ he
  unfold SlowFacts at hsf
  obtain ⟨-, hcs, hs, -⟩ := hsf
  have h1 : (1#32 : I32).toNat = 1 := rfl
  rw [h1, hs] at hlen
  exact truncated10_of (by omega) hcs (List.eq_nil_of_length_eq_zero (by omega))

/-- (9) Slow loop, `readAll` read a continuation byte: the head with `k + 1`. -/
theorem rv64_g9 {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {xs : List Value}
    {c1 c2 : ClassName} {f1 f2 : List (FieldKey × Value)}
    (hk5 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
    (hfr1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hown1 : ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a) (hn1 : σ0.next ≤ σ1.next)
    (hlen1 : (1#32 : I32).toNat ≤ (R.src σ1 t).length) (hinv' : R.inv σ' t)
    (htmp' : σ'.heap tmp = some (.array (.prim .byte)
        (List.take (0#32 : I32).toNat xs ++
          (List.take (1#32 : I32).toNat (List.map jbyte (R.src σ1 t)) ++ List.drop 1 xs))))
    (htmp1 : σ1.heap tmp = some (.array (.prim .byte) xs))
    (hsrc' : R.src σ' t = List.drop (1#32 : I32).toNat (R.src σ1 t)) (hsink' : R.sink σ' t = R.sink σ1 t)
    (hn' : σ1.next ≤ σ'.next)
    (hfr' : ∀ a, a < σ1.next → ¬a = t → ¬R.owns σ1 t a → ¬a = tmp → σ'.heap a = σ1.heap a)
    (hown' : ∀ a, a < σ1.next → ¬R.owns σ1 t a → ¬R.owns σ' t a)
    (hhigh : JInt.toShort (BitVec.signExtend 32 ((R.src σ1 t)[0]'(by
        have : (1#32 : I32).toNat = 1 := rfl; omega)).toBitVec) &&& 128#32 = 128#32)
    (hc1 : σ0.heap t = some (.plain c1 f1)) (hc2 : σ0.heap t = some (.plain c2 f2)) :
    ∃ k', k' ≤ 10 ∧ BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 k' ∧
      BitVec.ofNat 32 (7 * k) + 7#32 = BitVec.ofNat 32 (7 * k') ∧
      BitVec.ofNat 64 (acc32 (R.src σ0 t) k) |||
          JLong.shl (JInt.toLong (BitVec.signExtend 32 ((R.src σ1 t)[0]'(by
            have : (1#32 : I32).toNat = 1 := rfl; omega)).toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
        BitVec.ofNat 64 (acc32 (R.src σ0 t) k') ∧
      SlowFacts R σ0 σ' t k' ∧ CPAtRH R σ' p t tmp ∧ c1 = c2 ∧
      (σ0.next ≤ σ'.next ∧
        ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ'.heap a = σ0.heap a) ∧
      ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ' t a := by
  obtain ⟨u, rest, hsrc1⟩ := src_cons_of_len (by decide) hlen1
  have hu0 := head_of_cons hsrc1 (by have : (1#32 : I32).toNat = 1 := rfl; omega)
  have hs'' : R.src σ1 t = u :: R.src σ' t := by rw [hsrc', hsrc1]; rfl
  rw [hu0] at hhigh ⊢
  obtain ⟨hacc, hsf'⟩ := slow_cont64 hk5 hsf hs'' hsink' ((highbit_iff u).mp hhigh)
  have hR1' := CPAtRH.elim hR1
  obtain ⟨-, xs1, -, -, -, htm1, hl1, -⟩ := hR1'
  rw [htm1] at htmp1
  simp only [Option.some.injEq, Obj.array.injEq, true_and] at htmp1
  subst htmp1
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_readAll (CPAtRH.elim hR1) hinv' htmp'
    (readAll1_length xs1 _ hl1 hlen1) hfr' hown'
  refine ⟨k + 1, by omega, ofNat_succ32 k, ofNat_add7 k, hacc, hsf', CPAtRH.intro hR', ?_,
    ⟨Nat.le_trans hn1 hn', ?_⟩, ?_⟩
  · rw [hc1] at hc2
    simp only [Option.some.injEq, Obj.plain.injEq] at hc2
    exact hc2.1
  · intro a ha hat hatm hao
    rw [hfr' a (Nat.lt_of_lt_of_le ha hn1) hat (hown1 a ha hao) hatm, hfr1 a ha hat hatm hao]
  · intro a ha hao
    exact hown' a (Nat.lt_of_lt_of_le ha hn1) (hown1 a ha hao)

/-- (10) Slow loop, `readAll` read the last byte: the value and the rest. -/
theorem rv64_g10 {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {xs : List Value}
    {c : ClassName} {f0 w : List (FieldKey × Value)}
    (hCP0 : CPAtH P R σ0 p t tmp)
    (hk5 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
    (hfr1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hown1 : ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a) (hn1 : σ0.next ≤ σ1.next)
    (hlen1 : (1#32 : I32).toNat ≤ (R.src σ1 t).length) (hinv' : R.inv σ' t)
    (htmp' : σ'.heap tmp = some (.array (.prim .byte)
        (List.take (0#32 : I32).toNat xs ++
          (List.take (1#32 : I32).toNat (List.map jbyte (R.src σ1 t)) ++ List.drop 1 xs))))
    (htmp1 : σ1.heap tmp = some (.array (.prim .byte) xs))
    (hsrc' : R.src σ' t = List.drop (1#32 : I32).toNat (R.src σ1 t)) (hsink' : R.sink σ' t = R.sink σ1 t)
    (hn' : σ1.next ≤ σ'.next) (hin' : σ'.inits = σ0.inits) (hst' : σ'.statics = σ0.statics)
    (hfr' : ∀ a, a < σ1.next → ¬a = t → ¬R.owns σ1 t a → ¬a = tmp → σ'.heap a = σ1.heap a)
    (hown' : ∀ a, a < σ1.next → ¬R.owns σ1 t a → ¬R.owns σ' t a)
    (hc0 : σ0.heap t = some (.plain c f0)) (hct' : σ'.heap t = some (.plain c w))
    (hlow : ¬JInt.toShort (BitVec.signExtend 32 ((R.src σ1 t)[0]'(by
        have : (1#32 : I32).toNat = 1 := rfl; omega)).toBitVec) &&& 128#32 = 128#32) :
    rv64N P R [.ref p] σ0 (some (.long (BitVec.ofNat 64 (acc32 (R.src σ0 t) k) |||
      JLong.shl (JInt.toLong (BitVec.signExtend 32 ((R.src σ1 t)[0]'(by
        have : (1#32 : I32).toNat = 1 := rfl; omega)).toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k))))) σ' := by
  obtain ⟨u, rest, hsrc1⟩ := src_cons_of_len (by decide) hlen1
  have hu0 := head_of_cons hsrc1 (by have : (1#32 : I32).toNat = 1 := rfl; omega)
  have hs'' : R.src σ1 t = u :: R.src σ' t := by rw [hsrc', hsrc1]; rfl
  rw [hu0] at hlow ⊢
  have hu128 : u.toNat < 128 := by
    have := mt (highbit_iff u).mpr hlow
    omega
  obtain ⟨hrd, hacc, hsk⟩ := slow_ret64 hk5 hsf hs'' hsink' hu128
  have hR1' := CPAtRH.elim hR1
  obtain ⟨-, xs1, -, -, -, htm1, hl1, -⟩ := hR1'
  rw [htm1] at htmp1
  simp only [Option.some.injEq, Obj.array.injEq, true_and] at htmp1
  subst htmp1
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_readAll (CPAtRH.elim hR1) hinv' htmp'
    (readAll1_length xs1 _ hl1 hlen1) hfr' hown'
  exact rv64_normal hCP0 hrd (by rw [hacc]) rfl hsk (cpAt_of_R hCP0 hc0 hR' hct')
    ⟨Nat.le_trans hn1 hn', hin', hst', fun a ha hat hatm hao => by
      rw [hfr' a (Nat.lt_of_lt_of_le ha hn1) hat (hown1 a ha hao) hatm, hfr1 a ha hat hatm hao]⟩

/-- (12) Slow loop, the buffer gave a continuation byte: the head with `k + 1`. -/
theorem rv64_g12 {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {u : UInt8}
    {c1 c2 : ClassName} {f1 f2 : List (FieldKey × Value)}
    (hk5 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
    (hfr1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hown1 : ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a)
    (hhigh : JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hinv' : R.inv σ' t) (hsink' : R.sink σ' t = R.sink σ1 t)
    (hfr' : ∀ a, ¬a = t → σ'.heap a = σ1.heap a) (hown' : ∀ a, R.owns σ' t a ↔ R.owns σ1 t a)
    (hs'' : R.src σ1 t = u :: R.src σ' t)
    (hc1 : σ0.heap t = some (.plain c1 f1)) (hc2 : σ0.heap t = some (.plain c2 f2)) :
    ∃ k', k' ≤ 10 ∧ BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 k' ∧
      BitVec.ofNat 32 (7 * k) + 7#32 = BitVec.ofNat 32 (7 * k') ∧
      BitVec.ofNat 64 (acc32 (R.src σ0 t) k) |||
          JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k)) =
        BitVec.ofNat 64 (acc32 (R.src σ0 t) k') ∧
      SlowFacts R σ0 σ' t k' ∧ CPAtRH R σ' p t tmp ∧ c1 = c2 ∧
      (∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ'.heap a = σ0.heap a) ∧
      ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a := by
  obtain ⟨hacc, hsf'⟩ := slow_cont64 hk5 hsf hs'' hsink' ((highbit_iff u).mp hhigh)
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_consume (CPAtRH.elim hR1) hinv' hfr' hown'
  refine ⟨k + 1, by omega, ofNat_succ32 k, ofNat_add7 k, hacc, hsf', CPAtRH.intro hR', ?_, ?_, hown1⟩
  · rw [hc1] at hc2
    simp only [Option.some.injEq, Obj.plain.injEq] at hc2
    exact hc2.1
  · intro a ha hat hatm hao
    rw [hfr' a hat, hfr1 a ha hat hatm hao]

/-- (13) Slow loop, the buffer gave the last byte: the value and the rest. -/
theorem rv64_g13 {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {u : UInt8}
    {c : ClassName} {f0 w : List (FieldKey × Value)}
    (hCP0 : CPAtH P R σ0 p t tmp)
    (hk5 : ¬ 10 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
    (hfr1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hn1 : σ0.next ≤ σ1.next)
    (hinv' : R.inv σ' t) (hsink' : R.sink σ' t = R.sink σ1 t)
    (hn' : σ'.next = σ1.next) (hin' : σ'.inits = σ0.inits) (hst' : σ'.statics = σ0.statics)
    (hfr' : ∀ a, ¬a = t → σ'.heap a = σ1.heap a) (hown' : ∀ a, R.owns σ' t a ↔ R.owns σ1 t a)
    (hct' : σ'.heap t = some (.plain c w)) (hs'' : R.src σ1 t = u :: R.src σ' t)
    (hc0 : σ0.heap t = some (.plain c f0))
    (hlow : ¬JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32) :
    rv64N P R [.ref p] σ0 (some (.long (BitVec.ofNat 64 (acc32 (R.src σ0 t) k) |||
      JLong.shl (JInt.toLong (BitVec.signExtend 32 u.toBitVec &&& 127#32)) (BitVec.ofNat 32 (7 * k))))) σ' := by
  have hu128 : u.toNat < 128 := by
    have := mt (highbit_iff u).mpr hlow
    omega
  obtain ⟨hrd, hacc, hsk⟩ := slow_ret64 hk5 hsf hs'' hsink' hu128
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_consume (CPAtRH.elim hR1) hinv' hfr' hown'
  exact rv64_normal hCP0 hrd (by rw [hacc]) rfl hsk (cpAt_of_R hCP0 hc0 hR' hct')
    ⟨by rw [hn']; exact hn1, hin', hst', fun a ha hat hatm hao => by rw [hfr' a hat, hfr1 a ha hat hatm hao]⟩

end EquivLean.Demo.Thrift.Java
