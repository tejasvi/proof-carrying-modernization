import EquivLean.Demo.Thrift.Java.Rv32D

/-!
# Thrift → Java (T4): the closers of `readVarint32()`'s verification conditions

The facts the symbolic execution leaves, per path: the loop steps (the next group ORed in, the
loop facts carried), the returns (the value read and the rest), the exceptions (overlong,
truncated).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## Helpers -/

theorem cpAtR_of_cpAt {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    (h : CPAt P R σ p t tmp) : CPAtR R σ p t tmp := by
  obtain ⟨fs, xs, c, fst, hp, htr, hte, htm, hl, -, -, -, hinv, hpt, htt, hptm, hop, hot⟩ := h
  exact ⟨fs, xs, hp, htr, hte, htm, hl, hinv, hpt, htt, hptm, hop, hot⟩

theorem CPAtRH.intro {R : TRep} {σ : State} {p t tmp : Addr} (h : CPAtR R σ p t tmp) :
    CPAtRH R σ p t tmp := by unfold CPAtRH; exact h

theorem CPAtRH.elim {R : TRep} {σ : State} {p t tmp : Addr} (h : CPAtRH R σ p t tmp) :
    CPAtR R σ p t tmp := by unfold CPAtRH at h; exact h

theorem cpAtRH_of_cpAtH {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    (h : CPAtH P R σ p t tmp) : CPAtRH R σ p t tmp :=
  CPAtRH.intro (cpAtR_of_cpAt (CPAtH.elim h))

theorem slowFacts_zero (R : TRep) (σ : State) (t : Addr) : SlowFacts R σ σ t 0 := by
  unfold SlowFacts
  exact ⟨Nat.zero_le _, by simp, by simp, rfl⟩

/-- An element of the buffer, from the buffer's contents. -/
theorem buf_elem {arr : List Value} {pos n j : Nat} {src : Bytes}
    (h : (arr.drop pos).take n = (src.take n).map jbyte) (hj : j < n) (hjs : j < src.length) :
    arr[pos + j]? = some (jbyte (src[j]'hjs)) := by
  have h1 := congrArg (fun l => l[j]?) h
  simp only [List.getElem?_take, if_pos hj, List.getElem?_drop, List.getElem?_map] at h1
  rw [h1, List.getElem?_eq_getElem hjs]
  rfl

theorem highbit_iff (u : UInt8) :
    JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32 ↔ 128 ≤ u.toNat := by
  rw [toShort_sx, sx_and128]
  by_cases h : 128 ≤ u.toNat
  · simp [h]
  · simp only [h, if_false, iff_false]
    decide

theorem ofNat_add7 (k : Nat) : BitVec.ofNat 32 (7 * k) + 7#32 = BitVec.ofNat 32 (7 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The next group ORed into the accumulated value. -/
theorem acc_or (bs : Bytes) {k : Nat} (hk : k ≤ 4) (u : UInt8) :
    BitVec.ofNat 32 (acc32 bs k) |||
        JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 32 (acc32 bs k + 128 ^ k * (u.toNat % 128)) := by
  rw [shl_ofNat _ (by omega), or_acc32 bs hk, sx_and127_toNat]

theorem acc_step (bs : Bytes) {k : Nat} (hk : k ≤ 4) {u : UInt8} (h : bs[k]? = some u) :
    BitVec.ofNat 32 (acc32 bs k) |||
        JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 32 (acc32 bs (k + 1)) := by
  rw [acc_or bs hk, acc32_succ h]

theorem acc_last (bs : Bytes) {k : Nat} (hk : k ≤ 4) {u : UInt8} (hu : u.toNat < 128) :
    BitVec.ofNat 32 (acc32 bs k) |||
        JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 32 (acc32 bs k + 128 ^ k * u.toNat) := by
  rw [acc_or bs hk, Nat.mod_eq_of_lt hu]

/-- `take (k+1)` with all high bits, from `take k` and the next byte. -/
theorem take_succ_high {bs : Bytes} {k : Nat} {u : UInt8} (h : bs[k]? = some u)
    (hc : ∀ c ∈ bs.take k, 128 ≤ c.toNat) (hu : 128 ≤ u.toNat) :
    ∀ c ∈ bs.take (k + 1), 128 ≤ c.toNat := by
  rw [take_succ_of_get h]
  intro c hc'
  rcases List.mem_append.mp hc' with h1 | h1
  · exact hc c h1
  · rw [List.mem_singleton.mp h1]; exact hu

/-- The exception object of `new TProtocolException(...)` after its constructor: at the address
allocated first. -/
theorem heap_newExc (σ : State) (o1 s o2 o3 o4 : Obj) :
    (((((σ.alloc o1).2.alloc s).2.setObj σ.next o2).setObj σ.next o3).setObj σ.next o4).heap σ.next =
      some o4 := by
  apply setObj_heap_self
  rw [State.next_setObj, State.next_setObj, State.next_alloc, State.next_alloc]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _)

/-! ## The results: `rv32N`, `rv32E` from their facts -/

theorem rv_overlong {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} (hCP : CPAtH P R σ p t tmp)
    (hov : Spec.VarintOverlong 5 (R.src σ t)) (he : σ'.heap e = some (.plain tpeCls fs)) :
    rv32E P R [.ref p] σ e σ' := by
  unfold rv32E
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' (CPAtH.elim hCP)
  exact Or.inl ⟨hov, fs, he⟩

theorem rv_truncated {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} (hCP : CPAtH P R σ p t tmp)
    (htr : Spec.VarintTruncated 5 (R.src σ t)) (he : σ'.heap e = some (.plain ttExcCls fs)) :
    rv32E P R [.ref p] σ e σ' := by
  unfold rv32E
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' (CPAtH.elim hCP)
  exact Or.inr ⟨htr, fs, he⟩

theorem rv_normal {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr} {v : Nat} {rest : Bytes}
    {r : Value} (hCP : CPAtH P R σ p t tmp) (hrd : Spec.readVarint 5 (R.src σ t) = some (v, rest))
    (hr : r = .int (BitVec.ofNat 32 v)) (hsrc : R.src σ' t = rest) (hsink : R.sink σ' t = R.sink σ t)
    (hCP' : CPAt P R σ' p t tmp) (hpf : PFrame R σ σ' t tmp) (hom : OwnsMono R σ σ' t) :
    rv32N P R [.ref p] σ (some r) σ' := by
  unfold rv32N
  intro p' t' tmp' hargs hCP0
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP0 (CPAtH.elim hCP)
  exact ⟨v, rest, hrd, by rw [hr], hsrc, hsink, hCP', hpf, hom⟩

/-- `CPAt` from the program-free facts and the class of the transport object at the entry. -/
theorem cpAt_of_R {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {c : ClassName}
    {f0 w : List (FieldKey × Value)} (hCP0 : CPAtH P R σ0 p t tmp)
    (hc0 : σ0.heap t = some (.plain c f0)) (hR : CPAtR R σ p t tmp)
    (hct : σ.heap t = some (.plain c w)) : CPAt P R σ p t tmp := by
  obtain ⟨-, -, c1, f1, -, -, -, -, -, ht1, hc1, hc2, -⟩ := CPAtH.elim hCP0
  rw [hc0] at ht1
  simp only [Option.some.injEq, Obj.plain.injEq] at ht1
  obtain ⟨rfl, -⟩ := ht1
  obtain ⟨fs, xs, hp, htr, hte, htm, hl, hinv, hpt, htt, hptm, hop, hot⟩ := hR
  exact ⟨fs, xs, c, w, hp, htr, hte, htm, hl, hct, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩

/-! ## The objects after `readByte()` -/

theorem readAll1_length (xs : List Value) (bs : Bytes) (hxs : xs.length = 16) (hbs : 1 ≤ bs.length) :
    (List.take (0#32 : I32).toNat xs ++
      (List.take (1#32 : I32).toNat (List.map jbyte bs) ++ List.drop 1 xs)).length = 16 := by
  simp only [show (0#32 : I32).toNat = 0 from rfl, show (1#32 : I32).toNat = 1 from rfl,
    List.length_append, List.length_take, List.length_map, List.length_drop, hxs]
  omega

theorem cpAtR_after_readAll {R : TRep} {σ1 σ' : State} {p t tmp : Addr} {ys : List Value}
    (hR : CPAtR R σ1 p t tmp) (hinv' : R.inv σ' t)
    (htmp' : σ'.heap tmp = some (.array (.prim .byte) ys)) (hys : ys.length = 16)
    (hfr' : ∀ a, a < σ1.next → ¬a = t → ¬R.owns σ1 t a → ¬a = tmp → σ'.heap a = σ1.heap a)
    (hown' : ∀ a, a < σ1.next → ¬R.owns σ1 t a → ¬R.owns σ' t a) : CPAtR R σ' p t tmp := by
  obtain ⟨fs, xs, hp, htr, hte, htm, hl, hinv, hpt, htt, hptm, hop, hot⟩ := hR
  have hplt : p < σ1.next := State.lt_next_of_heap hp
  have htlt : tmp < σ1.next := State.lt_next_of_heap htm
  exact ⟨fs, ys, by rw [hfr' p hplt hpt hop hptm]; exact hp, htr, hte, htmp', hys, hinv', hpt, htt, hptm,
    hown' p hplt hop, hown' tmp htlt hot⟩

theorem cpAtR_after_consume {R : TRep} {σ1 σ' : State} {p t tmp : Addr}
    (hR : CPAtR R σ1 p t tmp) (hinv' : R.inv σ' t)
    (hfr' : ∀ a, ¬a = t → σ'.heap a = σ1.heap a) (hown' : ∀ a, R.owns σ' t a ↔ R.owns σ1 t a) :
    CPAtR R σ' p t tmp := by
  obtain ⟨fs, xs, hp, htr, hte, htm, hl, hinv, hpt, htt, hptm, hop, hot⟩ := hR
  exact ⟨fs, xs, by rw [hfr' p hpt]; exact hp, htr, hte, by rw [hfr' tmp htt]; exact htm, hl, hinv',
    hpt, htt, hptm, by rw [hown']; exact hop, by rw [hown']; exact hot⟩

/-! ## The slow loop -/

theorem slow_next {R : TRep} {σ0 σ1 σ' : State} {t : Addr} {k : Nat} {u : UInt8}
    (hsf : SlowFacts R σ0 σ1 t k) (hsrc1 : R.src σ1 t = u :: R.src σ' t)
    (hsink' : R.sink σ' t = R.sink σ1 t) :
    (R.src σ0 t)[k]? = some u ∧ k < (R.src σ0 t).length ∧
      R.src σ' t = (R.src σ0 t).drop (k + 1) ∧ R.sink σ' t = R.sink σ0 t ∧
      (∀ c ∈ (R.src σ0 t).take k, 128 ≤ c.toNat) := by
  unfold SlowFacts at hsf
  obtain ⟨hk, hc, hs, hsk⟩ := hsf
  rw [hs] at hsrc1
  have h1 : ((R.src σ0 t).drop k)[0]? = some u := by rw [hsrc1]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at h1
  refine ⟨h1, ?_, ?_, by rw [hsink', hsk], hc⟩
  · rcases Nat.lt_or_ge k (R.src σ0 t).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h1; cases h1
  · have := congrArg List.tail hsrc1
    simp only [List.tail_cons] at this
    rw [← this, List.tail_drop]

theorem slow_cont {R : TRep} {σ0 σ1 σ' : State} {t : Addr} {k : Nat} {u : UInt8}
    (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hsrc1 : R.src σ1 t = u :: R.src σ' t)
    (hsink' : R.sink σ' t = R.sink σ1 t) (hhigh : 128 ≤ u.toNat) :
    BitVec.ofNat 32 (acc32 (R.src σ0 t) k) |||
        JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
      BitVec.ofNat 32 (acc32 (R.src σ0 t) (k + 1)) ∧ SlowFacts R σ0 σ' t (k + 1) := by
  obtain ⟨hget, hlt, hs', hsk', hc⟩ := slow_next hsf hsrc1 hsink'
  refine ⟨acc_step _ (by omega) hget, ?_⟩
  unfold SlowFacts
  exact ⟨hlt, take_succ_high hget hc hhigh, hs', hsk'⟩

theorem slow_ret {R : TRep} {σ0 σ1 σ' : State} {t : Addr} {k : Nat} {u : UInt8}
    (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hsrc1 : R.src σ1 t = u :: R.src σ' t)
    (hsink' : R.sink σ' t = R.sink σ1 t) (hlow : u.toNat < 128) :
    Spec.readVarint 5 (R.src σ0 t) = some (acc32 (R.src σ0 t) k + 128 ^ k * u.toNat, R.src σ' t) ∧
      BitVec.ofNat 32 (acc32 (R.src σ0 t) k) |||
          JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
        BitVec.ofNat 32 (acc32 (R.src σ0 t) k + 128 ^ k * u.toNat) ∧
      R.sink σ' t = R.sink σ0 t := by
  obtain ⟨hget, -, hs', hsk', hc⟩ := slow_next hsf hsrc1 hsink'
  refine ⟨?_, acc_last _ (by omega) hlow, hsk'⟩
  rw [readVarint_at (by omega) hc hget hlow, hs']

theorem head_of_cons {l : Bytes} {u : UInt8} {rest : Bytes} (h : l = u :: rest) (hl : 0 < l.length) :
    l[0]'hl = u := by
  subst h; rfl

/-! ## The thirteen verification conditions -/

/-- (1) Entry, fewer than 5 bytes in the buffer: the slow loop's head with `k = 0`. -/
theorem rv_g1 {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (h : CPAtH P R σ p t tmp) :
    ∃ k, k ≤ 5 ∧ (0#32 : I32) = BitVec.ofNat 32 k ∧ (0#32 : I32) = BitVec.ofNat 32 (7 * k) ∧
      (0#32 : I32) = BitVec.ofNat 32 (acc32 (R.src σ t) k) ∧ SlowFacts R σ σ t k ∧
      CPAtRH R σ p t tmp :=
  ⟨0, by omega, rfl, rfl, by rw [acc32_zero], slowFacts_zero R σ t, cpAtRH_of_cpAtH h⟩

/-- (2) Entry, at least 5 bytes in the buffer: the fast loop's head with `i = 0`. -/
theorem rv_g2 {R : TRep} {σ : State} {t : Addr} {arr : List Value} {u : UInt8} {rest : Bytes}
    (hcond : ¬R.bufLen σ t < 5)
    (hlen : R.bufPos σ t + (R.bufLen σ t).toNat ≤ arr.length)
    (hbuf : List.take (R.bufLen σ t).toNat (List.drop (R.bufPos σ t) arr) =
      List.take (R.bufLen σ t).toNat (List.map jbyte (R.src σ t)))
    (hsl : R.bufLen σ t ≤ ((R.src σ t).length : Int))
    (hb : R.bufPos σ t + (R.bufLen σ t).toNat < 2147483648)
    (hsrc : R.src σ t = u :: rest)
    (hp : R.bufPos σ t < arr.length)
    (hel : arr[R.bufPos σ t]'hp = Value.int (BitVec.signExtend 32 u.toBitVec)) :
    ∃ x, x ≤ 4 ∧ (0#32 : I32) = BitVec.ofNat 32 x ∧ (0#32 : I32) = BitVec.ofNat 32 (7 * x) ∧
      (0#32 : I32) = BitVec.ofNat 32 (acc32 (u :: rest) x) ∧
      R.bufPos σ t + x < arr.length ∧ R.bufPos σ t + 4 < 2147483648 ∧
      ∃ x_1, arr[R.bufPos σ t + x]? = some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        (∃ h, arr[R.bufPos σ t + x]'h = Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        FastFacts R σ t arr x x_1 := by
  have h5 : 5 ≤ R.bufLen σ t := by omega
  refine ⟨0, by omega, rfl, rfl, by rw [acc32_zero], by omega, by omega, u, ?_, ⟨by omega, ?_⟩, ?_⟩
  · rw [Nat.add_zero, List.getElem?_eq_getElem hp, hel]
  · simp only [Nat.add_zero]; exact hel
  · unfold FastFacts
    refine ⟨h5, hlen, by rw [hbuf, List.map_take], by omega, hb, by simp, by rw [hsrc]; rfl⟩

/-- (3) Fast loop, a continuation byte, fewer than 5 so far: the head with `i + 1`. -/
theorem rv_g3 {R : TRep} {σ : State} {t : Addr} {arr : List Value} {i : Nat} {u : UInt8}
    (hi : i ≤ 4) (hhigh : JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hc : (i : Int) + 1 < 5) (hff : FastFacts R σ t arr i u) :
    ∃ x, x ≤ 4 ∧ BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 x ∧
      BitVec.ofNat 32 (7 * i) + 7#32 = BitVec.ofNat 32 (7 * x) ∧
      BitVec.ofNat 32 (acc32 (R.src σ t) i) |||
          JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * i)) =
        BitVec.ofNat 32 (acc32 (R.src σ t) x) ∧
      R.bufPos σ t + x < arr.length ∧
      ∃ x_1, arr[R.bufPos σ t + x]? = some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        (∃ h, arr[R.bufPos σ t + x]'h = Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
        FastFacts R σ t arr x x_1 := by
  unfold FastFacts at hff
  obtain ⟨h5, hlen, hbuf, hsl, hb, hcs, hu⟩ := hff
  have hs : i + 1 < (R.src σ t).length := by omega
  have hel := buf_elem hbuf (show i + 1 < (R.bufLen σ t).toNat by omega) hs
  have hlt : R.bufPos σ t + (i + 1) < arr.length := by omega
  refine ⟨i + 1, by omega, ofNat_succ32 i, ofNat_add7 i, acc_step _ hi hu, hlt,
    (R.src σ t)[i + 1]'hs, hel, ⟨hlt, ?_⟩, ?_⟩
  · have h2 := hel
    rw [List.getElem?_eq_getElem hlt] at h2
    exact Option.some.inj h2
  · unfold FastFacts
    exact ⟨h5, hlen, hbuf, hsl, hb, take_succ_high hu hcs ((highbit_iff u).mp hhigh),
      List.getElem?_eq_getElem hs⟩

/-- (4) Fast loop, a fifth continuation byte: overlong. -/
theorem rv_g4 {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr} {arr : List Value} {i : Nat}
    {u : UInt8} {fs : List (FieldKey × Value)}
    (hCP : CPAtH P R σ p t tmp) (hi : i ≤ 4)
    (hhigh : JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hc : ¬ (i : Int) + 1 < 5) (hff : FastFacts R σ t arr i u)
    (he : σ'.heap σ.next = some (.plain tpeCls fs)) : rv32E P R [.ref p] σ σ.next σ' := by
  apply rv_overlong hCP _ he
  unfold FastFacts at hff
  obtain ⟨h5, -, -, hsl, -, hcs, hu⟩ := hff
  have hi4 : i = 4 := by omega
  subst hi4
  exact ⟨by omega, take_succ_high hu hcs ((highbit_iff u).mp hhigh)⟩

/-- (5) Fast loop, the last byte: `consumeBuffer(i + 1)`'s precondition. -/
theorem rv_g5 {R : TRep} {σ : State} {t : Addr} {arr : List Value} {i : Nat} {u : UInt8}
    (hi : i ≤ 4) (hinv : R.inv σ t) (hff : FastFacts R σ t arr i u) :
    ∃ t' n, (t = t' ∧ BitVec.ofNat 32 i + 1#32 = n) ∧ R.inv σ t' ∧ 0 ≤ BitVec.toInt n ∧
      BitVec.toInt n ≤ R.bufLen σ t' := by
  unfold FastFacts at hff
  obtain ⟨h5, -⟩ := hff
  have ht : (BitVec.ofNat 32 i + 1#32).toInt = (i : Int) + 1 := by
    rw [ofNat_succ32, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    split <;> omega
  exact ⟨t, _, ⟨rfl, rfl⟩, hinv, by rw [ht]; omega, by rw [ht]; omega⟩

/-- (6) Fast loop, the last byte: the value and the rest. -/
theorem rv_g6 {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr} {arr : List Value} {i : Nat}
    {u : UInt8} {c : ClassName} {fst w : List (FieldKey × Value)}
    (hi : i ≤ 4) (hCP : CPAtH P R σ p t tmp) (hff : FastFacts R σ t arr i u)
    (hlow : ¬JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hinv' : R.inv σ' t) (hsrc : R.src σ' t = List.drop (i + 1) (R.src σ t))
    (hsink : R.sink σ' t = R.sink σ t)
    (hnext : σ'.next = σ.next) (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics)
    (hfr : ∀ a, ¬a = t → σ'.heap a = σ.heap a) (hown : ∀ a, R.owns σ' t a ↔ R.owns σ t a)
    (ht : σ.heap t = some (.plain c fst)) (ht' : σ'.heap t = some (.plain c w)) :
    rv32N P R [.ref p] σ (some (.int (BitVec.ofNat 32 (acc32 (R.src σ t) i) |||
      JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * i))))) σ' := by
  have hu128 : u.toNat < 128 := by
    have := mt (highbit_iff u).mpr hlow
    omega
  unfold FastFacts at hff
  obtain ⟨-, -, -, -, -, hcs, hu⟩ := hff
  have hR : CPAtR R σ' p t tmp :=
    cpAtR_after_consume (cpAtR_of_cpAt (CPAtH.elim hCP)) hinv' hfr hown
  exact rv_normal hCP (readVarint_at hi hcs hu hu128) (by rw [acc_last _ hi hu128]) hsrc hsink
    (cpAt_of_R hCP ht hR ht')
    ⟨Nat.le_of_eq hnext.symm, hin, hst, fun a _ hat _ _ => hfr a hat⟩
    (fun a _ h => by rw [hown]; exact h)

/-- (7) Slow loop, 5 continuation bytes read: overlong. -/
theorem rv_g7 {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {k : Nat}
    {fs : List (FieldKey × Value)}
    (hCP : CPAtH P R σ0 p t tmp) (hk : k ≤ 5) (hsf : SlowFacts R σ0 σ t k) (hc : 5 ≤ (k : Int))
    (he : σ'.heap σ.next = some (.plain tpeCls fs)) : rv32E P R [.ref p] σ0 σ.next σ' := by
  apply rv_overlong hCP _ he
  unfold SlowFacts at hsf
  obtain ⟨hl, hcs, -⟩ := hsf
  have hk5 : k = 5 := by omega
  subst hk5
  exact ⟨hl, hcs⟩

/-- (11) Slow loop, `readAll` threw (end of input): truncated. -/
theorem rv_g11 {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp e : Addr} {k : Nat}
    {fs : List (FieldKey × Value)}
    (hCP : CPAtH P R σ0 p t tmp) (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ t k)
    (hlen : (R.src σ t).length < (1#32 : I32).toNat)
    (he : σ'.heap e = some (.plain ttExcCls fs)) : rv32E P R [.ref p] σ0 e σ' := by
  apply rv_truncated hCP _ he
  unfold SlowFacts at hsf
  obtain ⟨-, hcs, hs, -⟩ := hsf
  have h1 : (1#32 : I32).toNat = 1 := rfl
  rw [h1, hs] at hlen
  exact truncated_of (by omega) hcs (List.eq_nil_of_length_eq_zero (by omega))

/-- (9) Slow loop, `readAll` read a continuation byte: the head with `k + 1`. -/
theorem rv_g9 {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {xs : List Value}
    {c1 c2 : ClassName} {f1 f2 : List (FieldKey × Value)}
    (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
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
    ∃ k', k' ≤ 5 ∧ BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 k' ∧
      BitVec.ofNat 32 (7 * k) + 7#32 = BitVec.ofNat 32 (7 * k') ∧
      BitVec.ofNat 32 (acc32 (R.src σ0 t) k) |||
          JInt.shl (BitVec.signExtend 32 ((R.src σ1 t)[0]'(by
            have : (1#32 : I32).toNat = 1 := rfl; omega)).toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
        BitVec.ofNat 32 (acc32 (R.src σ0 t) k') ∧
      SlowFacts R σ0 σ' t k' ∧ CPAtRH R σ' p t tmp ∧ c1 = c2 ∧
      (σ0.next ≤ σ'.next ∧
        ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ'.heap a = σ0.heap a) ∧
      ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ' t a := by
  obtain ⟨u, rest, hsrc1⟩ := src_cons_of_len (by decide) hlen1
  have hu0 := head_of_cons hsrc1 (by have : (1#32 : I32).toNat = 1 := rfl; omega)
  have hs'' : R.src σ1 t = u :: R.src σ' t := by rw [hsrc', hsrc1]; rfl
  rw [hu0] at hhigh ⊢
  obtain ⟨hacc, hsf'⟩ := slow_cont hk5 hsf hs'' hsink' ((highbit_iff u).mp hhigh)
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
theorem rv_g10 {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {xs : List Value}
    {c : ClassName} {f0 w : List (FieldKey × Value)}
    (hCP0 : CPAtH P R σ0 p t tmp)
    (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
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
    rv32N P R [.ref p] σ0 (some (.int (BitVec.ofNat 32 (acc32 (R.src σ0 t) k) |||
      JInt.shl (BitVec.signExtend 32 ((R.src σ1 t)[0]'(by
        have : (1#32 : I32).toNat = 1 := rfl; omega)).toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k))))) σ' := by
  obtain ⟨u, rest, hsrc1⟩ := src_cons_of_len (by decide) hlen1
  have hu0 := head_of_cons hsrc1 (by have : (1#32 : I32).toNat = 1 := rfl; omega)
  have hs'' : R.src σ1 t = u :: R.src σ' t := by rw [hsrc', hsrc1]; rfl
  rw [hu0] at hlow ⊢
  have hu128 : u.toNat < 128 := by
    have := mt (highbit_iff u).mpr hlow
    omega
  obtain ⟨hrd, hacc, hsk⟩ := slow_ret hk5 hsf hs'' hsink' hu128
  have hR1' := CPAtRH.elim hR1
  obtain ⟨-, xs1, -, -, -, htm1, hl1, -⟩ := hR1'
  rw [htm1] at htmp1
  simp only [Option.some.injEq, Obj.array.injEq, true_and] at htmp1
  subst htmp1
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_readAll (CPAtRH.elim hR1) hinv' htmp'
    (readAll1_length xs1 _ hl1 hlen1) hfr' hown'
  exact rv_normal hCP0 hrd (by rw [hacc]) rfl hsk (cpAt_of_R hCP0 hc0 hR' hct')
    ⟨Nat.le_trans hn1 hn', hin', hst', fun a ha hat hatm hao => by
      rw [hfr' a (Nat.lt_of_lt_of_le ha hn1) hat (hown1 a ha hao) hatm, hfr1 a ha hat hatm hao]⟩
    (fun a ha h => hown' a (Nat.lt_of_lt_of_le ha hn1) (hown1 a ha h))

/-- (12) Slow loop, the buffer gave a continuation byte: the head with `k + 1`. -/
theorem rv_g12 {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {u : UInt8}
    {c1 c2 : ClassName} {f1 f2 : List (FieldKey × Value)}
    (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
    (hfr1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hown1 : ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a)
    (hhigh : JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hinv' : R.inv σ' t) (hsink' : R.sink σ' t = R.sink σ1 t)
    (hfr' : ∀ a, ¬a = t → σ'.heap a = σ1.heap a) (hown' : ∀ a, R.owns σ' t a ↔ R.owns σ1 t a)
    (hs'' : R.src σ1 t = u :: R.src σ' t)
    (hc1 : σ0.heap t = some (.plain c1 f1)) (hc2 : σ0.heap t = some (.plain c2 f2)) :
    ∃ k', k' ≤ 5 ∧ BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 k' ∧
      BitVec.ofNat 32 (7 * k) + 7#32 = BitVec.ofNat 32 (7 * k') ∧
      BitVec.ofNat 32 (acc32 (R.src σ0 t) k) |||
          JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k)) =
        BitVec.ofNat 32 (acc32 (R.src σ0 t) k') ∧
      SlowFacts R σ0 σ' t k' ∧ CPAtRH R σ' p t tmp ∧ c1 = c2 ∧
      (∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ'.heap a = σ0.heap a) ∧
      ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a := by
  obtain ⟨hacc, hsf'⟩ := slow_cont hk5 hsf hs'' hsink' ((highbit_iff u).mp hhigh)
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_consume (CPAtRH.elim hR1) hinv' hfr' hown'
  refine ⟨k + 1, by omega, ofNat_succ32 k, ofNat_add7 k, hacc, hsf', CPAtRH.intro hR', ?_, ?_, hown1⟩
  · rw [hc1] at hc2
    simp only [Option.some.injEq, Obj.plain.injEq] at hc2
    exact hc2.1
  · intro a ha hat hatm hao
    rw [hfr' a hat, hfr1 a ha hat hatm hao]

/-- (13) Slow loop, the buffer gave the last byte: the value and the rest. -/
theorem rv_g13 {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr} {k : Nat} {u : UInt8}
    {c : ClassName} {f0 w : List (FieldKey × Value)}
    (hCP0 : CPAtH P R σ0 p t tmp)
    (hk5 : ¬ 5 ≤ (k : Int)) (hsf : SlowFacts R σ0 σ1 t k) (hR1 : CPAtRH R σ1 p t tmp)
    (hfr1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hn1 : σ0.next ≤ σ1.next)
    (hinv' : R.inv σ' t) (hsink' : R.sink σ' t = R.sink σ1 t)
    (hn' : σ'.next = σ1.next) (hin' : σ'.inits = σ0.inits) (hst' : σ'.statics = σ0.statics)
    (hfr' : ∀ a, ¬a = t → σ'.heap a = σ1.heap a) (hown' : ∀ a, R.owns σ' t a ↔ R.owns σ1 t a)
    (hct' : σ'.heap t = some (.plain c w)) (hs'' : R.src σ1 t = u :: R.src σ' t)
    (hc0 : σ0.heap t = some (.plain c f0))
    (hlow : ¬JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 128#32 = 128#32)
    (hown1 : ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ1 t a) :
    rv32N P R [.ref p] σ0 (some (.int (BitVec.ofNat 32 (acc32 (R.src σ0 t) k) |||
      JInt.shl (BitVec.signExtend 32 u.toBitVec &&& 127#32) (BitVec.ofNat 32 (7 * k))))) σ' := by
  have hu128 : u.toNat < 128 := by
    have := mt (highbit_iff u).mpr hlow
    omega
  obtain ⟨hrd, hacc, hsk⟩ := slow_ret hk5 hsf hs'' hsink' hu128
  have hR' : CPAtR R σ' p t tmp := cpAtR_after_consume (CPAtRH.elim hR1) hinv' hfr' hown'
  exact rv_normal hCP0 hrd (by rw [hacc]) rfl hsk (cpAt_of_R hCP0 hc0 hR' hct')
    ⟨by rw [hn']; exact hn1, hin', hst', fun a ha hat hatm hao => by rw [hfr' a hat, hfr1 a ha hat hatm hao]⟩
    (fun a ha h => by rw [hown']; exact hown1 a ha h)

end EquivLean.Demo.Thrift.Java
