import EquivLean.Demo.Thrift.Java.Rv32
import EquivLean.Demo.Thrift.Java.Wv32

/-!
# Thrift → Java (T4): compact varint32, the results (E, D, M)

In every program that contains the protocol classes and whose transport classes satisfy the
transport contracts (`Valid P (tContracts R).env`):
- (E) `writeVarint32(x)` appends `varint (toU 32 x)` to the transport and returns normally;
- (D) `readVarint32()` on a source `varint (toU 32 x) ++ rest` returns `x` and leaves `rest`;
- (M) on more than 5 continuation bytes it throws a `TProtocolException`; on an input that ends
  inside the varint, the transport's `TTransportException`; a varint of at most 5 bytes whose value
  is `2^32` or more is accepted and returned mod `2^32`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem toU32_toInt (x : I32) : Spec.toU 32 x.toInt = x.toNat := by
  have hx := x.isLt
  have hc := BitVec.toInt_eq_toNat_cond x
  have key : ((Spec.toU 32 x.toInt : Nat) : Int) = (x.toNat : Int) := by
    by_cases h : 2 * x.toNat < 2 ^ 32
    · rw [if_pos h] at hc
      rw [Spec.toU_of_nonneg (by rw [hc]; omega) (by rw [hc]; simp; omega), hc]
    · rw [if_neg h] at hc
      rw [Spec.toU_of_neg (by rw [hc]; simp at h ⊢; omega) (by rw [hc]; simp; omega), hc]
      simp
  exact_mod_cast key

theorem classOK_of_cpAt {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    (h : CPAt P R σ p t tmp) : ClassOK P σ t := by
  obtain ⟨-, -, c, fst, -, -, -, -, -, ht, hc, -⟩ := h
  unfold Program.isProgClass at hc
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨c, fst, d, ht, hd⟩

/-! ## varint32 read -/

/-- **The contract of `readVarint32()`.** -/
def rv32Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp ∧ σ.initOf tpeCls = .done)
  (rv32N P R) (rv32E P R)

theorem rv32_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) : Sat P rv32Ref (rv32Spec P R) := by
  have hI := BodyVCP.sat (rv32_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hCP, hin⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hin⟩ hm

/-- **D for varint32.** -/
theorem rv32_D {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (x : I32) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.varint (Spec.toU 32 x.toInt) ++ rest) {o : Outcome}
    (hm : MExec P rv32Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.int x)) σ' ∧ R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧
      CPAt P R σ' p t tmp := by
  have hpost := rv32_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  rw [toU32_toInt] at hsrc
  have hrd : Spec.readVarint 5 (R.src σ t) = some (x.toNat, rest) := by
    rw [hsrc]; exact Spec.readVarint_varint 5 _ rest (Spec.varint_length_le5 x.isLt)
  cases o with
  | normal r σ' =>
    have h := hpost
    simp only [rv32Spec, Spec.of] at h
    unfold rv32N at h
    obtain ⟨v, rest', hv, hr, hs, hk, hC, -⟩ := h p t tmp rfl hCP
    rw [hrd] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨σ', ?_, hs, hk, hC⟩
    rw [hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | exc e σ' =>
    have h := hpost
    simp only [rv32Spec, Spec.of] at h
    unfold rv32E at h
    have hnone : Spec.readVarint 5 (R.src σ t) = none := by
      rw [Spec.readVarint_eq_none_iff]
      rcases h p t tmp rfl hCP with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    rw [hrd] at hnone
    cases hnone
  | wrong msg =>
    simp only [rv32Spec, Spec.of] at hpost

/-- **M for varint32**: more than 5 continuation bytes throw a `TProtocolException`. -/
theorem rv32_M_overlong {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (hov : Spec.VarintOverlong 5 (R.src σ t)) {o : Outcome}
    (hm : MExec P rv32Ref [.ref p] σ o) :
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  have hpost := rv32_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  have hnone : Spec.readVarint 5 (R.src σ t) = none :=
    (Spec.readVarint_eq_none_iff 5 _).mpr (Or.inl hov)
  cases o with
  | normal r σ' =>
    simp only [rv32Spec, Spec.of] at hpost
    unfold rv32N at hpost
    obtain ⟨v, rest', hv, -⟩ := hpost p t tmp rfl hCP
    rw [hnone] at hv
    cases hv
  | exc e σ' =>
    simp only [rv32Spec, Spec.of] at hpost
    unfold rv32E at hpost
    rcases hpost p t tmp rfl hCP with ⟨-, fs, hfs⟩ | ⟨htr, -⟩
    · exact ⟨e, σ', fs, rfl, hfs⟩
    · exact absurd hov.1 (by have := htr.1; omega)
  | wrong msg =>
    simp only [rv32Spec, Spec.of] at hpost

/-- **M for varint32**: an input that ends inside the varint throws the transport's
`TTransportException`. -/
theorem rv32_M_truncated {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (htr : Spec.VarintTruncated 5 (R.src σ t)) {o : Outcome}
    (hm : MExec P rv32Ref [.ref p] σ o) :
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain ttExcCls fs) := by
  have hpost := rv32_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  have hnone : Spec.readVarint 5 (R.src σ t) = none :=
    (Spec.readVarint_eq_none_iff 5 _).mpr (Or.inr htr)
  cases o with
  | normal r σ' =>
    simp only [rv32Spec, Spec.of] at hpost
    unfold rv32N at hpost
    obtain ⟨v, rest', hv, -⟩ := hpost p t tmp rfl hCP
    rw [hnone] at hv
    cases hv
  | exc e σ' =>
    simp only [rv32Spec, Spec.of] at hpost
    unfold rv32E at hpost
    rcases hpost p t tmp rfl hCP with ⟨hov, -⟩ | ⟨-, fs, hfs⟩
    · exact absurd hov.1 (by have := htr.1; omega)
    · exact ⟨e, σ', fs, rfl, hfs⟩
  | wrong msg =>
    simp only [rv32Spec, Spec.of] at hpost

/-- **M for varint32**: a varint of at most 5 bytes whose value `v` is `2^32` or more (the spec's
`VarintExceeds 5 (2^32)`) is accepted: `readVarint32()` returns `v mod 2^32` and consumes it. -/
theorem rv32_M_exceeds {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) {v : Nat} {rest : Spec.Bytes}
    (hrd : Spec.readVarint 5 (R.src σ t) = some (v, rest)) {o : Outcome}
    (hm : MExec P rv32Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.int (BitVec.ofNat 32 v))) σ' ∧ R.src σ' t = rest := by
  have hpost := rv32_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  cases o with
  | normal r σ' =>
    simp only [rv32Spec, Spec.of] at hpost
    unfold rv32N at hpost
    obtain ⟨v', rest', hv, hr, hs, -⟩ := hpost p t tmp rfl hCP
    rw [hrd] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨σ', by rw [hr], hs⟩
  | exc e σ' =>
    simp only [rv32Spec, Spec.of] at hpost
    unfold rv32E at hpost
    have hnone : Spec.readVarint 5 (R.src σ t) = none := by
      rw [Spec.readVarint_eq_none_iff]
      rcases hpost p t tmp rfl hCP with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    rw [hrd] at hnone
    cases hnone
  | wrong msg =>
    simp only [rv32Spec, Spec.of] at hpost

/-- The byte sequence of the `VarintExceeds` case: `80 80 80 80 10` (value `2^32`) is read as `0`. -/
theorem rv32_exceeds_example :
    Spec.readVarint 5 [0x80, 0x80, 0x80, 0x80, 0x10] = some (2 ^ 32, []) ∧
      Spec.readVarint32 [0x80, 0x80, 0x80, 0x80, 0x10] = none ∧
      BitVec.ofNat 32 (2 ^ 32) = 0#32 := by
  decide

/-- A varint read from a prefix is read the same way when more bytes follow. -/
theorem readVarint_append : ∀ (k : Nat) (bs rest : Spec.Bytes) (v : Nat) (r : Spec.Bytes),
    Spec.readVarint k bs = some (v, r) → Spec.readVarint k (bs ++ rest) = some (v, r ++ rest)
  | 0, _, _, _, _, h => by simp [Spec.readVarint] at h
  | k + 1, [], _, _, _, h => by simp [Spec.readVarint] at h
  | k + 1, b :: bs, rest, v, r, h => by
    simp only [Spec.readVarint, List.cons_append] at h ⊢
    by_cases hb : b.toNat < 128
    · rw [if_pos hb] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb] at h ⊢
      cases h' : Spec.readVarint k bs with
      | none => rw [h'] at h; cases h
      | some q =>
        rw [h'] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [readVarint_append k bs rest q.1 q.2 (by rw [h'])]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩

/-- **M on the named input `exVarint32Exceeds`** (`85 80 80 80 10`, value `2^32 + 5`, which the spec
rejects): Java's `readVarint32()` returns `5` and consumes the 5 bytes. -/
theorem rv32_exVarint32Exceeds {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.exVarint32Exceeds ++ rest) {o : Outcome}
    (hm : MExec P rv32Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.int 5#32)) σ' ∧ R.src σ' t = rest := by
  have hrd : Spec.readVarint 5 (R.src σ t) = some (2 ^ 32 + 5, rest) := by
    rw [hsrc]
    simpa using readVarint_append 5 _ rest _ _ Spec.readVarint_exVarint32Exceeds
  have h5 : BitVec.ofNat 32 (2 ^ 32 + 5) = 5#32 := by
    apply BitVec.eq_of_toNat_eq
    simp
  obtain ⟨σ', ho, hs⟩ := rv32_M_exceeds hF hV hCP hin hrd hm
  exact ⟨σ', by rw [ho, h5], hs⟩

/-- **M on the named input `exVarint32Overlong`** (`80 80 80 80 80`): Java's `readVarint32()` throws a
`TProtocolException`, whatever follows (on the buffer fast path and on the `readByte()` path). -/
theorem rv32_exVarint32Overlong {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.exVarint32Overlong ++ rest) {o : Outcome}
    (hm : MExec P rv32Ref [.ref p] σ o) :
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  apply rv32_M_overlong hF hV hCP hin _ hm
  rw [hsrc]
  refine ⟨by simp [Spec.exVarint32Overlong], ?_⟩
  intro b hb
  simp only [Spec.exVarint32Overlong, List.cons_append, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## varint32 write -/

/-- **The contract of `writeVarint32(n)`.** -/
def wv32SpecP (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ CPAt P R σ p t tmp)
  (wv32N P R)
  (fun _ _ _ _ => False)

theorem wv32_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P wv32Ref (wv32SpecP P R) := by
  have hI := BodyVCP.sat (wv32_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, n, hargs, hCP, CPAtH.intro hCP⟩ hm

/-- **E for varint32.** -/
theorem wv32_E {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (x : I32) {o : Outcome} (hm : MExec P wv32Ref [.ref p, .int x] σ o) :
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.varint (Spec.toU 32 x.toInt) ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp := by
  have hpost := wv32_sat R hF hV [.ref p, .int x] σ o ⟨p, t, tmp, x, rfl, hCP⟩ hm
  rw [toU32_toInt]
  cases o with
  | normal r σ' =>
    simp only [wv32SpecP, Spec.of] at hpost
    unfold wv32N at hpost
    obtain ⟨hr, hC, hs, hsrc, -⟩ := hpost p t tmp x rfl hCP
    exact ⟨σ', by rw [hr], hs, hsrc, hC⟩
  | exc e σ' => simp only [wv32SpecP, Spec.of] at hpost
  | wrong msg => simp only [wv32SpecP, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
