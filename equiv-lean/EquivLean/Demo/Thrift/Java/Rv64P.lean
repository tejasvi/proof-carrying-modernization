import EquivLean.Demo.Thrift.Java.Rv64
import EquivLean.Demo.Thrift.Java.Zz

/-!
# Thrift → Java (T4): compact varint64 read, the results (D, M)

In every program that contains the protocol classes and whose transport classes satisfy the
transport contracts (`Valid P (tContracts R).env`):
- (D) `readVarint64()` on a source `varint (toU 64 x) ++ rest` returns `x` and leaves `rest`;
- (M) on more than 10 continuation bytes it throws a `TProtocolException`; on an input that ends
  inside the varint, the transport's `TTransportException`; a varint of at most 10 bytes whose
  value is `2^64` or more is accepted and returned mod `2^64`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## varint64 read -/

/-- **The contract of `readVarint64()`.** -/
def rv64Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp ∧ σ.initOf tpeCls = .done)
  (rv64N P R) (rv64E P R)

theorem rv64_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) : Sat P rv64Ref (rv64Spec P R) := by
  have hI := BodyVCP.sat (rv64_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hCP, hin⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hin⟩ hm

/-- **D for varint64.** -/
theorem rv64_D {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (x : I64) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.varint (Spec.toU 64 x.toInt) ++ rest) {o : Outcome}
    (hm : MExec P rv64Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.long x)) σ' ∧ R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧
      CPAt P R σ' p t tmp := by
  have hpost := rv64_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  rw [toU64_toInt] at hsrc
  have hrd : Spec.readVarint 10 (R.src σ t) = some (x.toNat, rest) := by
    rw [hsrc]; exact Spec.readVarint_varint 10 _ rest (Spec.varint_length_le10 x.isLt)
  cases o with
  | normal r σ' =>
    have h := hpost
    simp only [rv64Spec, Spec.of] at h
    unfold rv64N at h
    obtain ⟨v, rest', hv, hr, hs, hk, hC, -⟩ := h p t tmp rfl hCP
    rw [hrd] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨σ', ?_, hs, hk, hC⟩
    rw [hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | exc e σ' =>
    have h := hpost
    simp only [rv64Spec, Spec.of] at h
    unfold rv64E at h
    have hnone : Spec.readVarint 10 (R.src σ t) = none := by
      rw [Spec.readVarint_eq_none_iff]
      rcases h p t tmp rfl hCP with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    rw [hrd] at hnone
    cases hnone
  | wrong msg =>
    simp only [rv64Spec, Spec.of] at hpost

/-- **M for varint64**: more than 10 continuation bytes throw a `TProtocolException`. -/
theorem rv64_M_overlong {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (hov : Spec.VarintOverlong 10 (R.src σ t)) {o : Outcome}
    (hm : MExec P rv64Ref [.ref p] σ o) :
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  have hpost := rv64_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  have hnone : Spec.readVarint 10 (R.src σ t) = none :=
    (Spec.readVarint_eq_none_iff 10 _).mpr (Or.inl hov)
  cases o with
  | normal r σ' =>
    simp only [rv64Spec, Spec.of] at hpost
    unfold rv64N at hpost
    obtain ⟨v, rest', hv, -⟩ := hpost p t tmp rfl hCP
    rw [hnone] at hv
    cases hv
  | exc e σ' =>
    simp only [rv64Spec, Spec.of] at hpost
    unfold rv64E at hpost
    rcases hpost p t tmp rfl hCP with ⟨-, fs, hfs⟩ | ⟨htr, -⟩
    · exact ⟨e, σ', fs, rfl, hfs⟩
    · exact absurd hov.1 (by have := htr.1; omega)
  | wrong msg =>
    simp only [rv64Spec, Spec.of] at hpost

/-- **M for varint64**: an input that ends inside the varint throws the transport's
`TTransportException`. -/
theorem rv64_M_truncated {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (htr : Spec.VarintTruncated 10 (R.src σ t)) {o : Outcome}
    (hm : MExec P rv64Ref [.ref p] σ o) :
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain ttExcCls fs) := by
  have hpost := rv64_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  have hnone : Spec.readVarint 10 (R.src σ t) = none :=
    (Spec.readVarint_eq_none_iff 10 _).mpr (Or.inr htr)
  cases o with
  | normal r σ' =>
    simp only [rv64Spec, Spec.of] at hpost
    unfold rv64N at hpost
    obtain ⟨v, rest', hv, -⟩ := hpost p t tmp rfl hCP
    rw [hnone] at hv
    cases hv
  | exc e σ' =>
    simp only [rv64Spec, Spec.of] at hpost
    unfold rv64E at hpost
    rcases hpost p t tmp rfl hCP with ⟨hov, -⟩ | ⟨-, fs, hfs⟩
    · exact absurd hov.1 (by have := htr.1; omega)
    · exact ⟨e, σ', fs, rfl, hfs⟩
  | wrong msg =>
    simp only [rv64Spec, Spec.of] at hpost

/-- **M for varint64**: a varint of at most 10 bytes whose value `v` is `2^64` or more (the spec's
`VarintExceeds 10 (2^64)`) is accepted: `readVarint64()` returns `v mod 2^32` and consumes it. -/
theorem rv64_M_exceeds {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) {v : Nat} {rest : Spec.Bytes}
    (hrd : Spec.readVarint 10 (R.src σ t) = some (v, rest)) {o : Outcome}
    (hm : MExec P rv64Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.long (BitVec.ofNat 64 v))) σ' ∧ R.src σ' t = rest := by
  have hpost := rv64_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hCP, hin⟩ hm
  cases o with
  | normal r σ' =>
    simp only [rv64Spec, Spec.of] at hpost
    unfold rv64N at hpost
    obtain ⟨v', rest', hv, hr, hs, -⟩ := hpost p t tmp rfl hCP
    rw [hrd] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨σ', by rw [hr], hs⟩
  | exc e σ' =>
    simp only [rv64Spec, Spec.of] at hpost
    unfold rv64E at hpost
    have hnone : Spec.readVarint 10 (R.src σ t) = none := by
      rw [Spec.readVarint_eq_none_iff]
      rcases hpost p t tmp rfl hCP with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    rw [hrd] at hnone
    cases hnone
  | wrong msg =>
    simp only [rv64Spec, Spec.of] at hpost

/-- **M on the named input `exVarint64Exceeds`** (`80 80 80 80 80 80 80 80 80 02`, value `2^64`,
which the spec rejects): Java's `readVarint64()` returns `0` and consumes the 10 bytes. -/
theorem rv64_exVarint64Exceeds {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.exVarint64Exceeds ++ rest) {o : Outcome}
    (hm : MExec P rv64Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.long 0#64)) σ' ∧ R.src σ' t = rest := by
  have hrd : Spec.readVarint 10 (R.src σ t) = some (2 ^ 64, rest) := by
    rw [hsrc]
    simpa using readVarint_append 10 _ rest _ _ Spec.readVarint_exVarint64Exceeds
  have h5 : BitVec.ofNat 64 (2 ^ 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp
  obtain ⟨σ', ho, hs⟩ := rv64_M_exceeds hF hV hCP hin hrd hm
  exact ⟨σ', by rw [ho, h5], hs⟩

end EquivLean.Demo.Thrift.Java
