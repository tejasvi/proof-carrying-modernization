import EquivLean.Demo.Thrift.Java.FhR

/-!
# Thrift → Java (T4): the compact field header reader `readFieldBegin()` (D, M)

Under the transport contracts and `NoRedeclR` (no application subclass of `TCompactProtocol`
redeclares `readByte`, `getTType`, `readFieldId`, `readVarint32`, `writeVarint32`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The delta nibble of a header byte, as Java computes it. -/
theorem modJ_sx_fin : ∀ n : Fin 256,
    modJ (BitVec.signExtend 32 (UInt8.ofNat n).toBitVec) = BitVec.ofNat 32 ((UInt8.ofNat n).toNat / 16) := by
  decide +kernel

theorem modJ_sx (u : UInt8) : modJ (BitVec.signExtend 32 u.toBitVec) = BitVec.ofNat 32 (u.toNat / 16) := by
  have h := modJ_sx_fin ⟨u.toNat, u.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

/-- The contract of `readFieldBegin()` with the plain precondition. -/
def rfbSpec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (last : I32), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     LastAt σ p last ∧ BoolAt σ p ∧ σ.initOf tpeCls = .done ∧ σ.initOf cpCls = .done ∧
     σ.initOf tfCls = .done ∧ NibbleOK (R.src σ t))
  (rfbN P R) (rfbE P R)

theorem rfb_sat' (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) : Sat P rfbRef (rfbSpec P R) := by
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, last, hargs, hCP, hL, hB, h1, h2, h3, hnib⟩ := hpre
  exact rfb_sat R hF hV hn args σ o ⟨p, t, tmp, last, hargs, hCP, CPAtH.intro hCP, hL, hB, h1, h2, h3, hnib⟩ hm

/-- **What `readFieldBegin()` does on a header byte `u ≠ 0` with a known type nibble**: it returns
a new `TField` (the TType of the nibble, the id `readFieldId` computes) or throws when the
long-form id is not a varint of at most 5 bytes. -/
theorem rfb_run (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {last : I32}
    {u : UInt8} {rest0 : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hu : u.toNat ≠ 0)
    (htt : (Spec.ttypeOfCompact (u.toNat % 16)).isSome)
    (hm : MExec P rfbRef [.ref p] σ o) :
    (∃ tt id rest' σ' r0 ffs, Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧
      fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest0 = some (id, rest') ∧
      o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get ffs (tfCls, "id") = some (.int id) ∧ R.src σ' t = rest' ∧
      R.sink σ' t = R.sink σ t ∧ LastAt σ' p id ∧ CPAt P R σ' p t tmp ∧ RFrame R σ σ' p t tmp) ∨
    (∃ e σ', o = .exc e σ' ∧ fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest0 = none ∧
      ((Spec.VarintOverlong 5 rest0 ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
       (Spec.VarintTruncated 5 rest0 ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)))) := by
  have hnib : NibbleOK (R.src σ t) := by
    intro u' r' h hu'
    rw [hsrc] at h
    simp only [List.cons.injEq] at h
    rw [← h.1]
    exact htt
  have hpost := rfb_sat' R hF hV hn [.ref p] σ o ⟨p, t, tmp, last, rfl, hCP, ⟨fs, hp, hlast⟩, hB, h1, h2, h3, hnib⟩ hm
  obtain ⟨_, _, _, _, hp', htr, hte, _⟩ := hCP
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  cases o with
  | normal r σ' =>
    simp only [rfbSpec, Spec.of] at hpost
    unfold rfbN at hpost
    obtain ⟨u', rest, hs, hk, hC, hRF, hcase⟩ := hpost p t tmp _ last rfl hp htr hte hlast
    rw [hsrc] at hs
    simp only [List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rcases hcase with ⟨h0, -⟩ | ⟨-, tt, id, rest', r0, ffs, htt', hf, hs', hr, hr0, hty, hid, hL'⟩
    · exact absurd h0 hu
    · subst hr
      exact Or.inl ⟨tt, id, rest', σ', r0, ffs, htt', hf, rfl, hr0, hty, hid, hs', hk, hL', hC, hRF⟩
  | exc e σ' =>
    simp only [rfbSpec, Spec.of] at hpost
    unfold rfbE at hpost
    rcases hpost p t tmp _ last rfl hp htr hte hlast with ⟨h0, -⟩ | ⟨u', rest, hs, -, hf, hex⟩
    · rw [hsrc] at h0; cases h0
    · rw [hsrc] at hs
      simp only [List.cons.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact Or.inr ⟨e, σ', rfl, hf, hex⟩
  | wrong msg => simp only [rfbSpec, Spec.of] at hpost

/-- The byte 0 (STOP): `readFieldBegin()` returns the static `TSTOP` and consumes the byte. -/
theorem rfb_stop (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {last : I32}
    {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = Spec.fieldStop ++ rest)
    (hm : MExec P rfbRef [.ref p] σ o) :
    ∃ σ', o = .normal (some ((σ.static (cpCls, "TSTOP")).getD .null)) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ LastAt σ' p last ∧ CPAt P R σ' p t tmp := by
  have hnib : NibbleOK (R.src σ t) := by
    intro u' r' h hu'
    rw [hsrc] at h
    simp only [Spec.fieldStop, List.cons_append, List.nil_append, List.cons.injEq] at h
    rw [← h.1] at hu'
    exact absurd rfl hu'
  have hpost := rfb_sat' R hF hV hn [.ref p] σ o ⟨p, t, tmp, last, rfl, hCP, ⟨fs, hp, hlast⟩, hB, h1, h2, h3, hnib⟩ hm
  obtain ⟨_, _, _, _, hp', htr, hte, _⟩ := hCP
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  have hs0 : R.src σ t = 0 :: rest := by rw [hsrc]; rfl
  cases o with
  | normal r σ' =>
    simp only [rfbSpec, Spec.of] at hpost
    unfold rfbN at hpost
    obtain ⟨u', rest', hs, hk, hC, -, hcase⟩ := hpost p t tmp _ last rfl hp htr hte hlast
    rw [hs0] at hs
    simp only [List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rcases hcase with ⟨-, hr, hs', hL'⟩ | ⟨h0, -⟩
    · subst hr
      exact ⟨σ', rfl, hs', hk, hL', hC⟩
    · exact absurd rfl h0
  | exc e σ' =>
    simp only [rfbSpec, Spec.of] at hpost
    unfold rfbE at hpost
    rcases hpost p t tmp _ last rfl hp htr hte hlast with ⟨h0, -⟩ | ⟨u', rest', hs, hu', -⟩
    · rw [hs0] at h0; cases h0
    · rw [hs0] at hs
      simp only [List.cons.injEq] at hs
      rw [← hs.1] at hu'
      exact absurd rfl hu'
  | wrong msg => simp only [rfbSpec, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
