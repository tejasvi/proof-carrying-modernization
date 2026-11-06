import EquivLean.Demo.Thrift.Java.Rsb

/-!
# Thrift → Java (T4): the compact set header reader `readSetBegin()` (D, M)

`readSetBegin()` is `new TSet(readListBegin())`: under `NoRedeclS` (`NoRedeclL` and no application
subclass of `TCompactProtocol` redeclares `readListBegin()`) it returns a `TSet` with the element
type and size `readListBegin()` reads, and throws what `readListBegin()` throws.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rlbA_sat (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) : Sat P rlbRef (rlbSpecA P R) := by
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, lim, hargs, hCP, hlim, h1, h2, h3, hnib⟩ := hpre
  exact rlb_sat R hF hV hn args σ o ⟨p, t, tmp, lim, hargs, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, hnib⟩ hm

/-- No application subclass of `TCompactProtocol` redeclares `readListBegin()` or the methods it
calls. -/
def NoRedeclS (P : Program) : Prop := NoRedeclL P ∧ NoRedecl P rlbSig rlbRef

theorem valid_Γ7 (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) : Valid P (Γ7 P R) := by
  obtain ⟨hnl, hnr⟩ := hn
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ7 at hS
  by_cases h1 : sig = rlbSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (rlbA_sat R (contains_sub hF (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
        rcases hd with h | h | h | h | h | h | h | h | h <;> simp [h])) hV hnl) hnr
  · rw [if_neg h1] at hS
    exact hV sig S hS

theorem rsb_sat (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) : Sat P rsbRef (rsbSpecI P R) :=
  MethodVC.sat_of_valid (valid_Γ7 R hF hV hn) (rsb_body R P hF)

/-- **D for the set header**: on `Spec.listHeader size ety ++ rest` (as in `rlb_D`),
`readSetBegin()` returns a new `TSet` with element type `tt` and size `size`, and leaves `rest`. -/
theorem rsb_D (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) {σ : State} {p t tmp : Addr} {lim : I64}
    {size ety tt : Nat} {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size))
    (htt : Spec.ttypeOfCompact ety = some tt) (hms : (minSize tt).isSome = true)
    (hsrc : R.src σ t = Spec.listHeader size ety ++ rest) (hm : MExec P rsbRef [.ref p] σ o) :
    ∃ σ' s sfs, o = .normal (some (.ref s)) σ' ∧ σ'.heap s = some (.plain tsCls sfs) ∧
      Fields.get sfs (tsCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get sfs (tsCls, "size") = some (.int (BitVec.ofNat 32 size)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp := by
  have he : ety < 16 := Nat.lt_trans (ttypeOfCompact_dom _ _ htt) (by decide)
  obtain ⟨u, rest0, hcons, hmod, hsz⟩ := listHeader_cons hs he rest
  rw [hcons] at hsrc
  have hnibL : NibbleOKL (R.src σ t) := by
    intro u' rest' h
    rw [hsrc] at h
    injection h with e1 e2
    subst e1
    rw [hmod, htt]
    rfl
  have hpost := rsb_sat R hF hV hn [.ref p] σ o
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, h4, hnibL⟩ hm
  obtain ⟨fs, -, -, -, hp, htr, hte, -⟩ := hCP
  obtain ⟨fs', hp', hl⟩ := hlim
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  cases o with
  | normal r σ' =>
    simp only [rsbSpecI, Spec.of] at hpost
    unfold rsbN at hpost
    obtain ⟨u', rest', size', rest'', tt', k, s, sfs, hs1, hsz1, -, -, htt', -, hsr, hsk, hC, hr, hsh,
      hft, hfs⟩ := hpost p t tmp fs lim rfl hp htr hte hl
    rw [hsrc] at hs1
    injection hs1 with e1 e2
    subst e1 e2
    rw [hsz] at hsz1
    simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
    obtain ⟨rfl, e3⟩ := hsz1
    rw [hmod, htt] at htt'
    cases htt'
    exact ⟨σ', s, sfs, by rw [hr], hsh, hft, hfs, by rw [hsr, e3], hsk, hC⟩
  | exc e σ' =>
    simp only [rsbSpecI, Spec.of] at hpost
    unfold rlbE at hpost
    rcases hpost p t tmp fs lim rfl hp htr hte hl with ⟨h0, -⟩ | ⟨u', rest', hs1, hnone, -⟩ |
      ⟨u', rest', size', rest'', hs1, hsz1, hc, -⟩ | ⟨u', rest', size', rest'', tt', hs1, hsz1, -, -, htt',
        hms', -⟩
    · rw [hsrc] at h0
      cases h0
    · rw [hsrc] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hnone
      cases hnone
    · rw [hsrc] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hsz1
      simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
      obtain ⟨rfl, -⟩ := hsz1
      rcases hc with hc | hc
      · exact absurd hc (Int.not_lt.mpr (toInt_ofNat_nonneg hs))
      · exact absurd hin hc
    · rw [hsrc] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hmod, htt] at htt'
      cases htt'
      rw [hms'] at hms
      cases hms
  | wrong msg => simp only [rsbSpecI, Spec.of] at hpost

/-- **`exNegSize` for the set header**: `readSetBegin()` throws a `TProtocolException`. -/
theorem rsb_exNegSize (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) {σ : State} {p t tmp : Addr} {lim : I64}
    {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hsrc : R.src σ t = Spec.exNegSize ++ rest) (hm : MExec P rsbRef [.ref p] σ o) :
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  have hrv : Spec.readVarint 5 ([0x80, 0x80, 0x80, 0x80, 0x08] ++ rest) = some (2 ^ 31, rest) := by
    have h := Spec.readVarint_varint 5 (2 ^ 31) rest (by decide)
    rwa [show Spec.varint (2 ^ 31) = [0x80, 0x80, 0x80, 0x80, 0x08] by decide] at h
  have hsz := listSizeJ_long (u := 0xF5) (by decide) hrv
  have hsrc' : R.src σ t = 0xF5 :: ([0x80, 0x80, 0x80, 0x80, 0x08] ++ rest) := hsrc
  have hnibL : NibbleOKL (R.src σ t) := by
    intro u' rest' h
    rw [hsrc'] at h
    injection h with e1 e2
    subst e1
    decide
  have hpost := rsb_sat R hF hV hn [.ref p] σ o
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, h4, hnibL⟩ hm
  obtain ⟨fs, -, -, -, hp, htr, hte, -⟩ := hCP
  obtain ⟨fs', hp', hl⟩ := hlim
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  cases o with
  | normal r σ' =>
    simp only [rsbSpecI, Spec.of] at hpost
    unfold rsbN at hpost
    obtain ⟨u', rest', size', rest'', -, -, -, -, hs1, hsz1, h0, -⟩ := hpost p t tmp fs lim rfl hp htr hte hl
    rw [hsrc'] at hs1
    injection hs1 with e1 e2
    subst e1 e2
    rw [hsz] at hsz1
    simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
    obtain ⟨rfl, -⟩ := hsz1
    exact absurd h0 (by decide)
  | exc e σ' =>
    simp only [rsbSpecI, Spec.of] at hpost
    unfold rlbE at hpost
    rcases hpost p t tmp fs lim rfl hp htr hte hl with ⟨h0, -⟩ | ⟨u', rest', hs1, hnone, -⟩ |
      ⟨u', rest', size', rest'', hs1, hsz1, -, w, hw⟩ | ⟨u', rest', size', rest'', tt', hs1, hsz1, h0, -⟩
    · rw [hsrc'] at h0
      cases h0
    · rw [hsrc'] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hnone
      cases hnone
    · exact ⟨e, σ', w, rfl, hw⟩
    · rw [hsrc'] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hsz1
      simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
      obtain ⟨rfl, -⟩ := hsz1
      exact absurd h0 (by decide)
  | wrong msg => simp only [rsbSpecI, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
