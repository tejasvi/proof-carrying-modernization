-- Termination package by JimpleLean's session: TermT4/RlbAllP.lean (sha256 be3020babcc2ce88...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RlbAllT
import EquivLean.Demo.Thrift.Java.Term.RlbTotal

/-!
# Thrift → Java (T4): `readListBegin()` on every header byte, linked, total; the nibbles 14 and 15

`Γ6All`'s contracts are valid (`getTType`'s by `gttAll_sat`) and terminate (`gttAll_term`), so
`readListBegin()` satisfies `rlbSpecAll` and is totally correct on it, with the premises of `rlb_total`
(`TransportTerm`, `TRepConc`). The named case: a list header whose size is valid and whose element nibble is
14 or 15 makes every run throw a `TProtocolException` (`rlb_nib1415_total`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem mem8_of_mem9L' {d : ClassDecl} (hd : d ∈ [cpC, tpC, ttC]) :
    d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h <;> simp [h]

/-- The contracts `readListBegin()` uses on every header byte are valid. -/
theorem valid_Γ6All (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) : Valid P (Γ6All P R) := by
  obtain ⟨hnb, hng, hnc, hnk, hn1, hn2⟩ := hn
  have hF7 : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC] := contains_sub hF (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h | h | h | h | h <;> simp [h])
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  have hV2 := valid_Γ2 R hF7 hV hn1 hn2
  intro sig S hS
  unfold Γ6All at hS
  by_cases h1 : sig = rbSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (rbA_sat R (contains_sub hF (fun d hd => mem8_of_mem9L' hd)) hV) hnb
  · rw [if_neg h1] at hS
    by_cases h2 : sig = gttSig
    · rw [if_pos h2] at hS
      cases hS
      subst h2
      exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
        (gttAll_sat (contains_sub hF (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
          rcases hd with h | h | h <;> simp [h]))) hng
    · rw [if_neg h2] at hS
      by_cases h3 : sig = ccrlSig
      · rw [if_pos h3] at hS
        cases hS
        subst h3
        exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
          (ccrl_sat (contains_sub hF (by
            intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
            rcases hd with h | h | h <;> simp [h]))) hnc
      · rw [if_neg h3] at hS
        by_cases h4 : sig = crbaSig
        · rw [if_pos h4] at hS
          cases hS
          subst h4
          exact contractOK_tp hcp htp hO rfl rfl rfl rfl (by decide)
            (crbaA_sat R (contains_sub hF (by
              intro d hd
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
              rcases hd with h | h | h | h | h | h | h | h <;> simp [h])) hV) hnk
        · rw [if_neg h4] at hS
          exact hV2 sig S hS

/-- `readListBegin()` satisfies its contract on every header byte. -/
theorem rlbAll_sat (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) : Sat P rlbRef (rlbSpecAll P R) :=
  MethodVC.sat_of_valid (valid_Γ6All R hF hV hn) (rlbAll_body R P (contains_sub hF mem8_of_mem9L))

/-- The contracts of `Γ6All` terminate. -/
theorem Γ6All_term (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ6All P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  intro sig S hS
  by_cases e2 : sig = gttSig
  · unfold Γ6All at hS
    rw [if_neg (by rw [e2]; decide), if_pos e2] at hS
    cases hS
    subst e2
    obtain ⟨-, hng, -⟩ := hn
    have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
    have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
    have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => gttAll_term (contains_sub hF (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
        rcases hd with h | h | h <;> simp [h])) args σ hp.1) hng
  · -- every other signature has the contract of `Γ6`
    have h6 : Γ6 P R sig = some S := by
      unfold Γ6All at hS
      unfold Γ6
      rw [if_neg e2] at hS
      rw [if_neg e2]
      exact hS
    exact Γ6_term R hF hV hn hT hR sig S h6

theorem rlbAll_termI (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rlbSpecAll P R).pre args σ → MTerm P rlbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ6All R hF hV hn))
    (SpecEnv.strengthen_term (Γ6All_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (rlbAll_body R P (contains_sub hF mem8_of_mem9L)) (rlbAll_thin R P (contains_sub hF mem8_of_mem9L)))

/-- **`readListBegin()` on every header byte, total correctness.** -/
theorem rlbAll_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rlbSpecAll P R).pre args σ →
      (∃ o, MExec P rlbRef args σ o) ∧ ∀ o, MExec P rlbRef args σ o → (rlbSpecAll P R).post args σ o :=
  fun args σ hpre => ⟨(rlbAll_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => rlbAll_sat R hF hV hn args σ o hpre ho⟩

/-- **A list header with a valid size and element nibble 14 or 15, total**: `readListBegin()`
    terminates, and every run throws a `TProtocolException` (`getTType` has no TType for the nibble). -/
theorem rlb_nib1415_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {u : UInt8} {rest0 rest : Bytes} {size : I32}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hsz : listSizeJ u rest0 = some (size, rest))
    (h0 : 0 ≤ size.toInt) (hin : InLimit lim size) (hnib : 14 ≤ u.toNat % 16) :
    (∃ o, MExec P rlbRef [.ref p] σ o) ∧ ∀ o, MExec P rlbRef [.ref p] σ o →
      ∃ e σ' fs', o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs') := by
  have hpre : (rlbSpecAll P R).pre [.ref p] σ :=
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3⟩
  have hnone := ttype_none_of_ge14 hnib
  obtain ⟨fs0, -, -, -, hp0, htr, hte, -⟩ := id hCP
  obtain ⟨fsl, hpl, hlimf⟩ := hlim
  rw [hp0] at hpl
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hpl
  subst hpl
  refine ⟨(rlbAll_termI R hF hV hn hT hR _ σ hpre).run, fun o ho => ?_⟩
  have hpost := rlbAll_sat R hF hV hn _ σ o hpre ho
  cases o with
  | normal r σ' =>
    simp only [rlbSpecAll, Spec.of] at hpost
    unfold rlbN at hpost
    obtain ⟨u', rest', -, -, tt, -, -, -, hs, -, -, -, htt, -⟩ := hpost p t tmp _ lim rfl hp0 htr hte hlimf
    rw [hsrc] at hs
    simp only [List.cons.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    rw [hnone] at htt
    cases htt
  | exc e σ' =>
    simp only [rlbSpecAll, Spec.of] at hpost
    unfold rlbEAll at hpost
    rcases hpost p t tmp _ lim rfl hp0 htr hte hlimf with hE | hB
    · unfold rlbE at hE
      rcases hE p t tmp _ lim rfl hp0 htr hte hlimf with ⟨hs, -⟩ | ⟨u', r', hs, hno, -⟩ |
          ⟨u', r', sz', r'', hs, hsz', hc, -⟩ | ⟨u', r', sz', r'', tt, hs, -, -, -, htt, -⟩
      · rw [hsrc] at hs
        cases hs
      · rw [hsrc] at hs
        simp only [List.cons.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [hsz] at hno
        cases hno
      · rw [hsrc] at hs
        simp only [List.cons.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [hsz] at hsz'
        simp only [Option.some.injEq, Prod.mk.injEq] at hsz'
        obtain ⟨rfl, rfl⟩ := hsz'
        rcases hc with hc | hc
        · exfalso
          omega
        · exact absurd hin hc
      · rw [hsrc] at hs
        simp only [List.cons.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        rw [hnone] at htt
        cases htt
    · unfold rlbBadCase at hB
      obtain ⟨-, -, -, -, -, -, -, -, -, fs', h⟩ := hB
      exact ⟨e, σ', fs', rfl, h⟩
  | wrong msg => simp only [rlbSpecAll, Spec.of] at hpost

/-- **A list header with element nibble 14 or 15** (e.g. the byte `0x0E`, no elements): the specification
    reads it (`readListHeader`); Java's `readListBegin()` terminates, and every run throws a
    `TProtocolException` (`getTType` has no TType for the nibble). -/
theorem rlb_nib1415_spec_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {size ety : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size)) (hety : ety = 14 ∨ ety = 15)
    (hsrc : R.src σ t = Spec.listHeader size ety ++ rest) :
    Spec.readListHeader (Spec.listHeader size ety ++ rest) = some ((size, ety), rest) ∧
    (∃ o, MExec P rlbRef [.ref p] σ o) ∧ ∀ o, MExec P rlbRef [.ref p] σ o →
      ∃ e σ' fs', o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs') := by
  have he : ety < 16 := by omega
  refine ⟨Spec.readListHeader_listHeader hs he rest, ?_⟩
  obtain ⟨u, rest0, hcons, hmod, hsz⟩ := listHeader_cons hs he rest
  rw [hcons] at hsrc
  exact rlb_nib1415_total R hF hV hn hT hR hCP hlim h1 h2 h3 hsrc hsz (toInt_ofNat_nonneg hs) hin
    (by omega)

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rlbAll_total
#print axioms EquivLean.Demo.Thrift.Java.rlb_nib1415_total
#print axioms EquivLean.Demo.Thrift.Java.rlb_nib1415_spec_total
