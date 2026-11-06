-- Termination package by JimpleLean's session: TermT4/RsbAllP.lean (sha256 f8e93044f29b6719...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RsbAllT
import EquivLean.Demo.Thrift.Java.Term.RlbAllP
import EquivLean.Demo.Thrift.Java.Term.RsbTotal

/-!
# Thrift → Java (T4): `readSetBegin()` on every header byte, linked, total; the nibbles 14 and 15

`readListBegin()`'s contract on every header byte (`rlbSpecAAll`) is valid (from `rlbAll_sat`) and
terminates (from `rlbAll_termI`), so `readSetBegin()` satisfies `rsbSpecAll` and is totally correct on it,
with the premises of `rsb_total`. The named case: a set header whose size is valid and whose element nibble
is 14 or 15 makes every run throw a `TProtocolException` (`rsb_nib1415_total`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- `readListBegin()`'s contract on every header byte, for the callers, from its body. -/
theorem rlbAAll_sat (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) : Sat P rlbRef (rlbSpecAAll P R) := by
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, lim, hargs, hCP, hlim, h1, h2, h3⟩ := hpre
  exact rlbAll_sat R hF hV hn args σ o ⟨p, t, tmp, lim, hargs, hCP, CPAtH.intro hCP, hlim, h1, h2, h3⟩ hm

theorem rlbAAll_termR (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rlbSpecAAll P R).pre args σ → MTerm P rlbRef args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, lim, hargs, hCP, hlim, h1, h2, h3⟩ := hpre
  exact rlbAll_termI R hF hV hn hT hR args σ ⟨p, t, tmp, lim, hargs, hCP, CPAtH.intro hCP, hlim, h1, h2, h3⟩

/-- The contracts `readSetBegin()` uses on every header byte are valid. -/
theorem valid_Γ7All (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) : Valid P (Γ7All P R) := by
  obtain ⟨hnl, hnr⟩ := hn
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ7All at hS
  by_cases h1 : sig = rlbSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (rlbAAll_sat R (contains_sub hF mem9_of_mem10S) hV hnl) hnr
  · rw [if_neg h1] at hS
    exact hV sig S hS

/-- `readSetBegin()` satisfies its contract on every header byte. -/
theorem rsbAll_sat (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) : Sat P rsbRef (rsbSpecAll P R) :=
  MethodVC.sat_of_valid (valid_Γ7All R hF hV hn) (rsbAll_body R P hF)

/-- The contracts of `Γ7All` terminate. -/
theorem Γ7All_term (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ7All P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  obtain ⟨hnl, hnr⟩ := hn
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ7All at hS
  by_cases e1 : sig = rlbSig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => rlbAAll_termR R (contains_sub hF mem9_of_mem10S) hV hnl hT hR args σ hp.1) hnr
  · rw [if_neg e1] at hS
    exact transportTerm_X hT noX sig S hS

theorem rsbAll_termI (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rsbSpecAll P R).pre args σ → MTerm P rsbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ7All R hF hV hn))
    (SpecEnv.strengthen_term (Γ7All_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (rsbAll_body R P hF)
      (rsbAll_thin R P hF))

/-- **`readSetBegin()` on every header byte, total correctness.** -/
theorem rsbAll_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rsbSpecAll P R).pre args σ →
      (∃ o, MExec P rsbRef args σ o) ∧ ∀ o, MExec P rsbRef args σ o → (rsbSpecAll P R).post args σ o :=
  fun args σ hpre => ⟨(rsbAll_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => rsbAll_sat R hF hV hn args σ o hpre ho⟩

/-- **A set header with a valid size and element nibble 14 or 15, total**: `readSetBegin()` terminates,
    and every run throws a `TProtocolException`. -/
theorem rsb_nib1415_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {u : UInt8} {rest0 rest : Bytes} {size : I32}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hsz : listSizeJ u rest0 = some (size, rest))
    (h0 : 0 ≤ size.toInt) (hin : InLimit lim size) (hnib : 14 ≤ u.toNat % 16) :
    (∃ o, MExec P rsbRef [.ref p] σ o) ∧ ∀ o, MExec P rsbRef [.ref p] σ o →
      ∃ e σ' fs', o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs') := by
  have hpre : (rsbSpecAll P R).pre [.ref p] σ :=
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, h4⟩
  have hnone := ttype_none_of_ge14 hnib
  obtain ⟨fs0, -, -, -, hp0, htr, hte, -⟩ := id hCP
  obtain ⟨fsl, hpl, hlimf⟩ := hlim
  rw [hp0] at hpl
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hpl
  subst hpl
  refine ⟨(rsbAll_termI R hF hV hn hT hR _ σ hpre).run, fun o ho => ?_⟩
  have hpost := rsbAll_sat R hF hV hn _ σ o hpre ho
  cases o with
  | normal r σ' =>
    simp only [rsbSpecAll, Spec.of] at hpost
    unfold rsbN at hpost
    obtain ⟨u', rest', -, -, tt, -, -, -, hs, -, -, -, htt, -⟩ := hpost p t tmp _ lim rfl hp0 htr hte hlimf
    rw [hsrc] at hs
    simp only [List.cons.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    rw [hnone] at htt
    cases htt
  | exc e σ' =>
    simp only [rsbSpecAll, Spec.of] at hpost
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
  | wrong msg => simp only [rsbSpecAll, Spec.of] at hpost

/-- **A set header with element nibble 14 or 15**: the specification reads it (`readListHeader`); Java's
    `readSetBegin()` terminates, and every run throws a `TProtocolException`. -/
theorem rsb_nib1415_spec_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {size ety : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size)) (hety : ety = 14 ∨ ety = 15)
    (hsrc : R.src σ t = Spec.listHeader size ety ++ rest) :
    Spec.readListHeader (Spec.listHeader size ety ++ rest) = some ((size, ety), rest) ∧
    (∃ o, MExec P rsbRef [.ref p] σ o) ∧ ∀ o, MExec P rsbRef [.ref p] σ o →
      ∃ e σ' fs', o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs') := by
  have he : ety < 16 := by omega
  refine ⟨Spec.readListHeader_listHeader hs he rest, ?_⟩
  obtain ⟨u, rest0, hcons, hmod, hsz⟩ := listHeader_cons hs he rest
  rw [hcons] at hsrc
  exact rsb_nib1415_total R hF hV hn hT hR hCP hlim h1 h2 h3 h4 hsrc hsz (toInt_ofNat_nonneg hs) hin
    (by omega)

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rsbAll_total
#print axioms EquivLean.Demo.Thrift.Java.rsb_nib1415_total
#print axioms EquivLean.Demo.Thrift.Java.rsb_nib1415_spec_total
