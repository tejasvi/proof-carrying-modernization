-- Termination package by JimpleLean's session: TermT4/RsbTotal.lean (sha256 ff6a05d8f36543d5...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RlbTotal
import EquivLean.Demo.Thrift.Java.Term.RsbT
import EquivLean.Demo.Thrift.Java.RsbP

/-!
# Thrift → Java (T4): `readSetBegin()` terminates, and is totally correct

From `rsb_body` and its thin twin (`TermVC.of_thinX`, no extra callee premises), against `Γ7`
(`readListBegin()`, the transport), the transport contracts and `TransportTerm`; premise `TRepConc`, as
for `readListBegin()`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem mem9_of_mem10S : ∀ d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC],
    d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h | h | h | h | h | h | h <;> simp [h]

/-- `readListBegin()` terminates on its callers' contract. -/
theorem rlbA_termR (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rlbSpecA P R).pre args σ → MTerm P rlbRef args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, lim, hargs, hCP, hlim, h1, h2, h3, hnib⟩ := hpre
  exact rlb_termI R hF hV hn hT hR args σ
    ⟨p, t, tmp, lim, hargs, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, hnib⟩

/-- The contracts `readSetBegin()` uses terminate. -/
theorem Γ7_term (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ7 P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  obtain ⟨hnl, hnr⟩ := hn
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ7 at hS
  by_cases e1 : sig = rlbSig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => rlbA_termR R (contains_sub hF mem9_of_mem10S) hV hnl hT hR args σ hp.1) hnr
  · rw [if_neg e1] at hS
    exact transportTerm_X hT noX sig S hS

theorem rsb_termI (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rsbSpecI P R).pre args σ → MTerm P rsbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ7 R hF hV hn))
    (SpecEnv.strengthen_term (Γ7_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (rsb_body R P hF)
      (rsb_thin R P hF))

/-- **`readSetBegin()`, total correctness.** -/
theorem rsb_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rsbSpecI P R).pre args σ →
      (∃ o, MExec P rsbRef args σ o) ∧ ∀ o, MExec P rsbRef args σ o → (rsbSpecI P R).post args σ o :=
  fun args σ hpre => ⟨(rsb_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => rsb_sat R hF hV hn args σ o hpre ho⟩

/-- `readSetBegin()` terminates on a header byte `u` with a known type nibble. -/
theorem rsb_term_at (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {u : UInt8} {rest0 : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true) :
    MTerm P rsbRef [.ref p] σ := by
  have hnibL : NibbleOKL (R.src σ t) := by
    intro u' rest' h
    rw [hsrc] at h
    injection h with e1 e2
    subst e1
    exact hnib
  exact rsb_termI R hF hV hn hT hR [.ref p] σ
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, h4, hnibL⟩

/-- **D for the set header, total**: `readSetBegin()` terminates on `Spec.listHeader size ety ++ rest`,
    and every run returns the `TSet` of `rsb_D`. -/
theorem rsb_D_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {size ety tt : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size))
    (htt : Spec.ttypeOfCompact ety = some tt) (hms : (minSize tt).isSome = true)
    (hsrc : R.src σ t = Spec.listHeader size ety ++ rest) :
    (∃ o, MExec P rsbRef [.ref p] σ o) ∧ ∀ o, MExec P rsbRef [.ref p] σ o →
    ∃ σ' s sfs, o = .normal (some (.ref s)) σ' ∧ σ'.heap s = some (.plain tsCls sfs) ∧
      Fields.get sfs (tsCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get sfs (tsCls, "size") = some (.int (BitVec.ofNat 32 size)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp := by
  refine ⟨?_, fun _ hm => rsb_D R hF hV hn hCP hlim h1 h2 h3 h4 hs hin htt hms hsrc hm⟩
  have he : ety < 16 := Nat.lt_trans (ttypeOfCompact_dom _ _ htt) (by decide)
  obtain ⟨u, rest0, hcons, hmod, -⟩ := listHeader_cons hs he rest
  rw [hcons] at hsrc
  have hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true := by rw [hmod, htt]; rfl
  exact (rsb_term_at R hF hV hn hT hR hCP hlim h1 h2 h3 h4 hsrc hnib).run

/-- **`exNegSize` for the set header, total**: `readSetBegin()` terminates, and every run throws a
    `TProtocolException` (`rsb_exNegSize`). -/
theorem rsb_exNegSize_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclS P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done) (h4 : σ.initOf tsCls = .done)
    (hsrc : R.src σ t = Spec.exNegSize ++ rest) :
    (∃ o, MExec P rsbRef [.ref p] σ o) ∧ ∀ o, MExec P rsbRef [.ref p] σ o →
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  have hs : R.src σ t = (0xF5 : UInt8) :: ([0x80, 0x80, 0x80, 0x80, 0x08] ++ rest) := by
    rw [hsrc]
    all_goals rfl
  exact ⟨(rsb_term_at R hF hV hn hT hR hCP hlim h1 h2 h3 h4 hs (by decide)).run,
    fun _ hm => rsb_exNegSize R hF hV hn hCP hlim h1 h2 h3 h4 hsrc hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rsb_D_total
#print axioms EquivLean.Demo.Thrift.Java.rsb_exNegSize_total
#print axioms EquivLean.Demo.Thrift.Java.rsb_total
