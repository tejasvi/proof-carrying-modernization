-- Termination package by JimpleLean's session: TermT4/RlbTotal.lean (sha256 41c40fe5b7aea343...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Callee
import EquivLean.Demo.Thrift.Java.Term.RlbT
import EquivLean.Demo.Thrift.Java.RlbP

/-!
# Thrift → Java (T4): `readListBegin()` terminates, and is totally correct

From `rlb_body` and its thin twin (`TermVC.of_thinX`, no extra callee premises), against `Γ6`
(`readByte()`, `getTType(byte)`, `checkContainerReadLength(int)`, `checkReadBytesAvailable(TList)`, the
varint methods, the transport), the transport contracts and `TransportTerm`. `readListBegin()` makes a
protocol call after another, so its premise is `TRepConc`. The named inputs of the table (row L1 and the
agreement row `exNegSize`) get total versions.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem mem8_of_mem9L :
    ∀ d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC], d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h | h | h | h | h | h <;> simp [h]

/-- The contracts `readListBegin()` uses terminate. -/
theorem Γ6_term (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ6 P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  obtain ⟨hnb, hng, hnc, hnk, hn1, hn2⟩ := hn
  have hF7 : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC] := contains_sub hF (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h | h | h | h | h <;> simp [h])
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ6 at hS
  by_cases e1 : sig = rbSig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => rbA_termR R (contains_sub hF (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
        rcases hd with h | h | h <;> simp [h])) hV hT hR args σ hp.1) hnb
  · rw [if_neg e1] at hS
    by_cases e2 : sig = gttSig
    · rw [if_pos e2] at hS
      cases hS
      subst e2
      exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
        (fun args σ hp => gtt_term (contains_sub hF (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
          rcases hd with h | h | h <;> simp [h])) args σ hp.1) hng
    · rw [if_neg e2] at hS
      by_cases e3 : sig = ccrlSig
      · rw [if_pos e3] at hS
        cases hS
        subst e3
        exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
          (fun args σ hp => ccrl_term (contains_sub hF (by
            intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
            rcases hd with h | h | h <;> simp [h])) args σ hp.1) hnc
      · rw [if_neg e3] at hS
        by_cases e4 : sig = crbaSig
        · rw [if_pos e4] at hS
          cases hS
          subst e4
          exact contractTerm_tp hcp htp hO rfl rfl rfl rfl (by decide)
            (fun args σ hp => crbaA_termR R (contains_sub hF (by
              intro d hd
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
              rcases hd with h | h | h | h | h | h | h | h <;> simp [h])) hV hT hR args σ hp.1) hnk
        · rw [if_neg e4] at hS
          exact Γ2_term_noX R hF7 hV hn1 hn2 hT hR sig S hS

theorem rlb_termI (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rlbSpecI P R).pre args σ → MTerm P rlbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ6 R hF hV hn))
    (SpecEnv.strengthen_term (Γ6_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (rlb_body R P (contains_sub hF mem8_of_mem9L)) (rlb_thin R P (contains_sub hF mem8_of_mem9L)))

/-- **`readListBegin()`, total correctness.** -/
theorem rlb_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rlbSpecI P R).pre args σ →
      (∃ o, MExec P rlbRef args σ o) ∧ ∀ o, MExec P rlbRef args σ o → (rlbSpecI P R).post args σ o :=
  fun args σ hpre => ⟨(rlb_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => rlb_sat R hF hV hn args σ o hpre ho⟩

/-- `readListBegin()` terminates on a header byte `u` with a known type nibble (the premises of
    `rlb_out`). -/
theorem rlb_term_at (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {u : UInt8} {rest0 : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true) :
    MTerm P rlbRef [.ref p] σ := by
  have hnibL : NibbleOKL (R.src σ t) := by
    intro u' rest' h
    rw [hsrc] at h
    injection h with e1 e2
    subst e1
    exact hnib
  exact rlb_termI R hF hV hn hT hR [.ref p] σ
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, hnibL⟩

/-! ## The named inputs (row L1, the agreement row `exNegSize`), total -/

/-- **Agreement row, `exNegSize`, total**: `readListBegin()` terminates, and every run throws a
    `TProtocolException` (`rlb_exNegSize`). -/
theorem rlb_exNegSize_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hsrc : R.src σ t = Spec.exNegSize ++ rest) :
    (∃ o, MExec P rlbRef [.ref p] σ o) ∧ ∀ o, MExec P rlbRef [.ref p] σ o →
    Spec.readListHeader Spec.exNegSize = none ∧
      ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  have hs : R.src σ t = (0xF5 : UInt8) :: ([0x80, 0x80, 0x80, 0x80, 0x08] ++ rest) := by
    rw [hsrc]
    all_goals rfl
  exact ⟨(rlb_term_at R hF hV hn hT hR hCP hlim h1 h2 h3 hs (by decide)).run,
    fun _ hm => rlb_exNegSize R hF hV hn hCP hlim h1 h2 h3 hsrc hm⟩

/-- **L1, a list header with element nibble 13 (UUID), total**: `readListBegin()` terminates, and every
    run throws a `TTransportException` (`rlb_uuid`). -/
theorem rlb_uuid_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {size : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size))
    (hsrc : R.src σ t = Spec.listHeader size 13 ++ rest) :
    (∃ o, MExec P rlbRef [.ref p] σ o) ∧ ∀ o, MExec P rlbRef [.ref p] σ o →
    Spec.readListHeader (Spec.listHeader size 13 ++ rest) = some ((size, 13), rest) ∧
      ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain ttExcCls fs) := by
  refine ⟨?_, fun _ hm => rlb_uuid R hF hV hn hCP hlim h1 h2 h3 hs hin hsrc hm⟩
  obtain ⟨u, rest0, hcons, hmod, -⟩ := listHeader_cons hs (by decide : 13 < 16) rest
  rw [hcons] at hsrc
  have hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true := by rw [hmod]; rfl
  exact (rlb_term_at R hF hV hn hT hR hCP hlim h1 h2 h3 hsrc hnib).run

/-- **D for the list header, total**: `readListBegin()` terminates on `Spec.listHeader size ety ++ rest`,
    and every run returns the `TList` of `rlb_D`. -/
theorem rlb_D_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) (hT : TransportTerm P R) (hR : TRepConc P R)
    {σ : State} {p t tmp : Addr} {lim : I64} {size ety tt : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size))
    (htt : Spec.ttypeOfCompact ety = some tt) (hms : (minSize tt).isSome = true)
    (hsrc : R.src σ t = Spec.listHeader size ety ++ rest) :
    (∃ o, MExec P rlbRef [.ref p] σ o) ∧ ∀ o, MExec P rlbRef [.ref p] σ o →
    ∃ σ' l lfs, o = .normal (some (.ref l)) σ' ∧ σ'.heap l = some (.plain tlCls lfs) ∧
      Fields.get lfs (tlCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get lfs (tlCls, "size") = some (.int (BitVec.ofNat 32 size)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp := by
  refine ⟨?_, fun _ hm => rlb_D R hF hV hn hCP hlim h1 h2 h3 hs hin htt hms hsrc hm⟩
  have he : ety < 16 := Nat.lt_trans (ttypeOfCompact_dom _ _ htt) (by decide)
  obtain ⟨u, rest0, hcons, hmod, -⟩ := listHeader_cons hs he rest
  rw [hcons] at hsrc
  have hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true := by rw [hmod, htt]; rfl
  exact (rlb_term_at R hF hV hn hT hR hCP hlim h1 h2 h3 hsrc hnib).run

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rlb_D_total
#print axioms EquivLean.Demo.Thrift.Java.rlb_total
#print axioms EquivLean.Demo.Thrift.Java.rlb_exNegSize_total
#print axioms EquivLean.Demo.Thrift.Java.rlb_uuid_total
