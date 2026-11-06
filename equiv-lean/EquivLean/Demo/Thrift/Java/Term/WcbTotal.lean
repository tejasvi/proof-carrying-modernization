-- Termination package by JimpleLean's session: TermT4/WcbTotal.lean (sha256 a29f3292cad4cac6...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Callee
import EquivLean.Demo.Thrift.Java.Term.WcbT
import EquivLean.Demo.Thrift.Java.WcbP

/-!
# Thrift → Java (T4): `writeCollectionBegin(byte, int)` terminates, and is totally correct

From `wcb_body` and its thin twin (`TermVC.of_thinX`, no extra callee premises), against `Γ5`
(`writeByteDirect(byte)`, the varint methods, the transport), the transport contracts and
`TransportTerm`. The long form makes a protocol call after another, so the premise is `TRepConc`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts the list/set header writer uses terminate. -/
theorem Γ5_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ5 P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  obtain ⟨hn1, -, hn3, hn4⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ5 at hS
  by_cases e1 : sig = wbdSig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => wbdA_termR R (contains_sub hF mem8_of_mem3) hV hT hR args σ hp.1) hn1
  · rw [if_neg e1] at hS
    exact Γ2_term_noX R hF7 hV hn3 hn4 hT hR sig S hS

theorem wcb_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wcbSpecI P R).pre args σ → MTerm P wcbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ5 R hF hV hn))
    (SpecEnv.strengthen_term (Γ5_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (wcb_body R P hF)
      (wcb_thin R P hF))

/-- **`writeCollectionBegin(elemType, size)`, total correctness.** -/
theorem wcb_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wcbSpecI P R).pre args σ →
      (∃ o, MExec P wcbRef args σ o) ∧ ∀ o, MExec P wcbRef args σ o → (wcbSpecI P R).post args σ o :=
  fun args σ hpre => ⟨(wcb_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => wcb_sat R hF hV hn args σ o hpre ho⟩

/-- **E for the list/set header, total**: `writeCollectionBegin(elemType, size)` terminates, and every
    run returns normally after appending `Spec.listHeader size c` (`wcb_E`). -/
theorem wcb_E_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp ta : Addr}
    {et sz : I32} {c : Nat}
    (hCP : CPAt P R σ p t tmp) (hct : Spec.compactType et.toNat = some c) (hsz : 0 ≤ sz.toInt)
    (hinit : σ.initOf cpCls = .done)
    (hst : σ.static (cpCls, "ttypeToCompactType") = some (.ref ta))
    (hta : σ.heap ta = some (.array (.prim .byte) ctTable)) :
    (∃ o, MExec P wcbRef [.ref p, .int et, .int sz] σ o) ∧
    ∀ o, MExec P wcbRef [.ref p, .int et, .int sz] σ o →
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.listHeader sz.toNat c ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp := by
  refine ⟨?_, fun _ hm => wcb_E R hF hV hn hCP hct hsz hinit hst hta hm⟩
  have hle := compactType_le _ _ hct
  have hi : et.toInt = et.toNat := by
    have e := BitVec.toInt_eq_toNat_cond et
    rw [if_pos (by omega)] at e
    exact e
  have hix : et.toInt.toNat = et.toNat := by omega
  have hget := ctTable_get _ _ hct
  rw [← hix] at hget
  exact (wcb_termI R hF hV hn hT hR [.ref p, .int et, .int sz] σ
    ⟨p, t, tmp, ta, et, sz, c, rfl, hCP, CPAtH.intro hCP, hsz, by omega,
      by rw [ctTable_length]; omega, hct, Spec.compactType_lt hct, hinit, hst, hta, hget,
      List.getElem?_eq_some_iff.mp hget⟩).run

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wcb_total
#print axioms EquivLean.Demo.Thrift.Java.wcb_E_total
