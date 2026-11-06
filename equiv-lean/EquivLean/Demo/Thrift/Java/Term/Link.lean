-- Termination package by JimpleLean's session: TermT4/Link.lean (sha256 724018ce9041b377...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Rv32Total
import EquivLean.Demo.Thrift.Java.Term.BaseRep
import EquivLean.Demo.Thrift.Java.FhR
import EquivLean.Demo.Thrift.Java.RlbP

/-!
# Thrift → Java (T4), termination: linking the callee contracts

`TermVC.mterm` needs every callee contract to terminate (`ContractTerm`). For a protocol method that is
the method's own termination (`contractTerm_cp`; `contractTerm_tp` for `checkReadBytesAvailable(TList)`,
which `TCompactProtocol` inherits from `TProtocol`), under the callers' premise; for the transport's it is
`TransportTerm`. `Γ2_term` covers the varint contracts and the transport's, for either form of the callee
premise: `cpX` (the caller passes `TConc`) or `noX` (the callee gets `TConc` from `TRepConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem cpX_of_cp {P : Program} {sig : MethodSig} {args : List Value} {σ : State}
    (h : sig.cls = cpCls) (hx : cpX P sig args σ) : TConc P args σ := by
  unfold cpX at hx
  rw [if_pos h] at hx
  exact hx

theorem tconc_of_args {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} {args rest : List Value}
    (hR : TRepConc P R) (hargs : args = .ref p :: rest) (h : CPAt P R σ p t tmp) : TConc P args σ := by
  subst hargs
  exact tconc_of_cpAt hR h

/-- A transport contract terminates under any extra premise. -/
theorem transportTerm_X {P : Program} {R : TRep} (h : TransportTerm P R)
    (X : MethodSig → List Value → State → Prop) :
    ∀ sig S, (tContracts R).env sig = some S → ContractTerm P sig (S.strengthen (X sig)) :=
  fun sig S hs => ContractTerm.mono (h sig S hs) fun _ _ hp => hp.1

/-- A contract with an unsatisfiable precondition terminates. -/
theorem contractTerm_false {P : Program} {sig : MethodSig} {S : Spec} (h : ∀ args σ, ¬ S.pre args σ) :
    ContractTerm P sig S :=
  ⟨fun _ _ args σ hp => (h args σ hp).elim, fun _ _ _ _ _ args σ hp => (h args σ hp).elim⟩

/-- A contract of a `TProtocol` instance method that `TCompactProtocol` inherits terminates, from the
    method's termination and `NoRedecl` (`contractOK_tp` for termination). -/
theorem contractTerm_tp {P : Program} (hF : P.findClass cpCls = some cpC)
    (hT : P.findClass tpCls = some tpC) (hO : P.findClass "java.lang.Object" = none)
    {r : JType} {name : String} {ps : List JType} {m : MethodDecl} {S : Spec}
    (hm0 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ false = none)
    (hm : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ false = some m)
    (hm1 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ true = none)
    (hm2 : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ true = none)
    (hcl : name ≠ "<clinit>") (hterm : ∀ args σ, S.pre args σ → MTerm P ⟨tpCls, m⟩ args σ)
    (hnr : NoRedecl P ⟨cpCls, r, name, ps⟩ ⟨tpCls, m⟩) :
    ContractTerm P ⟨cpCls, r, name, ps⟩ S := by
  refine ⟨fun m' ht args σ hp => ?_,
    fun c hc hs _ _ args σ hp => vterm_of_jimple (hnr c hc hs) hterm args σ hp⟩
  obtain ⟨hsel, -⟩ := ht
  rcases hsel with hs | hs | ⟨hc, -⟩
  · simp only [Program.selectStatic, MethodSig.sub] at hs
    rw [show Program.fuel P = 4093 + 1 + 1 + 1 from rfl, chainN_static_cp hF hT hO 4093 hm1 hm2] at hs
    cases hs
  · simp only [Program.selectSpecial, MethodSig.sub] at hs
    rw [show Program.fuel P = 4094 + 1 + 1 from rfl, chainN_tp hF hT 4094 hm0 hm] at hs
    simp only [Program.Target.jimple.injEq] at hs
    subst hs
    exact hterm args σ hp
  · unfold clinitSig at hc
    simp only [MethodSig.mk.injEq] at hc
    exact absurd hc.2.2.1 hcl

/-- `readVarint32()` terminates on its callers' contract, given `TConc`. -/
theorem rv32A_termC (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rv32SpecA P R).pre args σ → TConc P args σ → MTerm P rv32Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, hargs, hCP, hin⟩ := hpre
  exact rv32_termI R hF hV hT args σ ⟨⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hin⟩, hc⟩

/-- `writeVarint32(int)` terminates on its callers' contract, given `TConc`. -/
theorem wv32A_termC (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wv32SpecA P R).pre args σ → TConc P args σ → MTerm P wv32Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := hpre
  exact wv32_termI R hF hV hT args σ ⟨⟨p, t, tmp, n, hargs, hCP, CPAtH.intro hCP⟩, hc⟩

theorem rv32A_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rv32SpecA P R).pre args σ → MTerm P rv32Ref args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, hargs, hCP, -⟩ := id hpre
  exact rv32A_termC R hF hV hT args σ hpre (tconc_of_args hR hargs hCP)

theorem wv32A_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wv32SpecA P R).pre args σ → MTerm P wv32Ref args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := id hpre
  exact wv32A_termC R hF hV hT args σ hpre (tconc_of_args hR hargs hCP)

/-- The varint contracts and the transport's terminate, under the extra callee premises `X`. -/
theorem Γ2_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hn1 : NoRedecl P rv32Sig rv32Ref) (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R)
    (X : MethodSig → List Value → State → Prop)
    (h1 : ∀ args σ, (rv32SpecA P R).pre args σ → X rv32Sig args σ → MTerm P rv32Ref args σ)
    (h2 : ∀ args σ, (wv32SpecA P R).pre args σ → X wv32Sig args σ → MTerm P wv32Ref args σ) :
    ∀ sig S, Γ2 P R sig = some S → ContractTerm P sig (S.strengthen (X sig)) := by
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ2 at hS
  by_cases e1 : sig = rv32Sig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide) (fun args σ hp => h1 args σ hp.1 hp.2) hn1
  · rw [if_neg e1] at hS
    by_cases e2 : sig = wv32Sig
    · rw [if_pos e2] at hS
      cases hS
      subst e2
      exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide) (fun args σ hp => h2 args σ hp.1 hp.2) hn2
    · rw [if_neg e2] at hS
      exact transportTerm_X hT X sig S hS

/-- `Γ2` under `cpX`: the callers pass `TConc`. -/
theorem Γ2_term_cpX (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ sig S, Γ2 P R sig = some S → ContractTerm P sig (S.strengthen (cpX P sig)) :=
  Γ2_term R hF hn1 hn2 hT (cpX P)
    (fun args σ hp hx => rv32A_termC R hF hV hT args σ hp (cpX_of_cp rfl hx))
    (fun args σ hp hx => wv32A_termC R (contains_sub hF mem7_of_mem3) hV hT args σ hp (cpX_of_cp rfl hx))

/-- `Γ2` under `noX`: the callees get `TConc` from `TRepConc`. -/
theorem Γ2_term_noX (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ2 P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) :=
  Γ2_term R hF hn1 hn2 hT noX (fun args σ hp _ => rv32A_termR R hF hV hT hR args σ hp)
    (fun args σ hp _ => wv32A_termR R (contains_sub hF mem7_of_mem3) hV hT hR args σ hp)

end EquivLean.Demo.Thrift.Java
