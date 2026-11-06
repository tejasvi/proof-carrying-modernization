-- Termination package by JimpleLean's session: TermT4/Wi16Total.lean (sha256 012951998cb56b7d...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Link
import EquivLean.Demo.Thrift.Java.Term.Wi16T
import EquivLean.Demo.Thrift.Java.WfbP

/-!
# Thrift → Java (T4): `writeI16(short)` terminates, and is totally correct

From `wi16_body` and its thin twin (`TermVC.of_thinX`), against `Γ2` with the callee premises `cpX`, the
transport contracts and `TransportTerm`; premise: the transport's class is concrete (`TConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem wi16_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ args σ, ((wi16SpecI P R).strengthen (TConc P)).pre args σ → MTerm P wi16Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen (cpX P) (valid_Γ2 R hF hV hn1 hn2))
    (SpecEnv.strengthen_term (Γ2_term_cpX R hF hV hn1 hn2 hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (wi16_body R P hF)) (wi16_thin R P hF))

/-- **`writeI16(short)` terminates** on every input of its callers' contract whose transport has a
    concrete class. -/
theorem wi16A_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ args σ, (wi16SpecA P R).pre args σ → TConc P args σ → MTerm P wi16Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, i, hargs, hCP⟩ := hpre
  exact wi16_termI R hF hV hn1 hn2 hT args σ ⟨⟨p, t, tmp, i, hargs, hCP, CPAtH.intro hCP⟩, hc⟩

theorem wi16A_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wi16SpecA P R).pre args σ → MTerm P wi16Ref args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, i, hargs, hCP⟩ := id hpre
  exact wi16A_term R hF hV hn1 hn2 hT args σ hpre (tconc_of_args hR hargs hCP)

/-- **`writeI16(short)`, total correctness** (its callers' contract). -/
theorem wi16A_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ args σ, (wi16SpecA P R).pre args σ → TConc P args σ →
      (∃ o, MExec P wi16Ref args σ o) ∧ ∀ o, MExec P wi16Ref args σ o → (wi16SpecA P R).post args σ o :=
  fun args σ hpre hc => ⟨(wi16A_term R hF hV hn1 hn2 hT args σ hpre hc).run,
    fun o ho => wi16A_sat R hF (valid_Γ2 R hF hV hn1 hn2) args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wi16A_total
