-- Termination package by JimpleLean's session: TermT4/RfiTotal.lean (sha256 a8bda6dd82571978...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Link
import EquivLean.Demo.Thrift.Java.Term.RfiT

/-!
# Thrift → Java (T4): `readFieldId(byte)` terminates, and is totally correct

From `rfi_body` and its thin twin (`TermVC.of_thinX`), against `Γ2` with the callee premises `cpX`, the
transport contracts and `TransportTerm`; premise: the transport's class is concrete (`TConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rfi_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ args σ, ((rfiSpecI P R).strengthen (TConc P)).pre args σ → MTerm P rfiRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen (cpX P) (valid_Γ2 R hF hV hn1 hn2))
    (SpecEnv.strengthen_term (Γ2_term_cpX R hF hV hn1 hn2 hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (rfi_body R P hF)) (rfi_thin R P hF))

/-- **`readFieldId(byte)` terminates** on every input of its callers' contract whose transport has a
    concrete class. -/
theorem rfiA_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ args σ, (rfiSpecA P R).pre args σ → TConc P args σ → MTerm P rfiRef args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, b, last, hargs, hCP, hL, hB, hin⟩ := hpre
  exact rfi_termI R hF hV hn1 hn2 hT args σ
    ⟨⟨p, t, tmp, b, last, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hL, hB, hin⟩, hc⟩

theorem rfiA_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rfiSpecA P R).pre args σ → MTerm P rfiRef args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, b, last, hargs, hCP, -⟩ := id hpre
  exact rfiA_term R hF hV hn1 hn2 hT args σ hpre (tconc_of_args hR hargs hCP)

/-- **`readFieldId(byte)`, total correctness** (its callers' contract). -/
theorem rfiA_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) (hT : TransportTerm P R) :
    ∀ args σ, (rfiSpecA P R).pre args σ → TConc P args σ →
      (∃ o, MExec P rfiRef args σ o) ∧ ∀ o, MExec P rfiRef args σ o → (rfiSpecA P R).post args σ o :=
  fun args σ hpre hc => ⟨(rfiA_term R hF hV hn1 hn2 hT args σ hpre hc).run,
    fun o ho => rfiA_sat R hF (valid_Γ2 R hF hV hn1 hn2) args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rfiA_total
