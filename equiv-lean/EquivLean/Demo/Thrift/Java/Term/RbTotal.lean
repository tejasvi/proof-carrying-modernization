-- Termination package by JimpleLean's session: TermT4/RbTotal.lean (sha256 d7399e68ecd357b1...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.FhR
import EquivLean.Demo.Thrift.Java.Term.RbT

/-!
# Thrift → Java (T4): `TCompactProtocol.readByte()` terminates, and is totally correct

From the partial-correctness VC (`rb_body`) and its thin twin (`TermVC.of_thinX`), against the transport
contracts and, as hypotheses like them, the transport's termination (`TransportTerm`); premise: the
transport's class is concrete (`TConc`). The contract is the callers' (`rbSpecA`, `rbA_sat`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rb_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((rbSpecI P R).strengthen (TConc P)).pre args σ → MTerm P rbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (rb_body R P hF)) (rb_thin R P hF))

/-- **`readByte()` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem rb_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rbSpecA P R).pre args σ → TConc P args σ → MTerm P rbRef args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, hargs, hCP⟩ := hpre
  exact rb_termI R hF hV hT args σ ⟨⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP⟩, hc⟩

/-- **`readByte()`, total correctness.** -/
theorem rb_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rbSpecA P R).pre args σ → TConc P args σ →
      (∃ o, MExec P rbRef args σ o) ∧ ∀ o, MExec P rbRef args σ o → (rbSpecA P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(rb_term R hF hV hT args σ hpre hc).run, fun o ho => rbA_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rb_total
