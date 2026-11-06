-- Termination package by JimpleLean's session: TermT4/Wv64Total.lean (sha256 35536eca223df253...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Wv64T

/-!
# Thrift → Java (T4): `TCompactProtocol.writeVarint64(long)` terminates, and is totally correct

From the partial-correctness VC (`wv64_body`) and its thin twin (`TermVC.of_thinX`), against the
transport contracts and, as hypotheses like them, the transport's termination (`TransportTerm`);
premise: the transport's class is concrete (`TConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem wv64_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((wv64SpecI P R).strengthen (TConc P)).pre args σ → MTerm P wv64Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (wv64_body R P hF)) (wv64_thin R P hF))

/-- **`writeVarint64(long)` terminates** on every input of its contract whose transport has a
    concrete class. -/
theorem wv64_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wv64Spec P R).pre args σ → TConc P args σ → MTerm P wv64Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := hpre
  exact wv64_termI R hF hV hT args σ ⟨⟨p, t, tmp, n, hargs, hCP, CPAtH.intro hCP⟩, hc⟩

/-- **`writeVarint64(long)`, total correctness.** -/
theorem wv64_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wv64Spec P R).pre args σ → TConc P args σ →
      (∃ o, MExec P wv64Ref args σ o) ∧ ∀ o, MExec P wv64Ref args σ o → (wv64Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(wv64_term R hF hV hT args σ hpre hc).run, fun o ho => wv64_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wv64_total
