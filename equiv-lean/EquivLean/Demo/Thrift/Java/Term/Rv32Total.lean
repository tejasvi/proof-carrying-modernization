-- Termination package by JimpleLean's session: TermT4/Rv32Total.lean (sha256 b17c7185e8cdd4af...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rv32P
import EquivLean.Demo.Thrift.Java.Term.Rv32T
import EquivLean.Demo.Thrift.Java.Term.Wv32T

/-!
# Thrift → Java (T4): `readVarint32()` and `writeVarint32(int)` terminate, and are totally correct

From the partial-correctness VCs (`rv32_body`, `wv32_body`) and their thin twins (`TermVC.of_thinX`),
against the transport contracts and, as hypotheses like them, the transport's termination
(`TransportTerm`); premise: the transport's class is concrete (`TConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rv32_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((rv32SpecI P R).strengthen (TConc P)).pre args σ → MTerm P rv32Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (rv32_body R P hF)) (rv32_thin R P hF))

/-- **`readVarint32()` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem rv32_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rv32Spec P R).pre args σ → TConc P args σ → MTerm P rv32Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, hargs, hCP, hin⟩ := hpre
  exact rv32_termI R hF hV hT args σ
    ⟨⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hin⟩, hc⟩

/-- **`readVarint32()`, total correctness.** -/
theorem rv32_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rv32Spec P R).pre args σ → TConc P args σ →
      (∃ o, MExec P rv32Ref args σ o) ∧ ∀ o, MExec P rv32Ref args σ o → (rv32Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(rv32_term R hF hV hT args σ hpre hc).run, fun o ho => rv32_sat R hF hV args σ o hpre ho⟩

theorem wv32_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((wv32SpecI P R).strengthen (TConc P)).pre args σ → MTerm P wv32Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (wv32_body R P hF)) (wv32_thin R P hF))

/-- **`writeVarint32(int)` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem wv32_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wv32SpecP P R).pre args σ → TConc P args σ → MTerm P wv32Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := hpre
  exact wv32_termI R hF hV hT args σ ⟨⟨p, t, tmp, n, hargs, hCP, CPAtH.intro hCP⟩, hc⟩

/-- **`writeVarint32(int)`, total correctness.** -/
theorem wv32_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wv32SpecP P R).pre args σ → TConc P args σ →
      (∃ o, MExec P wv32Ref args σ o) ∧ ∀ o, MExec P wv32Ref args σ o → (wv32SpecP P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(wv32_term R hF hV hT args σ hpre hc).run, fun o ho => wv32_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rv32_total
#print axioms EquivLean.Demo.Thrift.Java.wv32_total
