-- Termination package by JimpleLean's session: TermT4/BinRTotal.lean (sha256 c27d156f7d317a3d...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.BinRT

/-!
# Thrift → Java (T4): `TBinaryProtocol.readI16()` and `readI32()` terminate, and are totally correct

From the partial-correctness VCs (`ri16_body`, `ri32_body`) and their thin twins (`TermVC.of_thinX`),
against the transport contracts and, as hypotheses like them, the transport's termination
(`TransportTerm`); premise: the transport's class is concrete (`BConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem ri16_termI (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((ri16SpecI P R).strengthen (BConc P)).pre args σ → MTerm P ri16Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (BConc P) (ri16_body R P hF)) (ri16_thin R P hF))

/-- **`readI16()` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem ri16_term (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (ri16Spec P R).pre args σ → BConc P args σ → MTerm P ri16Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, hargs, hBP⟩ := hpre
  exact ri16_termI R hF hV hT args σ ⟨⟨p, t, tmp, hargs, hBP, BPAtH.intro hBP, classOK_of_bpAt hBP⟩, hc⟩

/-- **`readI16()`, total correctness.** -/
theorem ri16_total (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (ri16Spec P R).pre args σ → BConc P args σ →
      (∃ o, MExec P ri16Ref args σ o) ∧ ∀ o, MExec P ri16Ref args σ o → (ri16Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(ri16_term R hF hV hT args σ hpre hc).run, fun o ho => ri16_sat R hF hV args σ o hpre ho⟩

theorem ri32_termI (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((ri32SpecI P R).strengthen (BConc P)).pre args σ → MTerm P ri32Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (BConc P) (ri32_body R P hF)) (ri32_thin R P hF))

/-- **`readI32()` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem ri32_term (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (ri32Spec P R).pre args σ → BConc P args σ → MTerm P ri32Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, hargs, hBP⟩ := hpre
  exact ri32_termI R hF hV hT args σ ⟨⟨p, t, tmp, hargs, hBP, BPAtH.intro hBP, classOK_of_bpAt hBP⟩, hc⟩

/-- **`readI32()`, total correctness.** -/
theorem ri32_total (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (ri32Spec P R).pre args σ → BConc P args σ →
      (∃ o, MExec P ri32Ref args σ o) ∧ ∀ o, MExec P ri32Ref args σ o → (ri32Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(ri32_term R hF hV hT args σ hpre hc).run, fun o ho => ri32_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.ri16_total
#print axioms EquivLean.Demo.Thrift.Java.ri32_total
