-- Termination package by JimpleLean's session: TermT4/BinR64Total.lean (sha256 d30213507f92a201...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.BinR64T

/-!
# Thrift → Java (T4): `TBinaryProtocol.readI64()` terminates, and is totally correct

From the partial-correctness VC (`ri64_body`) and its thin twin (`TermVC.of_thinX`), against the
transport contracts and, as hypotheses like them, the transport's termination (`TransportTerm`);
premise: the transport's class is concrete (`BConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem ri64_termI (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((ri64SpecI P R).strengthen (BConc P)).pre args σ → MTerm P ri64Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (BConc P) (ri64_body R P hF)) (ri64_thin R P hF))

/-- **`readI64()` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem ri64_term (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (ri64Spec P R).pre args σ → BConc P args σ → MTerm P ri64Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, hargs, hBP⟩ := hpre
  exact ri64_termI R hF hV hT args σ ⟨⟨p, t, tmp, hargs, hBP, BPAtH.intro hBP, classOK_of_bpAt hBP⟩, hc⟩

/-- **`readI64()`, total correctness.** -/
theorem ri64_total (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (ri64Spec P R).pre args σ → BConc P args σ →
      (∃ o, MExec P ri64Ref args σ o) ∧ ∀ o, MExec P ri64Ref args σ o → (ri64Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(ri64_term R hF hV hT args σ hpre hc).run, fun o ho => ri64_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.ri64_total
