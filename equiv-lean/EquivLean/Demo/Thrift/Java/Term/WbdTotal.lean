-- Termination package by JimpleLean's session: TermT4/WbdTotal.lean (sha256 a9e8b55c12d789d1...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.WfbP
import EquivLean.Demo.Thrift.Java.Term.WbdT

/-!
# Thrift → Java (T4): `TCompactProtocol.writeByteDirect(byte)` terminates, and is totally correct

From the partial-correctness VC (`wbd_body`) and its thin twin (`TermVC.of_thinX`), against the
transport contracts and, as hypotheses like them, the transport's termination (`TransportTerm`);
premise: the transport's class is concrete (`TConc`). The contract is the callers' (`wbdSpecA`,
`wbdA_sat`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem wbd_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((wbdSpecI P R).strengthen (TConc P)).pre args σ → MTerm P wbdRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (wbd_body R P hF)) (wbd_thin R P hF))

/-- **`writeByteDirect(byte)` terminates** on every input of its contract whose transport has a
    concrete class. -/
theorem wbd_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wbdSpecA P R).pre args σ → TConc P args σ → MTerm P wbdRef args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, b, hargs, hCP⟩ := hpre
  exact wbd_termI R hF hV hT args σ ⟨⟨p, t, tmp, b, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP⟩, hc⟩

/-- **`writeByteDirect(byte)`, total correctness.** -/
theorem wbd_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wbdSpecA P R).pre args σ → TConc P args σ →
      (∃ o, MExec P wbdRef args σ o) ∧ ∀ o, MExec P wbdRef args σ o → (wbdSpecA P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(wbd_term R hF hV hT args σ hpre hc).run, fun o ho => wbdA_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wbd_total
