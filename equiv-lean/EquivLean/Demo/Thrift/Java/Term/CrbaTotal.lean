-- Termination package by JimpleLean's session: TermT4/CrbaTotal.lean (sha256 9c122dfd22083ac0...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.RlbP
import EquivLean.Demo.Thrift.Java.Term.CrbaT

/-!
# Thrift → Java (T4): `TProtocol.checkReadBytesAvailable(TList)` on a `TCompactProtocol` terminates, and
is totally correct

From the partial-correctness VC (`crba_body`) and its thin twin (`TermVC.of_thinX`), against the
transport contracts and, as hypotheses like them, the transport's termination (`TransportTerm`);
premise: the transport's class is concrete (`TConc`). The contract is the callers' (`crbaSpec`,
`crbaA_sat`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem crba_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((crbaSpecI P R).strengthen (TConc P)).pre args σ → MTerm P crbaRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (crba_body R P hF)) (crba_thin R P hF))

/-- **`checkReadBytesAvailable(TList)` terminates** on every input of its contract whose transport has
    a concrete class. -/
theorem crba_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (crbaSpec P R).pre args σ → TConc P args σ → MTerm P crbaRef args σ := by
  intro args σ hpre hc
  obtain ⟨p, l, t, tmp, lfs, b, s, hargs, hH, hl, he, hs, hi⟩ := hpre
  have hC := CPAtH.elim hH
  exact crba_termI R hF hV hT args σ
    ⟨⟨p, l, t, tmp, lfs, b, s, hargs, hC, hH, classOK_of_cpAt hC, hl, he, hs, hi⟩, hc⟩

/-- **`checkReadBytesAvailable(TList)`, total correctness.** -/
theorem crba_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (crbaSpec P R).pre args σ → TConc P args σ →
      (∃ o, MExec P crbaRef args σ o) ∧ ∀ o, MExec P crbaRef args σ o → (crbaSpec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(crba_term R hF hV hT args σ hpre hc).run, fun o ho => crbaA_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.crba_total
