-- Termination package by JimpleLean's session: TermT4/Rv64Total.lean (sha256 4665728e41fb15b5...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Rv64T

/-!
# Thrift → Java (T4): `TCompactProtocol.readVarint64()` terminates, and is totally correct

From the partial-correctness VC (`rv64_body`) and its thin twin (`TermVC.of_thinX`), against the
transport contracts and, as hypotheses like them, the transport's termination (`TransportTerm`);
premise: the transport's class is concrete (`TConc`). The sources state `readVarint64()` by its
body's contract only (`rv64SpecI`), so the theorems here do too.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rv64_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((rv64SpecI P R).strengthen (TConc P)).pre args σ → MTerm P rv64Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (TConc P) (rv64_body R P hF)) (rv64_thin R P hF))

/-- **`readVarint64()` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem rv64_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rv64SpecI P R).pre args σ → TConc P args σ → MTerm P rv64Ref args σ :=
  fun args σ hpre hc => rv64_termI R hF hV hT args σ ⟨hpre, hc⟩

/-- **`readVarint64()`, total correctness.** -/
theorem rv64_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (rv64SpecI P R).pre args σ → TConc P args σ →
      (∃ o, MExec P rv64Ref args σ o) ∧ ∀ o, MExec P rv64Ref args σ o → (rv64SpecI P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(rv64_term R hF hV hT args σ hpre hc).run,
      fun o ho => BodyVCP.sat (rv64_body R) hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rv64_total
