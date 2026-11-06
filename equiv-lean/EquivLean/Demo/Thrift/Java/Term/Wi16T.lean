-- Termination package by JimpleLean's session: TermT4/Wi16T.lean (sha256 af795cfc0db2528f...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Wi16
import EquivLean.Demo.Thrift.Java.Term.BaseCp

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.writeI16(short)` (thin VC)

The thin twin of `wi16_body` (no loop), against `Γ2` with the callee premises `cpX`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wi16_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun P => Γ2 P R) cpX 1 wi16Ref (fun P => (wi16SpecI P R).strengthen (TConc P)) []
    (fun _ _ _ _ _ => 0) 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, TConc, TConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, CPAt, ClassOK, wi16SpecI, Γ2, rv32Sig, wv32Sig, Program.selectVirtual,
      tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
      tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, ttCls, cpCls, tpCls, cpX]
    all_goals first
      | assumption
      | exact tconc_intro (by assumption) (by assumption) (by assumption) (by assumption)
      | skip

end EquivLean.Demo.Thrift.Java
