-- Termination package by JimpleLean's session: TermT4/RfiT.lean (sha256 e8ec0b05ee55af22...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rfi
import EquivLean.Demo.Thrift.Java.Term.BaseCp

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.readFieldId(byte)` (thin VC)

The thin twin of `rfi_body` (no loop), against `Γ2` with the callee premises `cpX`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rfi_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun P => Γ2 P R) cpX 3 rfiRef (fun P => (rfiSpecI P R).strengthen (TConc P)) []
    (fun _ _ _ _ _ => 0) 200 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, TConc, TConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, CPAt, ClassOK, rfiSpecI, LastAt, BoolAt, Γ2, rv32Sig, wv32Sig,
      Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer,
      tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame, PFrame,
      ttCls, cpCls, tpCls, tpeCls, cpX]
    all_goals first
      | assumption
      | exact tconc_intro (by assumption) (by assumption) (by assumption) (by assumption)
      | skip

end EquivLean.Demo.Thrift.Java
