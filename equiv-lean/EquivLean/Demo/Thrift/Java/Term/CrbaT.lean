-- Termination package by JimpleLean's session: TermT4/CrbaT.lean (sha256 b8331cd4783fab78...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Crba
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TProtocol.checkReadBytesAvailable(TList)` on a `TCompactProtocol`
(thin VC)

The thin twin of `crba_body`: no loop (the variant is constant), the premise `TConc` (the transport's
class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem crba_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (fun _ => (tContracts R).env) (fun _ => noX) 4 crbaRef
    (fun P => (crbaSpecI P R).strengthen (TConc P)) [] (fun _ _ _ _ _ => 0) 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  simp only [Spec.strengthen, TConc, TConcAt] at hpre
  obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
  dsimp only
  jvc_body [Contains, CPAt, ClassOK, crbaSpecI, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none,
    Program.selectVirtual, instanceFields_tte, ctorCall_exc_str, ttCls, cpCls, tpCls, tlCls, ttExcCls,
    noX]
  all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
