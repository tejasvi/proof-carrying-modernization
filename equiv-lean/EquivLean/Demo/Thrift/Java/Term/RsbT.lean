-- Termination package by JimpleLean's session: TermT4/RsbT.lean (sha256 397aaa18a93e1064...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rsb
import EquivLean.Demo.Thrift.Java.Term.BaseRep

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.readSetBegin()` (thin VC)

The thin twin of `rsb_body`, against `Γ7` with no extra callee premises (`noX`). Two cut points
(statements 2 and 3), no loop: the path from 2 reaches 3, so 3 gets the smaller variant.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The variant of `readSetBegin`'s cut points (no loop). -/
def rsbVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 2 then 1 else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rsb_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] →
    ThinVCX P (Γ7 P R) noX 3 rsbRef (rsbSpecI P R) (rsbInv P R) rsbVs 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, rsbSpecI, rsbInv, LimitAt, Γ7, rlbSig, Program.selectVirtual, tc_write,
      tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, instanceFields_ts, tsNew, cpCls, tpCls, tlCls, tsCls, rsbVs,
      noX]
    all_goals first | assumption | exact concrete_cp (by assumption) | skip

end EquivLean.Demo.Thrift.Java
