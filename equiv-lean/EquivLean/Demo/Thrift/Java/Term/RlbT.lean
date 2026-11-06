-- Termination package by JimpleLean's session: TermT4/RlbT.lean (sha256 0cf1e6db11abe9a9...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rlb
import EquivLean.Demo.Thrift.Java.Term.BaseRep

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.readListBegin()` (thin VC)

The thin twin of `rlb_body`, against `Γ6` with no extra callee premises (`noX`). Two cut points
(statements 2 and 7), no loop: the path from 2 reaches 7, so 7 gets the smaller variant.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The variant of `readListBegin`'s cut points (no loop). -/
def rlbVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 2 then 1 else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rlb_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC] →
    ThinVCX P (Γ6 P R) noX 2 rlbRef (rlbSpecI P R) (rlbInv P R) rlbVs 300 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, CPAt, ClassOK, rlbSpecI, rlbInv, LimitAt, Γ6, Γ2, rbSig, gttSig, ccrlSig,
      crbaSig, rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll,
      tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, gttN, gttE, ccrlN, ccrlE, crbaN, crbaE,
      instanceFields_tl, jbyte, tlNew, ttCls, cpCls, tpCls, tpeCls, tlCls, rlbVs, noX]
    all_goals first | assumption | exact concrete_cp (by assumption) | skip

end EquivLean.Demo.Thrift.Java
