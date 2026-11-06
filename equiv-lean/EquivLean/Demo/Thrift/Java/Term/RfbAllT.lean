-- Termination package by JimpleLean's session: TermT4/RfbAllT.lean (sha256 43414ffc9058be70...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RfbAll
import EquivLean.Demo.Thrift.Java.Term.BaseRep

/-!
# Thrift → Java (T4), termination: `readFieldBegin()` on every header byte (thin VC)

The thin twin of `rfbAll_body`, as `RfbT` for `rfb_body`: against `Γ3All` with no extra callee premises
(`noX`), the same cut point (statement 8, no loop).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rfbAll_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    ThinVCX P (Γ3All P R) noX 3 rfbRef (rfbSpecAll P R) (rfbInv P R) (fun _ _ _ _ _ => 0) 200 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, CPAt, ClassOK, rfbSpecAll, rfbInv, LastAt, BoolAt, Γ3All, Γ2, rbSig, gttSig,
      rfiSig, rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
      tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame,
      PFrame, RFrame, gttN, gttE, gttSpecAll, instanceFields_tf, jbyte, tfNew, ttCls, cpCls, tpCls, tpeCls,
      tfCls, noX]
    all_goals first | assumption | exact concrete_cp (by assumption) | skip

end EquivLean.Demo.Thrift.Java
