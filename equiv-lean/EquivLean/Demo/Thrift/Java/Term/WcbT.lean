-- Termination package by JimpleLean's session: TermT4/WcbT.lean (sha256 a246a8fb3e8206b1...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Wcb
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.writeCollectionBegin(byte, int)` (thin VC)

The thin twin of `wcb_body` (no loop, no cut point), against `Γ5` with no extra callee premises
(`noX`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wcb_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    ThinVCX P (Γ5 P R) noX 2 wcbRef (wcbSpecI P R) [] (fun _ _ _ _ _ => 0) 200 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, CPAt, ClassOK, wcbSpecI, Γ5, Γ2, wbdSig, rv32Sig, wv32Sig, wbdN,
      Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer,
      tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame, PFrame,
      ttCls, cpCls, tpCls, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
