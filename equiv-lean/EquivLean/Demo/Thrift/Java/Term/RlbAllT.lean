-- Termination package by JimpleLean's session: TermT4/RlbAllT.lean (sha256 d88b15e1852cb225...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RlbAll
import EquivLean.Demo.Thrift.Java.Term.RlbT

/-!
# Thrift → Java (T4), termination: `readListBegin()` on every header byte (thin VC)

The thin twin of `rlbAll_body`, as `RlbT` for `rlb_body`: against `Γ6All` with no extra callee premises
(`noX`), the same cut points and variant (`rlbVs`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rlbAll_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC] →
    ThinVCX P (Γ6All P R) noX 2 rlbRef (rlbSpecAll P R) (rlbInvAll P R) rlbVs 300 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, CPAt, ClassOK, rlbSpecAll, rlbInvAll, LimitAt, Γ6All, Γ2, rbSig, gttSig, ccrlSig,
      crbaSig, rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll,
      tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, gttN, gttE, gttSpecAll, ccrlN, ccrlE, crbaN, crbaE,
      instanceFields_tl, jbyte, tlNew, ttCls, cpCls, tpCls, tpeCls, tlCls, rlbVs, noX]
    all_goals first | assumption | exact concrete_cp (by assumption) | skip

end EquivLean.Demo.Thrift.Java
