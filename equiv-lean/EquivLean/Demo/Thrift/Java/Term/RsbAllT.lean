-- Termination package by JimpleLean's session: TermT4/RsbAllT.lean (sha256 a67d71afdbe401dd...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RsbAll
import EquivLean.Demo.Thrift.Java.Term.RsbT

/-!
# Thrift → Java (T4), termination: `readSetBegin()` on every header byte (thin VC)

The thin twin of `rsbAll_body`, as `RsbT` for `rsb_body`: against `Γ7All` with no extra callee premises
(`noX`), the same cut points and variant (`rsbVs`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rsbAll_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] →
    ThinVCX P (Γ7All P R) noX 3 rsbRef (rsbSpecAll P R) (rsbInv P R) rsbVs 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, rsbSpecAll, rlbSpecAAll, rsbInv, LimitAt, Γ7All, rlbSig, Program.selectVirtual,
      tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
      tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, instanceFields_ts, tsNew, cpCls, tpCls, tlCls,
      tsCls, rsbVs, noX]
    all_goals first | assumption | exact concrete_cp (by assumption) | skip

end EquivLean.Demo.Thrift.Java
