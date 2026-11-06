-- Termination package by JimpleLean's session: TermT4/CcrlT.lean (sha256 59136c3024289430...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Ccrl
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.checkContainerReadLength(int)` (thin VC)

The thin twin of `ccrl_body`: no loop (the variant is constant), no transport call (the contract
table is empty: no premise).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ccrl_thin : ThinVCPX (Contains · [cpC, tpeC, teC]) (fun _ => Contracts.env []) (fun _ => noX) 3
    ccrlRef (fun _ => ccrlSpec) [] (fun _ _ _ _ _ => 0) 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  dsimp only
  jvc_body [Contains, ccrlSpec, instanceFields_tpe, ctorCall_exc_str, instanceFields_sb, ctorCall_sb,
    tpeCls, cpCls, noX]
  all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
