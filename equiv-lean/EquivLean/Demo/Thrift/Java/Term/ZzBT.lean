-- Termination package by JimpleLean's session: TermT4/ZzBT.lean (sha256 248fb645cdb047c9...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.ZzB
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: the zigzag methods (thin VCs)

The thin twins of `zz32_body`, `zz64_body`, `uzz32_body`, `uzz64_body`: no loop (the variant is
constant), no call (the contract table is empty: no premise).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem zz32_thin : ThinVCPX (Contains · [cpC]) (fun _ => Contracts.env []) (fun _ => noX) 0 zz32Ref
    (fun _ => zz32Spec) [] (fun _ _ _ _ _ => 0) 20 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  dsimp only
  jvc_body [Contains, zz32Spec, noX]
  all_goals first | assumption | skip

theorem zz64_thin : ThinVCPX (Contains · [cpC]) (fun _ => Contracts.env []) (fun _ => noX) 0 zz64Ref
    (fun _ => zz64Spec) [] (fun _ _ _ _ _ => 0) 20 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  dsimp only
  jvc_body [Contains, zz64Spec, noX]
  all_goals first | assumption | skip

theorem uzz32_thin : ThinVCPX (Contains · [cpC]) (fun _ => Contracts.env []) (fun _ => noX) 0 uzz32Ref
    (fun _ => uzz32Spec) [] (fun _ _ _ _ _ => 0) 20 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  dsimp only
  jvc_body [Contains, uzz32Spec, noX]
  all_goals first | assumption | skip

theorem uzz64_thin : ThinVCPX (Contains · [cpC]) (fun _ => Contracts.env []) (fun _ => noX) 0 uzz64Ref
    (fun _ => uzz64Spec) [] (fun _ _ _ _ _ => 0) 20 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  dsimp only
  jvc_body [Contains, uzz64Spec, noX]
  all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
