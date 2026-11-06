-- Termination package by JimpleLean's session: TermT4/BinRT.lean (sha256 75814dc280e9b695...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.BinR
import EquivLean.Demo.Thrift.Java.Term.BinBase

/-!
# Thrift → Java (T4), termination: `TBinaryProtocol.readI16/readI32` (thin VCs)

The thin twins of `ri16_body`, `ri32_body`: their invariants (one cut point each, `label2`, where the
buffer path and the `readAll` path join, on no loop: the variant is constant), the premise `BConc` (the
transport's class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ri16_thin (R : TRep) : ThinVCPX (Contains · [bpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 1 ri16Ref
    (fun P => (ri16SpecI P R).strengthen (BConc P)) (ri16Inv R) (fun _ _ _ _ _ => 0) 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, BConc, BConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, BPAt, ClassOK, ri16SpecI, ri16Inv, tc_write, tc_readAll,
      tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, BufView, TFrame, jbyte, ofNat_succ32, ttCls, bpCls, tpCls, noX]
    all_goals first | assumption | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ri32_thin (R : TRep) : ThinVCPX (Contains · [bpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 1 ri32Ref
    (fun P => (ri32SpecI P R).strengthen (BConc P)) (ri32Inv R) (fun _ _ _ _ _ => 0) 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, BConc, BConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, BPAt, ClassOK, ri32SpecI, ri32Inv, tc_write, tc_readAll,
      tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, BufView, TFrame, jbyte, ofNat_succ32, ttCls, bpCls, tpCls, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
