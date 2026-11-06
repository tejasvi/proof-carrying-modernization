-- Termination package by JimpleLean's session: TermT4/BinR64T.lean (sha256 753c9cbcfb4a848f...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.BinR64
import EquivLean.Demo.Thrift.Java.Term.BinBase

/-!
# Thrift → Java (T4), termination: `TBinaryProtocol.readI64()` (thin VC)

The thin twin of `ri64_body`: its invariant (one cut point, `label2`, where the buffer path and the
`readAll` path join, on no loop: the variant is constant), the premise `BConc` (the transport's class
is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ri64_thin (R : TRep) : ThinVCPX (Contains · [bpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 1 ri64Ref
    (fun P => (ri64SpecI P R).strengthen (BConc P)) (ri64Inv R) (fun _ _ _ _ _ => 0) 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, BConc, BConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, BPAt, ClassOK, ri64SpecI, ri64Inv, tc_write, tc_readAll,
      tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, BufView, TFrame, jbyte, ofNat_succ32, ttCls, bpCls, tpCls, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
