-- Termination package by JimpleLean's session: TermT4/RbT.lean (sha256 64c95cb4a29449aa...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rb
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.readByte()` (thin VC)

The thin twin of `rb_body`: no loop (the variant is constant), the premise `TConc` (the transport's
class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rb_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 0 rbRef
    (fun P => (rbSpecI P R).strengthen (TConc P)) [] (fun _ _ _ _ _ => 0) 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  simp only [Spec.strengthen, TConc, TConcAt] at hpre
  obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
  dsimp only
  jvc_body [Contains, CPAt, ClassOK, rbSpecI, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, BufView, TFrame,
    List.getElem?_eq_getElem, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    List.getElem_cons_zero, getElem?_zero_of_one32, ttCls, cpCls, tpCls, noX]
  all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
