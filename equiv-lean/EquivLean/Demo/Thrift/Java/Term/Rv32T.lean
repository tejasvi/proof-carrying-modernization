-- Termination package by JimpleLean's session: TermT4/Rv32T.lean (sha256 1d817bbe0d31e45d...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rv32
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.readVarint32()` (thin VC)

The thin twin of `rv32_body`: its invariants, the variants of its two loops (the buffer path, statement
13, `i` local 9, at most 4; the byte-by-byte path, statement 35, `k` local 6, at most 5), the premise
`TConc` (the transport's class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The variants of `readVarint32`'s loops. -/
def rv32Vs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 13 then (match fr.get 9 with | some (.int i) => (5 - i.toInt).toNat | _ => 0)
  else if pc = 35 then (match fr.get 6 with | some (.int k) => (6 - k.toInt).toNat | _ => 0)
  else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rv32_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun _ => (tContracts R).env) (fun _ => noX) 3 rv32Ref
    (fun P => (rv32SpecI P R).strengthen (TConc P)) (rv32Inv R) rv32Vs 120 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, TConc, TConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, CPAt, CPAtR, ClassOK, rv32SpecI, rv32Inv, PFrame, Program.selectVirtual,
      tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
      tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, BufView, TFrame, List.getElem?_eq_getElem,
      List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem_cons_zero,
      getElem?_zero_of_one32, jbyte, instanceFields_tpe, ctorCall_exc_str, ttCls, cpCls, tpCls, tpeCls,
      rv32Vs, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
