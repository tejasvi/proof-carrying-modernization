-- Termination package by JimpleLean's session: TermT4/Rv64T.lean (sha256 7e9e3077467dbfe9...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rv64
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.readVarint64()` (thin VC)

The thin twin of `rv64_body`: its invariants, the variants of its two loops (the buffer path, statement
13, `off` local 7, at most 9; the byte-by-byte path, statement 35, `shift` local 9, at most 10), the
premise `TConc` (the transport's class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The variants of `readVarint64`'s loops. -/
def rv64Vs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 13 then (match fr.get 7 with | some (.int i) => (10 - i.toInt).toNat | _ => 0)
  else if pc = 35 then (match fr.get 9 with | some (.int k) => (11 - k.toInt).toNat | _ => 0)
  else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rv64_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun _ => (tContracts R).env) (fun _ => noX) 3 rv64Ref
    (fun P => (rv64SpecI P R).strengthen (TConc P)) (rv64Inv R) rv64Vs 200 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, TConc, TConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, CPAt, CPAtR, ClassOK, rv64SpecI, rv64Inv, PFrame, Program.selectVirtual,
      tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
      tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, BufView, TFrame, List.getElem?_eq_getElem,
      List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem_cons_zero,
      getElem?_zero_of_one32, jbyte, instanceFields_tpe, ctorCall_exc_str, ttCls, cpCls, tpCls, tpeCls,
      rv64Vs, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
