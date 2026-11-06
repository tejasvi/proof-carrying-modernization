-- Termination package by JimpleLean's session: TermT4/Wv64T.lean (sha256 da98f746a9dbc5c0...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Wv64
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.writeVarint64(long)` (thin VC)

The thin twin of `wv64_body`: its invariants, the variant of its loop (statements 3 and 4, `idx`
local 7, at most 9; then statement 6, the last byte, and statement 22, the call), the premise `TConc`
(the transport's class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The variant of `writeVarint64`'s loop. -/
def wv64Vs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 3 then (match fr.get 7 with | some (.int i) => 2 * (10 - i.toInt).toNat + 3 | _ => 0)
  else if pc = 4 then (match fr.get 7 with | some (.int i) => 2 * (10 - i.toInt).toNat + 2 | _ => 0)
  else if pc = 6 then 1
  else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wv64_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 0 wv64Ref
    (fun P => (wv64SpecI P R).strengthen (TConc P)) wv64Inv wv64Vs 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, TConc, TConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, tContracts, CPAt, PFrame, wv64SpecI, wv64Inv, writeSpec, writeSig, ttCls,
      cpCls, tpCls, wv64Vs, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
