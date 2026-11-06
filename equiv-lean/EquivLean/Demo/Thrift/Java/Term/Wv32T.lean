-- Termination package by JimpleLean's session: TermT4/Wv32T.lean (sha256 f0e707cb37dd1f38...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Wv32
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.writeVarint32(int)` (thin VC)

The thin twin of `wv32_body`: its invariant, the variant of its loop (statement 3, `i` local 6, at most
4), the premise `TConc` (the transport's class is concrete).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The variant of `writeVarint32`'s loop. -/
def wv32Vs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 3 then (match fr.get 6 with | some (.int i) => (5 - i.toInt).toNat | _ => 0) else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wv32_thin (R : TRep) : ThinVCPX (Contains · [cpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 0 wv32Ref
    (fun P => (wv32SpecI P R).strengthen (TConc P)) wv32Inv wv32Vs 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, TConc, TConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, tContracts, CPAt, PFrame, wv32SpecI, wv32Inv, writeSpec, writeSig, ttCls,
      cpCls, tpCls, wv32Vs, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java
