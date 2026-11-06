-- Termination package by JimpleLean's session: TermT4/GttT.lean (sha256 eaba72bc6db98bcb...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Gtt
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.getTType(byte)` (thin VC)

The thin twin of `gtt_body`: no loop (the variant is constant), no transport call (the contract table
is empty: no premise). The `default` branch (nibbles 14 and 15) is closed as `gtt_body` closes it: it
contradicts the precondition (`gtt_default`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem gtt_thin : ThinVCPX (Contains · [cpC, tpeC, teC]) (fun _ => Contracts.env []) (fun _ => noX) 3
    gttRef (fun _ => gttSpec) [] (fun _ _ _ _ _ => 0) 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  dsimp only
  jvc_body [Contains, gttSpec, instanceFields_tpe, ctorCall_exc_str, tpeCls, and15_toInt, and15_toNat,
    bmod_and15, noX]
  -- the nibbles 14 and 15 (the `default` branch) contradict the precondition, as in `gtt_body`
  all_goals first | assumption | exact (gtt_default ‹_› ‹_›).elim | skip

end EquivLean.Demo.Thrift.Java
