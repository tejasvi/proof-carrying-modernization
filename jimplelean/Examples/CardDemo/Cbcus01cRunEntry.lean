/-
  Examples/CardDemo/Cbcus01cRunEntry.lean

  `Cbcus01c.run`, entry segment: from the start to the head of the read loop (statement 26),
  where the invariant holds with no record read.
-/
import Examples.CardDemo.Cbcus01cRun

open Jimple

namespace Examples.CardDemo

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_entry (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0) :
    cuRunWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, cuRunWP, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees, cuFmtRecordInitialSig,
    cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows]

end Examples.CardDemo

#print axioms Examples.CardDemo.cu_run_entry
