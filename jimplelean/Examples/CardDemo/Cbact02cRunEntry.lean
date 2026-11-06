/-
  Examples/CardDemo/Cbact02cRunEntry.lean

  `run`, entry segment: from the start to the head of the read loop (statement 32), where the
  invariant holds with no record read.
-/
import Examples.CardDemo.Cbact02cRun

open Jimple

namespace Examples.CardDemo

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_entry (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0) :
    runWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, runWP, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig, spacesSig, startText,
    endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk, cardLine,
    fieldOf, fieldLong, argText, cardCls]

end Examples.CardDemo

#print axioms Examples.CardDemo.run_entry
