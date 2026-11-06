/-
  Examples/CardDemo/Cbact03cRunEntry.lean

  `Cbact03c.run`, entry segment: from the start to the head of the read loop (statement 29).
-/
import Examples.CardDemo.Cbact03cRun

open Jimple

namespace Examples.CardDemo

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_entry (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0) :
    c3RunWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, c3RunWP, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig, c3FixLenSig,
    c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows]

end Examples.CardDemo

#print axioms Examples.CardDemo.c3_run_entry
