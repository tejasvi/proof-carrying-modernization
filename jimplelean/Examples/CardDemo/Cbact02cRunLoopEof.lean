/-
  Examples/CardDemo/Cbact02cRunLoopEof.lean

  `run`, from the head of the read loop (statement 32) when all records read: the end-of-file status sets the flag, back at the loop head.
-/
import Examples.CardDemo.Cbact02cRun

open Jimple

namespace Examples.CardDemo

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_loop_eof (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i n : I32) (r5 : Addr) (z : I32)
    (h : RunAt σ0 fr σ a xs res fs l ys m i n r5 z) (hz : z = 0) (hi : n.toInt ≤ i.toInt) :
    runWP args σ0 32 fr σ := by
  jvc [ite_nat_ne, runWP, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig, spacesSig, startText,
    endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk, cardLine,
    fieldOf, fieldLong, argText, cardCls]

end Examples.CardDemo

#print axioms Examples.CardDemo.run_loop_eof
