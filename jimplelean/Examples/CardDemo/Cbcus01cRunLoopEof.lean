/-
  Examples/CardDemo/Cbcus01cRunLoopEof.lean

  `Cbcus01c.run`, from the head of the read loop (statement 26) when all records read: the end-of-file status sets the flag, back at the loop head.
-/
import Examples.CardDemo.Cbcus01cRun

open Jimple

namespace Examples.CardDemo

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_loop_eof (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i z : I32) (h : CuRunAt σ0 fr σ a xs res fs l ys m i z) (hz : z = 0) (hi : (xs.length : Int) ≤ i.toInt) :
    cuRunWP args σ0 26 fr σ := by
  jvc [ite_nat_ne, cuRunWP, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees, cuFmtRecordInitialSig,
    cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows]

end Examples.CardDemo

#print axioms Examples.CardDemo.cu_run_loop_eof
