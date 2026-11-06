-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cRunLoopEof.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cRunLoopEof.lean

  `Cbcus01c.run`, from the head of the read loop (statement 26) when all records read: the end-of-file status sets the flag, back at the loop head.
-/
import EquivLean.Modernize.JL.Cbcus01cRun

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_loop_eof (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i z : I32) (h : CuRunAt σ0 fr σ a xs res fs l ys m i z) (hz : z = 0) (hi : (xs.length : Int) ≤ i.toInt) :
    cuRunWP args σ0 26 fr σ := by
  jvc [ite_nat_ne, cuRunWP, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees, cuFmtRecordInitialSig,
    cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.cu_run_loop_eof
