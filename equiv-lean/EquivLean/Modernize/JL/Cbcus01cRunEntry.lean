-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cRunEntry.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cRunEntry.lean

  `Cbcus01c.run`, entry segment: from the start to the head of the read loop (statement 26),
  where the invariant holds with no record read.
-/
import EquivLean.Modernize.JL.Cbcus01cRun

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_entry (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0) :
    cuRunWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, cuRunWP, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees, cuFmtRecordInitialSig,
    cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.cu_run_entry
