-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cRunEntry.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cRunEntry.lean

  `run`, entry segment: from the start to the head of the read loop (statement 32), where the
  invariant holds with no record read.
-/
import EquivLean.Modernize.JL.Cbact02cRun

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_entry (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0) :
    runWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, runWP, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig, spacesSig, startText,
    endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk, cardLine,
    fieldOf, fieldLong, argText, cardCls]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.run_entry
