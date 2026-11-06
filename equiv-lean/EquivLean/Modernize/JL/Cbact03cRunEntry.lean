-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact03cRunEntry.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`C3`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact03c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact03cRunEntry.lean

  `Cbact03c.run`, entry segment: from the start to the head of the read loop (statement 29).
-/
import EquivLean.Modernize.JL.Cbact03cRun

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_entry (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0) :
    c3RunWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, c3RunWP, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig, c3FixLenSig,
    c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.c3_run_entry
