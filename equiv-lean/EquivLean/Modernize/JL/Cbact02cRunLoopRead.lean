-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cRunLoopRead.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cRunLoopRead.lean

  `run`, from the head of the read loop (statement 32) when a record is left: its line is displayed, back at the loop head.
-/
import EquivLean.Modernize.JL.Cbact02cRun

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_loop_read (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i n : I32) (r5 : Addr) (z : I32)
    (h : RunAt σ0 fr σ a xs res fs l ys m i n r5 z) (hz : z = 0) (hi : i.toInt < n.toInt) :
    runWP args σ0 32 fr σ := by
  jvc [ite_nat_ne, runWP, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig, spacesSig, startText,
    endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk, cardLine,
    fieldOf, fieldLong, argText, cardCls]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.run_loop_read
