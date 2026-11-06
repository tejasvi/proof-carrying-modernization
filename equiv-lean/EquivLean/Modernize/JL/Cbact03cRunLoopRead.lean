-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact03cRunLoopRead.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`C3`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact03c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact03cRunLoopRead.lean

  `Cbact03c.run`, from the head of the read loop (statement 29) when a record is left: `getNext` reads it, its line is displayed twice, back at the loop head.
-/
import EquivLean.Modernize.JL.Cbact03cRun

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_loop_read (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (st : Addr) (sfs : List (FieldKey × Value)) (res : Addr)
    (fs : List (FieldKey × Value)) (l : Addr) (ys : List Value) (m : Nat) (i z : I32) (e : Addr)
    (sv ap rc rcu rac rf : Value)
    (h : C3RunAt σ0 fr σ a xs st sfs res fs l ys m i z e sv ap rc rcu rac rf) (hz : z = 0) (hi : i.toInt < xs.length) :
    c3RunWP args σ0 29 fr σ := by
  jvc [ite_nat_ne, c3RunWP, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig, c3FixLenSig,
    c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.c3_run_loop_read
