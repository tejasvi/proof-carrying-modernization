-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cRunVC.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cRunVC.lean

  The verification conditions of `run` from its segments: the entry segment, and the three cases
  at the head of the read loop (end-of-file flag set; a record left; all records read).
-/
import EquivLean.Modernize.JL.Cbact02cRunEntry
import EquivLean.Modernize.JL.Cbact02cRunLoopExit
import EquivLean.Modernize.JL.Cbact02cRunLoopRead
import EquivLean.Modernize.JL.Cbact02cRunLoopEof

open Jimple

namespace EquivLean.Modernize.JL

/-- From the head of the read loop, in each case of the flag and the record count. -/
theorem run_loop (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0) (fr : Frame)
    (σ : State) (hI : runInv32 args σ0 fr σ) : runWP args σ0 32 fr σ := by
  have hpre' := hpre
  obtain ⟨a, et, xs, ha, harr, -⟩ := hpre'
  obtain ⟨res, fs, l, ys, m, i, n, r5, z, h⟩ := hI a et xs ha harr
  by_cases hz : z = 0
  · rcases Int.lt_or_le i.toInt n.toInt with hi | hi
    · exact run_loop_read args σ0 hpre fr σ a et xs ha harr res fs l ys m i n r5 z h hz hi
    · exact run_loop_eof args σ0 hpre fr σ a et xs ha harr res fs l ys m i n r5 z h hz hi
  · exact run_loop_exit args σ0 hpre fr σ a et xs ha harr res fs l ys m i n r5 z h hz

theorem run_vc : MethodVC EquivLean.Modernize.Cbact02c.Java.Gen.prog runCallees.env 1 runRef runSpecJ runInv 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨run_entry args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  subst hp
  exact run_loop args σ0 hpre fr σ hI

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.run_vc
