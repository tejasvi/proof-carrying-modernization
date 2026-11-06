-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cRunVC.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cRunVC.lean

  The verification conditions of `Cbcus01c.run` from its segments: the entry segment, and the
  three cases at the head of the read loop (end-of-file flag set; a record left; all read).
-/
import EquivLean.Modernize.JL.Cbcus01cRunEntry
import EquivLean.Modernize.JL.Cbcus01cRunLoopExit
import EquivLean.Modernize.JL.Cbcus01cRunLoopRead
import EquivLean.Modernize.JL.Cbcus01cRunLoopEof

open Jimple

namespace EquivLean.Modernize.JL

theorem cu_run_loop (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0) (fr : Frame)
    (σ : State) (hI : cuRunInv26 args σ0 fr σ) : cuRunWP args σ0 26 fr σ := by
  have hpre' := hpre
  obtain ⟨a, et, xs, ha, harr, -⟩ := hpre'
  obtain ⟨res, fs, l, ys, m, i, z, h⟩ := hI a et xs ha harr
  by_cases hz : z = 0
  · rcases Int.lt_or_le i.toInt xs.length with hi | hi
    · exact cu_run_loop_read args σ0 hpre fr σ a et xs ha harr res fs l ys m i z h hz hi
    · exact cu_run_loop_eof args σ0 hpre fr σ a et xs ha harr res fs l ys m i z h hz hi
  · exact cu_run_loop_exit args σ0 hpre fr σ a et xs ha harr res fs l ys m i z h hz

theorem cu_run_vc : MethodVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunCallees.env 1 cuRunRef cuRunSpecJ cuRunInv 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨cu_run_entry args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [cuRunInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  subst hp
  exact cu_run_loop args σ0 hpre fr σ hI

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.cu_run_vc
