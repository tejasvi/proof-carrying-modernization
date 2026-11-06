-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact03cRunVC.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`C3`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact03c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact03cRunVC.lean

  The verification conditions of `Cbact03c.run` from its segments.
-/
import EquivLean.Modernize.JL.Cbact03cRunEntry
import EquivLean.Modernize.JL.Cbact03cRunLoopExit
import EquivLean.Modernize.JL.Cbact03cRunLoopRead
import EquivLean.Modernize.JL.Cbact03cRunLoopEof

open Jimple

namespace EquivLean.Modernize.JL

theorem c3_run_loop (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0) (fr : Frame)
    (σ : State) (hI : c3RunInv29 args σ0 fr σ) : c3RunWP args σ0 29 fr σ := by
  have hpre' := hpre
  obtain ⟨a, et, xs, ha, harr, -⟩ := hpre'
  obtain ⟨st, sfs, res, fs, l, ys, m, i, z, e, sv, ap, rc, rcu, rac, rf, h⟩ := hI a et xs ha harr
  by_cases hz : z = 0
  · rcases Int.lt_or_le i.toInt xs.length with hi | hi
    · exact c3_run_loop_read args σ0 hpre fr σ a et xs ha harr st sfs res fs l ys m i z e sv ap rc rcu
        rac rf h hz hi
    · exact c3_run_loop_eof args σ0 hpre fr σ a et xs ha harr st sfs res fs l ys m i z e sv ap rc rcu
        rac rf h hz hi
  · exact c3_run_loop_exit args σ0 hpre fr σ a et xs ha harr st sfs res fs l ys m i z e sv ap rc rcu
      rac rf h hz

theorem c3_run_vc : MethodVC EquivLean.Modernize.Cbact03c.Java.Gen.prog c3RunCallees.env 1 c3RunRef c3RunSpecJ c3RunInv 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨c3_run_entry args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [c3RunInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  subst hp
  exact c3_run_loop args σ0 hpre fr σ hI

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.c3_run_vc
