/-
  Examples/CardDemo/Cbact03cRunVC.lean

  The verification conditions of `Cbact03c.run` from its segments.
-/
import Examples.CardDemo.Cbact03cRunEntry
import Examples.CardDemo.Cbact03cRunLoopExit
import Examples.CardDemo.Cbact03cRunLoopRead
import Examples.CardDemo.Cbact03cRunLoopEof

open Jimple

namespace Examples.CardDemo

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

theorem c3_run_vc : MethodVC C3.prog c3RunCallees.env 1 c3RunRef c3RunSpecJ c3RunInv 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨c3_run_entry args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [c3RunInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  subst hp
  exact c3_run_loop args σ0 hpre fr σ hI

end Examples.CardDemo

#print axioms Examples.CardDemo.c3_run_vc
