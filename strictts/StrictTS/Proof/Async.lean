/-
StrictTS proof layer: the job queue and async functions.

`drain` (the microtask loop) is a fixpoint; these lemmas unfold it one job at a time when the
queue is known, so symbolic execution can follow an async function through its suspensions.
-/
import StrictTS.Proof.Unfold

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- An empty queue: the microtask loop stops. -/
theorem exec_drain_nil (I : Impl) (P : Program TT) (w : World TT) (h : w.jobs = []) :
    exec (drain I P) w = some (.ok (), w) := by
  rw [drain.eq_1]
  simp [h]

/-- A non-empty queue: run the first job, then continue. -/
theorem exec_drain_cons (I : Impl) (P : Program TT) (w : World TT) (j : Job TT) (rest : List (Job TT))
    (h : w.jobs = j :: rest) :
    exec (drain I P) w = exec (runJob I P j >>= fun _ => drain I P) { w with jobs := rest } := by
  conv => lhs; rw [drain.eq_1]
  simp only [exec_bind, exec_get, h, exec_set]

attribute [ts_sym] runJob resume handleStep JS.settle JS.addReaction JS.newPromise JS.resolveOnce
attribute [ts_sym] JS.tupReactions JS.tupDone JS.readSlots JS.promsOfTup JS.settledVal
attribute [ts_sym] execAB execAS applyK loopA

end StrictTS
