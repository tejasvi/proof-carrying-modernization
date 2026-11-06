/-
`examples/Async/double.ts`: the promise returned by `double(n)` is fulfilled with `2n` once the
microtask queue has run, for every `n` and every world whose queue is initially empty.
The proof follows the execution through the `await` suspension, the reaction job, and the
resumption of the async body.
-/
import Async.DoubleEx
import StrictTS.Proof.Async
import StrictTS.Proof.Tactics

open StrictTS JS DoubleEx

theorem double_resolves (I : Impl) (n : Int) (w : World TT) (hj : w.jobs = []) :
    ∃ p w₁ w₂ c, exec (callFun I program doubleRef (.cons (.bigint n) .nil)) w = some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bigint, p) = some c ∧ c.state = .fulfilled (.bigint (n * 2)) := by
  rw [double_call]
  simp [ts_sym, doubleDef, hj]
  refine ⟨w.next, _, ⟨rfl, rfl⟩, ?_⟩
  -- the queue holds one job: the resumption of `double` after its `await`
  rw [exec_drain_cons _ _ _ _ _ rfl]
  simp [ts_sym]
  rw [exec_drain_nil _ _ _ rfl]
  simp
