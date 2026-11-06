/-
End-to-end example: `examples/Refactor/sum.ts` was translated by the frontend
(`node frontend/dist/cli.js --namespace SumEx -o examples/Refactor/SumEx.lean examples/Refactor/sum.ts`);
here we prove that its two functions are interchangeable.
-/
import Refactor.SumEx
import StrictTS.Proof.Tactics
import StrictTS.Proof.Summarize

open StrictTS JS SumEx

/-- The common meaning of both functions: the IEEE-754 left fold of `+` (no assumption that the
numbers are integers, finite, or small; NaN and ±0 behave as in JavaScript). -/
def sumSpec (xs : List (Val TT .num)) : F64 := xs.foldl (fun s x => s + x.toNum) 0

theorem foldl_num' (g : Val TT .num → Val TT .num → F64) (z : F64) (l : Array (Val TT .num)) :
    l.foldl (fun acc x => Val.num (g acc x)) (Val.num z) = Val.num (l.foldl (fun s x => g (.num s) x) z) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize l.toList = l
  induction l generalizing z with
  | nil => rfl
  | cons x l ih => exact ih (g (.num z) x)

/-- `sumReduce` computes `sumSpec` and leaves the world unchanged. -/
theorem sumReduce_spec (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sumReduceRef (.cons (.arr a) .nil)) w = some (.ok (.num (sumSpec xs.toList)), w) := by
  rw [sumReduce_call]
  simp only [sumReduceDef, ts_sym]
  rw [arrReduce_pure' I program a xs _ _ (fun acc x => .num (acc.toNum + x.toNum)) _ w hw]
  · simp [ts_sym, sumSpec, foldl_num']
  · intro vs w'
    match vs with
    | .cons acc (.cons x (.cons i (.cons arr .nil))) => simp [ts_sym]

/-- `sumLoop` computes `sumSpec` and leaves the world unchanged (index-based loop invariant). -/
theorem sumLoop_spec (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sumLoopRef (.cons (.arr a) .nil)) w = some (.ok (.num (sumSpec xs.toList)), w) := by
  rw [sumLoop_call]
  simp only [sumLoopDef, ts_sym]
  ts_forof xs using
    (fun i env w₁ => env = .cons (.num (sumSpec (xs.toList.take i))) (.cons (.arr a) .nil) ∧ w₁ = w)
  case cell => rintro i env w₁ ⟨-, rfl⟩; exact hw
  case step =>
    rintro i env w₁ hi ⟨rfl, rfl⟩
    simp [ts_sym, sumSpec, List.take_add_one, List.foldl_append, hi]
  case init => exact ⟨by simp [sumSpec], rfl⟩
  obtain ⟨rfl, rfl⟩ := hinv
  have htake : xs.toList.take xs.size = xs.toList := List.take_of_length_le (by simp)
  simp [ts_sym, htake]

/-- **Differential equivalence** of the two TypeScript functions, on every input array and every world. -/
theorem sumLoop_eq_sumReduce (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sumLoopRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumReduceRef (.cons (.arr a) .nil)) w := by
  rw [sumLoop_spec I a xs w hw, sumReduce_spec I a xs w hw]

/-- The same equivalence with no invariant and no callback meaning written by hand:
`ts_summarize` computes the loop's fold and `ts_callbacks` the `reduce` callback's meaning. -/
theorem sumLoop_eq_sumReduce_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sumLoopRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumReduceRef (.cons (.arr a) .nil)) w := by
  rw [sumLoop_call, sumReduce_call]
  simp only [sumLoopDef, sumReduceDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]
