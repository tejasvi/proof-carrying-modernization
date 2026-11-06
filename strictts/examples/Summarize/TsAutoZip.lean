/-
Counted loops that read a second array at the counter (`examples/Summarize/zip.ts`): the loop
runs over `xs`, and `ys[i]` is in bounds because `xs.size ≤ ys.size`. The summary decides the
bounds test of the second read by `omega` from that hypothesis, so the step function is read off
without a case split (a split would leave the branch's proof inside the value).
-/
import Summarize.ZipEx
import StrictTS.Proof.Auto

open StrictTS JS ZipEx

/-- The dot product never panics or throws when `ys` is at least as long as `xs`. -/
theorem dot_returns_auto (I : Impl) (a b : Nat) (xs ys : Array (Val TT .num)) (w : World TT)
    (hx : w.heap.get? (.arr .num, a) = some xs) (hy : w.heap.get? (.arr .num, b) = some ys)
    (hsize : xs.size < 2 ^ 32) (hle : xs.size ≤ ys.size) :
    JS.Returns (callFun I program dotRef (.cons (.arr a) (.cons (.arr b) .nil))) w := by
  ts_auto

/-- The dot product, computed: the fold over the positions of `xs`. -/
theorem dot_eq (I : Impl) (a b : Nat) (xs ys : Array (Val TT .num)) (w : World TT)
    (hx : w.heap.get? (.arr .num, a) = some xs) (hy : w.heap.get? (.arr .num, b) = some ys)
    (hsize : xs.size < 2 ^ 32) (hle : xs.size ≤ ys.size) :
    exec (callFun I program dotRef (.cons (.arr a) (.cons (.arr b) .nil))) w =
      some (.ok ((List.finRange xs.size).foldl
        (fun s i => .num (s.toNum + xs[i].toNum * (ys[i.val]'(by omega)).toNum)) (.num 0)), w) := by
  rw [dot_call]
  simp only [dotDef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- Counting the positions where two arrays differ never panics or throws. -/
theorem countDiff_returns_auto (I : Impl) (a b : Nat) (xs ys : Array (Val TT .num)) (w : World TT)
    (hx : w.heap.get? (.arr .num, a) = some xs) (hy : w.heap.get? (.arr .num, b) = some ys)
    (hsize : xs.size < 2 ^ 32) (hle : xs.size ≤ ys.size) :
    JS.Returns (callFun I program countDiffRef (.cons (.arr a) (.cons (.arr b) .nil))) w := by
  ts_auto
