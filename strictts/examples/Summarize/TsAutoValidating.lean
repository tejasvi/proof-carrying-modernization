/-
Functions that validate their arguments before a loop (`validating.ts`), proved by `ts_auto`
alone. After symbolic execution, the outcome of the validating `if` statement is an `if` whose
condition the heap hypotheses do not decide, and the loop sits in the continuation of the `match`
on that outcome, out of the summaries' reach; `ts_auto` splits on the test first (by cases on
the innermost undecided test of the goal), then summarizes the loop in each case.

* `JS.NoPanic` (throwing allowed) holds for every array and every argument.
* `JS.Returns` and the exact result hold under a precondition that rules the validation out:
  `xs.size ≠ 0` (a `Nat` fact, compared with the test by `omega` via `numEq_ofNat`), or the
  negation of the test in the form symbolic execution computes it (`k.lt 0 = false`,
  `lo.gt hi = false`, `(xs.any fun x => x.toNum.lt 0) = false` for the summarized `some`), or
  `t ≠ .nan` for `Number.isNaN(t)`.
-/
import Summarize.ValidEx
import StrictTS.Proof.Auto

open StrictTS JS ValidEx

/-- `maxOf` throws on an empty array and never panics. -/
theorem maxOf_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program maxOfRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- On a non-empty array, `maxOf` is the fold of its loop. -/
theorem maxOf_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) (hne : xs.size ≠ 0) :
    exec (callFun I program maxOfRef (.cons (.arr a) .nil)) w =
      some (.ok (xs.toList.foldl (fun m x => if x.toNum.gt m.toNum = true then x else m)
        (.num (-F64.inf false))), w) := by
  ts_auto

theorem mean_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program meanRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- The mean of a non-empty array: the code after the loop reads the array again. -/
theorem mean_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) (hne : 0 < xs.size) :
    exec (callFun I program meanRef (.cons (.arr a) .nil)) w =
      some (.ok (Val.num ((xs.toList.foldl (fun s x => Val.num (s.toNum + x.toNum))
        (Val.num 0 : Val TT .num)).toNum / F64.ofNat xs.size)), w) := by
  ts_auto

theorem sumScaled_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (k : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program sumScaledRef (.cons (.arr a) (.cons (.num k) .nil))) w := by
  ts_auto

/-- With a factor that is not negative (`NaN` included), `sumScaled` returns. -/
theorem sumScaled_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (k : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hk : k.lt 0 = false) :
    JS.Returns (callFun I program sumScaledRef (.cons (.arr a) (.cons (.num k) .nil))) w := by
  ts_auto

/-- The validation is itself an array method with a callback (`xs.some(x => x < 0)`): it is
summarized first, then split on. -/
theorem sumNonNegative_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program sumNonNegativeRef (.cons (.arr a) .nil)) w := by
  ts_auto

theorem sumNonNegative_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hpos : (xs.any fun x => x.toNum.lt 0) = false) :
    JS.Returns (callFun I program sumNonNegativeRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A search loop with `return` after an argument check. -/
theorem firstAbove_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (t : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program firstAboveRef (.cons (.arr a) (.cons (.num t) .nil))) w := by
  ts_auto

theorem firstAbove_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (t : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ht : t ≠ .nan) :
    JS.Returns (callFun I program firstAboveRef (.cons (.arr a) (.cons (.num t) .nil))) w := by
  ts_auto

/-- Two tests before the loop: a validation throw and an early return. -/
theorem countBetween_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (lo hi : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program countBetweenRef (.cons (.arr a) (.cons (.num lo) (.cons (.num hi) .nil)))) w := by
  ts_auto

theorem countBetween_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (lo hi : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hlh : lo.gt hi = false) :
    JS.Returns (callFun I program countBetweenRef (.cons (.arr a) (.cons (.num lo) (.cons (.num hi) .nil)))) w := by
  ts_auto

/-- Straight-line code after the validation (no loop): in the remaining case `xs[0]` is in
bounds, since the test's outcome gives `xs.size ≠ 0`. -/
theorem firstOrThrow_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.NoPanic (callFun I program firstOrThrowRef (.cons (.arr a) .nil)) w := by
  ts_auto

theorem firstOrThrow_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) (hne : xs.size ≠ 0) :
    JS.Returns (callFun I program firstOrThrowRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- The last element after an early return on the empty array: `xs.length - 1` is a valid index
once the test's outcome gives `xs.size ≠ 0` (`ofNat_sub_ofNat`, side conditions by `omega`). -/
theorem lastOr_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (d : F64) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program lastOrRef (.cons (.arr a) (.cons (.num d) .nil))) w := by
  ts_auto

theorem sqrtChecked_noPanic (I : Impl) (x : F64) (w : World TT) :
    JS.NoPanic (callFun I program sqrtCheckedRef (.cons (.num x) .nil)) w := by
  ts_auto

/-- A caller that catches the validation's exception returns for every array. -/
theorem safeMax_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program safeMaxRef (.cons (.arr a) .nil)) w := by
  ts_auto
