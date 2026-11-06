/-
The theorems of `BreakProofs.lean`, each proved by `ts_auto` alone.
-/
import Summarize.BreaksEx
import StrictTS.Proof.Auto

open StrictTS JS BreaksEx

/-- `firstNegative` returns the first negative element (or `0`): the computed fold stops at it. -/
theorem firstNegative_brk_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program firstNegativeRef (.cons (.arr a) .nil)) w =
      some (.ok (xs.toList.foldl (brkStep (fun x _ (_ : Unit) => x.toNum.lt 0)
        (fun x s _ => if x.toNum.lt 0 = true then x else s) (fun _ _ _ => ())) (false, .num 0, ())).2.1, w) := by
  ts_auto

/-- `hasNegative` (a flag and `break`) never throws or panics. -/
theorem hasNegative_brk_returns_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program hasNegativeRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `takeUntilZero` (a `push` and a `break`) never throws or panics. -/
theorem takeUntilZero_returns_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    JS.Returns (callFun I program takeUntilZeroRef (.cons (.arr a) .nil)) w := by
  ts_auto
