/-
Search loops with `return` (`returns.ts`), each proved equal to the library call by `ts_auto`
alone: the loop is a fold that stops at the first returned value (`retStep`), the code after the
loop runs for both completions (`Completion.ofRet`), and the first-match lemmas
(`findSome?_ite_const`, …, `Array.findIdx?_eq_finRange`) turn the fold into `any`, `all`, `find?`
and `findIdx?`.
-/
import Summarize.ReturnsEx
import StrictTS.Proof.Auto

open StrictTS JS ReturnsEx

/-- `for … of` with `return true` is `some`. -/
theorem anyNegative_eq_some (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program anyNegativeRef (.cons (.arr a) .nil)) w =
      exec (callFun I program anyNegativeSomeRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `for … of` with `return false` on a negated test is `every`. -/
theorem allShort_eq_every (I : Impl) (a : Nat) (ws : Array (Val TT .str)) (m : F64) (w : World TT)
    (hw : w.heap.get? (.arr .str, a) = some ws) :
    exec (callFun I program allShortRef (.cons (.arr a) (.cons (.num m) .nil))) w =
      exec (callFun I program allShortEveryRef (.cons (.arr a) (.cons (.num m) .nil))) w := by
  ts_auto

/-- `for … of` returning the element is `find`. -/
theorem firstBig_eq_find (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program firstBigRef (.cons (.arr a) .nil)) w =
      exec (callFun I program firstBigFindRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A counted loop returning the position is `findIndex` (on arrays shorter than `2^32`, as
JavaScript arrays are). -/
theorem indexOfLong_eq_findIndex (I : Impl) (a : Nat) (ws : Array (Val TT .str)) (m : F64) (w : World TT)
    (hw : w.heap.get? (.arr .str, a) = some ws) (hs : ws.size < 2 ^ 32) :
    exec (callFun I program indexOfLongRef (.cons (.arr a) (.cons (.num m) .nil))) w =
      exec (callFun I program indexOfLongFindRef (.cons (.arr a) (.cons (.num m) .nil))) w := by
  ts_auto

/-- A loop that returns its running sum at the first negative element never throws or panics. -/
theorem sumUntilNegative_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program sumUntilNegativeRef (.cons (.arr a) .nil)) w := by
  ts_auto
