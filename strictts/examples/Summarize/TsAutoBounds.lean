/-
Counted loops with other bounds, starts and directions (`bounds.ts`), each proved to terminate
normally by `ts_auto` alone: `i < xs.length - 1` (reading `xs[i + 1]`), `i <= 10`, a start above
the bound (`for (let i = 1; i <= xs.length - 1; i++)` on an empty array), and backwards loops
`for (let i = xs.length - 1; i >= 0; i--)` or from a literal, with `return` (also one that
allocates: `return xs.slice(0, i + 1)`), `while` loops whose body ends with the counter step, and a
computed start (`Math.min(Math.floor(n), 50)`).
-/
import Summarize.BoundsEx
import StrictTS.Proof.Auto

open StrictTS JS BoundsEx

/-- Differences of neighbours: `i < xs.length - 1` and `xs[i + 1]`. -/
theorem sumUpTo_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program sumUpToRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `return false` under the bound `xs.length - 1`. -/
theorem isSorted_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program isSortedRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `i <= 10`. -/
theorem sumLe_returns (I : Impl) (w : World TT) :
    JS.Returns (callFun I program sumLeRef .nil) w := by
  ts_auto

/-- A start (`1`) that may lie above the bound (`xs.length - 1`). -/
theorem sumLeLast_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program sumLeLastRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- Backwards over an array, ending at the counter `-1`. -/
theorem sumDown_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program sumDownRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- Backwards from a literal, `i > 0`. -/
theorem sumDown10_returns (I : Impl) (w : World TT) :
    JS.Returns (callFun I program sumDown10Ref .nil) w := by
  ts_auto

/-- The last negative position: `return i` in a backwards loop. -/
theorem lastNeg_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program lastNegRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `dropRightWhile`: the returning iteration allocates the result. -/
theorem dropRightPos_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program dropRightPosRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `while (i < 10) { …; i++ }`. -/
theorem countWhile_returns (I : Impl) (w : World TT) :
    JS.Returns (callFun I program countWhileRef .nil) w := by
  ts_auto

/-- `while (i < xs.length) { s += xs[i]; i = i + 1; }`. -/
theorem sumWhile_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program sumWhileRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `while (i >= 0) { s += xs[i]; i--; }` from `xs.length - 1`. -/
theorem sumWhileDown_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program sumWhileDownRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `while (i > 0) { out = out + String(i) + " "; i = i - 1; }` from `5`. -/
theorem countDown5_returns (I : Impl) (w : World TT) :
    JS.Returns (callFun I program countDown5Ref .nil) w := by
  ts_auto

/-- A computed start, `for (let i = Math.min(Math.floor(n), 50); i > 0; i--)`, for every number
`n` (NaN, the infinities and `-0` run no iteration): split on the condition at the start. -/
theorem countDownMin_returns (I : Impl) (w : World TT) (n : F64) :
    JS.Returns (callFun I program countDownMinRef (.cons (.num n) .nil)) w := by
  ts_auto
