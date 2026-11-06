/-
Loops and array callbacks inside loop and callback bodies (`nested.ts`), each proved to return
by `ts_auto` alone: the inner loop or callback is summarized on the symbolic state of the outer
iteration (`ts_merge` calls `ts_summarize`/`ts_callbacks` on what it evaluates), so the outer
step function contains the inner fold. A mutable variable that a loop never assigns (the outer
counter, seen from the inner loop) keeps its value instead of joining the fold's state. Calls of
non-recursive functions in a body or a callback are unfolded (also when the callee has a loop),
and a callback that reads the heap (`ys.every(…)` inside `filter`) is pure in the world of the
call (`arrFilter_pureAt`, …). A counted loop that updates in place the array whose length it
reads keeps the array's size, so the bound is fixed (`evalLoop_count_sized`).
-/
import Summarize.NestedEx
import StrictTS.Proof.Auto

open StrictTS JS NestedEx

/-- Nested `for … of` loops over two arrays. -/
theorem sumProducts_returns (I : Impl) (w : World TT) (a b : Nat) (xs ys : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hv : w.heap.get? (.arr .num, b) = some ys) :
    JS.Returns (callFun I program sumProductsRef (.cons (.arr a) (.cons (.arr b) .nil))) w := by
  ts_auto

/-- Nested counted loops reading `xs[i]` and `xs[j]`. -/
theorem countLess_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program countLessRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `result.every(…)` over the array the loop builds (`uniqWith`). -/
theorem uniqVals_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hn : a < w.next) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program uniqValsRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `xs.filter(x => ys.every(y => x !== y))` (`differenceWith`): the `filter` callback reads `ys`. -/
theorem diffWith_returns (I : Impl) (w : World TT) (a b : Nat) (xs ys : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hv : w.heap.get? (.arr .num, b) = some ys)
    (ha : a < w.next) (hb : b < w.next) :
    JS.Returns (callFun I program diffWithRef (.cons (.arr a) (.cons (.arr b) .nil))) w := by
  ts_auto

/-- A callback that calls a helper function. -/
theorem anyBig_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program anyBigRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A loop body that calls a helper with a loop of its own. -/
theorem sumSums_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program sumSumsRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- An in-place update of the array whose length the condition reads. -/
theorem doubleInPlace_returns (I : Impl) (w : World TT) (a : Nat) (xs : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hs : xs.size < 2 ^ 32) :
    JS.Returns (callFun I program doubleInPlaceRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A `map` callback that reads another array (pure in the world after the result array is
allocated: `arrMap_pureAt`). -/
theorem addLen_returns (I : Impl) (w : World TT) (a b : Nat) (xs ys : Array (Val TT .num))
    (hw : w.heap.get? (.arr .num, a) = some xs) (hv : w.heap.get? (.arr .num, b) = some ys)
    (ha : a < w.next) (hb : b < w.next) :
    JS.Returns (callFun I program addLenRef (.cons (.arr a) (.cons (.arr b) .nil))) w := by
  ts_auto
