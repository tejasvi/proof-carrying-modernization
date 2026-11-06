/-
`break` and `return` inside loops over maps, sets and strings (`liveexits.ts`), each proved by
`ts_auto` alone: the loop is a flagged fold over the live entries (`brkStep`, `retStep`), as for
`for … of` over an array.
-/
import Summarize.LiveExitsEx
import StrictTS.Proof.Auto

open StrictTS JS LiveExitsEx

/-- `every` over a map, by hand: `return false` at the first entry that fails. -/
theorem mapEvery_returns (I : Impl) (w : World TT) (a : Nat) (m : JSMap (Val TT .num) (Val TT .num))
    (hw : w.heap.get? (.map .num .num, a) = some m) :
    JS.Returns (callFun I program mapEveryRef (.cons (.map a) .nil)) w := by
  ts_auto

/-- The key of the first matching entry, with a flag variable and `break`. -/
theorem mapFindKey_returns (I : Impl) (w : World TT) (a : Nat) (m : JSMap (Val TT .num) (Val TT .num))
    (hw : w.heap.get? (.map .num .num, a) = some m) :
    JS.Returns (callFun I program mapFindKeyRef (.cons (.map a) .nil)) w := by
  ts_auto

/-- `some` over a set: `return true` at the first match. -/
theorem setSome_returns (I : Impl) (w : World TT) (a : Nat) (m : JSMap (Val TT .num) Unit)
    (hw : w.heap.get? (.set .num, a) = some m) :
    JS.Returns (callFun I program setSomeRef (.cons (.set a) .nil)) w := by
  ts_auto

/-- The first matching element of a set. -/
theorem setFind_returns (I : Impl) (w : World TT) (a : Nat) (m : JSMap (Val TT .num) Unit)
    (hw : w.heap.get? (.set .num, a) = some m) :
    JS.Returns (callFun I program setFindRef (.cons (.set a) .nil)) w := by
  ts_auto

/-- `return` inside a loop over the code points of a string. -/
theorem strHasSpace_returns (I : Impl) (w : World TT) (s : JSStr) :
    JS.Returns (callFun I program strHasSpaceRef (.cons (.str s) .nil)) w := by
  ts_auto

/-- `break` inside a loop over the code points of a string. -/
theorem strWordLen_returns (I : Impl) (w : World TT) (s : JSStr) :
    JS.Returns (callFun I program strWordLenRef (.cons (.str s) .nil)) w := by
  ts_auto

