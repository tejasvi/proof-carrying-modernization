/-
Synchronous library calls (`libcalls.ts`) proved by `ts_auto`: a regular-expression test, a
string method and a regex `split` are external calls answered by the world's oracle. `ts_auto`
splits on each answer that no hypothesis fixes (an error, or a value of each form), so that
statements for every oracle need no case analysis. `JS.NoPanic` holds for every oracle (an
error answer is thrown as a JavaScript exception, not a panic); `JS.Returns` holds when the
library does not throw (`World.ExtReturns w f`, an optional hypothesis); exact results follow
from the answers (`w.answer f vs n = .ok (.val v)`, by absolute call number).
-/
import Extern.LibEx
import StrictTS.Proof.Auto

open StrictTS JS LibEx

/-- Whatever the regex library answers (a Boolean or an exception), `isLowerWord` never panics. -/
theorem isLowerWord_noPanic (I : Impl) (s : JSStr) (w : World TT) :
    JS.NoPanic (callFun I program isLowerWordRef (.cons (.str s) .nil)) w := by
  ts_auto

/-- If the regex library does not throw, `isLowerWord` returns. -/
theorem isLowerWord_returns (I : Impl) (s : JSStr) (w : World TT)
    (hre : w.ExtReturns «RegExp.test_ext») :
    JS.Returns (callFun I program isLowerWordRef (.cons (.str s) .nil)) w := by
  ts_auto

/-- The result is the library's answer, and the call is the next one. -/
theorem isLowerWord_eq (I : Impl) (s : JSStr) (b : Bool) (w : World TT)
    (h0 : w.answer «RegExp.test_ext» (.cons (.str (JSStr.ofString "^[a-z]+$"))
      (.cons (.str (JSStr.ofString "")) (.cons (.str s) .nil))) w.extIdx = .ok (.val (.bool b))) :
    exec (callFun I program isLowerWordRef (.cons (.str s) .nil)) w =
      some (.ok (.bool b), { w with extIdx := w.extIdx + 1 }) := by
  ts_auto [h0]

theorem checkedName_noPanic (I : Impl) (s : JSStr) (w : World TT) :
    JS.NoPanic (callFun I program checkedNameRef (.cons (.str s) .nil)) w := by
  ts_auto

/-- A validation by a regex: when the library says the name is not blank, the result is the
trimmed name. -/
theorem checkedName_eq (I : Impl) (s : JSStr) (w : World TT)
    (h0 : w.answer «RegExp.test_ext» (.cons (.str (JSStr.ofString "^\\s*$"))
      (.cons (.str (JSStr.ofString "")) (.cons (.str s) .nil))) w.extIdx = .ok (.val (.bool false))) :
    exec (callFun I program checkedNameRef (.cons (.str s) .nil)) w =
      some (.ok (.str s.trim), { w with extIdx := w.extIdx + 1 }) := by
  ts_auto [h0]

theorem nameLength_returns (I : Impl) (s : JSStr) (w : World TT)
    (hn : w.ExtReturns «String.normalize_ext») :
    JS.Returns (callFun I program nameLengthRef (.cons (.str s) .nil)) w := by
  ts_auto

/-- Two calls (the second only when the first answers `true`). -/
theorem bothWords_noPanic (I : Impl) (a b : JSStr) (w : World TT) :
    JS.NoPanic (callFun I program bothWordsRef (.cons (.str a) (.cons (.str b) .nil))) w := by
  ts_auto

theorem bothWords_returns (I : Impl) (a b : JSStr) (w : World TT)
    (hre : w.ExtReturns «RegExp.test_ext») :
    JS.Returns (callFun I program bothWordsRef (.cons (.str a) (.cons (.str b) .nil))) w := by
  ts_auto

/-- A regex test before a loop: split on the answer, then summarize the loop. -/
theorem sumIfWord_noPanic (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (s : JSStr) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.NoPanic (callFun I program sumIfWordRef (.cons (.arr a) (.cons (.str s) .nil))) w := by
  ts_auto

theorem sumIfWord_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (s : JSStr) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hre : w.ExtReturns «RegExp.test_ext») :
    JS.Returns (callFun I program sumIfWordRef (.cons (.arr a) (.cons (.str s) .nil))) w := by
  ts_auto

/-- A regex `split`: the answer is a reference or the elements of a fresh array, which is
allocated (`exec_materializeList_ok`). -/
theorem words_returns (I : Impl) (s : JSStr) (w : World TT) (hs : w.ExtReturns «String.split_ext») :
    JS.Returns (callFun I program wordsRef (.cons (.str s) .nil)) w := by
  ts_auto
