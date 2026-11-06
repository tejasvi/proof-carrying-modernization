/-
The theorems of `AutoProofs.lean`, each proved by `ts_auto` alone (no invariant, no callback
meaning, no argument).
-/
import Summarize.LoopsEx
import StrictTS.Proof.Auto

open StrictTS JS LoopsEx

/-- A loop with a conditional update equals a `reduce` with a ternary, on every array and every
world (NaN and ±0 included: both are the same IEEE fold). -/
theorem maxOf_eq_maxOfReduce_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program maxOfRef (.cons (.arr a) .nil)) w =
      exec (callFun I program maxOfReduceRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- The meaning of a loop with `continue`, computed rather than written. -/
theorem countPositive_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program countPositiveRef (.cons (.arr a) .nil)) w =
      some (.ok (xs.toList.foldl (fun n x => if x.toNum.le 0 = true then n else .num (n.toNum + 1)) (.num 0)),
        w) := by
  ts_auto

/-- A loop updating two variables: never panics or throws, for every array and world. -/
theorem range_returns_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program rangeRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A loop over strings with a boolean flag: never panics or throws. -/
theorem joinWords_returns_auto (I : Impl) (a : Nat) (ws : Array (Val TT .str)) (w : World TT)
    (hw : w.heap.get? (.arr .str, a) = some ws) :
    JS.Returns (callFun I program joinWordsRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A push loop is `filter` (both allocate one array, at the same address, with the same
contents). -/
theorem positives_eq_positivesFilter_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    exec (callFun I program positivesRef (.cons (.arr a) .nil)) w =
      exec (callFun I program positivesFilterRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A flag loop is `some`. -/
theorem hasNegative_eq_hasNegativeSome_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program hasNegativeRef (.cons (.arr a) .nil)) w =
      exec (callFun I program hasNegativeSomeRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A flag loop with a negated test is `every` (`!(x > 0)` is exact: it holds for NaN). -/
theorem allPositive_eq_allPositiveEvery_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program allPositiveRef (.cons (.arr a) .nil)) w =
      exec (callFun I program allPositiveEveryRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- `find` is `Array.find?` of the callback's meaning (`undefined` when absent). -/
theorem firstNegative_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program firstNegativeRef (.cons (.arr a) .nil)) w =
      some (.ok ((xs.find? (fun x => x.toNum.lt 0)).elim .none .some), w) := by
  ts_auto

/-- `findIndex` is `Array.findIdx?` as a JavaScript number (`-1` when absent). -/
theorem firstNegativeIndex_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program firstNegativeIndexRef (.cons (.arr a) .nil)) w =
      some (.ok ((xs.findIdx? (fun x => x.toNum.lt 0)).elim (.num (F64.ofInt (-1))) num), w) := by
  ts_auto

/-- `findLast` searches the reversed array. -/
theorem lastNegative_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program lastNegativeRef (.cons (.arr a) .nil)) w =
      some (.ok ((xs.reverse.find? (fun x => x.toNum.lt 0)).elim .none .some), w) := by
  ts_auto

/-- `findLastIndex` is the position, counted from the start, of the last element that passes. -/
theorem lastNegativeIndex_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program lastNegativeIndexRef (.cons (.arr a) .nil)) w =
      some (.ok (((xs.reverse.findIdx? (fun x => x.toNum.lt 0)).map (fun j => xs.size - 1 - j)).elim
        (.num (F64.ofInt (-1))) num), w) := by
  ts_auto

/-- `forEach` with a callback that has no effect changes nothing. -/
theorem touchAll_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program touchAllRef (.cons (.arr a) .nil)) w = some (.ok .undef, w) := by
  ts_auto

/-- `sort` with a pure comparator sorts the array in place by `sortBy`, the merge sort of
`sortL` as a pure function (a permutation; sorted when the comparator is a total preorder). -/
theorem sortAsc_eq_auto (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sortAscRef (.cons (.arr a) .nil)) w =
      some (.ok (.arr a), { w with
        heap := w.heap.insert (.arr .num, a) (sortBy (fun x y => !Conv.isPos (x.toNum - y.toNum)) xs.toList).toArray }) := by
  ts_auto
