/-
Invariant-free proofs on translator output (`examples/Summarize/loops.ts`): `ts_summarize`
turns each `for … of` loop into the left fold of its body's effect, and `ts_callbacks` turns
`reduce`/`map`/`filter`/`some`/`every`/`find`/`findIndex`/`findLast`/`findLastIndex`/`forEach`/`sort`
into the standard functions of their callbacks' meanings, both computed by symbolic execution;
the fold lemmas of `StrictTS.Proof.Arrays` (`foldl_push_filter`, `foldl_flag_true`, …) identify
the loops' folds with those functions. Every proof below is the same few lines.
-/
import Summarize.LoopsEx
import StrictTS.Proof.Summarize
import StrictTS.Proof.Contract

open StrictTS JS LoopsEx

/-- A loop with a conditional update equals a `reduce` with a ternary, on every array and every
world (NaN and ±0 included: both are the same IEEE fold). -/
theorem maxOf_eq_maxOfReduce (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program maxOfRef (.cons (.arr a) .nil)) w =
      exec (callFun I program maxOfReduceRef (.cons (.arr a) .nil)) w := by
  rw [maxOf_call, maxOfReduce_call]
  simp only [maxOfDef, maxOfReduceDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

/-- The meaning of a loop with `continue`, computed rather than written. -/
theorem countPositive_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program countPositiveRef (.cons (.arr a) .nil)) w =
      some (.ok (xs.toList.foldl (fun n x => if x.toNum.le 0 = true then n else .num (n.toNum + 1)) (.num 0)),
        w) := by
  rw [countPositive_call]
  simp only [countPositiveDef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- A loop updating two variables: never panics or throws, for every array and world. -/
theorem range_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program rangeRef (.cons (.arr a) .nil)) w := by
  unfold JS.Returns
  rw [range_call]
  simp only [rangeDef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- A loop over strings with a boolean flag: never panics or throws. -/
theorem joinWords_returns (I : Impl) (a : Nat) (ws : Array (Val TT .str)) (w : World TT)
    (hw : w.heap.get? (.arr .str, a) = some ws) :
    JS.Returns (callFun I program joinWordsRef (.cons (.arr a) .nil)) w := by
  unfold JS.Returns
  rw [joinWords_call]
  simp only [joinWordsDef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- A push loop is `filter` (both allocate one array, at the same address, with the same
contents). -/
theorem positives_eq_positivesFilter (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    exec (callFun I program positivesRef (.cons (.arr a) .nil)) w =
      exec (callFun I program positivesFilterRef (.cons (.arr a) .nil)) w := by
  rw [positives_call, positivesFilter_call]
  simp only [positivesDef, positivesFilterDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

/-- A flag loop is `some`. -/
theorem hasNegative_eq_hasNegativeSome (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program hasNegativeRef (.cons (.arr a) .nil)) w =
      exec (callFun I program hasNegativeSomeRef (.cons (.arr a) .nil)) w := by
  rw [hasNegative_call, hasNegativeSome_call]
  simp only [hasNegativeDef, hasNegativeSomeDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

/-- A flag loop with a negated test is `every` (`!(x > 0)` is exact: it holds for NaN). -/
theorem allPositive_eq_allPositiveEvery (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program allPositiveRef (.cons (.arr a) .nil)) w =
      exec (callFun I program allPositiveEveryRef (.cons (.arr a) .nil)) w := by
  rw [allPositive_call, allPositiveEvery_call]
  simp only [allPositiveDef, allPositiveEveryDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

/-- `find` is `Array.find?` of the callback's meaning (`undefined` when absent). -/
theorem firstNegative_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program firstNegativeRef (.cons (.arr a) .nil)) w =
      some (.ok ((xs.find? (fun x => x.toNum.lt 0)).elim .none .some), w) := by
  rw [firstNegative_call]
  simp only [firstNegativeDef, ts_sym]
  ts_callbacks
  simp [ts_sym]

/-- `findIndex` is `Array.findIdx?` as a JavaScript number (`-1` when absent). -/
theorem firstNegativeIndex_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program firstNegativeIndexRef (.cons (.arr a) .nil)) w =
      some (.ok ((xs.findIdx? (fun x => x.toNum.lt 0)).elim (.num (F64.ofInt (-1))) num), w) := by
  rw [firstNegativeIndex_call]
  simp only [firstNegativeIndexDef, ts_sym]
  ts_callbacks
  simp [ts_sym]

/-- `findLast` searches the reversed array. -/
theorem lastNegative_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program lastNegativeRef (.cons (.arr a) .nil)) w =
      some (.ok ((xs.reverse.find? (fun x => x.toNum.lt 0)).elim .none .some), w) := by
  rw [lastNegative_call]
  simp only [lastNegativeDef, ts_sym]
  ts_callbacks
  simp [ts_sym]

/-- `findLastIndex` is the position, counted from the start, of the last element that passes. -/
theorem lastNegativeIndex_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program lastNegativeIndexRef (.cons (.arr a) .nil)) w =
      some (.ok (((xs.reverse.findIdx? (fun x => x.toNum.lt 0)).map (fun j => xs.size - 1 - j)).elim
        (.num (F64.ofInt (-1))) num), w) := by
  rw [lastNegativeIndex_call]
  simp only [lastNegativeIndexDef, ts_sym]
  ts_callbacks
  simp [ts_sym]

/-- `forEach` with a callback that has no effect changes nothing. -/
theorem touchAll_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program touchAllRef (.cons (.arr a) .nil)) w = some (.ok .undef, w) := by
  rw [touchAll_call]
  simp only [touchAllDef, ts_sym]
  ts_callbacks
  simp [ts_sym]

/-- `sort` with a pure comparator sorts the array in place by `sortBy`, the merge sort of
`sortL` as a pure function (a permutation; sorted when the comparator is a total preorder). -/
theorem sortAsc_eq (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sortAscRef (.cons (.arr a) .nil)) w =
      some (.ok (.arr a), { w with
        heap := w.heap.insert (.arr .num, a) (sortBy (fun x y => !Conv.isPos (x.toNum - y.toNum)) xs.toList).toArray }) := by
  rw [sortAsc_call]
  simp only [sortAscDef, ts_sym]
  ts_callbacks
  simp [ts_sym]
