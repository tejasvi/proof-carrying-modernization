/-
`for … of` loops over a `Map`, a `Set` and a string (`examples/Summarize/iterables.ts`):
`ts_summarize` turns each into a fold over the live entries `m.toList` (insertion order), the
set's elements, or the string's code points.
-/
import Summarize.IterEx
import StrictTS.Proof.Summarize

open StrictTS JS IterEx

/-- Summing a map's values is the fold over its entries in insertion order. -/
theorem sumValues_eq (I : Impl) (a : Nat) (m : JSMap (Val TT .str) (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.map .str .num, a) = some m) :
    exec (callFun I program sumValuesRef (.cons (.map a) .nil)) w =
      some (.ok (m.toList.foldl (fun s kv => .num (s.toNum + kv.2.toNum)) (.num 0)), w) := by
  rw [sumValues_call]
  simp only [sumValuesDef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- Counting a set's positive elements never faults: the loop is a fold over the elements. -/
theorem countPositiveIn_returns (I : Impl) (a : Nat) (m : JSMap (Val TT .num) Unit) (w : World TT)
    (hw : w.heap.get? (.set .num, a) = some m) :
    ∃ v, exec (callFun I program countPositiveInRef (.cons (.set a) .nil)) w = some (.ok v, w) := by
  rw [countPositiveIn_call]
  simp only [countPositiveInDef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- A loop over the code points of a string. -/
theorem countA_returns (I : Impl) (s : JSStr) (w : World TT) :
    ∃ v, exec (callFun I program countARef (.cons (.str s) .nil)) w = some (.ok v, w) := by
  rw [countA_call]
  simp only [countADef, ts_sym]
  ts_summarize
  simp [ts_sym]

/-- A loop over a map that pushes into a fresh array (one cell written). -/
theorem keysOf_returns (I : Impl) (a : Nat) (m : JSMap (Val TT .str) (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.map .str .num, a) = some m) :
    ∃ v w', exec (callFun I program keysOfRef (.cons (.map a) .nil)) w = some (.ok v, w') := by
  rw [keysOf_call]
  simp only [keysOfDef, ts_sym]
  ts_summarize
  simp [ts_sym]
