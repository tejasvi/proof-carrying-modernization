/-
Counted loops (`for (let i = 0; i < xs.length; i++)`) on translator output
(`examples/Summarize/counted.ts`): `ts_summarize` turns a counted loop into a fold over the
positions; when the body reads the array only at the counter, into the fold over the elements
that a `for … of` loop has, so the index loop, the `for … of` loop and the array method are
proved equal by the same five lines. The hypothesis `xs.size < 2^32` makes the counter a valid
array index (JavaScript arrays are shorter). A body that calls another function needs the callee's
contract: `ts_summarize [contract]`, `ts_callbacks [contract]`.
-/
import Summarize.CountedEx
import StrictTS.Proof.Summarize
import StrictTS.Proof.Contract

open StrictTS JS CountedEx

/-- An index loop sums like the `for … of` loop. -/
theorem sumIdx_eq_sumOf (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hsize : xs.size < 2 ^ 32) :
    exec (callFun I program sumIdxRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumOfRef (.cons (.arr a) .nil)) w := by
  rw [sumIdx_call, sumOf_call]
  simp only [sumIdxDef, sumOfDef, ts_sym]
  ts_summarize
  ts_summarize
  simp [ts_sym]

/-- An index loop sums like `reduce`. -/
theorem sumIdx_eq_sumReduce (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hsize : xs.size < 2 ^ 32) :
    exec (callFun I program sumIdxRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumReduceRef (.cons (.arr a) .nil)) w := by
  rw [sumIdx_call, sumReduce_call]
  simp only [sumIdxDef, sumReduceDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

/-- An index loop that pushes into a fresh array is `map` (both allocate one array, at the
same address, with the same contents). -/
theorem doubleIdx_eq_doubleMap (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hsize : xs.size < 2 ^ 32) (ha : a < w.next) :
    exec (callFun I program doubleIdxRef (.cons (.arr a) .nil)) w =
      exec (callFun I program doubleMapRef (.cons (.arr a) .nil)) w := by
  rw [doubleIdx_call, doubleMap_call]
  simp only [doubleIdxDef, doubleMapDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

/-- A loop with a constant bound and the counter in the body: the fold over the positions,
computed. -/
theorem sumBelow10_eq (I : Impl) (w : World TT) :
    exec (callFun I program sumBelow10Ref .nil) w = some (.ok (.num 45), w) := by
  rw [sumBelow10_call]
  simp only [sumBelow10Def, ts_sym]
  ts_summarize
  simp [ts_sym]
  rfl

/-- The contract of a callee. -/
theorem square_spec (I : Impl) (v : Val TT .num) (w : World TT) :
    exec (callFun I program squareRef (.cons v .nil)) w = some (.ok (.num (v.toNum * v.toNum)), w) := by
  rw [square_call]
  simp [squareDef, ts_sym]

/-- Loops whose bodies call another function: `ts_summarize [contract]` uses the callee's
contract in the symbolic execution of the body. -/
theorem sumSquaresIdx_eq_sumSquares (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hsize : xs.size < 2 ^ 32) :
    exec (callFun I program sumSquaresIdxRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumSquaresRef (.cons (.arr a) .nil)) w := by
  have hsq := square_spec I
  rw [sumSquaresIdx_call, sumSquares_call]
  simp only [sumSquaresIdxDef, sumSquaresDef, ts_sym]
  ts_summarize [hsq]
  ts_summarize [hsq]
  simp [ts_sym]

/-- A callback that calls another function: `ts_callbacks [contract]`. -/
theorem sumSquares_eq_sumSquaresReduce (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sumSquaresRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumSquaresReduceRef (.cons (.arr a) .nil)) w := by
  have hsq := square_spec I
  rw [sumSquares_call, sumSquaresReduce_call]
  simp only [sumSquaresDef, sumSquaresReduceDef, ts_sym]
  ts_summarize [hsq]
  ts_callbacks [hsq]
  simp [ts_sym]
