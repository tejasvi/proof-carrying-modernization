/-
Bitwise loop states (`examples/Summarize/bits.ts`): the state of a table-driven hash is an
arbitrary number, so the read `table[(h ^ xs[i]) & 0xFF]` is in bounds only because the mask
leaves an index below 256. The `ts_bits` simp set (StrictTS/Proof/Bits.lean) rewrites the bitwise
operators on any operand into 32-bit operations, which decides the index and its bound inside the
loop's step.
-/
import Summarize.BitsEx
import StrictTS.Proof.Auto
import StrictTS.Proof.Bits

open StrictTS JS BitsEx

/-- With a 256-entry table, the hash never panics or throws: the masked index is always in
bounds (without `ts_bits`, the step's read is left undecided). -/
theorem tableHash_returns_auto (I : Impl) (a t : Nat) (xs tbl : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ht : w.heap.get? (.arr .num, t) = some tbl)
    (hsize : xs.size < 2 ^ 32) (htbl : tbl.size = 256) :
    JS.Returns (callFun I program tableHashRef (.cons (.arr a) (.cons (.arr t) .nil))) w := by
  ts_auto [ts_bits, htbl]
