import CIR
import Examples.Gen.ArrLoop

/-!
  Loops that write arrays (`Examples/cpp/arrloop.c`): a local array, a
  global, and a function-local static (as tiny-regex-c's `re_compile`).
  `cir_loop` names an array by its C name (a global's symbol, or the part
  after the `.` of a static's `f.name`); the binder is the array's elements,
  a `List Val`, and the loop keeps the block's kind, type and length
  (`ArrSlot`). Element facts are stated with `a[j]?`; `cir_close`
  instantiates them at the indices the code reads.
-/

open CIR Gen.ArrLoop

set_option maxHeartbeats 4000000

namespace Examples.ArrLoop

/-- `fill_local(n)`: a local array filled with `n`. -/
theorem fill_local_spec (n : Int) (m : Mem) (hn : -2147483648 ≤ n ∧ n ≤ 2147483647) :
    Returns ctx "fill_local" [.int n] m (fun r _ => r = some (.int n)) := by
  cir_start
  cir_vcg
  cir_loop (fun i a => 0 ≤ i ∧ i ≤ 8 ∧ ∀ j : Nat, j < 8 → j < i.toNat → a[j]? = some (Val.int n))
    (fun i a => 8 - i)
  all_goals cir_vcg

/-- `fill_static(k)` fills the global `table` (block 1 of this module) with `k`. -/
theorem fill_static_spec (k : Int) (vs : List Int) (kd : BlockKind) (m : Mem)
    (hk : -2147483648 ≤ k ∧ k ≤ 2147483647)
    (hb : m.blocks 1 = some ⟨kd, true, .array (.int true 32) 16, .arr (vs.map .int)⟩)
    (hkd : kd ≠ .readonly) (hn : 2 ≤ m.next) (hlen : vs.length = 16) :
    Returns ctx "fill_static" [.int k] m (fun r _ => r = some (.int k)) := by
  cir_start
  cir_vcg
  cir_loop (fun i table => 0 ≤ i ∧ i ≤ 16 ∧ ∀ j : Nat, j < 16 → j < i.toNat → table[j]? = some (Val.int k))
    (fun i table => 16 - i)
  all_goals cir_vcg

/-- `bump_all(n)` counts `i % 4` for `i < n` in its static array `counts`
(block 0); from zero counters, `counts[0]` stays within `[0, n]`. -/
theorem bump_all_spec (n : Int) (kd : BlockKind) (m : Mem) (hn0 : 0 ≤ n ∧ n ≤ 1000)
    (hb : m.blocks 0 = some ⟨kd, true, .array (.int true 32) 4, .arr (List.replicate 4 (.int 0))⟩)
    (hkd : kd ≠ .readonly) (hnx : 2 ≤ m.next) :
    Returns ctx "bump_all" [.int n] m (fun r _ => ∃ c, r = some (.int c) ∧ 0 ≤ c ∧ c ≤ n) := by
  cir_start
  cir_vcg
  cir_loop (fun i counts => 0 ≤ i ∧ i ≤ n ∧
      ∀ j : Nat, j < 4 → ∃ v, counts[j]? = some (Val.int v) ∧ 0 ≤ v ∧ v ≤ i)
    (fun i counts => n - i)
  all_goals cir_vcg

end Examples.ArrLoop
