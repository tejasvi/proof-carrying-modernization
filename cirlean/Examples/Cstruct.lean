import CIR
import Examples.Gen.Cstruct

/-!
  Loop state in a struct of the caller (`Examples/cpp/cstruct.cpp`): the
  invariant names the members `c->pos` and `c->total` as `c_0` and `c_1`
  (pointer variable, member index).
-/

open CIR Gen.Cstruct

set_option maxHeartbeats 4000000

namespace Examples.Cstruct

/-- `void advance(struct counter* c, int n)`: moves `c->pos` to `n`, adding 2
to `c->total` per step. -/
theorem advance_spec (b : Nat) (pos total n : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (hc : m.blocks b = some ⟨k, true, .record "counter", .agg [.int pos, .int total]⟩)
    (hk : k ≠ .readonly) (hpos : -2147483648 ≤ pos ∧ pos ≤ n) (hn : n ≤ 2147483647)
    (htot : -2147483648 ≤ total ∧ total + 2 * (n - pos) ≤ 2147483647) :
    Returns ctx fn_advance.sym [.ptr (.loc b []), .int n] m (fun _ m' =>
      m'.blocks b = some ⟨k, true, .record "counter", .agg [.int n, .int (total + 2 * (n - pos))]⟩) := by
  cir_start
  cir_vcg
  cir_loop (fun c_0 c_1 => pos ≤ c_0 ∧ c_0 ≤ n ∧ c_1 = total + 2 * (c_0 - pos)) (fun c_0 c_1 => n - c_0)
  all_goals cir_vcg

end Examples.Cstruct
