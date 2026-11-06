import CIR
import Examples.Gen.Misc

/-!
  Assorted loop-free functions (`Examples/cpp/misc.cpp`): C++ division
  (truncating), short-circuit `&&`/`||`, `bool`-to-`int` conversions, `switch`
  with fall-through, references, multiple inheritance (a base class at a
  non-zero offset). Every proof is `cir_start; cir_vcg`.
-/

open CIR Gen.Misc

set_option maxHeartbeats 4000000

namespace Examples.Misc

/-- `arith_mix`: `/` and `%` truncate toward zero (`Int.tdiv`, `Int.tmod`). -/
theorem arith_mix_spec (a b : Int) (m : Mem)
    (ha : -100000 ≤ a ∧ a ≤ 100000) (hb : -100000 ≤ b ∧ b ≤ 100000) :
    Returns ctx fn_arith_mix.sym [.int a, .int b] m (fun v _ =>
      v = some (.int (a * 3 - b + a.tdiv 2 - b.tmod 5 + (if a > b then 7 else -7)))) := by
  cir_start
  cir_vcg

theorem ternary_chain_spec (a : Int) (m : Mem) (ha : -2147483648 ≤ a ∧ a ≤ 2147483647) :
    Returns ctx fn_ternary_chain.sym [.int a] m (fun v _ =>
      v = some (.int (if a < 0 then -1 else if a = 0 then 0 else if a < 10 then 1 else 2))) := by
  cir_start
  cir_vcg

theorem bool_logic_spec (a b : Int) (m : Mem)
    (ha : -2147483648 ≤ a ∧ a ≤ 2147483647) (hb : -2147483648 ≤ b ∧ b ≤ 2147483647) :
    Returns ctx fn_bool_logic.sym [.int a, .int b] m (fun v _ =>
      v = some (.int ((if 0 < a ∧ 0 < b then 4 else 0) + (if a < 0 ∨ b < 0 then 2 else 0) +
        (if a ≠ b then 1 else 0)))) := by
  cir_start
  cir_vcg

theorem switch_fall_spec (x : Int) (m : Mem) (hx : -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Returns ctx fn_switch_fall.sym [.int x] m (fun v _ =>
      v = some (.int (if x = 1 then 11 else if x = 2 then 10 else if x = 3 ∨ x = 4 then 100
        else if x = 7 then 1005 else 5))) := by
  cir_start
  cir_vcg

theorem refs_spec (a : Int) (m : Mem) (ha : -2147483648 ≤ a ∧ a + 6 ≤ 2147483647) :
    Returns ctx fn_refs.sym [.int a] m (fun v _ => v = some (.int (a + 6))) := by
  cir_start
  cir_vcg

theorem inherit_spec (x : Int) (m : Mem) (hx : -1000000 ≤ x ∧ x ≤ 1000000) :
    Returns ctx fn_inherit.sym [.int x] m (fun v _ => v = some (.int (301 * x + 609))) := by
  cir_start
  cir_vcg

end Examples.Misc
