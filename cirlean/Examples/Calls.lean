import CIR
import Examples.Gen.Calls

/-!
  Modular verification (`Examples/cpp/calls.cpp`).

  A theorem tagged `@[cir_spec]` whose statement is `Returns ctx f.sym args m
  post` is used by `cir_vcg` at every call of `f`: the precondition becomes a
  goal, and execution continues from an arbitrary result and memory
  satisfying `post` (named `cirH_post*`). The body of `f` is not executed
  again, so a caller needs no loop invariant of its callees, and proofs scale
  with the size of each function, not of its call tree.

  `Frame m m' mods` in a postcondition says which blocks of the caller the
  callee may change. Ghost values of a specification (here the current value
  `x` behind the pointer of `incr`) are found while its precondition is
  proved.

  `cir.inline false` makes the callers' proofs fail rather than fall back to
  executing a callee's body, so they are checked to be modular.
-/

open CIR Gen.Calls

set_option maxHeartbeats 4000000

namespace Examples.Calls

/-- `int twice(int x) { return x + x; }` -/
@[cir_spec]
theorem twice_spec (x : Int) (m : Mem) (h1 : -1073741824 ≤ x) (h2 : x ≤ 1073741823) :
    Returns ctx fn_twice.sym [.int x] m (fun v m' => v = some (.int (2 * x)) ∧ Frame m m' []) := by
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `int quad(int x) { return twice(twice(x)); }`, from `twice_spec`. -/
theorem quad_spec (x : Int) (m : Mem) (h1 : -536870912 ≤ x) (h2 : x ≤ 536870911) :
    Returns ctx fn_quad.sym [.int x] m (fun v _ => v = some (.int (4 * x))) := by
  cir_start
  cir_vcg

set_option maxHeartbeats 1000000 in
/-- `count_to`: the loop is verified once, here. -/
@[cir_spec]
theorem count_to_spec (n : Int) (m : Mem) (h0 : 0 ≤ n) (hn : n ≤ 2147483647) :
    Returns ctx fn_count_to.sym [.int n] m (fun v m' => v = some (.int n) ∧ Frame m m' []) := by
  cir_start
  cir_vcg
  cir_loop (fun c i => 0 ≤ i ∧ i ≤ n ∧ c = i) (fun c i => n - i)
  all_goals cir_vcg

set_option cir.inline false in
/-- `int count_plus_one(int n) { return count_to(n) + 1; }`: no invariant needed. -/
theorem count_plus_one_spec (n : Int) (m : Mem) (h0 : 0 ≤ n) (hn : n < 2147483647) :
    Returns ctx fn_count_plus_one.sym [.int n] m (fun v _ => v = some (.int (n + 1))) := by
  cir_start
  cir_vcg

/-- `void incr(int *p) { *p = *p + 1; }` changes exactly the block `b`. -/
@[cir_spec]
theorem incr_spec (b : Nat) (x : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (hp : m.blocks b = some ⟨k, true, .int true 32, .int x⟩) (hk : k ≠ .readonly)
    (h1 : -2147483648 ≤ x) (h2 : x < 2147483647) :
    Returns ctx fn_incr.sym [.ptr (.loc b [])] m (fun v m' =>
      v = none ∧ m'.blocks b = some ⟨k, true, .int true 32, .int (x + 1)⟩ ∧ Frame m m' [b]) := by
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `incr_twice`: two calls that write into the caller's local `y`. -/
theorem incr_twice_spec (x : Int) (m : Mem) (h1 : -2147483648 ≤ x) (h2 : x + 2 ≤ 2147483647) :
    Returns ctx fn_incr_twice.sym [.int x] m (fun v _ => v = some (.int (x + 2))) := by
  cir_start
  cir_vcg

end Examples.Calls
