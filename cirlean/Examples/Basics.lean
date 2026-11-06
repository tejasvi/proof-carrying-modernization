import CIR
import Examples.Gen.Basics

/-!
  Verified functions from `Examples/cpp/basics.cpp`.

  `Examples/Gen/Basics.lean` is generated from the ClangIR of that file by
  `cir2lean`. Each theorem states total correctness: the call terminates,
  has no undefined behaviour (no signed overflow, no invalid memory access,
  no use of an indeterminate value, ...) and satisfies the postcondition.
-/

open CIR Gen.Basics

set_option maxHeartbeats 4000000

namespace Examples.Basics

/-- `int add3(int a) { return a + 3; }` -/
theorem add3_spec (a : Int) (m : Mem) (h1 : -2147483648 ≤ a) (h2 : a + 3 ≤ 2147483647) :
    Returns ctx fn_add3.sym [.int a] m (fun v _ => v = some (.int (a + 3))) := by
  cir_start
  cir_vcg

/-- `int max2(int a, int b) { return a > b ? a : b; }` -/
theorem max2_spec (a b : Int) (m : Mem)
    (ha : -2147483648 ≤ a ∧ a ≤ 2147483647) (hb : -2147483648 ≤ b ∧ b ≤ 2147483647) :
    Returns ctx fn_max2.sym [.int a, .int b] m (fun v _ => v = some (.int (max a b))) := by
  cir_start
  cir_vcg

/-- `int abs_val(int x) { if (x < 0) return -x; return x; }` -/
theorem abs_val_spec (x : Int) (m : Mem) (h1 : -2147483648 < x) (h2 : x ≤ 2147483647) :
    Returns ctx fn_abs_val.sym [.int x] m (fun v _ => v = some (.int x.natAbs)) := by
  cir_start
  cir_vcg

set_option maxHeartbeats 1000000 in
/-- `int count_up(int n) { int c = 0; for (int i = 0; i < n; ++i) c += 2; return c; }` -/
theorem count_up_spec (n : Int) (m : Mem) (h0 : 0 ≤ n) (hn : 2 * n ≤ 2147483647) :
    Returns ctx fn_count_up.sym [.int n] m (fun v _ => v = some (.int (2 * n))) := by
  cir_start
  cir_vcg
  cir_loop (fun c i => 0 ≤ i ∧ i ≤ n ∧ c = 2 * i) (fun c i => n - i)
  all_goals cir_vcg

/-- `int countdown(int n) { int steps = 0; while (n > 0) { n = n - 1; steps = steps + 1; } return steps; }` -/
theorem countdown_spec (n0 : Int) (m : Mem) (h0 : 0 ≤ n0) (hn : n0 ≤ 2147483647) :
    Returns ctx fn_countdown.sym [.int n0] m (fun v _ => v = some (.int n0)) := by
  cir_start
  cir_vcg
  cir_loop (fun n steps => 0 ≤ n ∧ n + steps = n0) (fun n steps => n)
  all_goals cir_vcg

/-- `void swap_ints(int *a, int *b) { int t = *a; *a = *b; *b = t; }`
on two distinct live `int` objects of the caller. -/
theorem swap_ints_spec (ba bb : Nat) (x y : Int) (ka kb : BlockKind) (m : Mem)
    (hab : ba ≠ bb) (hba : ba < m.next) (hbb : bb < m.next)
    (ha : m.blocks ba = some ⟨ka, true, .int true 32, .int x⟩)
    (hb : m.blocks bb = some ⟨kb, true, .int true 32, .int y⟩)
    (hka : ka ≠ .readonly) (hkb : kb ≠ .readonly)
    (hx : -2147483648 ≤ x ∧ x ≤ 2147483647) (hy : -2147483648 ≤ y ∧ y ≤ 2147483647) :
    Returns ctx fn_swap_ints.sym [.ptr (.loc ba []), .ptr (.loc bb [])] m (fun v m' =>
      v = none ∧ m'.blocks ba = some ⟨ka, true, .int true 32, .int y⟩ ∧
        m'.blocks bb = some ⟨kb, true, .int true 32, .int x⟩) := by
  cir_start
  cir_vcg

/-- `int manhattan(const Point &p)`: reads both members of a struct through a reference. -/
theorem manhattan_spec (bp : Nat) (x y : Int) (k : BlockKind) (m : Mem) (hbp : bp < m.next)
    (hp : m.blocks bp = some ⟨k, true, .record "Point", .agg [.int x, .int y]⟩)
    (hx : -2147483648 < x ∧ x ≤ 2147483647) (hy : -2147483648 < y ∧ y ≤ 2147483647)
    (hsum : x.natAbs + y.natAbs ≤ 2147483647) :
    Returns ctx fn_manhattan.sym [.ptr (.loc bp [])] m (fun v _ => v = some (.int (x.natAbs + y.natAbs))) := by
  cir_start
  cir_vcg

end Examples.Basics
