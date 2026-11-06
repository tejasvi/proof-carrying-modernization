import CIR
import Examples.Gen.Raii

/-!
  RAII: verified functions from `Examples/cpp/raii.cpp`.

  `Counter` increments `*count` in its constructor and decrements it in its
  destructor. ClangIR keeps the C++ scope structure: the destructor call is in
  the `cleanup` region of a `cir.cleanup.scope`, which the semantics runs on
  every exit of the body (normal exit, `return`, `break`, `continue`,
  exceptions). The proofs below show the count is restored on all paths.
-/

open CIR Gen.Raii

set_option maxHeartbeats 4000000

namespace Examples.Raii

/-- `raii_scope`: the early `return -1` and the normal `return *live` both run
`~Counter`, so the caller's count is unchanged; inside the scope it is `c + 1`. -/
theorem raii_scope_spec (bl : Nat) (c x : Int) (k : BlockKind) (m : Mem) (hbl : bl < m.next)
    (hl : m.blocks bl = some ⟨k, true, .int true 32, .int c⟩) (hk : k ≠ .readonly)
    (hc : -2147483648 ≤ c ∧ c + 1 ≤ 2147483647) (hx : -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Returns ctx fn_raii_scope.sym [.ptr (.loc bl []), .int x] m (fun v m' =>
      v = some (.int (if x < 0 then -1 else c + 1)) ∧
        m'.blocks bl = some ⟨k, true, .int true 32, .int c⟩) := by
  cir_start
  cir_vcg

/-- `raii_loop`: one `Counter` per iteration; `break` (at `i == 5`) and
`continue` (odd `i`) both leave the iteration's cleanup scope through
`~Counter`. Starting from a count of 0, the loop adds the live count (1) for
every even `i < min n 5`, and the count is 0 again at the end. -/
theorem raii_loop_spec (bl : Nat) (n : Int) (k : BlockKind) (m : Mem) (hbl : bl < m.next)
    (hl : m.blocks bl = some ⟨k, true, .int true 32, .int 0⟩) (hk : k ≠ .readonly)
    (hn : 0 ≤ n ∧ n ≤ 2147483647) :
    Returns ctx fn_raii_loop.sym [.ptr (.loc bl []), .int n] m (fun v m' =>
      v = some (.int ((min n 5 + 1) / 2)) ∧
        m'.blocks bl = some ⟨k, true, .int true 32, .int 0⟩) := by
  cir_start
  cir_vcg
  cir_loop (fun s i => 0 ≤ i ∧ i ≤ n ∧ i ≤ 5 ∧ s = (i + 1) / 2) (fun s i => n - i)
  all_goals cir_vcg

end Examples.Raii
