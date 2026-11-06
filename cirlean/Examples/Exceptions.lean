import CIR
import Examples.Gen.Exceptions

/-!
  Exceptions (`Examples/cpp/exceptions.cpp`).

  `std::vector::at` throws `std::out_of_range` (library model); `cir.try`
  enters the handler whose type matches; on the way out of the `try` scope,
  the destructor of the RAII guard runs (`cir.cleanup.scope` with an `eh`
  cleanup). Both functions are verified on both paths with no proof steps
  beyond `cir_start; cir_vcg`.
-/

open CIR Gen.Exceptions

set_option maxHeartbeats 4000000

namespace Examples.Exceptions

/-- `int safe_get(const std::vector<int>& v, size_t i)`: `v.at(i)`, or `-1`
when `at` throws. -/
theorem safe_get_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (i : Nat) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hi : i < 2 ^ 64) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Returns ctx fn_safe_get.sym [.ptr (.loc bv []), .int i] m
      (fun r _ => r = some (.int (if h : i < xs.length then xs[i] else -1))) := by
  cir_start
  cir_vcg

/-- `int guarded_get(int* live, const std::vector<int>& v, size_t i)`: a guard
increments `*live` for the duration of the `try` block; when `at` throws,
its destructor runs before the handler, which sees the restored count. -/
theorem guarded_get_spec (bl bv g : Nat) (c : Int) (kl k : BlockKind) (ty : Ty) (xs : List Int)
    (i : Nat) (m : Mem) (hlv : bl ≠ bv)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, .int c⟩) (hbl : bl < m.next) (hkl : kl ≠ .readonly)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hi : i < 2 ^ 64) (hc : -2147483648 ≤ c ∧ c < 2147483647)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hfit : ∀ (h : i < xs.length), -2147483648 ≤ xs[i] + (c + 1) ∧ xs[i] + (c + 1) ≤ 2147483647) :
    Returns ctx fn_guarded_get.sym [.ptr (.loc bl []), .ptr (.loc bv []), .int i] m
      (fun r m' => r = some (.int (if h : i < xs.length then xs[i] + (c + 1) else c)) ∧
        m'.blocks bl = some ⟨kl, true, .int true 32, .int c⟩) := by
  cir_start
  cir_vcg

end Examples.Exceptions
