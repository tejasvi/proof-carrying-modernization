import CIR
import Examples.Gen.Carray

/-!
  C-style arrays (`Examples/cpp/carray.cpp`): `a[i]` is pointer arithmetic
  with a variable offset into an array block; `goto found` leaves the loop to
  a label later in the function.
-/

open CIR Gen.Carray

set_option maxHeartbeats 4000000

namespace Examples.Carray

/-- `int sum_arr(const int* a, int n)` over the first `n` elements of an
array `xs`. -/
theorem sum_arr_spec (b : Nat) (xs : List Int) (n : Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩) (hb : b < m.next)
    (hn : 0 ≤ n ∧ n ≤ xs.length) (hlen : xs.length < 2 ^ 31)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hsum : Lib.PrefixSumsIn (-2147483648) 2147483647 xs)
    (hty : ∃ es tlen, ty = .array (.int es 32) tlen) :
    Returns ctx fn_sum_arr.sym [.ptr (.loc b [.idx 0]), .int n] m
      (fun r _ => r = some (.int (xs.take n.toNat).sum)) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  have := hsum.succ
  cir_start
  cir_vcg
  cir_loop (fun s i => 0 ≤ i ∧ i ≤ n ∧ s = (xs.take i.toNat).sum) (fun s i => n - i)
  all_goals cir_vcg

/-- `int find_first(const int* a, int n, int key)`: the loop leaves with
`goto found` at the first match. -/
theorem find_first_spec (b : Nat) (xs : List Int) (n key : Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩) (hb : b < m.next)
    (hn : 0 ≤ n ∧ n ≤ xs.length) (hlen : xs.length < 2 ^ 31)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hkey : -2147483648 ≤ key ∧ key ≤ 2147483647)
    (hty : ∃ es tlen, ty = .array (.int es 32) tlen) :
    Returns ctx fn_find_first.sym [.ptr (.loc b [.idx 0]), .int n, .int key] m
      (fun v _ => ∃ r, v = some (.int r) ∧ -1 ≤ r ∧ r < n ∧ (0 ≤ r → xs[r.toNat]? = some key)) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun i => 0 ≤ i ∧ i ≤ n) (fun i => n - i)
  all_goals cir_vcg

end Examples.Carray
