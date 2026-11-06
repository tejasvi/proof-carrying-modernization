import CIR
import Examples.Gen.Vectors

/-!
  Verified `std::vector` functions from `Examples/cpp/vectors.cpp`.

  Calls to `std::vector<int>` members are executed by the native Lean models
  (`CIR.Std.runModel`): the vector argument is a block holding
  `Val.vec g (xs.map Val.int)`.
-/

open CIR Gen.Vectors

namespace Examples.Vectors

set_option maxHeartbeats 4000000 in
/-- `int vsum(const std::vector<int>& v)`: index loop with `v.size()` / `v[i]`.
The index is a `size_t`, so the invariant names it as a `Nat`. -/
theorem vsum_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hsum : Lib.PrefixSumsIn (-2147483648) 2147483647 xs) :
    Returns ctx fn_vsum.sym [.ptr (.loc bv [])] m (fun r _ => r = some (.int xs.sum)) := by
  have := hsum.succNat
  cir_start
  cir_vcg
  cir_loop (fun s i => i ≤ xs.length ∧ s = (xs.take i).sum) (fun s i => xs.length - i)
  all_goals cir_vcg

set_option maxHeartbeats 4000000 in
/-- `int vsum_range(const std::vector<int>& v)`: range-`for`. The binder `it`
is the position of the hidden iterator (an element index). -/
theorem vsum_range_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hsum : Lib.PrefixSumsIn (-2147483648) 2147483647 xs) :
    Returns ctx fn_vsum_range.sym [.ptr (.loc bv [])] m (fun r _ => r = some (.int xs.sum)) := by
  have := hsum.succNat
  cir_start
  cir_vcg
  cir_loop (fun s it => it ≤ xs.length ∧ s = (xs.take it).sum) (fun s it => xs.length - it)
  all_goals cir_vcg

set_option maxHeartbeats 4000000 in
/-- `int count_eq(const std::vector<int>& v, int key)`: a branch in the loop. -/
theorem count_eq_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (key : Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 31)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hkey : -2147483648 ≤ key ∧ key ≤ 2147483647) :
    Returns ctx fn_count_eq.sym [.ptr (.loc bv []), .int key] m
      (fun r _ => r = some (.int (xs.count key))) := by
  cir_start
  cir_vcg
  cir_loop (fun c i => i ≤ xs.length ∧ c = (xs.take i).count key) (fun c i => xs.length - i)
  all_goals cir_vcg

set_option maxHeartbeats 4000000 in
/-- `std::optional<int> find_index(const std::vector<int>& v, int key)`:
early return from the loop, `std::optional` / `std::nullopt` results. -/
theorem find_index_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (key : Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 31)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hkey : -2147483648 ≤ key ∧ key ≤ 2147483647) :
    Returns ctx fn_find_index.sym [.ptr (.loc bv []), .int key] m
      (fun r _ => r = some (.opt ((xs.findIdx? (· == key)).map fun (i : Nat) => .int (i : Int)))) := by
  cir_start
  cir_vcg
  cir_loop (fun i => i ≤ xs.length ∧ Lib.NoneBefore xs key i) (fun i => xs.length - i)
  all_goals cir_vcg

set_option maxHeartbeats 4000000 in
/-- `void fill_iota(std::vector<int>& out, int n)`: `clear`, then `push_back`
in a loop. The binder `out` (the reference parameter) stands for the elements
of the caller's vector; each `push_back` installs a new generation. -/
theorem fill_iota_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (n : Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hk : k ≠ .readonly) (hn : 0 ≤ n ∧ n ≤ 2147483647) :
    Returns ctx fn_fill_iota.sym [.ptr (.loc bv []), .int n] m (fun v m' =>
      v = none ∧ ∃ g', m'.blocks bv = some ⟨k, true, ty, .vec g' ((Lib.iotaInt n.toNat).map .int)⟩) := by
  cir_start
  cir_vcg
  cir_loop (fun i out => 0 ≤ i ∧ i ≤ n ∧ out = Lib.iotaInt i.toNat) (fun i out => n - i)
  all_goals cir_vcg

end Examples.Vectors
