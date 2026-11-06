import EquivLean.Bridge.Cir.Tactic
import EquivLean.Demo.Gen.Cir.VOld
import EquivLean.Demo.Gen.Cir.VNew

/-!
# Demo (b3): `std::vector` index loop refactored into a range-`for`

`examples/cir/v_old.cpp` → `v_new.cpp` (translated by clang -fclangir and cir2lean, with
libc++ headers, into `EquivLean.Demo.Gen.Cir.VOld` / `VNew`):

```cpp
// old                                              // new
int vsum(const std::vector<int> &v) {               int vsum(const std::vector<int> &v) {
  int s = 0;                                          int s = 0;
  for (std::size_t i = 0; i < v.size(); ++i)          for (int x : v) s += x;
    s += v[i];                                        return s;
  return s;                                         }
}
```

`v.size()`, `v[i]`, `begin`/`end` and the iterator operations run against cirlean's library
models.  The loops are paired in lockstep: the old version's `size_t` index `i` (a `Nat`)
moves with the new version's hidden iterator (`it`, its element index), and the sums agree.
The vector is any caller block holding `int`s; no assumption on the sums is needed: both
versions overflow (undefined behaviour) at the same element.
-/

namespace EquivLean.Demo.Cir.VectorLoop

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

/-- new ⊑ old (binders: `s`, `it` the new version's sum and iterator position, `s' i'` the
old version's sum and index). -/
theorem vsum_sim (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Sim (ObsEq m) (evalCall VNew.ctx VNew.fn_vsum.sym [.ptr (.loc bv [])] m)
      (evalCall VOld.ctx VOld.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  cir_sim_loop (fun s it s' i' => s = s' ∧ it = i' ∧ it ≤ xs.length)

/-- old ⊑ new. -/
theorem vsum_sim_rev (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Sim (ObsEq m) (evalCall VOld.ctx VOld.fn_vsum.sym [.ptr (.loc bv [])] m)
      (evalCall VNew.ctx VNew.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  cir_sim_loop (fun s i s' it' => s = s' ∧ i = it' ∧ i ≤ xs.length)

theorem vsum_equiv (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Equiv (ObsEq m) (evalCall VNew.ctx VNew.fn_vsum.sym [.ptr (.loc bv [])] m)
      (evalCall VOld.ctx VOld.fn_vsum.sym [.ptr (.loc bv [])] m) :=
  ⟨vsum_sim bv g k ty xs m hv hbv hlen hxs,
   by rw [obsEq_flip]; exact vsum_sim_rev bv g k ty xs m hv hbv hlen hxs⟩

end EquivLean.Demo.Cir.VectorLoop
