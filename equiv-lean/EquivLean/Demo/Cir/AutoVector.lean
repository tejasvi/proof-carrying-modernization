import EquivLean.Bridge.Cir.AutoCouple
import EquivLean.Demo.Gen.Cir.VOld
import EquivLean.Demo.Gen.Cir.VNew

/-!
# Demo: the `std::vector` refactor of `VectorLoop.lean` with NO coupling written

`examples/cir/v_old.cpp` (index loop `for (std::size_t i = 0; i < v.size(); ++i) s += v[i];`)
against `v_new.cpp` (range-`for` `for (int x : v) s += x;`), as in `VectorLoop.lean`, which
writes the coupling `s = s' ∧ it = i' ∧ it ≤ xs.length`.  Here plain `cir_sim_loop_auto` /
`equiv_cir` generate it (`Bridge/Cir/AutoCouple.lean`): the range-`for` iterator is paired with
the `size_t` index (both element positions), and the position is bounded by the length of the
caller's vector, read off the hypothesis `hv`.
-/

namespace EquivLean.Demo.Cir.AutoVector

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

/-- new ⊑ old, no coupling written. -/
theorem vsum_sim_auto (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Sim (ObsEq m) (evalCall VNew.ctx VNew.fn_vsum.sym [.ptr (.loc bv [])] m)
      (evalCall VOld.ctx VOld.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  cir_sim_loop_auto

/-- old ⊑ new, no coupling written. -/
theorem vsum_sim_rev_auto (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Sim (ObsEq m) (evalCall VOld.ctx VOld.fn_vsum.sym [.ptr (.loc bv [])] m)
      (evalCall VNew.ctx VNew.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  cir_sim_loop_auto

-- both directions in one declaration: on cirlean bd8614f (heavier `cir_disch`) past 4M heartbeats
set_option maxHeartbeats 12000000 in
/-- **The vector refactor, both directions, with plain `equiv_cir`.** -/
theorem vsum_equiv_auto (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647) :
    Equiv (ObsEq m) (evalCall VNew.ctx VNew.fn_vsum.sym [.ptr (.loc bv [])] m)
      (evalCall VOld.ctx VOld.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  equiv_cir

end EquivLean.Demo.Cir.AutoVector

#print axioms EquivLean.Demo.Cir.AutoVector.vsum_equiv_auto
