import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.VecPR.Funs

/-!
# A strength-reduction PR on vectors (real Charon + Aeneas output)

`examples/rust/vecpr/src/lib.rs`: `v1::squares n` pushes `(i as u64) * (i as u64)` for
`i < n`; the PR (`v2::squares`) preallocates the vector and maintains the square incrementally
(`sq = sq + 2 * i + 1`).  Both build the same `Vec<u64>` and panic in the same cases (only
`push` can fail, on the same vector).  Lockstep with the coupling invariant "same vector, same
`i`, `sq = i * i`, `i ≤ n`"; the overflow side conditions are non-linear (`scalar_tac +nonLin`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.VecPR

theorem squares_v2_equiv_v1 (n : U32) :
    Equiv (· = ·) (vecpr.v2.squares n) (vecpr.v1.squares n) := by
  equiv_aeneas [vecpr.v2.squares, vecpr.v1.squares, vecpr.v2.squares_loop,
      vecpr.v1.squares_loop, vecpr.v2.squares_loop.body, vecpr.v1.squares_loop.body,
      lift, bind_ok, alloc.vec.Vec.with_capacity]
    using fun p q => p.1 = q.1 ∧ p.2.1 = q.2 ∧ p.2.2.val = q.2.val * q.2.val ∧ q.2.val ≤ n.val

end EquivLean.Demo.Aeneas.VecPR

#print axioms EquivLean.Demo.Aeneas.VecPR.squares_v2_equiv_v1
