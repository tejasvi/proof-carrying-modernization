import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.FindPR.Funs

/-!
# An early-exit refactoring on real Charon + Aeneas output

`examples/rust/findpr/src/lib.rs`: `v1::find` loops `while i < len && v[i] != x` and returns
`i`; the PR (`v2::find`) returns from inside the loop when `v[i] == x` and returns `v.len()`
after it.  The two loops leave at the same iteration with the same result, so they are paired in
lockstep; the exits through `return` (Aeneas `done` inside the body) and through the loop
condition are matched by the loop rule (`StepRel`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.FindPR

theorem find_v2_equiv_v1 (v : Slice U32) (x : U32) :
    Equiv (· = ·) (findpr.v2.find v x) (findpr.v1.find v x) := by
  equiv_aeneas [findpr.v2.find, findpr.v1.find, findpr.v2.find_loop, findpr.v1.find_loop,
      findpr.v2.find_loop.body, findpr.v1.find_loop.body]
    using fun i j => i = j ∧ i.val ≤ v.val.length

end EquivLean.Demo.Aeneas.FindPR

#print axioms EquivLean.Demo.Aeneas.FindPR.find_v2_equiv_v1
