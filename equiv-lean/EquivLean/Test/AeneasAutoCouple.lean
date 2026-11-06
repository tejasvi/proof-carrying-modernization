import EquivLean.Bridge.Aeneas.AutoCouple
import EquivLean.Demo.Gen.Aeneas.SumPR.Funs
import EquivLean.Demo.Gen.Aeneas.VecPR.Funs
import EquivLean.Demo.Gen.Aeneas.AutoPR.Funs

/-!
# Tests of the generated couplings of `equiv_aeneas` on hand-written loops

Two cases of `Bridge/Aeneas/AutoCouple.lean` that the Charon + Aeneas output of
`Demo/Aeneas/AutoCouple.lean` does not reach, on loops written by hand in the shape of Aeneas
output (`@[rust_loop]`, `@[rust_loop_body]`), each against a generated function:

* `flag`: a flag in the loop state that no iteration changes (Aeneas itself moves an assignment
  made right before `break` to the exit of the loop), against `autopr.v1.contains`; the flag keeps
  its entry value: `p.2 = q ∧ p.1 = false`;
* `renamed`: the loop variables renamed and in the other order, against `sumpr.v1.sum`; no Rust
  name in common, so they are paired by type and position: `p.1 = q.2 ∧ p.2 = q.1`.

And the fallback: when no generated coupling closes the goal (`vecpr`, strength reduction),
`equiv_aeneas` fails and a coupling is given with `using`.
-/

open Aeneas Aeneas.Std Result ControlFlow EquivLean EquivLean.Aeneas

namespace EquivLean.Test.AeneasAutoCouple

/-- A search that keeps a flag in its loop state; the flag is passed on unchanged and returned
when the loop ends. -/
@[rust_loop_body]
def flag_loop.body (v : Slice U32) (x : U32) (found : Bool) (i : Usize) :
    Result (ControlFlow (Bool × Usize) Bool) := do
  if i < Slice.len v then
    let y ← Slice.index_usize v i
    if y = x then ok (done true)
    else
      let i1 ← i + 1#usize
      ok (cont (found, i1))
  else ok (done found)

@[rust_loop]
def flag_loop (v : Slice U32) (x : U32) (found : Bool) (i : Usize) : Result Bool :=
  loop (fun (found1, i1) => flag_loop.body v x found1 i1) (found, i)

def flag (v : Slice U32) (x : U32) : Result Bool := flag_loop v x false 0#usize

theorem flag_equiv_contains (v : Slice U32) (x : U32) :
    Equiv (· = ·) (flag v x) (autopr.v1.contains v x) := by
  equiv_aeneas [flag, autopr.v1.contains, flag_loop, autopr.v1.contains_loop, flag_loop.body,
    autopr.v1.contains_loop.body]

theorem contains_equiv_flag (v : Slice U32) (x : U32) :
    Equiv (· = ·) (autopr.v1.contains v x) (flag v x) := by
  equiv_aeneas [flag, autopr.v1.contains, flag_loop, autopr.v1.contains_loop, flag_loop.body,
    autopr.v1.contains_loop.body]

/-- `sumpr.v1.sum` with the loop variables renamed and in the other order. -/
@[rust_loop_body]
def renamed_loop.body (v : Slice U32) (k : Usize) (acc : U32) :
    Result (ControlFlow (Usize × U32) U32) := do
  if k < Slice.len v then
    let y ← Slice.index_usize v k
    let acc1 ← acc + y
    let k1 ← k + 1#usize
    ok (cont (k1, acc1))
  else ok (done acc)

@[rust_loop]
def renamed_loop (v : Slice U32) (k : Usize) (acc : U32) : Result U32 :=
  loop (fun (k1, acc1) => renamed_loop.body v k1 acc1) (k, acc)

def renamed (v : Slice U32) : Result U32 := renamed_loop v 0#usize 0#u32

theorem renamed_equiv_sum (v : Slice U32) : Equiv (· = ·) (renamed v) (sumpr.v1.sum v) := by
  equiv_aeneas [renamed, sumpr.v1.sum, renamed_loop, sumpr.v1.sum_loop, renamed_loop.body,
    sumpr.v1.sum_loop.body]

/-- No generated coupling closes the strength reduction of `vecpr` (`equiv_aeneas` fails, with
the list of couplings it tried); the hand-written coupling of `Demo/Aeneas/VecPR.lean` is given
with `using`. -/
theorem squares_fallback (n : U32) :
    Equiv (· = ·) (vecpr.v2.squares n) (vecpr.v1.squares n) := by
  fail_if_success equiv_aeneas [vecpr.v2.squares, vecpr.v1.squares, vecpr.v2.squares_loop,
    vecpr.v1.squares_loop, vecpr.v2.squares_loop.body, vecpr.v1.squares_loop.body,
    lift, bind_ok, alloc.vec.Vec.with_capacity]
  equiv_aeneas [vecpr.v2.squares, vecpr.v1.squares, vecpr.v2.squares_loop,
      vecpr.v1.squares_loop, vecpr.v2.squares_loop.body, vecpr.v1.squares_loop.body,
      lift, bind_ok, alloc.vec.Vec.with_capacity]
    using fun p q => p.1 = q.1 ∧ p.2.1 = q.2 ∧ p.2.2.val = q.2.val * q.2.val ∧ q.2.val ≤ n.val

end EquivLean.Test.AeneasAutoCouple

#print axioms EquivLean.Test.AeneasAutoCouple.flag_equiv_contains
#print axioms EquivLean.Test.AeneasAutoCouple.contains_equiv_flag
#print axioms EquivLean.Test.AeneasAutoCouple.renamed_equiv_sum
#print axioms EquivLean.Test.AeneasAutoCouple.squares_fallback
