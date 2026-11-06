import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.SumPR.Funs

/-!
# Rust PR diffs on real Charon + Aeneas output

`examples/rust/sumpr/src/lib.rs` holds three versions of a slice sum (a PR history); the Lean
code in `Demo/Gen/Aeneas/SumPR/Funs.lean` is the unmodified output of Charon + Aeneas.
Arithmetic is checked: `s + v[i]` panics (`Error.integerOverflow`) when the sum overflows `u32`.

* (a) `v2_equiv_v1`: PR 1 (loop condition `i != len` instead of `i < len`, the element read
  once, zero entries skipped) is equivalent to the original, with `(· = ·)` on outcomes: same
  result, and the same panic on exactly the same inputs.  One `equiv_aeneas` call: the loops
  are paired in lockstep with the coupling invariant "same state, `i ≤ len`" (needed because
  `i != len` and `i < len` only agree below the length).
* (b) `v3_equivOn_v1`: PR 2 (saturating addition) changes the behaviour, but only on `Bad`
  inputs, and `Bad` is exactly the set of inputs on which the original panics
  (`v1_panics_iff`, from the one-sided specification `v1_spec`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.SumPR

/-! ## (a) An equivalence-preserving refactoring -/

theorem v2_equiv_v1 (v : Slice U32) : Equiv (· = ·) (sumpr.v2.sum v) (sumpr.v1.sum v) := by
  equiv_aeneas [sumpr.v2.sum, sumpr.v1.sum, sumpr.v2.sum_loop, sumpr.v1.sum_loop,
      sumpr.v2.sum_loop.body, sumpr.v1.sum_loop.body]
    using fun p q => p = q ∧ p.2.val ≤ v.val.length

/-- The same, as a statement about the two functions. -/
theorem v2_fequiv_v1 : FEquiv (· = ·) (· = ·) sumpr.v2.sum sumpr.v1.sum := by
  rintro v _ rfl
  exact v2_equiv_v1 v

/-- Callers are unaffected: for Rust computations `Equiv (· = ·)` is equality
(`equiv_eq_iff`), so the callee equivalence rewrites inside the caller. -/
theorem v6_equiv_v5 (v : Slice U32) :
    Equiv (· = ·) (sumpr.v6.double_sum v) (sumpr.v5.double_sum v) := by
  unfold sumpr.v6.double_sum sumpr.v5.double_sum
  rw [equiv_eq_iff.1 (v2_equiv_v1 v)]
  exact Equiv.refl _

/-! ## (b) A behaviour change confined to the panicking inputs -/

/-- The mathematical sum of the elements. -/
def total (v : Slice U32) : Nat := (v.val.map UScalar.val).sum

/-- The inputs on which the original version overflows. -/
def Bad (v : Slice U32) : Prop := 4294967295 < total v

theorem sum_drop_succ (l : List Nat) (i : Nat) (h : i < l.length) :
    (l.drop i).sum = l[i] + (l.drop (i + 1)).sum := by
  rw [List.drop_eq_getElem_cons h, List.sum_cons]

/-- PR 2 behaves like the original on every input on which the original does not panic. -/
theorem v3_equivOn_v1 : EquivOn Bad (· = ·) sumpr.v3.sum sumpr.v1.sum := by
  intro v hbad
  simp only [Bad, Nat.not_lt] at hbad
  equiv_aeneas [sumpr.v3.sum, sumpr.v1.sum, sumpr.v3.sum_loop, sumpr.v1.sum_loop,
      sumpr.v3.sum_loop.body, sumpr.v1.sum_loop.body]
    using fun p q => p = q ∧ p.2.val ≤ v.val.length ∧
      p.1.val + ((v.val.map UScalar.val).drop p.2.val).sum = total v
    with [sum_drop_succ, total]

/-- The original version: the sum, or an overflow panic exactly on `Bad` inputs. -/
theorem v1_spec (v : Slice U32) :
    wp (sumpr.v1.sum v) (fun o => match o with
      | .ok s => s.val = total v ∧ ¬ Bad v
      | .error e => e = .integerOverflow ∧ Bad v) := by
  wp_aeneas_loop [sumpr.v1.sum, sumpr.v1.sum_loop, sumpr.v1.sum_loop.body]
    using (fun p => p.2.val ≤ v.val.length ∧
      p.1.val + ((v.val.map UScalar.val).drop p.2.val).sum = total v),
      (fun p => v.val.length - p.2.val)
    with [Bad, sum_drop_succ, total]

/-- `Bad` is exactly the set of inputs on which the original version panics. -/
theorem v1_panics_iff (v : Slice U32) : (∃ e, sumpr.v1.sum v = Result.fail e) ↔ Bad v := by
  have h := v1_spec v
  rcases (wp_iff _ _).1 h with ⟨s, hs, hok⟩ | ⟨e, he, herr⟩
  · rw [hs]; simp only [ok_not_fail, exists_false, false_iff]; exact hok.2
  · rw [he]; simp only [Result.fail.injEq, exists_eq', true_iff]; exact herr.2

/-- Hence the changed inputs of PR 2 are among the inputs on which the original panics. -/
theorem v3_changed_only_where_v1_panics (v : Slice U32)
    (h : ¬ Equiv (· = ·) (sumpr.v3.sum v) (sumpr.v1.sum v)) :
    ∃ e, sumpr.v1.sum v = Result.fail e :=
  (v1_panics_iff v).2 (v3_equivOn_v1.changed_subset v h)

end EquivLean.Demo.Aeneas.SumPR

#print axioms EquivLean.Demo.Aeneas.SumPR.v2_equiv_v1
#print axioms EquivLean.Demo.Aeneas.SumPR.v3_equivOn_v1
#print axioms EquivLean.Demo.Aeneas.SumPR.v1_panics_iff
