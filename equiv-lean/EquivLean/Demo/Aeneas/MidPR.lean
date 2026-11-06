import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.MidPR.Funs

/-!
# The midpoint overflow fix (loop-free, real Charon + Aeneas output)

`examples/rust/midpr/src/lib.rs`: `v1::mid a b = (a + b) / 2` panics when `a + b` overflows
`u32`; the PR `v2::mid a b = a / 2 + b / 2 + (a % 2 + b % 2) / 2` never panics.  The behaviour
changes exactly on the inputs on which the original panics (`EquivOn Bad`), and `Bad` is that set
(`v1_panics_iff`); the PR computes the rounded-down average on every input
(`v2_equiv_average`, against a pure value).  Each proof is one tactic call.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.MidPR

/-- The original overflows. -/
def Bad (p : U32 × U32) : Prop := 4294967295 < p.1.val + p.2.val

theorem v2_equivOn_v1 :
    EquivOn Bad (· = ·) (fun p => midpr.v2.mid p.1 p.2) (fun p => midpr.v1.mid p.1 p.2) := by
  rintro ⟨a, b⟩ hbad
  simp only [Bad, Nat.not_lt] at hbad
  equiv_aeneas_straight [midpr.v2.mid, midpr.v1.mid]

theorem v1_panics_iff (a b : U32) :
    wp (midpr.v1.mid a b) (fun o => (∃ e, o = .error e) ↔ Bad (a, b)) := by
  aeneas_wp [midpr.v1.mid, Bad]
  aeneas_leaves

/-- The PR never panics. -/
theorem v2_no_panic (a b : U32) : wp (midpr.v2.mid a b) (fun o => ∀ e, o ≠ .error e) := by
  aeneas_wp [midpr.v2.mid]
  aeneas_leaves

/-- The PR computes the rounded-down average, for all inputs (comparison with a pure value). -/
theorem v2_equiv_average (a b : U32) :
    Equiv (fun o r => o = .ok r) (midpr.v2.mid a b)
      (pureVal (UScalar.ofNatCore ((a.val + b.val) / 2)
        (by have := a.hBounds; have := b.hBounds; simp at *; omega) : U32)) := by
  equiv_aeneas_pure [midpr.v2.mid]

end EquivLean.Demo.Aeneas.MidPR

#print axioms EquivLean.Demo.Aeneas.MidPR.v2_equivOn_v1
#print axioms EquivLean.Demo.Aeneas.MidPR.v1_panics_iff
