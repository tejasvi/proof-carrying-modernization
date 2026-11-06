import EquivLean.Core.Facts
import EquivLean.Core.OptionLoop
import EquivLean.Repr.Corr
import EquivLean.Repr.Int
import EquivLean.Tactic.Basic

/-!
# The `Simulates` typeclass across kinds of computations

`t ⊑ s` (`Simulates.sim`) compares a target computation with a source computation of a
different kind; the outcome relation comes from `Corr`.  These tests show the three ends of
the bridge on plain Lean programs (the encodings' monads work the same way through their
bridges):

* a **pure function** (`Id`, via `pureVal`) as the specification;
* a **local-state transformer** (`StateM`), observed through `.run s₀`;
* an **error monad** (`Except`) and a **partial computation** (`Option`, divergence as `none`);
* **representation refinement**: machine words (`BitVec 32`) against integers, lists against
  arrays.
-/

namespace EquivLean.Test.SimulatesTests

open EquivLean

/-! ## Correspondences used below -/

/-- A 32-bit word represents the integer it denotes in two's complement. -/
instance : Corr (BitVec 32) Int := ⟨fun b v => b.toInt = v⟩

/-! ## Error monad against a pure specification -/

/-- Checked addition, as a Rust or Java `Math.addExact` would do it. -/
def addChecked (a b : BitVec 32) : Except String (BitVec 32) :=
  if SRange 32 (a.toInt + b.toInt) then .ok (a + b) else .error "overflow"

/-- On inputs whose sum fits, the checked addition simulates mathematical addition. -/
theorem addChecked_sim (a b : BitVec 32) (h : SRange 32 (a.toInt + b.toInt)) :
    Sim (fun (o : Except String (BitVec 32)) (v : Int) => o.toOption.map BitVec.toInt = some v)
      (addChecked a b) (pureVal (a.toInt + b.toInt)) := by
  equiv_intro P hs
  simp only [addChecked, h, ite_true, wp_except]
  simp only [wp_id] at hs
  exact ⟨_, hs, by simp [Except.toOption, toInt_add_of_srange h]⟩

/-! ## Local-state transformer against a pure specification -/

/-- A counter in a state monad: add each element to the state. -/
def sumState : List Int → StateM Int Unit
  | [] => pure ()
  | x :: xs => do modify (· + x); sumState xs

theorem sumState_run (xs : List Int) (s₀ : Int) :
    (sumState xs).run s₀ = ((), s₀ + xs.sum) := by
  induction xs generalizing s₀ with
  | nil => simp [sumState, StateT.run, pure, StateT.pure]
  | cons x xs ih =>
    show (sumState xs).run (s₀ + x) = _
    rw [ih]; simp [Int.add_assoc]

/-- The state transformer, run from 0, simulates the pure `List.sum`; the outcome relation
reads the final state. -/
theorem sumState_sim (xs : List Int) :
    Sim (fun (o : Unit × Int) (v : Int) => o.2 = v)
      ((sumState xs).run 0 : Id (Unit × Int)) (pureVal xs.sum) := by
  equiv_intro P hs
  simp only [wp_id] at hs ⊢
  exact ⟨_, hs, by rw [sumState_run]; simp⟩

/-! ## A partial computation (divergence = `none`) against an error monad

Two implementations of integer square root by search: an `optLoop` (which would diverge if
its loop did not stop) and a fuelled `Except` version.  The relation is equality of the
result. -/

/-- Smallest `k` with `(k+1)^2 > n`, by counting up from `k₀`. -/
def isqrtBody (n : Nat) (k : Nat) : Option (Nat ⊕ Nat) :=
  if (k + 1) * (k + 1) ≤ n then some (.inr (k + 1)) else some (.inl k)

def isqrtLoop (n : Nat) : Option Nat := optLoop (isqrtBody n) 0

/-- The specification as a pure function. -/
def isqrtSpec : Nat → Nat → Nat → Nat
  | 0, _, k => k
  | fuel + 1, n, k => if (k + 1) * (k + 1) ≤ n then isqrtSpec fuel n (k + 1) else k

/-- The loop simulates the pure specification (with enough fuel). -/
theorem isqrtLoop_sim (n : Nat) :
    Sim (· = ·) (isqrtLoop n) (pureVal (isqrtSpec (n + 1) n 0)) := by
  equiv_intro P hs
  simp only [wp_id] at hs
  -- one-sided loop rule; the invariant says the specification from `k` is the answer
  have key : wp (optLoop (isqrtBody n) 0) (fun o => o = isqrtSpec (n + 1) n 0) := by
    refine wp_loop (optLoop_shape _)
      (fun k => k * k ≤ n ∧ isqrtSpec (n + 1 - k) n k = isqrtSpec (n + 1) n 0)
      (fun k => n + 1 - k) ?_ 0 ⟨by simp, by simp⟩
    rintro k ⟨hk, hspec⟩
    obtain ⟨f, hf⟩ : ∃ f, n + 1 - k = f + 1 := ⟨n - k, by have := Nat.le_mul_self k; omega⟩
    unfold isqrtBody
    by_cases h : (k + 1) * (k + 1) ≤ n
    · simp only [h, ite_true, wp_some, id]
      have hlt : k + 1 ≤ n := Nat.le_trans (Nat.le_mul_self (k + 1)) h
      have hf' : n + 1 - (k + 1) = f := by omega
      refine ⟨⟨trivial, ?_⟩, by omega⟩
      rw [hf', ← hspec, hf]
      simp [isqrtSpec, h]
    · simp only [h, ite_false, wp_some, id]
      rw [← hspec, hf]
      simp [isqrtSpec, h]
  exact wp_mono key fun o ho => ⟨_, hs, ho⟩

/-! ## The typeclass form: the relation comes from `Corr`

`t ⊑ s` resolves `Simulates T S` through the default instance (`Behaves` on both sides and
`Corr` on their outcomes), so the statement needs no explicit relation. -/

theorem add_sim_typeclass (a b : BitVec 32) (h : SRange 32 (a.toInt + b.toInt)) :
    (pureVal (a + b)) ⊑ (pureVal (a.toInt + b.toInt)) := by
  show Sim Corr.corr _ _
  equiv_intro P hs
  simp only [wp_id] at hs ⊢
  exact ⟨_, hs, toInt_add_of_srange h⟩

/-- Lists of words against lists of integers, element by element (`ListRel`). -/
theorem map_sim_typeclass (xs : List (BitVec 32)) :
    (pureVal xs) ⊑ (pureVal (xs.map BitVec.toInt)) := by
  show Sim Corr.corr _ _
  equiv_intro P hs
  simp only [wp_id] at hs ⊢
  refine ⟨_, hs, ?_⟩
  show ListRel Corr.corr xs (xs.map BitVec.toInt)
  rw [ListRel.map_right]
  have refl : ∀ ys : List (BitVec 32), ListRel (fun a c => Corr.corr a c.toInt) ys ys := by
    intro ys
    induction ys with
    | nil => exact .nil
    | cons y ys ih => exact .cons rfl ih
  exact refl xs

end EquivLean.Test.SimulatesTests
