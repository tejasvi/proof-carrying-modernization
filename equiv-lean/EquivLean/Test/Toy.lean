import EquivLean.Core.OptionLoop
import EquivLean.Tactic.Auto
import EquivLean.Tactic.Call
import EquivLean.Tactic.LoopAuto

/-!
# Tests of the generic layer on plain Lean programs

Two versions of a loop written as state-passing Lean functions (`optLoop`), standing in for
two versions of a function after a refactor.  The new version applies strength reduction:
`acc += i * c` becomes `acc += t; t += c`.  The proof pairs the loops in lockstep with the
coupling invariant `i₁ = i₂ ∧ acc₁ = acc₂ ∧ t = i * c`; no variant is needed because the old
loop's termination is assumed (it is the source).
-/

namespace EquivLean.Test

open EquivLean

/-- Old: `for (i = 0; i < n; i++) acc += i * c;` -/
def oldBody (n c : Nat) : Nat × Nat → Option (Nat ⊕ (Nat × Nat))
  | (i, acc) => if i < n then some (.inr (i + 1, acc + i * c)) else some (.inl acc)

def oldSum (n c : Nat) : Option Nat := optLoop (oldBody n c) (0, 0)

/-- New: `t = 0; for (i = 0; i < n; i++) { acc += t; t += c; }` -/
def newBody (n c : Nat) : Nat × Nat × Nat → Option (Nat ⊕ (Nat × Nat × Nat))
  | (i, acc, t) => if i < n then some (.inr (i + 1, acc + t, t + c)) else some (.inl acc)

def newSum (n c : Nat) : Option Nat := optLoop (newBody n c) (0, 0, 0)

/-- The coupling invariant. -/
def Coupled (c : Nat) : Nat × Nat × Nat → Nat × Nat → Prop
  | (i, acc, t), (i', acc') => i = i' ∧ acc = acc' ∧ t = i * c

theorem newSum_sim_oldSum (n c : Nat) : Sim (· = ·) (newSum n c) (oldSum n c) := by
  equiv_intro P hs
  unfold newSum
  unfold oldSum at hs
  equiv_loop (Coupled c) using optLoop_shape _, optLoop_shape _, optLoop_terminates _
  case init => simp [Coupled]
  case step =>
    rintro ⟨i, acc, t⟩ ⟨i', acc'⟩ ⟨rfl, rfl, rfl⟩
    equiv_intro Q hq
    by_cases h : i < n
    · simp only [newBody, oldBody, h, ite_true, wp_some] at hq ⊢
      refine ⟨_, hq, ?_⟩
      simp [StepRel, Coupled, Nat.succ_mul]
    · simp only [newBody, oldBody, h, ite_false, wp_some] at hq ⊢
      exact ⟨_, hq, rfl⟩
  case post =>
    intro o₁ o₂ ho hk
    exact ⟨o₂, hk, ho⟩

/-- Both directions: the two versions are equivalent on every input. -/
theorem newSum_equiv_oldSum (n c : Nat) : Equiv (· = ·) (newSum n c) (oldSum n c) := by
  refine ⟨newSum_sim_oldSum n c, ?_⟩
  equiv_intro P hs
  unfold newSum at hs
  unfold oldSum
  equiv_loop (fun (s : Nat × Nat) (s' : Nat × Nat × Nat) => Coupled c s' s)
    using optLoop_shape _, optLoop_shape _, optLoop_terminates _
  case init => simp [Coupled]
  case step =>
    rintro ⟨i, acc⟩ ⟨i', acc', t⟩ ⟨rfl, rfl, rfl⟩
    equiv_intro Q hq
    by_cases h : i' < n
    · simp only [newBody, oldBody, h, ite_true, wp_some] at hq ⊢
      refine ⟨_, hq, ?_⟩
      simp [StepRel, Coupled, Nat.succ_mul]
    · simp only [newBody, oldBody, h, ite_false, wp_some] at hq ⊢
      exact ⟨_, hq, rfl⟩
  case post =>
    intro o₁ o₂ ho hk
    exact ⟨o₂, hk, ho.symm⟩

end EquivLean.Test

namespace EquivLean.Test
open EquivLean

/-! ## The same proof with the automation of `EquivLean.Tactic.Auto` -/

theorem newSum_sim_oldSum' (n c : Nat) : Sim (· = ·) (newSum n c) (oldSum n c) := by
  equiv_intro P hs
  unfold newSum; unfold oldSum at hs
  equiv_loop (Coupled c) using optLoop_shape _, optLoop_shape _, optLoop_terminates _
  case init => simp [Coupled]
  case step =>
    rintro ⟨i, acc, t⟩ ⟨i', acc'⟩ ⟨rfl, rfl, rfl⟩
    equiv_body [newBody, oldBody, Coupled, Nat.succ_mul]
  case post => intro o₁ o₂ ho hk; exact ⟨o₂, hk, ho⟩

/-! ## Asynchronous alignment: an unrolled loop

The new version adds two elements per iteration while it can, then finishes one at a time;
the old version adds one per iteration.  The scheduler runs the old loop alone (`right`)
for the second element of each unrolled step. -/

/-- Old: `for (i = 0; i < n; i++) acc += f i;` -/
def oldB (n : Nat) (f : Nat → Nat) : Nat × Nat → Option (Nat ⊕ (Nat × Nat))
  | (i, acc) => if i < n then some (.inr (i + 1, acc + f i)) else some (.inl acc)

/-- New: `for (i = 0; i + 1 < n; i += 2) acc += f i + f (i+1); if (i < n) acc += f i;` written
as one loop whose iterations take two steps or one. -/
def newB (n : Nat) (f : Nat → Nat) : Nat × Nat → Option (Nat ⊕ (Nat × Nat))
  | (i, acc) =>
    if i + 1 < n then some (.inr (i + 2, acc + f i + f (i + 1)))
    else if i < n then some (.inr (i + 1, acc + f i))
    else some (.inl acc)

/-- Product state: either in lockstep (`j = i`), or the old loop is one element behind in the
middle of an unrolled step (`j + 1 = i`, the old loop must still add `f j`). -/
def UnrollInv (n : Nat) (f : Nat → Nat) : Nat × Nat → Nat × Nat → Prop
  | (i, acc), (j, acc') => (j = i ∧ acc' = acc) ∨ (j + 1 = i ∧ i ≤ n ∧ acc' + f j = acc)

theorem unrolled_sim (n : Nat) (f : Nat → Nat) :
    Sim (· = ·) (optLoop (newB n f) (0, 0)) (optLoop (oldB n f) (0, 0)) := by
  refine sim_loop_stutter (optLoop_shape _) (optLoop_shape _) (UnrollInv n f)
    (fun s₁ s₂ => 2 * (n - s₂.1) + (if s₂.1 = s₁.1 then 1 else 0))
    (fun s₁ s₂ => if s₂.1 = s₁.1 then .both else .right) ?both ?left ?right (0, 0) (0, 0) ?init
  case init => simp [UnrollInv]
  case both =>
    rintro ⟨i, acc⟩ ⟨j, acc'⟩ hI hs
    simp only [UnrollInv] at hI
    split at hs
    · next h =>
      simp only at h; subst h
      have hacc : acc' = acc := by omega
      subst hacc
      equiv_body [newB, oldB, UnrollInv]
      all_goals omega
    · simp at hs
  case left => intro s₁ s₂ _ hs; split at hs <;> simp at hs
  case right =>
    rintro ⟨i, acc⟩ ⟨j, acc'⟩ hI hs _
    simp only at hs
    split at hs
    · simp at hs
    · next h =>
      simp only [UnrollInv] at hI
      have hj : j + 1 = i ∧ i ≤ n ∧ acc' + f j = acc := by omega
      obtain ⟨rfl, hn, rfl⟩ := hj
      have hjn : j < n := by omega
      simp only [oldB, hjn, ite_true, wp_some]
      refine ⟨_, rfl, ?_, ?_⟩
      · simp [UnrollInv]
      · simp; omega

end EquivLean.Test

namespace EquivLean.Test
open EquivLean

/-! ## Modular proofs: a caller uses the loop equivalence as a relational specification -/

attribute [equiv_spec] newSum_sim_oldSum

def newMain (n c : Nat) : Option Nat := do
  let s ← newSum n c
  pure (s + 1)

def oldMain (n c : Nat) : Option Nat := do
  let s ← oldSum n c
  pure (s + 1)

theorem newMain_sim_oldMain (n c : Nat) : Sim (· = ·) (newMain n c) (oldMain n c) := by
  equiv_intro P hs
  simp only [newMain, oldMain, wp_option_bind] at hs ⊢
  equiv_call
  rintro ot os rfl hk
  simp only [pure, wp_some] at hk ⊢
  exact ⟨_, hk, rfl⟩

end EquivLean.Test

namespace EquivLean.Test
open EquivLean

/-! ## Automatic loop pairing from the shape database -/

attribute [equiv_loop_shape] optLoop_shape
attribute [equiv_loop_term] optLoop_terminates

theorem newSum_sim_oldSum'' (n c : Nat) : Sim (· = ·) (newSum n c) (oldSum n c) := by
  equiv_intro P hs
  unfold newSum; unfold oldSum at hs
  equiv_loop_auto (Coupled c)
  case init => simp [Coupled]
  case step =>
    rintro ⟨i, acc, t⟩ ⟨i', acc'⟩ ⟨rfl, rfl, rfl⟩
    equiv_body [newBody, oldBody, Coupled, Nat.succ_mul]
  case post => intro o₁ o₂ ho hk; exact ⟨o₂, hk, ho⟩

end EquivLean.Test

namespace EquivLean.Test
open EquivLean

/-- The unrolled loop again, with `equiv_loop_async` (shapes from the registry). -/
theorem unrolled_sim' (n : Nat) (f : Nat → Nat) :
    Sim (· = ·) (optLoop (newB n f) (0, 0)) (optLoop (oldB n f) (0, 0)) := by
  equiv_intro P hs
  equiv_loop_async (UnrollInv n f)
    (fun s₁ s₂ => 2 * (n - s₂.1) + (if s₂.1 = s₁.1 then 1 else 0))
    (fun s₁ s₂ => if s₂.1 = s₁.1 then Sched.both else .right)
  case init => simp [UnrollInv]
  case both =>
    rintro ⟨i, acc⟩ ⟨j, acc'⟩ hI hs
    simp only [UnrollInv] at hI
    split at hs
    · next h =>
      simp only at h; subst h
      have hacc : acc' = acc := by omega
      subst hacc
      equiv_body [newB, oldB, UnrollInv]
      all_goals omega
    · simp at hs
  case left => intro s₁ s₂ _ hs; split at hs <;> simp at hs
  case right =>
    rintro ⟨i, acc⟩ ⟨j, acc'⟩ hI hs _
    simp only at hs
    split at hs
    · simp at hs
    · next h =>
      simp only [UnrollInv] at hI
      have hj : j + 1 = i ∧ i ≤ n ∧ acc' + f j = acc := by omega
      obtain ⟨rfl, hn, rfl⟩ := hj
      have hjn : j < n := by omega
      simp only [oldB, hjn, ite_true, wp_some]
      refine ⟨_, rfl, ?_, ?_⟩
      · simp [UnrollInv]
      · simp; omega
  case post => intro o₁ o₂ ho hk; exact ⟨o₂, hk, ho⟩

end EquivLean.Test

namespace EquivLean.Test
open EquivLean

/-! ## A refactoring that keeps the loop state: no coupling invariant at all -/

def oldCount (n : Nat) : Nat × Nat → Option (Nat ⊕ (Nat × Nat))
  | (i, c) => if i < n then some (.inr (i + 1, if i % 3 = 0 then c + 1 else c)) else some (.inl c)

/-- New: the branch is rewritten as an arithmetic expression. -/
def newCount (n : Nat) : Nat × Nat → Option (Nat ⊕ (Nat × Nat))
  | (i, c) => if n ≤ i then some (.inl c) else some (.inr (i + 1, c + (if i % 3 = 0 then 1 else 0)))

theorem count_sim (n : Nat) : Sim (· = ·) (optLoop (newCount n) (0, 0)) (optLoop (oldCount n) (0, 0)) := by
  equiv_intro P hs
  equiv_loop_same
  case init => rfl
  case step =>
    rintro ⟨i, c⟩ _ rfl
    equiv_body [newCount, oldCount]
    all_goals (first | omega | (split <;> simp_all) | simp_all)
  case post => intro o₁ o₂ ho hk; exact ⟨o₂, hk, ho⟩

end EquivLean.Test
