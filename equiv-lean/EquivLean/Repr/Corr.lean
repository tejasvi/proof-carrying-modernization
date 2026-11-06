import EquivLean.Core.Sim

/-!
# Representation correspondence

`Corr A B` (declared in `EquivLean.Core.Sim`) relates a value of one representation to a value
of another that stands for the same observable data.  This file gives the structural
instances: equal values, pairs, options, sums, `Except`, and lists element by element
(`ListRel`, the pointwise relation; Mathlib's `List.Forall₂` is not available in core Lean).

Bridges add instances from their encodings' value types to the mathematical models of
`EquivLean.Repr` (machine integers, decimals, lists, finite maps).  With them, `t ⊑ s` and
`t ≈ s` (`Simulates`, `Equivalent`) need no explicit outcome relation.
-/

namespace EquivLean

universe u v w x

/-- Two lists related element by element. -/
inductive ListRel {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

attribute [simp] ListRel.nil

namespace ListRel
variable {α : Type u} {β : Type v} {R : α → β → Prop}

@[simp] theorem cons_iff {a : α} {b : β} {as bs} :
    ListRel R (a :: as) (b :: bs) ↔ R a b ∧ ListRel R as bs :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›⟩, fun ⟨h₁, h₂⟩ => .cons h₁ h₂⟩

@[simp] theorem nil_cons {b : β} {bs} : ¬ ListRel R [] (b :: bs) := fun h => nomatch h
@[simp] theorem cons_nil {a : α} {as} : ¬ ListRel R (a :: as) [] := fun h => nomatch h

theorem length_eq {as : List α} {bs : List β} (h : ListRel R as bs) : as.length = bs.length := by
  induction h <;> simp [*]

theorem of_eq {as bs : List α} (h : as = bs) : ListRel (· = ·) as bs := by
  subst h; induction as <;> simp [*]

theorem eq_of_eq {as bs : List α} (h : ListRel (· = ·) as bs) : as = bs := by
  induction h <;> simp_all

@[simp] theorem eq_iff {as bs : List α} : ListRel (· = ·) as bs ↔ as = bs :=
  ⟨eq_of_eq, of_eq⟩

theorem map_left {γ : Type w} {f : γ → α} {cs : List γ} {bs : List β} :
    ListRel R (cs.map f) bs ↔ ListRel (fun c b => R (f c) b) cs bs := by
  induction cs generalizing bs <;> cases bs <;> simp [*]

theorem map_right {γ : Type w} {f : γ → β} {as : List α} {cs : List γ} :
    ListRel R as (cs.map f) ↔ ListRel (fun a c => R a (f c)) as cs := by
  induction as generalizing cs <;> cases cs <;> simp [*]

theorem mono {S : α → β → Prop} {as : List α} {bs : List β} (h : ListRel R as bs)
    (hRS : ∀ a b, R a b → S a b) : ListRel S as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hRS _ _ hab) ih

theorem append {as as' : List α} {bs bs' : List β} (h : ListRel R as bs) (h' : ListRel R as' bs') :
    ListRel R (as ++ as') (bs ++ bs') := by
  induction h with
  | nil => simpa
  | cons hab _ ih => exact .cons hab ih

/-- Element access in related lists gives related elements. -/
theorem get {as : List α} {bs : List β} (h : ListRel R as bs) (i : Nat) (hi : i < as.length) :
    R (as[i]'hi) (bs[i]'(h.length_eq ▸ hi)) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hab _ ih =>
    cases i with
    | zero => simpa
    | succ i => simpa using ih i (by simpa using hi)

/-- Folding related lists with related step functions gives related results; this is how a
loop over a container in one language is matched with a loop over its model in another. -/
theorem foldl {γ : Type w} {δ : Type x} {S : γ → δ → Prop} {f : γ → α → γ} {g : δ → β → δ}
    {as : List α} {bs : List β} (h : ListRel R as bs)
    (hfg : ∀ c d a b, S c d → R a b → S (f c a) (g d b)) {c : γ} {d : δ} (hcd : S c d) :
    S (as.foldl f c) (bs.foldl g d) := by
  induction h generalizing c d with
  | nil => exact hcd
  | cons hab _ ih => exact ih (hfg _ _ _ _ hcd hab)

end ListRel

/-! ## Structural instances -/

instance (priority := low) instCorrEq (α : Type u) : Corr α α := ⟨(· = ·)⟩

instance instCorrProd {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Corr α γ] [Corr β δ] : Corr (α × β) (γ × δ) :=
  ⟨fun p q => Corr.corr p.1 q.1 ∧ Corr.corr p.2 q.2⟩

instance instCorrOption {α : Type u} {β : Type v} [Corr α β] : Corr (Option α) (Option β) :=
  ⟨fun a b => match a, b with
    | some a, some b => Corr.corr a b
    | none, none => True
    | _, _ => False⟩

instance instCorrSum {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Corr α γ] [Corr β δ] : Corr (α ⊕ β) (γ ⊕ δ) :=
  ⟨fun a b => match a, b with
    | .inl a, .inl c => Corr.corr a c
    | .inr b, .inr d => Corr.corr b d
    | _, _ => False⟩

instance instCorrExcept {ε : Type u} {α : Type v} {ε' : Type w} {β : Type x}
    [Corr ε ε'] [Corr α β] : Corr (Except ε α) (Except ε' β) :=
  ⟨fun a b => match a, b with
    | .ok a, .ok b => Corr.corr a b
    | .error e, .error e' => Corr.corr e e'
    | _, _ => False⟩

instance instCorrList {α : Type u} {β : Type v} [Corr α β] : Corr (List α) (List β) :=
  ⟨ListRel Corr.corr⟩

instance instCorrArray {α : Type u} {β : Type v} [Corr α β] : Corr (Array α) (List β) :=
  ⟨fun a l => ListRel Corr.corr a.toList l⟩

@[simp] theorem corr_eq_iff {α : Type u} (a b : α) :
    @Corr.corr α α (instCorrEq α) a b ↔ a = b := Iff.rfl

end EquivLean
