import EquivLean.Repr.Corr

/-!
# Collections across encodings

Sequences: every encoding exposes its containers as lists (`std::vector` = `Val.vec gen elems`,
Aeneas `Vec T` = a list with a length bound, a StrictTS array cell, a Java `ArrayList`/array
object, a COBOL `OCCURS` table read field by field).  `ListRel` (`EquivLean.Repr.Corr`) relates
them element by element; `ListRel.foldl` matches a loop over one container with a loop over
another.

Finite maps: `java.util.HashMap`/`TreeMap`, the StrictTS `Map`, Rust `HashMap` and their
models differ in iteration order.  The common model is the lookup function: two association
lists represent the same map when every key looks up to the same value (`AEquiv`).  Programs
whose observable output depends on iteration order must expose that order separately (for
example as a sorted list of entries).
-/

namespace EquivLean

universe u v

section
variable {K : Type u} {V : Type v} [DecidableEq K]

/-- Lookup in an association list (first binding wins). -/
def alookup (k : K) : List (K × V) → Option V
  | [] => none
  | (k', v) :: l => if k' = k then some v else alookup k l

/-- Insert or overwrite a binding. -/
def ainsert (k : K) (v : V) (l : List (K × V)) : List (K × V) := (k, v) :: l

/-- Remove every binding of a key. -/
def aerase (k : K) (l : List (K × V)) : List (K × V) := l.filter (fun p => !decide (p.1 = k))

/-- Two association lists represent the same finite map. -/
def AEquiv (l₁ l₂ : List (K × V)) : Prop := ∀ k, alookup k l₁ = alookup k l₂

/-- An association list represents the lookup function `f`. -/
def MapRepr (l : List (K × V)) (f : K → Option V) : Prop := ∀ k, alookup k l = f k

@[simp] theorem alookup_nil (k : K) : alookup k ([] : List (K × V)) = none := rfl

@[simp] theorem alookup_ainsert (k k' : K) (v : V) (l : List (K × V)) :
    alookup k (ainsert k' v l) = if k' = k then some v else alookup k l := by
  simp [ainsert, alookup]

@[simp] theorem alookup_aerase (k k' : K) (l : List (K × V)) :
    alookup k (aerase k' l) = if k' = k then none else alookup k l := by
  induction l with
  | nil => simp [aerase, alookup]
  | cons p l ih =>
    obtain ⟨k₁, v₁⟩ := p
    by_cases h₁ : k₁ = k' <;> by_cases h₂ : k₁ = k <;> by_cases h₃ : k' = k <;>
      simp_all [aerase, alookup, List.filter]

theorem AEquiv.refl (l : List (K × V)) : AEquiv l l := fun _ => rfl
theorem AEquiv.symm {l₁ l₂ : List (K × V)} (h : AEquiv l₁ l₂) : AEquiv l₂ l₁ :=
  fun k => (h k).symm
theorem AEquiv.trans {l₁ l₂ l₃ : List (K × V)} (h₁ : AEquiv l₁ l₂) (h₂ : AEquiv l₂ l₃) :
    AEquiv l₁ l₃ := fun k => (h₁ k).trans (h₂ k)

theorem AEquiv.insert {l₁ l₂ : List (K × V)} (h : AEquiv l₁ l₂) (k : K) (v : V) :
    AEquiv (ainsert k v l₁) (ainsert k v l₂) := fun k' => by simp [h k']

theorem AEquiv.erase {l₁ l₂ : List (K × V)} (h : AEquiv l₁ l₂) (k : K) :
    AEquiv (aerase k l₁) (aerase k l₂) := fun k' => by simp [h k']

/-- Overwriting a key twice keeps the last value. -/
theorem ainsert_ainsert (k : K) (v v' : V) (l : List (K × V)) :
    AEquiv (ainsert k v' (ainsert k v l)) (ainsert k v' l) := fun k' => by
  by_cases h : k = k' <;> simp [h]

/-- Bindings of different keys commute. -/
theorem ainsert_comm {k₁ k₂ : K} (hk : k₁ ≠ k₂) (v₁ v₂ : V) (l : List (K × V)) :
    AEquiv (ainsert k₁ v₁ (ainsert k₂ v₂ l)) (ainsert k₂ v₂ (ainsert k₁ v₁ l)) := fun k => by
  by_cases h₁ : k₁ = k <;> by_cases h₂ : k₂ = k <;> simp_all

end

end EquivLean
