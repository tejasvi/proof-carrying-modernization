import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Cobol.Corr

/-!
# Observations of COBOL runs

What two COBOL runs must agree on depends on the program's interface: the fields a caller or a
later job step reads (a record area, a `LINKAGE` item), the output files and `DISPLAY` lines,
and how the run ends.  `ObsEq fs` compares exactly that: the same completion signal, the same
output events (`DISPLAY`, `WRITE`, `CALL`, in order) and the same bytes in the observed fields
`fs`.  `DecEq` compares numeric fields by value through the shared decimal model (`descDec`),
so a patch may change a `PICTURE` or a `USAGE` as long as the values agree.

For a same-language patch (old program `P₁`, new program `P₂`), `CobolEquivOn Bad fs P₁ P₂ env
fuel inp` is the encoding-level `EquivOn`: on every initial storage outside `Bad`, the new run
is safe exactly when the old one is, and then they are observably equal; `changed_subset`
bounds the inputs on which behaviour changed by `Bad`.

Both runs are deterministic, so `equiv_exec_iff` turns an `Equiv` between two COBOL runs into
a statement about their two results, which coblean's symbolic executor evaluates
(`equiv_cobol`, `Bridge/Cobol/Tactic.lean`).
-/

open Cobol

namespace EquivLean.Cobol

/-- The observed fields hold the same bytes. -/
def SameFields (fs : List FieldDesc) (m₁ m₂ : Mem) : Prop := ∀ f ∈ fs, m₁.field f = m₂.field f

/-- Observable equality of two COBOL outcomes on the fields `fs`: same signal, same output
events, same bytes in `fs`. -/
def ObsEq (fs : List FieldDesc) (r₁ r₂ : Signal × State) : Prop :=
  r₁.1 = r₂.1 ∧ r₁.2.out = r₂.2.out ∧ SameFields fs r₁.2.mem r₂.2.mem

/-- The decimal a numeric item holds (`none` for invalid data or a non-numeric item). -/
def descDec (d : FieldDesc) (m : Mem) : Option EquivLean.Decimal :=
  match d.kind with
  | .num f => fieldDec {} f (m.field d)
  | _ => none

/-- Numeric fields compared by value: each pair `(d₁, d₂)` (old and new layout of the same
item) holds the same number. -/
def DecEq (ds : List (FieldDesc × FieldDesc)) (r₁ r₂ : Signal × State) : Prop :=
  r₁.1 = r₂.1 ∧ r₁.2.out = r₂.2.out ∧
    ∀ p ∈ ds, (descDec p.1 r₁.2.mem).map EquivLean.Decimal.val =
      (descDec p.2 r₂.2.mem).map EquivLean.Decimal.val

theorem obsEq_refl (fs : List FieldDesc) (r : Signal × State) : ObsEq fs r r :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem obsEq_symm {fs : List FieldDesc} {r₁ r₂ : Signal × State} (h : ObsEq fs r₁ r₂) :
    ObsEq fs r₂ r₁ :=
  ⟨h.1.symm, h.2.1.symm, fun f hf => (h.2.2 f hf).symm⟩

theorem obsEq_trans {fs : List FieldDesc} {r₁ r₂ r₃ : Signal × State} (h₁ : ObsEq fs r₁ r₂)
    (h₂ : ObsEq fs r₂ r₃) : ObsEq fs r₁ r₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun f hf => (h₁.2.2 f hf).trans (h₂.2.2 f hf)⟩

@[simp] theorem sameFields_nil (m₁ m₂ : Mem) : SameFields [] m₁ m₂ := fun _ h => nomatch h

@[simp] theorem sameFields_cons (f : FieldDesc) (fs : List FieldDesc) (m₁ m₂ : Mem) :
    SameFields (f :: fs) m₁ m₂ ↔ m₁.field f = m₂.field f ∧ SameFields fs m₁ m₂ := by
  simp [SameFields]

/-! ## Two COBOL runs -/

/-- Simulation between two COBOL runs: if the source result is safe, so is the target result,
and they are related. -/
theorem sim_exec_exec_iff {R : Signal × State → Signal × State → Prop} (r₁ r₂ : Sem.Res) :
    Sim R (Exec.mk r₁) (Exec.mk r₂) ↔ (Ok r₂ → Ok r₁ ∧ R r₁ r₂) := by
  rw [sim_exec_iff, wp_exec]

/-- **Equivalence of two COBOL runs**: safe on the same inputs, and related when safe. -/
theorem equiv_exec_iff {R : Signal × State → Signal × State → Prop} (r₁ r₂ : Sem.Res) :
    Equiv R (Exec.mk r₁) (Exec.mk r₂) ↔ (Ok r₁ ↔ Ok r₂) ∧ (Ok r₂ → R r₁ r₂) := by
  unfold Equiv
  rw [sim_exec_exec_iff, sim_exec_exec_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨fun h => (h₂ h).1, fun h => (h₁ h).1⟩, fun h => (h₁ h).2⟩
  · rintro ⟨hiff, hR⟩
    exact ⟨fun h => ⟨hiff.2 h, hR h⟩, fun h => ⟨hiff.1 h, hR (hiff.1 h)⟩⟩

theorem equiv_run_iff {R : Signal × State → Signal × State → Prop} (P₁ P₂ : Program) (env₁ env₂ : Env)
    (fuel₁ fuel₂ : Nat) (st₁ st₂ : State) :
    Equiv R (run P₁ env₁ fuel₁ st₁) (run P₂ env₂ fuel₂ st₂) ↔
      (Ok (P₁.run env₁ fuel₁ st₁) ↔ Ok (P₂.run env₂ fuel₂ st₂)) ∧
        (Ok (P₂.run env₂ fuel₂ st₂) → R (P₁.run env₁ fuel₁ st₁) (P₂.run env₂ fuel₂ st₂)) :=
  equiv_exec_iff _ _

/-! ## Patches -/

/-- **A COBOL patch changes behaviour only on `Bad` inputs**: for every initial storage `m`
outside `Bad`, the new program `P₂` and the old program `P₁` (same environment, fuel and input
files) are equivalent up to `ObsEq fs`. -/
def CobolEquivOn (Bad : Mem → Prop) (fs : List FieldDesc) (P₁ P₂ : Program) (env : Env)
    (fuel : Nat) (inp : List (Nat × List (List UInt8))) : Prop :=
  EquivOn Bad (ObsEq fs) (fun m => run P₂ env fuel (P₂.initState m inp))
    (fun m => run P₁ env fuel (P₁.initState m inp))

theorem CobolEquivOn.changed_subset {Bad : Mem → Prop} {fs : List FieldDesc} {P₁ P₂ : Program}
    {env : Env} {fuel : Nat} {inp : List (Nat × List (List UInt8))}
    (h : CobolEquivOn Bad fs P₁ P₂ env fuel inp) (m : Mem)
    (hm : ¬ Equiv (ObsEq fs) (run P₂ env fuel (P₂.initState m inp))
      (run P₁ env fuel (P₁.initState m inp))) : Bad m :=
  EquivOn.changed_subset h m hm

/-- A program is equivalent to itself on every input. -/
theorem cobolEquivOn_refl (fs : List FieldDesc) (P : Program) (env : Env) (fuel : Nat)
    (inp : List (Nat × List (List UInt8))) : CobolEquivOn (fun _ => False) fs P P env fuel inp :=
  fun _ _ => (equiv_exec_iff _ _).2 ⟨Iff.rfl, fun _ => obsEq_refl fs _⟩

end EquivLean.Cobol
