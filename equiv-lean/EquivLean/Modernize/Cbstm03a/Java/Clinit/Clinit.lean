import EquivLean.Modernize.Cbstm03a.Java.Clinit.VC

/-!
# CBSTM03A → Java: `ClinitRan` gives the `CP037` table

The contract of `Cbstm03a.<clinit>` (`clinitSpec`, verified in `CbAClinit.VC` against itself: the class
initialization of its first `putstatic` may run `<clinit>` again) holds for every run; a normal run from any
state ends with the static `CP037` holding an allocated `int` array with the entries `cp037Arr`. `ClinitRan`
transfers the statics and the objects of that run's final state to `σ`.
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- `EquivLean.Jimple.ClinitRan` (equiv-lean `EquivLean/Bridge/Jimple/Init.lean`), verbatim: its module is not
on this build's path; at packaging the original replaces this copy. The static initializer of class `c` has
run: `c` is initialized, its static fields hold what `<clinit>` stored, and the objects that existed when
`<clinit>` returned are unchanged. -/
def ClinitRanC (P : Program) (c : ClassName) (σ : State) : Prop :=
  σ.initOf c = .done ∧ ∃ m σ0 σ1, P.clinitOf c = some m ∧ MExec P ⟨c, m⟩ [] σ0 (.normal none σ1) ∧
    (∀ f, σ.static (c, f) = σ1.static (c, f)) ∧ (∀ x, x < σ1.next → σ.heap x = σ1.heap x)

theorem selectSpecial_clinit :
    Gen.prog.selectSpecial (clinitSig "Cbstm03a") = .native "java.lang.Object" := rfl

/-- Annotations of `<clinit>` (its cut points and exploration budget). -/
def clinitAnn : Annotations := ⟨fun _ => clinitInv, fun _ => 100⟩

/-- The contract table of `<clinit>` holds. -/
theorem clinit_valid : Valid Gen.prog clinitT.env := by
  apply Contracts.valid (d := 0) (Ann := clinitAnn)
  intro p hp
  simp only [clinitT, List.mem_singleton] at hp
  subst hp
  simp only [ContractVC]
  refine ⟨fun m ht => ?_, fun c _ _ hst => ?_⟩
  · obtain ⟨hsel, _⟩ := ht
    have hm : m = clinitRef := by
      rcases hsel with h | h | ⟨hs, hd⟩
      · rw [selectStatic_clinit] at h
        cases h
        rfl
      · rw [selectSpecial_clinit] at h
        cases h
      · obtain ⟨c, d⟩ := m
        have hc : "Cbstm03a" = c := congrArg MethodSig.cls hs
        subst hc
        dsimp only at hd
        rw [clinitOf_eq] at hd
        cases hd
        rfl
    subst hm
    exact clinit_vc
  · exact absurd (staticDecl_clinit.symm.trans hst) (by decide)

/-- Every run of `<clinit>` satisfies its contract. -/
theorem clinit_sat : Sat Gen.prog clinitRef clinitSpec :=
  (clinit_valid (clinitSig "Cbstm03a") clinitSpec clinitT_env).1 clinitRef ⟨Or.inl selectStatic_clinit, rfl⟩

/-- After `Cbstm03a`'s static initializer has run (`ClinitRan`), the class is initialized and its static
`CP037` holds the code page table. -/
theorem cp037At_of_clinitRan {σ : State} (h : ClinitRanC Gen.prog "Cbstm03a" σ) : CP037At σ := by
  obtain ⟨hdone, m, σ0, σ1, hm, hex, hst, hheap⟩ := h
  rw [clinitOf_eq] at hm
  cases hm
  have hpost : (σ0.initOf "Cbstm03a" = .done → σ1.initOf "Cbstm03a" = .done) ∧
      ∃ a, σ1.static ("Cbstm03a", "CP037") = some (.ref a) ∧
        σ1.heap a = some (.array (.prim .int) cp037Arr) ∧ a < σ1.next :=
    clinit_sat [] σ0 _ trivial hex
  obtain ⟨-, a, h1, h2, h3⟩ := hpost
  unfold CP037At
  exact ⟨hdone, a, (hst "CP037").trans h1, (hheap a h3).trans h2⟩

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.cp037At_of_clinitRan
