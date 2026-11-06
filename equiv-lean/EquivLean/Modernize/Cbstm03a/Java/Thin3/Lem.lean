import EquivLean.Modernize.Cbstm03a.Java.Thin3.Cut
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java, `run`'s thin VC: frames for the segments (namespace `…Java.Thin3`)

`KeepsK`: a callee's `Keeps`, kept folded across the symbolic executor (as `GrowsK` for `Grows`); `keeps_split`
gives the executor the unfolded facts. `slotsAt_mono`: the slots array unchanged and every string kept.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

/-- A callee's `Keeps`, kept folded across the symbolic executor. -/
@[irreducible] def KeepsK (A : Addr → Prop) (σ σ' : State) : Prop := Keeps A σ σ'

/-- `Keeps` for the executor: a folded copy, and the facts it unfolds to. -/
theorem keeps_split (A : Addr → Prop) (σ σ' : State) :
    Keeps A σ σ' ↔ KeepsK A σ σ' ∧ σ.next ≤ σ'.next ∧ ∀ y, y < σ.next → ¬ A y → σ'.heap y = σ.heap y := by
  constructor
  · intro h; exact ⟨by unfold KeepsK; exact h, h.1, h.2⟩
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

theorem keepsK_elim {A : Addr → Prop} {σ σ' : State} (h : KeepsK A σ σ') : Keeps A σ σ' := by
  unfold KeepsK at h; exact h

theorem slotsAt_mono {σ σ' : State} {a : Addr} {m : Nat → JChar} (h : SlotsAt σ a m)
    (ha : σ'.heap a = σ.heap a) (hs : StrMono σ σ') : SlotsAt σ' a m := by
  obtain ⟨vs, h1, h2, h3⟩ := h
  refine ⟨vs, ha.trans h1, h2, fun i hi => ?_⟩
  rcases h3 i hi with h4 | ⟨x, t, h5, h6, h7, h8⟩
  · exact Or.inl h4
  · exact Or.inr ⟨x, t, h5, hs x t h6, h7, h8⟩

/-- Two objects of different contents are at different addresses (`jdisch`'s `jne_heap` is off without
`jimple.modelContracts`). -/
theorem ne_of_heap {σ : State} {a b : Addr} {o1 o2 : Obj} (h1 : σ.heap a = some o1) (h2 : σ.heap b = some o2)
    (h : o1 ≠ o2) : a ≠ b := fun e => h (by rw [e] at h1; rw [h1] at h2; exact Option.some.inj h2)

theorem slotsAt_heap {σ : State} {a : Addr} {m : Nat → JChar} (h : SlotsAt σ a m) :
    ∃ vs, σ.heap a = some (.array (.cls "java.lang.String") vs) := by
  obtain ⟨vs, h1, -, -⟩ := h
  exact ⟨vs, h1⟩

/-- A new `int[2]` (the simproc expanding `List.replicate` at literals is turned off in the segment files: it
spelled out the 561 slots and the 1000 spaces of `spaces(1000)`). -/
theorem rep2 {α : Type} (x : α) : List.replicate 2 x = [x, x] := rfl

end EquivLean.Modernize.Cbstm03a.Java.Thin3
