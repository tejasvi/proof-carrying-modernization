import EquivLean.Modernize.Cbstm03a.Java.RunInv
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java `run`, the load loop (statement 80): frames and pure facts

`KeepsK`: a callee's `Keeps`, kept folded across the symbolic executor (as `GrowsK` for `Grows`); `keeps_split`
gives the executor the unfolded facts. Lengths of the records the load reads; one load step keeps the bounds.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK growsK_elim
  grows_split keeps_refl keeps_trans keeps_of_grows Kept zpadStr_length fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- A callee's `Keeps`, kept folded across the symbolic executor. -/
@[irreducible] def KeepsK (A : Addr → Prop) (σ σ' : State) : Prop := Keeps A σ σ'

theorem keepsK_elim {A : Addr → Prop} {σ σ' : State} (h : KeepsK A σ σ') : Keeps A σ σ' := by
  unfold KeepsK at h; exact h

/-- `Keeps` for the executor: a folded copy, and the facts it unfolds to. -/
theorem keeps_split (A : Addr → Prop) (σ σ' : State) :
    Keeps A σ σ' ↔ KeepsK A σ σ' ∧ σ.next ≤ σ'.next ∧ ∀ y, y < σ.next → ¬ A y → σ'.heap y = σ.heap y := by
  constructor
  · intro h; exact ⟨by unfold KeepsK; exact h, h.1, h.2⟩
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

theorem trnxTextR_length (t : TrnxR) : (trnxTextR t).length = 350 := by
  simp [trnxTextR, zuI, zsI, zpadStr_length, fixStr_length]

theorem T1_length (g : RunG) : g.T1.length = g.trs.length := by simp [RunG.T1]

theorem R1_length (g : RunG) : g.R1.length = g.trs.length := by simp [RunG.R1, RunG.T1]

theorem T1_getD_length (g : RunG) {i : Nat} (h : i < g.T1.length) : (g.T1.getD i []).length = 350 := by
  simp only [RunG.T1] at h ⊢
  rw [List.getD_eq_getElem _ _ h, List.getElem_map, trnxTextR_length]

theorem R1_getD (g : RunG) {i : Nat} (h : i < g.T1.length) :
    g.R1.getD i [] = sub (fixStr (g.T1.getD i []) 1000) 0 350 := by
  have h' : i < g.R1.length := by simp only [RunG.R1, List.length_map]; exact h
  rw [List.getD_eq_getElem _ _ h', List.getD_eq_getElem _ _ h]
  simp [RunG.R1, recOf]

theorem R1_getD_length (g : RunG) {i : Nat} (h : i < g.R1.length) : (g.R1.getD i []).length = 350 := by
  have h' : i < g.T1.length := by simp only [RunG.R1, List.length_map] at h; exact h
  rw [R1_getD g h']
  simp [sub, fixStr_length]

end EquivLean.Modernize.Cbstm03a.Java.Seg2
