import Cobol
open Cobol

/-- Soundness of de-editing, for every picture, content and configuration: the de-edited value is
a value whose editing is the content, or it is 0 and the content is the editing of a negative value
that editing truncated to zero (`-0.00`). (`scripts/lean1.sh tests/DeEditSound.lean`) -/
theorem deEdit_sound (c : Config) (pic : List ESym) (bwz : Bool) (bs : List UInt8) (w t : Int)
    (h : Sem.deEdit c pic bwz bs = .ok (w, t)) :
    Edit.edit c pic bwz w t = some bs ∨ (w = 0 ∧ Edit.edit c pic bwz (-1) (t + 1) = some bs) := by
  unfold Sem.deEdit at h
  dsimp only at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · rename_i hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      left
      rw [he, beq_iff_eq.mp hb]
    · split at h
      · rename_i hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        left
        exact beq_iff_eq.mp hb
      · split at h
        · rename_i hb
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          right
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact ⟨rfl, hb.2⟩
        · cases h

#print axioms deEdit_sound
