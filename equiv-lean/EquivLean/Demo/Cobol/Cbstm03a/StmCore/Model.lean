/-
# CBSTM03A+B: functional model of the transaction table

`8500-READTRNX-READ` loads the transaction file into `WS-TRNX-TABLE` (51 cards of 10
transactions): consecutive records with the same card number form one table entry.  `grp`
is that grouping, built record by record as the program builds it (`grpSnoc` adds one record:
to the last group when its card is the card of the group's last record, else as a new group).
-/
import Cobol
open Cobol

namespace Cobol.StmCore

/-- Card number, transaction id and the rest of a 350-byte `TRNX-RECORD`. -/
def tCard (r : List UInt8) : List UInt8 := r.take 16
def tId (r : List UInt8) : List UInt8 := (r.drop 16).take 16
def tRest (r : List UInt8) : List UInt8 := r.drop 32

/-- The card of a group: the card of its last record. -/
def gCard (g : List (List UInt8)) : List UInt8 := tCard (g.getLastD [])

/-- Add a record to the consecutive same-card groups. -/
def grpSnoc (gs : List (List (List UInt8))) (r : List UInt8) : List (List (List UInt8)) :=
  match gs.getLast? with
  | some g => if gCard g = tCard r then gs.dropLast ++ [g ++ [r]] else gs ++ [[r]]
  | none => [[r]]

/-- The consecutive same-card groups of a transaction file. -/
def grp (rs : List (List UInt8)) : List (List (List UInt8)) := rs.foldl grpSnoc []

/-- Induction from the end of a list. -/
@[elab_as_elim] theorem list_snoc_ind {α : Type _} {motive : List α → Prop} (l : List α)
    (nil : motive []) (snoc : ∀ l a, motive l → motive (l ++ [a])) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a l ih => rw [List.reverse_cons]; exact snoc _ _ ih

theorem grp_nil : grp [] = [] := rfl

theorem grp_snoc (rs : List (List UInt8)) (r : List UInt8) :
    grp (rs ++ [r]) = grpSnoc (grp rs) r := by
  simp [grp, List.foldl_append]

/-- The last group ends with the last record. -/
theorem grp_getLast (rs : List (List UInt8)) (r : List UInt8) :
    ∃ g, (grp (rs ++ [r])).getLast? = some (g ++ [r]) := by
  rw [grp_snoc, grpSnoc]
  split
  · rename_i g _
    split
    · exact ⟨g, by simp⟩
    · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩

theorem grp_eq_nil (rs : List (List UInt8)) : grp rs = [] ↔ rs = [] := by
  constructor
  · intro h
    induction rs using list_snoc_ind with
    | nil => rfl
    | snoc rs r _ =>
      obtain ⟨g, hg⟩ := grp_getLast rs r
      rw [h] at hg
      simp at hg
  · rintro rfl; rfl

/-- The card of the last group is the card of the last record. -/
theorem gCard_getLast (rs : List (List UInt8)) (r : List UInt8) (g : List (List UInt8))
    (h : (grp (rs ++ [r])).getLast? = some g) : gCard g = tCard r := by
  obtain ⟨g', hg'⟩ := grp_getLast rs r
  rw [h] at hg'
  cases hg'
  simp [gCard]

/-- Adding a record keeps the earlier groups and extends the last one, or adds a group. -/
theorem grpSnoc_cases (gs : List (List (List UInt8))) (r : List UInt8) :
    (gs = [] ∧ grpSnoc gs r = [[r]]) ∨
    (∃ g, gs.getLast? = some g ∧ gCard g = tCard r ∧ grpSnoc gs r = gs.dropLast ++ [g ++ [r]]) ∨
    (∃ g, gs.getLast? = some g ∧ gCard g ≠ tCard r ∧ grpSnoc gs r = gs ++ [[r]]) := by
  unfold grpSnoc
  split
  · rename_i g hg
    by_cases h : gCard g = tCard r
    · exact Or.inr (Or.inl ⟨g, hg, h, by simp [h]⟩)
    · exact Or.inr (Or.inr ⟨g, hg, h, by simp [h]⟩)
  · rename_i hg
    exact Or.inl ⟨by simpa using hg, rfl⟩

theorem getD_append_left' {α : Type _} (l l' : List α) (d : α) (i : Nat) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type _} (l l' : List α) (d : α) (i : Nat) (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_dropLast' {α : Type _} (l : List α) (d : α) (i : Nat) (h : i < l.dropLast.length) :
    l.dropLast.getD i d = l.getD i d := by
  simp only [List.length_dropLast] at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_dropLast, h, ↓reduceIte]

theorem getD_last' {α : Type _} (l : List α) (d g : α) (h : l.getLast? = some g) :
    l.getD (l.length - 1) d = g := by
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- Group count and group lengths only grow along the file. -/
theorem grp_mono (a b : List (List UInt8)) :
    (grp a).length ≤ (grp (a ++ b)).length ∧
    ∀ i, i < (grp a).length → ((grp a).getD i []).length ≤ ((grp (a ++ b)).getD i []).length := by
  induction b using list_snoc_ind with
  | nil => simp
  | snoc b r ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [← List.append_assoc, grp_snoc]
    rcases grpSnoc_cases (grp (a ++ b)) r with ⟨h0, h⟩ | ⟨g, hg, -, h⟩ | ⟨g, hg, -, h⟩
    · rw [h0] at ih1
      simp only [List.length_nil, Nat.le_zero] at ih1
      simp [ih1]
    · rw [h]
      have hne : grp (a ++ b) ≠ [] := by intro h'; simp [h'] at hg
      have hpos := List.length_pos_iff.mpr hne
      have hl : (grp (a ++ b)).dropLast.length + 1 = (grp (a ++ b)).length := by
        simp; omega
      refine ⟨by simp; omega, fun i hi => ?_⟩
      have h2 := ih2 i hi
      by_cases hi2 : i < (grp (a ++ b)).dropLast.length
      · rw [getD_append_left' _ _ _ _ hi2, getD_dropLast' _ _ _ hi2]
        exact h2
      · have hi3 : i = (grp (a ++ b)).length - 1 := by omega
        rw [getD_append_right' _ _ _ _ (by omega)]
        have hlast : (grp (a ++ b)).getD i [] = g := by rw [hi3]; exact getD_last' _ _ _ hg
        rw [hlast] at h2
        have : i - (grp (a ++ b)).dropLast.length = 0 := by omega
        rw [this]; simp only [List.getD_cons_zero, List.length_append, List.length_singleton]; omega
    · rw [h]
      refine ⟨by simp; omega, fun i hi => ?_⟩
      have h2 := ih2 i hi
      rwa [getD_append_left' _ _ _ _ (by omega)]

theorem getD_snoc_eq {α : Type _} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  rw [getD_append_right' _ _ _ _ (Nat.le_refl _)]; simp

theorem getD_snoc_lt {α : Type _} (l : List α) (a d : α) (i : Nat) (h : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := getD_append_left' _ _ _ _ h

theorem getLastD_snoc {α : Type _} (l : List α) (a d : α) : (l ++ [a]).getLastD d = a := by
  simp [List.getLastD_eq_getLast?]

theorem grp_snoc_same (done : List (List UInt8)) (cur : List UInt8)
    (gs0 : List (List (List UInt8))) (g : List (List UInt8)) (hgs : grp done = gs0 ++ [g])
    (h : gCard g = tCard cur) : grp (done ++ [cur]) = gs0 ++ [g ++ [cur]] := by
  rw [grp_snoc, hgs, grpSnoc]; simp [h]

theorem grp_snoc_diff (done : List (List UInt8)) (cur : List UInt8)
    (gs0 : List (List (List UInt8))) (g : List (List UInt8)) (hgs : grp done = gs0 ++ [g])
    (h : gCard g ≠ tCard cur) : grp (done ++ [cur]) = gs0 ++ [g] ++ [[cur]] := by
  rw [grp_snoc, hgs, grpSnoc]; simp [h]

/-- The bounds of the whole file's groups hold for the groups of every prefix. -/
theorem grp_bounds (a b : List (List UInt8)) (hG : (grp (a ++ b)).length ≤ 50)
    (hT : ∀ g ∈ grp (a ++ b), g.length ≤ 10) :
    (grp a).length ≤ 50 ∧ ∀ i, i < (grp a).length → ((grp a).getD i []).length ≤ 10 := by
  obtain ⟨h1, h2⟩ := grp_mono a b
  refine ⟨by omega, fun i hi => ?_⟩
  have hmem : (grp (a ++ b)).getD i [] ∈ grp (a ++ b) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  exact Nat.le_trans (h2 i hi) (hT _ hmem)

/-- A nonempty file's groups end with a group. -/
theorem grp_snoc_form (done : List (List UInt8)) (h : done ≠ []) :
    ∃ gs0 g, grp done = gs0 ++ [g] ∧ gCard g = tCard (done.getLastD []) := by
  obtain ⟨d0, d, rfl⟩ : ∃ d0 d, done = d0 ++ [d] := ⟨done.dropLast, done.getLast h,
    (List.dropLast_concat_getLast h).symm⟩
  obtain ⟨g', hg'⟩ := grp_getLast d0 d
  refine ⟨(grp (d0 ++ [d])).dropLast, g' ++ [d], ?_, ?_⟩
  · have hne : grp (d0 ++ [d]) ≠ [] := by intro h'; simp [h'] at hg'
    conv => lhs; rw [← List.dropLast_concat_getLast hne]
    congr 2
    rw [List.getLast?_eq_some_getLast hne] at hg'
    exact Option.some.inj hg'
  · simp [gCard]

end Cobol.StmCore
