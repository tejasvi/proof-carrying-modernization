import EquivLean.Modernize.Cbact04c.Every.JavaRunModelFacts

/-!
# CBACT04C: what holds of every state of `Model.run`

The account table keeps its ids and groups, its records stay valid; the current account and
cross-reference are the lookups of the last account id; the running total stays below `10^11`
and the transaction suffix below `10^6`.
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Model

abbrev FV := EquivLean.Cobol.Rec.FVal

theorem replaceFirst_map {α β : Type} (p : α → Bool) (x : α) (f : α → β)
    (hx : ∀ y, p y = true → f x = f y) : ∀ l : List α, (replaceFirst p x l).map f = l.map f
  | [] => rfl
  | y :: ys => by
    simp only [replaceFirst]
    split
    · next h => simp [hx y h]
    · simp [replaceFirst_map p x f hx ys]

theorem mem_replaceFirst {α : Type} (p : α → Bool) (x : α) :
    ∀ (l : List α) (a : α), a ∈ replaceFirst p x l → a = x ∨ a ∈ l
  | [], a, h => by simp [replaceFirst] at h
  | y :: ys, a, h => by
    simp only [replaceFirst] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rcases mem_replaceFirst p x ys a h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem getD_set_ne {α : Type} (l : List α) (i j : Nat) (v d : α) (h : i ≠ j) :
    (l.set i v).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem aId_posted (a : List FV) (t : Int) : aId (posted a t) = aId a := by
  simp only [aId, posted, getD_set_ne _ _ _ _ _ (by decide : (9 : Nat) ≠ 0),
    getD_set_ne _ _ _ _ _ (by decide : (8 : Nat) ≠ 0), getD_set_ne _ _ _ _ _ (by decide : (2 : Nat) ≠ 0)]

theorem aGrp_posted (a : List FV) (t : Int) : aGrp (posted a t) = aGrp a := by
  simp only [aGrp, posted, getD_set_ne _ _ _ _ _ (by decide : (9 : Nat) ≠ 11),
    getD_set_ne _ _ _ _ _ (by decide : (8 : Nat) ≠ 11), getD_set_ne _ _ _ _ _ (by decide : (2 : Nat) ≠ 11)]

theorem find?_mem_of_exists {α : Type} (p : α → Bool) (l : List α) (h : ∃ a ∈ l, p a = true) :
    ∃ a, l.find? p = some a ∧ a ∈ l ∧ p a = true := by
  obtain ⟨i, hi, hp, hj⟩ := exists_first p l h
  exact ⟨l[i], find?_eq_getElem p l i hi hp hj, List.getElem_mem hi, hp⟩

theorem findAcct_spec (accts : List (List FV)) (id : Int) (h : ∃ a ∈ accts, aId a = id) :
    findAcct accts id ∈ accts ∧ aId (findAcct accts id) = id := by
  obtain ⟨a, ha, haid⟩ := h
  obtain ⟨b, hb, hbm, hbp⟩ := find?_mem_of_exists (fun a => aId a == id) accts ⟨a, ha, by simpa using haid⟩
  simp only [findAcct, hb, Option.getD_some]
  exact ⟨hbm, by simpa using hbp⟩

/-- Two tables with the same ids and groups give the found account the same group. -/
theorem aGrp_findAcct_of_map : ∀ (l l' : List (List FV)) (id : Int),
    l.map aId = l'.map aId → l.map aGrp = l'.map aGrp →
    aGrp (findAcct l id) = aGrp (findAcct l' id)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: l, a' :: l', id, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    simp only [findAcct, List.find?_cons]
    rw [h1.1]
    split
    · simp [h2.1]
    · exact aGrp_findAcct_of_map l l' id h1.2 h2.2

end EquivLean.Modernize.Cbact04c.Model
