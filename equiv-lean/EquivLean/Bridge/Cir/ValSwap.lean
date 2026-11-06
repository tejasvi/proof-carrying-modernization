import CIR

/-!
# Two writes into one structured value, in either order

`Val.set?_swap`: writing `x` at path `p` and then `y` at path `q` gives the same value as the
other order when both positions hold leaf values (`Val.IsLeaf`; values that passed a typed load
are leaves, `Val.isLeaf_of_fitsTy`). Equal positions need equal written values. This lets a
tactic match two C functions that write the same two locations in a different order.

Proof: one path step at a time through `Val.child?` (the child at a step) and `Val.setChild`
(replace that child). Two leaf positions are either equal or diverge at one step, at two
different indices of the same list, and writes at two different indices of a list commute.
-/

namespace EquivLean.Cir
open CIR

/-- A leaf value: no path step descends into it. -/
def Val.IsLeaf : Val → Prop
  | .agg _ => False
  | .arr _ => False
  | .vec _ _ => False
  | .opt _ => False
  | _ => True

end EquivLean.Cir

/- Field notation `a.IsLeaf` for `a : CIR.Val` looks up `CIR.Val.IsLeaf`: an alias of
`EquivLean.Cir.Val.IsLeaf` (no new constant). -/
namespace CIR.Val
export EquivLean.Cir.Val (IsLeaf)
end CIR.Val

namespace EquivLean.Cir
open CIR

/-- Values that pass a typed-load check are leaves. -/
theorem Val.isLeaf_of_fitsTy {ty : Ty} {a : Val} (h : fitsTy ty a = true) : a.IsLeaf := by
  cases a <;> first | trivial | (cases ty <;> cases h)

/-! ### One path step -/

/-- The child of a value at one path step (`none` where `Val.get?` does not descend). -/
def Val.child? : Val → PathElem → Option Val
  | .agg fs, .idx i => fs[i]?
  | .arr xs, .idx i => xs[i]?
  | .vec g xs, .vel g' i => if g = g' then xs[i]? else none
  | .opt (some v), .idx 0 => some v
  | _, _ => none

/-- Replace the child at one path step (used where `Val.child?` finds a child). -/
def Val.setChild : Val → PathElem → Val → Val
  | .agg fs, .idx i, c => .agg (fs.set i c)
  | .arr xs, .idx i, c => .arr (xs.set i c)
  | .vec g xs, .vel _ i, c => .vec g (xs.set i c)
  | .opt (some _), .idx 0, c => .opt (some c)
  | v, _, _ => v

/-- `Val.get?` takes one step through `Val.child?`. -/
theorem Val.get?_cons (v : Val) (e : PathElem) (p : List PathElem) :
    v.get? (e :: p) = (Val.child? v e).bind (fun c => c.get? p) := by
  cases v with
  | agg fs => cases e with
    | idx i => simp only [Val.get?, Val.child?]; cases fs[i]? <;> rfl
    | _ => rfl
  | arr xs => cases e with
    | idx i => simp only [Val.get?, Val.child?]; cases xs[i]? <;> rfl
    | _ => rfl
  | vec g xs => cases e with
    | vel g' i =>
      simp only [Val.get?, Val.child?]
      split
      · cases xs[i]? <;> rfl
      · rfl
    | _ => rfl
  | opt o => cases o with
    | none => cases e <;> rfl
    | some c => cases e with
      | idx i => cases i <;> rfl
      | _ => rfl
  | _ => cases e <;> rfl

/-- `Val.set?` takes one step through `Val.child?` and puts the new child back (`Val.setChild`). -/
theorem Val.set?_cons (v : Val) (e : PathElem) (p : List PathElem) (w : Val) :
    v.set? (e :: p) w = (Val.child? v e).bind (fun c => (c.set? p w).map (Val.setChild v e)) := by
  cases v with
  | agg fs => cases e with
    | idx i =>
      simp only [Val.set?, Val.child?]
      cases fs[i]? with
      | none => rfl
      | some f => simp only [Option.bind_some]; cases f.set? p w <;> rfl
    | _ => rfl
  | arr xs => cases e with
    | idx i =>
      simp only [Val.set?, Val.child?]
      cases xs[i]? with
      | none => rfl
      | some f => simp only [Option.bind_some]; cases f.set? p w <;> rfl
    | _ => rfl
  | vec g xs => cases e with
    | vel g' i =>
      simp only [Val.set?, Val.child?]
      split
      · cases xs[i]? with
        | none => rfl
        | some f => simp only [Option.bind_some]; cases f.set? p w <;> rfl
      · rfl
    | _ => rfl
  | opt o => cases o with
    | none => cases e <;> rfl
    | some c => cases e with
      | idx i => cases i with
        | zero => simp only [Val.set?, Val.child?, Option.bind_some]; cases c.set? p w <;> rfl
        | succ _ => rfl
      | _ => rfl
  | _ => cases e <;> rfl

/-- A leaf has no children. -/
theorem Val.child?_of_isLeaf {v : Val} (h : v.IsLeaf) (e : PathElem) : Val.child? v e = none := by
  cases v <;> first | exact (h : False).elim | (cases e <;> rfl)

/-- No path step resolves inside a leaf. -/
theorem Val.get?_leaf_cons {a : Val} (h : a.IsLeaf) (e : PathElem) (q : List PathElem) :
    a.get? (e :: q) = none := by
  rw [Val.get?_cons, Val.child?_of_isLeaf h]; rfl

/-- Reading a replaced child gives the new child. -/
theorem Val.child?_setChild_self {v c c' : Val} {e : PathElem} (h : Val.child? v e = some c) :
    Val.child? (Val.setChild v e c') e = some c' := by
  cases v with
  | agg fs => cases e with
    | idx i =>
      simp only [Val.child?, Val.setChild] at h ⊢
      exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1
    | _ => cases h
  | arr xs => cases e with
    | idx i =>
      simp only [Val.child?, Val.setChild] at h ⊢
      exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1
    | _ => cases h
  | vec g xs => cases e with
    | vel g' i =>
      simp only [Val.child?, Val.setChild] at h ⊢
      by_cases hg : g = g'
      · rw [ite_eq_left hg] at h ⊢
        exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1
      · rw [ite_eq_right hg] at h; cases h
    | _ => cases h
  | opt o => cases o with
    | none => cases e <;> cases h
    | some w => cases e with
      | idx i => cases i with
        | zero => rfl
        | succ _ => cases h
      | _ => cases h
  | _ => cases e <;> cases h

/-- Replacing the same child twice keeps the last one. -/
theorem Val.setChild_setChild_self (v : Val) (e : PathElem) (c' c'' : Val) :
    Val.setChild (Val.setChild v e c') e c'' = Val.setChild v e c'' := by
  cases v with
  | agg fs => cases e with
    | idx i => simp only [Val.setChild, List.set_set]
    | _ => rfl
  | arr xs => cases e with
    | idx i => simp only [Val.setChild, List.set_set]
    | _ => rfl
  | vec g xs => cases e with
    | vel g' i => simp only [Val.setChild, List.set_set]
    | _ => rfl
  | opt o => cases o with
    | none => cases e <;> rfl
    | some w => cases e with
      | idx i => cases i <;> rfl
      | _ => rfl
  | _ => cases e <;> rfl

/-- Replacing one child leaves another child unchanged. -/
theorem Val.child?_setChild_ne {v c d c' : Val} {e e' : PathElem}
    (hc : Val.child? v e = some c) (hd : Val.child? v e' = some d) (hne : e ≠ e') :
    Val.child? (Val.setChild v e c') e' = some d := by
  cases v with
  | agg fs => cases e with
    | idx i => cases e' with
      | idx j =>
        have hij : i ≠ j := fun h => hne (h ▸ rfl)
        simp only [Val.child?, Val.setChild] at hd ⊢
        rw [List.getElem?_set_ne hij]; exact hd
      | _ => cases hd
    | _ => cases hc
  | arr xs => cases e with
    | idx i => cases e' with
      | idx j =>
        have hij : i ≠ j := fun h => hne (h ▸ rfl)
        simp only [Val.child?, Val.setChild] at hd ⊢
        rw [List.getElem?_set_ne hij]; exact hd
      | _ => cases hd
    | _ => cases hc
  | vec g xs => cases e with
    | vel g1 i => cases e' with
      | vel g2 j =>
        simp only [Val.child?, Val.setChild] at hc hd ⊢
        by_cases hg1 : g = g1
        · by_cases hg2 : g = g2
          · subst hg1; subst hg2
            have hij : i ≠ j := fun h => hne (h ▸ rfl)
            rw [ite_eq_left rfl] at hd ⊢
            rw [List.getElem?_set_ne hij]; exact hd
          · rw [ite_eq_right hg2] at hd; cases hd
        · rw [ite_eq_right hg1] at hc; cases hc
      | _ => cases hd
    | _ => cases hc
  | opt o => cases o with
    | none => cases e <;> cases hc
    | some w => cases e with
      | idx i => cases i with
        | zero => cases e' with
          | idx j => cases j with
            | zero => exact absurd rfl hne
            | succ _ => cases hd
          | _ => cases hd
        | succ _ => cases hc
      | _ => cases hc
  | _ => cases e <;> cases hc

/-- Replacing two different children commutes. -/
theorem Val.setChild_comm {v c d c' d' : Val} {e e' : PathElem}
    (hc : Val.child? v e = some c) (hd : Val.child? v e' = some d) (hne : e ≠ e') :
    Val.setChild (Val.setChild v e c') e' d' = Val.setChild (Val.setChild v e' d') e c' := by
  cases v with
  | agg fs => cases e with
    | idx i => cases e' with
      | idx j =>
        have hij : i ≠ j := fun h => hne (h ▸ rfl)
        simp only [Val.setChild, List.set_comm c' d' hij]
      | _ => cases hd
    | _ => cases hc
  | arr xs => cases e with
    | idx i => cases e' with
      | idx j =>
        have hij : i ≠ j := fun h => hne (h ▸ rfl)
        simp only [Val.setChild, List.set_comm c' d' hij]
      | _ => cases hd
    | _ => cases hc
  | vec g xs => cases e with
    | vel g1 i => cases e' with
      | vel g2 j =>
        simp only [Val.child?] at hc hd
        by_cases hg1 : g = g1
        · by_cases hg2 : g = g2
          · subst hg1; subst hg2
            have hij : i ≠ j := fun h => hne (h ▸ rfl)
            simp only [Val.setChild, List.set_comm c' d' hij]
          · rw [ite_eq_right hg2] at hd; cases hd
        · rw [ite_eq_right hg1] at hc; cases hc
      | _ => cases hd
    | _ => cases hc
  | opt o => cases o with
    | none => cases e <;> cases hc
    | some w => cases e with
      | idx i => cases i with
        | zero => cases e' with
          | idx j => cases j with
            | zero => exact absurd rfl hne
            | succ _ => cases hd
          | _ => cases hd
        | succ _ => cases hc
      | _ => cases hc
  | _ => cases e <;> cases hc

/-! ### Swapping two writes -/

/-- Writes at two leaf positions commute (equal positions: equal written values). -/
theorem Val.set?_swap {v w1 w2 a b x y : Val} {p q : List PathElem}
    (hp : v.get? p = some a) (hq : v.get? q = some b) (ha : a.IsLeaf) (hb : b.IsLeaf)
    (hxy : p = q → x = y) (h1 : v.set? p x = some w1) (h2 : w1.set? q y = some w2) :
    ∃ w1', v.set? q y = some w1' ∧ w1'.set? p x = some w2 := by
  induction p generalizing v q a b w1 w2 with
  | nil =>
    have hva : v = a := Option.some.inj hp
    subst hva
    cases q with
    | nil =>
      have hxy' : x = y := hxy rfl
      subst hxy'
      have hw1 : x = w1 := Option.some.inj h1
      subst hw1
      have hw2 : x = w2 := Option.some.inj h2
      subst hw2
      exact ⟨x, rfl, rfl⟩
    | cons e' q' =>
      rw [Val.get?_leaf_cons ha] at hq
      cases hq
  | cons e p' ih =>
    rw [Val.get?_cons] at hp
    obtain ⟨c, hc, hca⟩ := Option.bind_eq_some_iff.mp hp
    simp only [Val.set?_cons, hc, Option.bind_some] at h1
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h1
    cases q with
    | nil =>
      have hvb : v = b := Option.some.inj hq
      subst hvb
      rw [Val.child?_of_isLeaf hb] at hc
      cases hc
    | cons e' q' =>
      rw [Val.get?_cons] at hq
      obtain ⟨d, hd, hdb⟩ := Option.bind_eq_some_iff.mp hq
      by_cases hee : e = e'
      · subst hee
        rw [hc] at hd
        cases hd
        simp only [Val.set?_cons, Val.child?_setChild_self hc, Option.bind_some] at h2
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h2
        obtain ⟨w1'', h3, h4⟩ := ih hca hdb ha hb (fun h => hxy (by rw [h])) hc' hd'
        refine ⟨Val.setChild v e w1'', ?_, ?_⟩
        · simp only [Val.set?_cons, hc, Option.bind_some, h3, Option.map_some]
        · simp only [Val.set?_cons, Val.child?_setChild_self hc, Option.bind_some, h4,
            Option.map_some, Val.setChild_setChild_self]
      · simp only [Val.set?_cons, Val.child?_setChild_ne hc hd hee, Option.bind_some] at h2
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h2
        refine ⟨Val.setChild v e' d', ?_, ?_⟩
        · simp only [Val.set?_cons, hd, Option.bind_some, hd', Option.map_some]
        · simp only [Val.set?_cons, Val.child?_setChild_ne hd hc (Ne.symm hee), Option.bind_some,
            hc', Option.map_some, Val.setChild_comm hc hd hee]

end EquivLean.Cir

