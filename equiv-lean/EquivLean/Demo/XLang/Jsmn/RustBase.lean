import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.XLang.Jsmn.RustDefs

/-!
# jsmn → model, Rust side: the representation and the leaf functions

The Rust parser state is a `JsmnParser` (`pos`, `toknext`, `toksuper`) and the whole token array;
the model's state `St` holds the filled tokens only.  `absSt p ts` is the model's view: the first
`toknext` tokens of `ts`.  This file proves the leaf functions (`is_container`, `type_is`,
`is_hex`, `is_simple_escape`, `fill_token`, `alloc_token`) and the list facts the token updates need.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas jsmn_rs

namespace EquivLean.Demo.XLang.Jsmn.Rust

/-! ## Symbolic execution helpers -/

/- The `Decidable` instance is an implicit argument, taken from the goal by unification: the
goal's instance may be a cast left by `simp`, which a synthesized instance only matches after
unfolding both (deep for `Int` bounds). -/

theorem ite_prop_intro {c : Prop} {inst : Decidable c} {P Q : Prop} (h1 : c → P) (h2 : ¬c → Q) :
    @ite Prop c inst P Q := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

theorem dite_prop_intro {c : Prop} {inst : Decidable c} {P : c → Prop} {Q : ¬c → Prop}
    (h1 : ∀ h, P h) (h2 : ∀ h, Q h) : @dite Prop c inst P Q := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

open Lean Meta Elab Tactic in
/-- Splits the goal when it is a `Prop`-valued `if`: the proof term `ite_prop_intro` /
`dite_prop_intro` is built directly, without unification (`refine` can exhaust the recursion
depth on branches holding large `simp`-made proof terms, and `split` simplifies every branch). -/
elab "rust_split1" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) && (t.getArg! 0).isProp do
      throwError "rust_split1: the goal is not an if"
    let c := t.getArg! 1
    let inst := t.getArg! 2
    let a := t.getArg! 3
    let b := t.getArg! 4
    let tag ← g.getTag
    let (ty1, ty2, thm) ←
      if t.isAppOfArity ``ite 5 then
        pure (← mkArrow c a, ← mkArrow (mkNot c) b, ``ite_prop_intro)
      else
        pure (Expr.forallE `h c (mkApp a (.bvar 0)).headBeta .default,
          Expr.forallE `h (mkNot c) (mkApp b (.bvar 0)).headBeta .default, ``dite_prop_intro)
    let g1 ← mkFreshExprSyntheticOpaqueMVar ty1 tag
    let g2 ← mkFreshExprSyntheticOpaqueMVar ty2 tag
    g.assign (mkAppN (mkConst thm) #[c, inst, a, b, g1, g2])
    let (_, g1') ← g1.mvarId!.intro1
    let (_, g2') ← g2.mvarId!.intro1
    replaceMainGoal [g1', g2']

/-- Splits the `if`s of a symbolically executed Rust function, branch by branch. -/
macro "rust_split" : tactic => `(tactic| repeat' rust_split1)

/-- A computation whose outcome satisfies `∃ v, r = .ok v ∧ P v` returns such a `v`. -/
theorem exists_ok_of_wp {α : Type} {c : Result α} {P : α → Prop}
    (h : wp c (fun r => ∃ v, r = .ok v ∧ P v)) : ∃ v, c = Result.ok v ∧ P v := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, ha⟩ | ⟨e, rfl, he⟩
  · obtain ⟨v, hv, hp⟩ := ha
    cases hv
    exact ⟨_, rfl, hp⟩
  · simp at he

theorem eq_ok_of_wp {α : Type} {c : Result α} {v : α} (h : wp c (· = .ok v)) : c = Result.ok v := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, ha⟩ | ⟨e, rfl, he⟩
  · cases ha; rfl
  · cases he

/-- `&mut s[i]` for a slice: the element and the write-back. -/
theorem slice_index_mut_usize_eq {α : Type} (s : Slice α) (i : Usize) :
    Slice.index_mut_usize s i =
      if h : i.val < s.val.length then .ok (s.val[i.val], Slice.set s i) else .fail .arrayOutOfBounds := by
  unfold Slice.index_mut_usize Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  by_cases h : i.val < s.val.length
  · rw [List.getElem?_eq_getElem h, dite_eq_left h]
    simp
  · rw [List.getElem?_eq_none (by omega), dite_eq_right h]
    simp

/-! ## The leaf functions -/

/-- A container token (object or array). -/
def isCont (t : JsmnType) : Bool :=
  match t with
  | .Object => true
  | .Array => true
  | _ => false

theorem is_container_eq (t : JsmnType) : is_container t = .ok (isCont t) := by
  cases t <;> rfl

theorem isCont_iff (t : JsmnType) : isCont t = true ↔ (typeCode t = ARRAY ∨ typeCode t = OBJECT) := by
  cases t <;> decide

/-- `token->type == type` for the type of a closing bracket. -/
def typeIs (t : JsmnType) (object : Bool) : Bool :=
  match t with
  | .Object => object
  | .Array => !object
  | _ => false

theorem type_is_eq (t : JsmnType) (object : Bool) : type_is t object = .ok (typeIs t object) := by
  cases t <;> cases object <;> rfl

theorem typeIs_iff (t : JsmnType) (object : Bool) :
    typeIs t object = true ↔ typeCode t = (if object then OBJECT else ARRAY) := by
  cases t <;> cases object <;> decide

theorem is_hex_eq (h : U8) : is_hex h = .ok (hexDigit h.val) := by
  apply eq_ok_of_wp
  unfold is_hex
  aeneas_wp
  rust_split <;> simp_all [hexDigit]

theorem is_simple_escape_eq (e : U8) : is_simple_escape e = .ok (escChar e.val) := by
  apply eq_ok_of_wp
  unfold is_simple_escape
  aeneas_wp
  rust_split <;> simp_all [escChar, Bool.beq_eq_decide_eq]

theorem fill_token_eq (t : JsmnTok) (ty : JsmnType) (s e : I32) :
    fill_token t ty s e = .ok ⟨ty, s, e, 0#i32⟩ := rfl

/-! ## The model's view of the token array -/

/-- The first `k` tokens of `ts`, as the model's tokens. -/
def mtoks (ts : Slice JsmnTok) (k : Nat) : List Tok := (ts.val.take k).map toTok

/-- The model's view of a Rust parser state. -/
def absSt (p : JsmnParser) (ts : Slice JsmnTok) : St := ⟨p.pos.val, mtoks ts p.toknext.val, p.toksuper.val⟩

theorem mtoks_length {ts : Slice JsmnTok} {k : Nat} (h : k ≤ ts.val.length) : (mtoks ts k).length = k := by
  simp [mtoks, h]

theorem mtoks_getD {ts : Slice JsmnTok} {k i : Nat} (hi : i < k) (hk : k ≤ ts.val.length) (d : Tok) :
    (mtoks ts k).getD i d = toTok (ts.val[i]'(by omega)) := by
  simp [mtoks, List.getD_eq_getElem?_getD, hi, Nat.lt_of_lt_of_le hi hk]

theorem mtoks_set_lt {ts : Slice JsmnTok} {k : Nat} (i : Usize) (x : JsmnTok) :
    mtoks (ts.set i x) k = (mtoks ts k).set i.val (toTok x) := by
  simp only [mtoks, Slice.set_val_eq]
  rw [List.take_set, List.map_set]

theorem mtoks_set_eq {ts : Slice JsmnTok} (i : Usize) (x : JsmnTok) (hi : i.val < ts.val.length) :
    mtoks (ts.set i x) (i.val + 1) = mtoks ts i.val ++ [toTok x] := by
  simp only [mtoks, Slice.set_val_eq]
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]; omega
  · intro j h1 h2
    simp only [List.length_map, List.length_take, List.length_set] at h1
    by_cases hj : j < i.val
    · rw [List.getElem_map, List.getElem_take, List.getElem_set_ne (by omega),
        List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_take]
    · have hj' : j = i.val := by omega
      subst hj'
      rw [List.getElem_map, List.getElem_take, List.getElem_set_self,
        List.getElem_append_right (by simp)]
      simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), Nat.sub_self,
        List.getElem_cons_zero]

theorem mtoks_set_ge {ts : Slice JsmnTok} {k : Nat} (i : Usize) (x : JsmnTok) (hi : k ≤ i.val) :
    mtoks (ts.set i x) k = mtoks ts k := by
  simp only [mtoks, Slice.set_val_eq]
  rw [List.take_set, List.set_eq_of_length_le (by simp; omega)]

end EquivLean.Demo.XLang.Jsmn.Rust
