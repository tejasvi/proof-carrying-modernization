import StrictTS.Lib.Dyn
import StrictTS.Proof.Attr

/-!
# An unknown value passed to an optional unknown parameter

A call `f(x)` with `x : unknown` and `f(value?: unknown)` lowers to the checked cast
`Dyn.cast (.opt .dyn) x` with a non-null assertion, and `f` reads its parameter back as unknown
(`.toDyn (.opt .dyn)`). The cast never fails (`cast_opt_dyn`), and the value read back has the same
runtime value (`base_dyn_optDyn`), so `typeof`, truthiness, `===` and the casts to primitive types
see the original value. These rewrites let a call through a widened `value?: unknown` parameter
(the difftool's compatibility wrapper) evaluate symbolically.
-/

namespace StrictTS.Dyn

variable {TT : TypeTable}

/-- The value of `x : unknown` at type `unknown | undefined` (the cast never fails). -/
def optDyn (v : Val TT .dyn) : Val TT (.opt .dyn) :=
  match Dyn.cast (.opt .dyn) v with
  | some x => x
  | none => .none

theorem castBase_opt_dyn (t : Ty) (x : Val TT t) :
    Dyn.castBase (.opt .dyn) t x = some (if t = .undef then .none else .some (.dyn t x)) := by
  rw [Dyn.castBase]
  split <;> simp [Dyn.castBase]

@[ts_sym] theorem cast_opt_dyn (v : Val TT .dyn) : Dyn.cast (.opt .dyn) v = some (optDyn v) := by
  unfold optDyn
  cases v with
  | dyn t x =>
    unfold Dyn.cast
    split
    · rfl
    · rw [castBase_opt_dyn]

/-- `Dyn.base` returns a value that is its own base. -/
theorem base_base : {t : Ty} → (v : Val TT t) → Dyn.base (Dyn.base v).2 = Dyn.base v
  | _, .some x => by simp only [Dyn.base]; exact base_base x
  | _, .none => rfl
  | _, .inj _ x => by simp only [Dyn.base]; exact base_base x
  | _, .fold x => by simp only [Dyn.base]; exact base_base x
  | _, .dyn _ x => by simp only [Dyn.base]; exact base_base x
  | _, .num _ => rfl
  | _, .bigint _ => rfl
  | _, .bool _ => rfl
  | _, .str _ => rfl
  | _, .undef => rfl
  | _, .null => rfl
  | _, .err _ => rfl
  | _, .arr _ => rfl
  | _, .tarr _ => rfl
  | _, .map _ => rfl
  | _, .set _ => rfl
  | _, .tup _ => rfl
  | _, .record _ => rfl
  | _, .obj _ => rfl
  | _, .enum _ => rfl
  | _, .clo _ _ _ => rfl
  | _, .fnRef _ => rfl
  | _, .resolver _ => rfl
  | _, .rejecter _ _ => rfl
  | _, .promise _ => rfl
  | _, .box _ => rfl
  | _, .ext _ => rfl
  | _, .dict _ => rfl

/-- A base of type `undefined` is `undefined`. -/
theorem base_undef {t : Ty} (v : Val TT t) (h : (Dyn.base v).1 = .undef) :
    Dyn.base v = ⟨.undef, .undef⟩ := by
  rcases hb : Dyn.base v with ⟨t', y⟩
  rw [hb] at h
  dsimp only at h
  subst h
  cases y
  rfl

@[ts_sym] theorem base_optDyn (v : Val TT .dyn) : Dyn.base (optDyn v) = Dyn.base v := by
  have hc := cast_opt_dyn v
  cases v with
  | dyn t x =>
    unfold Dyn.cast at hc
    split at hc
    · rename_i h
      simp only [Option.some.injEq] at hc
      rw [← hc]
      simp only [Val.dynTy] at h
      subst h
      rfl
    · rw [castBase_opt_dyn] at hc
      simp only [Option.some.injEq] at hc
      rw [← hc]
      split
      · rename_i h
        exact (base_undef _ h).symm
      · show Dyn.base (Dyn.base (Val.dyn t x)).2 = Dyn.base (Val.dyn t x)
        exact base_base _

@[ts_sym] theorem base_dyn_optDyn (v : Val TT .dyn) :
    Dyn.base (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.base v := base_optDyn v

/-- A cast of the value read back, to a type whose values are their own base and cast to
themselves, equals the cast of the original value. -/
theorem cast_dyn_opt_of (t : Ty) (ht : Ty.opt Ty.dyn ≠ t)
    (hcast : ∀ x : Val TT t, Dyn.castBase t (Dyn.base x).1 (Dyn.base x).2 = some x)
    (v : Val TT .dyn) : Dyn.cast t (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.cast t v := by
  conv => lhs; unfold Dyn.cast
  split
  · rename_i h
    exact absurd h ht
  show Dyn.castBase t (Dyn.base (optDyn v)).1 (Dyn.base (optDyn v)).2 = _
  rw [base_optDyn]
  cases v with
  | dyn t0 x =>
    unfold Dyn.cast
    split
    · rename_i h
      simp only [Val.dynTy] at h
      subst h
      exact hcast x
    · rfl

@[ts_sym] theorem cast_num_optDyn (v : Val TT .dyn) :
    Dyn.cast .num (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.cast .num v :=
  cast_dyn_opt_of .num (by decide) (fun x => by cases x; simp [Dyn.base, Dyn.castBase]) v

@[ts_sym] theorem cast_str_optDyn (v : Val TT .dyn) :
    Dyn.cast .str (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.cast .str v :=
  cast_dyn_opt_of .str (by decide) (fun x => by cases x; simp [Dyn.base, Dyn.castBase]) v

@[ts_sym] theorem cast_bool_optDyn (v : Val TT .dyn) :
    Dyn.cast .bool (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.cast .bool v :=
  cast_dyn_opt_of .bool (by decide) (fun x => by cases x; simp [Dyn.base, Dyn.castBase]) v

@[ts_sym] theorem cast_bigint_optDyn (v : Val TT .dyn) :
    Dyn.cast .bigint (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.cast .bigint v :=
  cast_dyn_opt_of .bigint (by decide) (fun x => by cases x; simp [Dyn.base, Dyn.castBase]) v

@[ts_sym] theorem typeof_optDyn (v : Val TT .dyn) :
    Dyn.typeof (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.typeof v := by
  unfold Dyn.typeof; rw [base_dyn_optDyn]

@[ts_sym] theorem truthy_optDyn (v : Val TT .dyn) :
    Dyn.truthy (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.truthy v := by
  unfold Dyn.truthy; rw [base_dyn_optDyn]

@[ts_sym] theorem eq_optDyn_left (v b : Val TT .dyn) :
    Dyn.eq (Val.dyn (.opt .dyn) (optDyn v)) b = Dyn.eq v b := by
  unfold Dyn.eq; rw [base_dyn_optDyn]

@[ts_sym] theorem eq_optDyn_right (a v : Val TT .dyn) :
    Dyn.eq a (Val.dyn (.opt .dyn) (optDyn v)) = Dyn.eq a v := by
  unfold Dyn.eq; rw [base_dyn_optDyn]

end StrictTS.Dyn
