import StrictTS.Lib.Dyn
import StrictTS.Proof.Attr

/-!
# `===` of an unknown value with `undefined` or `null` never panics

`Dyn.eq` answers `none` only for two values of the same type without identity (records, tuples,
functions). Against `undefined` or `null` it always answers: the value is `undefined` (`null`) exactly
when its runtime type is. These rewrites let `x == null`, `x === undefined` and `x === null` on unknown
values evaluate symbolically (the translator lowers each to `.dynEq` against the literal).
-/

namespace StrictTS.Dyn

variable {TT : TypeTable}

@[ts_sym] theorem eq_undef_right (a : Val TT .dyn) :
    Dyn.eq a (.dyn .undef .undef) = some (decide ((Dyn.base a).1 = .undef)) := by
  unfold Dyn.eq
  have hb : Dyn.base (Val.dyn Ty.undef (Val.undef : Val TT .undef)) = ⟨.undef, .undef⟩ := rfl
  rw [hb]
  rcases Dyn.base a with ⟨ta, x⟩
  dsimp only
  have hs : Dyn.strOf Ty.undef (Val.undef : Val TT .undef) = none := rfl
  rw [hs]
  by_cases h : ta = Ty.undef
  · subst h
    cases x
    rfl
  · have h' : ¬ Ty.undef = ta := fun e => h e.symm
    cases Dyn.strOf ta x <;> simp [h, h']

@[ts_sym] theorem eq_null_right (a : Val TT .dyn) :
    Dyn.eq a (.dyn .null .null) = some (decide ((Dyn.base a).1 = .null)) := by
  unfold Dyn.eq
  have hb : Dyn.base (Val.dyn Ty.null (Val.null : Val TT .null)) = ⟨.null, .null⟩ := rfl
  rw [hb]
  rcases Dyn.base a with ⟨ta, x⟩
  dsimp only
  have hs : Dyn.strOf Ty.null (Val.null : Val TT .null) = none := rfl
  rw [hs]
  by_cases h : ta = Ty.null
  · subst h
    cases x
    rfl
  · have h' : ¬ Ty.null = ta := fun e => h e.symm
    cases Dyn.strOf ta x <;> simp [h, h']

@[ts_sym] theorem eq_undef_left (a : Val TT .dyn) :
    Dyn.eq (.dyn .undef .undef) a = some (decide ((Dyn.base a).1 = .undef)) := by
  unfold Dyn.eq
  have hb : Dyn.base (Val.dyn Ty.undef (Val.undef : Val TT .undef)) = ⟨.undef, .undef⟩ := rfl
  rw [hb]
  rcases Dyn.base a with ⟨ta, x⟩
  dsimp only
  have hs : Dyn.strOf Ty.undef (Val.undef : Val TT .undef) = none := rfl
  rw [hs]
  by_cases h : ta = Ty.undef
  · subst h
    cases x
    rfl
  · cases Dyn.strOf ta x <;> simp [h]

@[ts_sym] theorem eq_null_left (a : Val TT .dyn) :
    Dyn.eq (.dyn .null .null) a = some (decide ((Dyn.base a).1 = .null)) := by
  unfold Dyn.eq
  have hb : Dyn.base (Val.dyn Ty.null (Val.null : Val TT .null)) = ⟨.null, .null⟩ := rfl
  rw [hb]
  rcases Dyn.base a with ⟨ta, x⟩
  dsimp only
  have hs : Dyn.strOf Ty.null (Val.null : Val TT .null) = none := rfl
  rw [hs]
  by_cases h : ta = Ty.null
  · subst h
    cases x
    rfl
  · cases Dyn.strOf ta x <;> simp [h]

end StrictTS.Dyn
