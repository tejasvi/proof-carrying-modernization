import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunC

/-!
# CBTRN02C → Java: the work-storage records `run` builds

The constructors store their arguments (`setFields`): every field is then present (`WSObj`),
the `FILLER` of spaces is the model's (`WSFill`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem isSome_setFields {cls : ClassName} {k : FieldKey} :
    ∀ {fs : List (FieldKey × Value)} {names : List String} {vals : List Value},
      (Fields.get fs k).isSome → (Fields.get (setFields cls fs names vals) k).isSome
  | _, [], _, h => by simpa [setFields] using h
  | _, _ :: _, [], h => by simpa [setFields] using h
  | fs, n :: ns, v :: vs, h => by
    simp only [setFields]
    refine isSome_setFields ?_
    rw [Fields.get_set]
    split
    · rfl
    · exact h

theorem isSome_setFields_mem {cls : ClassName} {n : String} :
    ∀ {fs : List (FieldKey × Value)} {names : List String} {vals : List Value},
      n ∈ names → names.length ≤ vals.length →
        (Fields.get (setFields cls fs names vals) (cls, n)).isSome
  | _, [], _, h, _ => by simp at h
  | _, _ :: _, [], _, hl => by simp at hl
  | fs, m :: ms, v :: vs, h, hl => by
    simp only [setFields]
    by_cases hm : n ∈ ms
    · exact isSome_setFields_mem hm (by simp at hl; omega)
    · have : n = m := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact h
        · exact absurd h hm
      subst this
      refine isSome_setFields ?_
      rw [Fields.get_set, if_pos rfl]
      rfl

/-- A record object just built by its constructor has all its fields. -/
theorem wsobj_of_setFields {σ : State} {w : Addr} {cls : ClassName} {s : Schema}
    {fs : List (FieldKey × Value)} {names : List String} {vals : List Value}
    (h : σ.heap w = some (.plain cls (setFields cls fs names vals)))
    (hn : ∀ f ∈ s.fields, f.jname ∈ names) (hl : names.length ≤ vals.length) :
    WSObj σ w cls (keysOf s cls) := by
  refine ⟨_, h, fun k hk => ?_⟩
  simp only [keysOf, List.mem_map] at hk
  obtain ⟨f, hf, rfl⟩ := hk
  exact isSome_setFields_mem (hn f hf) hl

theorem cp037Str_sp (n : Nat) : cp037Str (Model.sp n) = spJ n := by
  have h : cp037Unit 64 = space := by decide +kernel
  rw [cp037Str, Model.sp, List.map_replicate, h]
  rfl

end EquivLean.Modernize.Cbtrn02c.Java
