import CIR.Std.Models

/-!
  Facts about glibc's `<ctype.h>` table (`__ctype_b_loc`, C locale) for
  symbolic characters: the class tests `table[c] & mask` used by the macros
  `isdigit`, `isalpha`, ... as ranges of `c`. Each is checked over all 384
  table indices (-128 to 255) by `decide`.
-/

namespace CIR.Std

/-- The class test of `c` (`table[c] & mask ≠ 0`), as glibc's macros compute it. -/
def ctypeHas (mask c : Int) : Prop :=
  bitwise true 32 (fun x1 x2 => x1 &&& x2) (ctypeEntry 0 c) mask ≠ 0

private theorem forall_ctype_range {P : Int → Prop} (h : ∀ i : Fin 384, P ((i : Int) - 128))
    (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) : P c := by
  have := h ⟨(c + 128).toNat, by omega⟩
  simp only at this
  rwa [show (((c + 128).toNat : Nat) : Int) - 128 = c by omega] at this

/-- Every entry fits in an `unsigned short`. -/
theorem ctypeEntry_range (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    0 ≤ ctypeEntry 0 c ∧ ctypeEntry 0 c ≤ 65535 :=
  forall_ctype_range (P := fun c => 0 ≤ ctypeEntry 0 c ∧ ctypeEntry 0 c ≤ 65535) (by decide +kernel) c h0 h1

theorem ctype_digit (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 2048 c ↔ 48 ≤ c ∧ c ≤ 57 :=
  forall_ctype_range (P := fun c => ctypeHas 2048 c ↔ 48 ≤ c ∧ c ≤ 57) (by unfold ctypeHas; decide +kernel) c h0 h1

theorem ctype_alpha (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 1024 c ↔ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) :=
  forall_ctype_range (P := fun c => ctypeHas 1024 c ↔ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122))
    (by unfold ctypeHas; decide +kernel) c h0 h1

theorem ctype_alnum (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 8 c ↔ (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) :=
  forall_ctype_range (P := fun c => ctypeHas 8 c ↔ (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122))
    (by unfold ctypeHas; decide +kernel) c h0 h1

theorem ctype_space (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 8192 c ↔ c = 32 ∨ (9 ≤ c ∧ c ≤ 13) :=
  forall_ctype_range (P := fun c => ctypeHas 8192 c ↔ c = 32 ∨ (9 ≤ c ∧ c ≤ 13))
    (by unfold ctypeHas; decide +kernel) c h0 h1

theorem ctype_upper (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 256 c ↔ 65 ≤ c ∧ c ≤ 90 :=
  forall_ctype_range (P := fun c => ctypeHas 256 c ↔ 65 ≤ c ∧ c ≤ 90) (by unfold ctypeHas; decide +kernel) c h0 h1

theorem ctype_lower (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 512 c ↔ 97 ≤ c ∧ c ≤ 122 :=
  forall_ctype_range (P := fun c => ctypeHas 512 c ↔ 97 ≤ c ∧ c ≤ 122) (by unfold ctypeHas; decide +kernel) c h0 h1

theorem ctype_xdigit (c : Int) (h0 : -128 ≤ c) (h1 : c ≤ 255) :
    ctypeHas 4096 c ↔ (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) ∨ (97 ≤ c ∧ c ≤ 102) :=
  forall_ctype_range (P := fun c => ctypeHas 4096 c ↔ (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) ∨ (97 ≤ c ∧ c ≤ 102))
    (by unfold ctypeHas; decide +kernel) c h0 h1

end CIR.Std
