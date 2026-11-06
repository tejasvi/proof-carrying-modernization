import CIR
import Examples.Gen.Ctype

/-!
  Character classes on symbolic characters (`Examples/cpp/ctype.c`, compiled
  with glibc headers): `isdigit(c)` is the macro
  `(*__ctype_b_loc())[(int) c] & _ISdigit`. The lemmas of `CIR/Std/Ctype.lean`
  (`ctype_digit`, `ctype_alpha`, ..., checked over all 384 table indices)
  give the class as a range of `c`; `ctypeEntry_range` bounds the table
  entries.
-/

open CIR Gen.Ctype CIR.Std

set_option maxHeartbeats 4000000

namespace Examples.Ctype

/-- `match_digit(c)` is non-zero exactly for the characters '0'..'9'. -/
theorem match_digit_spec (c : Int) (m : Mem) (h : -128 ≤ c ∧ c ≤ 127) :
    Returns ctx "match_digit" [.int c] m
      (fun r _ => ∃ v, r = some (.int v) ∧ (v ≠ 0 ↔ 48 ≤ c ∧ c ≤ 57)) := by
  have hr := ctypeEntry_range c (by omega) (by omega)
  have hd := ctype_digit c (by omega) (by omega)
  unfold ctypeHas at hd
  cir_start
  cir_vcg

/-- `match_alpha(c)` is non-zero exactly for the letters. -/
theorem match_alpha_spec (c : Int) (m : Mem) (h : -128 ≤ c ∧ c ≤ 127) :
    Returns ctx "match_alpha" [.int c] m
      (fun r _ => ∃ v, r = some (.int v) ∧ (v ≠ 0 ↔ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122))) := by
  have hr := ctypeEntry_range c (by omega) (by omega)
  have hd := ctype_alpha c (by omega) (by omega)
  unfold ctypeHas at hd
  cir_start
  cir_vcg

end Examples.Ctype
