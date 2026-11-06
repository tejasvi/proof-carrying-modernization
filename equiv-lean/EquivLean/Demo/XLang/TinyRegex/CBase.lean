import CIR

/-!
# tiny-regex-c → model, C side: shared definitions

The `char` value of a byte read through `const char*` (`s8`), the C tests of the character classes
on a `char` value, and list facts for the blocks of bytes (`xs.map .int`, `0 ≤ x ≤ 255`).
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- The `char` value of a byte read through `const char*`. -/
@[irreducible] def s8 (x : Int) : Int := if x < 128 then x else x - 256

def digitP (c : Int) : Prop := 48 ≤ c ∧ c ≤ 57
def alphaP (c : Int) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)
def spaceP (c : Int) : Prop := c = 32 ∨ (9 ≤ c ∧ c ≤ 13)
def alnumP (c : Int) : Prop := c = 95 ∨ alphaP c ∨ digitP c

/-- The test of `ismetachar(c)` (opaque in contracts: an atom for `omega`). -/
@[irreducible] def metacharP (c : Int) : Prop := c = 115 ∨ c = 83 ∨ c = 119 ∨ c = 87 ∨ c = 100 ∨ c = 68

/-- The test of `matchrange(c, &xs[j])`. -/
@[irreducible] def rangeP (c : Int) (xs : List Int) (j : Nat) : Prop :=
  c ≠ 45 ∧ xs.getD j 0 ≠ 0 ∧ xs.getD j 0 ≠ 45 ∧ xs.getD (j + 1) 0 = 45 ∧ xs.getD (j + 2) 0 ≠ 0 ∧
    s8 (xs.getD j 0) ≤ c ∧ c ≤ s8 (xs.getD (j + 2) 0)

/-- The test of `matchmetachar(c, str)` when `str[0]` holds the byte `s`. -/
@[irreducible] def metaP (c s : Int) : Prop :=
  if s = 100 then digitP c else if s = 68 then ¬ digitP c else if s = 119 then alnumP c
  else if s = 87 then ¬ alnumP c else if s = 115 then spaceP c else if s = 83 then ¬ spaceP c
  else c = s8 s

instance (c : Int) : Decidable (metacharP c) := by unfold metacharP; infer_instance
instance (c : Int) (xs : List Int) (j : Nat) : Decidable (rangeP c xs j) := by
  unfold rangeP; infer_instance
instance (c s : Int) : Decidable (metaP c s) := by
  unfold metaP alnumP; unfold alphaP digitP spaceP; infer_instance

theorem getD_range {xs : List Int} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (i : Nat) :
    0 ≤ xs.getD i 0 ∧ xs.getD i 0 ≤ 255 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : xs[i]? with
  | none => simp
  | some x => simpa using hxs x (List.mem_of_getElem? h)

theorem getElem_eq_getD {xs : List Int} {i : Nat} (h : i < xs.length) : xs[i] = xs.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Facts about a byte `x` read through `const char*` (`s8 x`), as rewrite rules for symbolic
execution: the conversions, the range, and the tests the code makes against characters. -/
theorem s8_facts {x : Int} (h : 0 ≤ x ∧ x ≤ 255) :
    CIR.wrap true 8 x = s8 x ∧ CIR.wrap true 32 (s8 x) = s8 x ∧ (-128 ≤ s8 x ∧ s8 x ≤ 127) ∧
    ((s8 x = 0) = (x = 0)) ∧ ((s8 x = 45) = (x = 45)) ∧ ((s8 x = 92) = (x = 92)) ∧
    ((s8 x = 93) = (x = 93)) ∧ ((s8 x = 94) = (x = 94)) ∧
    ((s8 x = 100) = (x = 100)) ∧ ((s8 x = 68) = (x = 68)) ∧ ((s8 x = 119) = (x = 119)) ∧
    ((s8 x = 87) = (x = 87)) ∧ ((s8 x = 115) = (x = 115)) ∧ ((s8 x = 83) = (x = 83)) := by
  have hw8 : CIR.wrap true 8 x = s8 x := by
    unfold CIR.wrap s8
    by_cases hx : x < 128
    · simp [hx]; omega
    · simp [hx]; omega
  have hr : -128 ≤ s8 x ∧ s8 x ≤ 127 := by unfold s8; split <;> omega
  refine ⟨hw8, ?_, hr, ?_⟩
  · unfold CIR.wrap; simp; omega
  · unfold s8; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply propext; split <;> omega)

theorem s8_of_lt {x : Int} (h : x < 128) : s8 x = x := by unfold s8; simp [h]

theorem s8_cases (x : Int) : (x < 128 ∧ s8 x = x) ∨ (128 ≤ x ∧ s8 x = x - 256) := by
  unfold s8; by_cases h : x < 128 <;> simp [h] <;> omega

end EquivLean.Demo.XLang.TinyRegex.C
