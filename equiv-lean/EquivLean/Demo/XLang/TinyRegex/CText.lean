import EquivLean.Demo.XLang.TinyRegex.CEnc
import EquivLean.Demo.XLang.TinyRegex.CBase

/-!
# tiny-regex-c → model, C side: facts about a C string's block

`patL s` (the bytes of `s` as `char`s, then the NUL): its length, its characters' range, and
where its NUL is, for strings without a 0 byte.
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open EquivLean.Demo.XLang.TinyRegex (sc)

theorem sc_range' {b : Nat} (h : b < 256) : -128 ≤ sc b ∧ sc b ≤ 127 := by
  unfold sc; split <;> omega

theorem sc_ne_zero {b : Nat} (h0 : 0 < b) (h1 : b < 256) : sc b ≠ 0 := by
  unfold sc; split <;> omega

theorem patL_length (s : List Nat) : (patL s).length = s.length + 1 := by
  simp [patL]

theorem patL_getD_lt {s : List Nat} {i : Nat} (h : i < s.length) :
    (patL s).getD i 0 = sc (s.getD i 0) := by
  have h' : i < (s.map (fun b => sc b)).length := by simpa using h
  simp only [patL, List.getD_eq_getElem?_getD, List.getElem?_append_left h', List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem patL_getD_len (s : List Nat) : (patL s).getD s.length 0 = 0 := by
  simp [patL, List.getD_eq_getElem?_getD]

theorem patL_getD_ge {s : List Nat} {i : Nat} (h : s.length ≤ i) : (patL s).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.eq_or_lt_of_le h with h' | h'
  · subst h'; simp [patL]
  · rw [List.getElem?_eq_none (by rw [patL_length]; omega)]; rfl

/-- The characters of a string without 0 bytes: in the `char` range, and 0 exactly at the end. -/
theorem patL_char {s : List Nat} (hs : ∀ b ∈ s, 0 < b ∧ b < 256) (i : Nat) :
    (-128 ≤ (patL s).getD i 0 ∧ (patL s).getD i 0 ≤ 127) ∧
    ((patL s).getD i 0 = 0 ↔ s.length ≤ i) := by
  by_cases h : i < s.length
  · rw [patL_getD_lt h]
    have hb := hs (s.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; simp)
    exact ⟨sc_range' hb.2, ⟨fun h0 => absurd h0 (sc_ne_zero hb.1 hb.2), fun h' => absurd h' (by omega)⟩⟩
  · rw [patL_getD_ge (by omega)]; exact ⟨by omega, ⟨fun _ => by omega, fun _ => rfl⟩⟩

end EquivLean.Demo.XLang.TinyRegex.C
