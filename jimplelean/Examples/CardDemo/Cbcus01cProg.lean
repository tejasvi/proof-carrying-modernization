/-
  Examples/CardDemo/Cbcus01cProg.lean

  CardDemo's CBCUS01C (customer file listing) as translated to Java: the program
  (`examples_java/cbcus01c`, Soot Jimple of the guided translation) and the facts about field
  texts its proofs use. The texts are those of CBACT02C (`fixStr`, `zpadStr`).
-/
import Examples.CardDemo.Cbact02cLemmas

open Jimple

jimple_import "examples_java/cbcus01c/jimple" as CU

namespace Examples.CardDemo

@[simp] theorem fixStr_length (s : JStr) : ∀ n, (fixStr s n).length = n
  | 0 => rfl
  | n + 1 => by simp [fixStr, fixStr_length s n]

/-- A text at least as long as the field is cut to the field's width. -/
theorem fixStr_eq_take {s : JStr} {n : Nat} (h : n ≤ s.length) : fixStr s n = s.take n := by
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  simp at h1
  simp [List.getElem?_eq_getElem (show i < s.length by omega)]

/-- Past the text, the field is padded with spaces. -/
theorem fixStr_succ_of_ge {s : JStr} {k : Nat} (h : s.length ≤ k) :
    fixStr s (k + 1) = fixStr s k ++ [space] := by
  rw [fixStr]
  congr 2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem jstr_empty : JStr.ofString "" = [] := rfl

theorem max_zero_of_nonneg {a : Int} (h : 0 ≤ a) : max a 0 = a := by omega

end Examples.CardDemo
