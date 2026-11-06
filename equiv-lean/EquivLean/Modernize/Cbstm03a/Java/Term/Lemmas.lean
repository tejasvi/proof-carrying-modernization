import EquivLean.Modernize.Cbstm03a.Java.Term.Defs

/-! # CBSTM03A → Java, termination: lemmas for the symbolic executor -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term

/-- Characters of a string by `getD` (no bound proof inside the term: the symbolic executor's case splits look
    for branch conditions inside terms, proofs included). -/
theorem jstr_getElem_eq_getD (w : List (BitVec 16)) (j : Nat) (h : j < w.length) : w[j] = w.getD j 0 :=
  (List.getD_eq_getElem w 0 h).symm

/-- `0 ≤ i.toInt`: `i.toNat = i.toInt`. -/
theorem bv32_toNat_of_toInt_nonneg (i : I32) (h0 : 0 ≤ i.toInt) : (i.toNat : Int) = i.toInt := by
  have := BitVec.toInt_eq_toNat_cond i
  split at this <;> omega

/-- An element of an `int` array read at an index in range, by `getD`. -/
theorem getElem?_map_int (ks : List I32) (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < ks.length) :
    (ks.map Value.int)[i.toNat]? = some (.int (ks.getD i.toNat 0)) := by
  have := bv32_toNat_of_toInt_nonneg i h0
  have hl : i.toNat < ks.length := by omega
  rw [List.getElem?_map, List.getElem?_eq_getElem hl, List.getD_eq_getElem _ _ hl]
  rfl

end EquivLean.Modernize.Cbstm03a.Java.Term
