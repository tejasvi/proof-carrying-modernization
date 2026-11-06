import EquivLean.Modernize.Cbstm03a.Java.Term.Lemmas

/-! # CBSTM03A → Java, termination: string characters opaque to the symbolic executor -/

namespace EquivLean.Modernize.Cbstm03a.Java.Term

/-- A string's character at `j` (`0` past the end). Not unfolded by the symbolic executor: a character read
    `w[j]'h` becomes `chr w j`, with no bound proof inside (the executor's case splits look for branch conditions
    inside terms, proofs included). -/
def chr (w : List (BitVec 16)) (j : Nat) : BitVec 16 := w.getD j 0

theorem getElem_eq_chr (w : List (BitVec 16)) (j : Nat) (h : j < w.length) : w[j] = chr w j :=
  (List.getD_eq_getElem w 0 h).symm

end EquivLean.Modernize.Cbstm03a.Java.Term
