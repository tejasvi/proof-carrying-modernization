/-
StrictTS proof layer: the `ts_sym` simp set (symbolic execution of IR on explicit worlds).
-/
import Lean

/-- Simp set for symbolic execution: monad/world lemmas, interpreter equations for each IR
construct (not loops, not calls of top-level functions), value and environment lemmas. -/
register_simp_attr ts_sym

/-- Simp set for bitwise code on arbitrary numbers (`StrictTS/Proof/Bits.lean`): the bitwise
operators rewritten into 32-bit operations on `toInt32`. Not part of `ts_sym`. -/
register_simp_attr ts_bits
