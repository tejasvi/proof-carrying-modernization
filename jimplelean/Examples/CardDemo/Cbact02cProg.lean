/-
  Examples/CardDemo/Cbact02cProg.lean

  CardDemo's CBACT02C translated to Java (veriforch's guided translation,
  `examples_java/cbact02c/src/Cbact02c.java`; the Jimple is equiv-lean's
  `EquivLean/Demo/Gen/Jimple/mod_cbact02c`, `SHA256SUMS` beside it), and the string
  functions its contracts are stated with.
-/
import Jimple

open Jimple

jimple_import "examples_java/cbact02c/jimple" as CB

namespace Examples.CardDemo

/-- `v` is a reference to the string `s`. -/
def JStrAt (σ : State) (v : Value) (s : JStr) : Prop := ∃ x, v = .ref x ∧ σ.heap x = some (.str s)

/-- The heap only grows: objects that existed are unchanged. -/
def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

def space : JChar := BitVec.ofNat 16 32

/-- The text of a string argument: its characters, `""` for `null` (and for a non-string). -/
def argText (σ : State) (v : Value) : JStr := (strOf σ v).getD []

/-- A string argument: `null`, or a string (of `int` length, as every Java string). -/
def StrOk (σ : State) (v : Value) : Prop :=
  v = .null ∨ ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `fixStr s n`: the first `n` characters of `s`, padded with spaces to `n` (`Cbact02c.fix`). -/
def fixStr (s : JStr) : Nat → JStr
  | 0 => []
  | i + 1 => fixStr s i ++ [s.getD i space]

/-- The digit `d` as a character. -/
def digitChar (d : Nat) : JChar := BitVec.ofNat 16 (48 + d)

/-- `zpadStr c m`: the last `m` decimal digits of `c`, zero-padded (`Cbact02c.zeroPad`). -/
def zpadStr (c : Nat) : Nat → JStr
  | 0 => []
  | m + 1 => zpadStr (c / 10) m ++ [digitChar (c % 10)]

/-! ### Machine arithmetic of the digit loop (non-negative `long`s) -/

theorem msb_false_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : l.msb = false := by
  have := BitVec.toInt_eq_toNat_cond l
  have hl := l.isLt
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  by_cases hc : 2 * l.toNat < 2 ^ 64
  · omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)] at this
    · omega

theorem srem10_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    l.srem 10#64 = BitVec.ofNat 64 (l.toNat % 10) := by
  have hmsb := msb_false_of_toInt_nonneg l h
  have h10 : (10#64).msb = false := by decide
  rw [BitVec.srem_eq, hmsb, h10]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : l.toNat % 10 < 2 ^ 64 := by omega
  simp [Nat.mod_eq_of_lt this]

theorem sdiv10_toNat_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (l.sdiv 10#64).toNat = l.toNat / 10 := by
  have hmsb := msb_false_of_toInt_nonneg l h
  have h10 : (10#64).msb = false := by decide
  rw [BitVec.sdiv_eq, hmsb, h10]
  simp [BitVec.toNat_udiv]

theorem sdiv10_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : 0 ≤ (l.sdiv 10#64).toInt := by
  have hn := sdiv10_toNat_of_nonneg l h
  have hc := BitVec.toInt_eq_toNat_cond (l.sdiv 10#64)
  have hl := l.isLt
  by_cases hq : 2 * (l.sdiv 10#64).toNat < 2 ^ 64
  · rw [ite_eq_left_iff.mpr (fun h' => absurd hq h')] at hc; omega
  · rw [hn] at hq; omega

/-- The character `zeroPad` stores: `(char) ('0' + (int) (l % 10))`. -/
theorem digit_char (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (JInt.toChar (48#32 + JLong.toInt (l.srem 10#64))).setWidth 16 = digitChar (l.toNat % 10) := by
  rw [srem10_of_nonneg l h]
  apply BitVec.eq_of_toNat_eq
  simp only [digitChar, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem drop_set_self {α : Type} : ∀ (xs : List α) (k : Nat) (e : α), k < xs.length →
    (xs.set k e).drop k = e :: xs.drop (k + 1)
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, k + 1, e, h => by
    simp only [List.set_cons_succ, List.drop_succ_cons]
    exact drop_set_self xs k e (by simpa using h)

end Examples.CardDemo
