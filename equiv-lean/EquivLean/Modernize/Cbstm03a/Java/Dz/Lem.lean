import EquivLean.Modernize.Cbstm03a.Java.Dz.Base

/-!
# CBSTM03A → Java `decodeZoned`: closers of the paths' goals

The goals `jvc` leaves at the join (statement 57), in the form its `simp` gives them: the digit `d` of the
character `c` at `k` (`c - 48`, `(c & 15) % 10`, the overpunch digits) and `zAcc`'s next step, value and sign.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

theorem lowd_lt (c : JChar) : (BitVec.srem (BitVec.setWidth 32 c &&& 15#32) 10#32).toNat < 10 := by
  rw [lowd_toNat]; exact lowDigit_lt c

/-- A digit: `d = c - 48` (as `jvc` leaves it). -/
theorem dig_v (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (h1 : ¬ c.toNat < 48)
    (h2 : ¬ 57 < c.toNat) :
    (zAcc t (k + 1)).1 = (zAcc t k).1 * 10 + (4294967248 + c.toNat) % 4294967296 := by
  simp only [zAcc_digit t k c hd (by omega) (by omega)]
  omega

theorem dig_s (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (h1 : ¬ c.toNat < 48)
    (h2 : ¬ 57 < c.toNat) : (zAcc t (k + 1)).2 = (zAcc t k).2 := by
  simp only [zAcc_digit t k c hd (by omega) (by omega)]

/-- Not a digit, not the last character: `d = (c & 15) % 10`. -/
theorem mid_v (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hne : k + 1 ≠ t.length) :
    (zAcc t (k + 1)).1 = (zAcc t k).1 * 10 + (BitVec.srem (BitVec.setWidth 32 c &&& 15#32) 10#32).toNat := by
  simp only [zAcc_mid t k c hd hnd hne, lowd_toNat]

theorem mid_s (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hne : k + 1 ≠ t.length) : (zAcc t (k + 1)).2 = (zAcc t k).2 := by
  simp only [zAcc_mid t k c hd hnd hne]

theorem sign_true {a b : Bool} (h : a = b) (hb : b = true) : a = true := h ▸ hb

theorem sign_false {a b : Bool} (h : a = b) (hb : ¬ b = true) : a = false := by
  cases b <;> simp_all

end EquivLean.Modernize.Cbstm03a.Java.Dz

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

/-- Restate the paths' branch conditions on a character (`57 < c`, `c = 123`, …, as `jvc`'s `simp` leaves them:
some numerals there are not read as numerals by `omega`) with standard numerals, for `omega`. -/
macro "dz_lits" : tactic => `(tactic| (
    (try have : (48 : Nat) ≤ BitVec.toNat _ := Nat.not_lt.mp ‹¬ BitVec.toNat _ < 48›)
    (try have : BitVec.toNat _ < (48 : Nat) := ‹_›)
    (try have : (57 : Nat) < BitVec.toNat _ := ‹_›)
    (try have : BitVec.toNat _ ≤ (57 : Nat) := Nat.not_lt.mp ‹¬ 57 < BitVec.toNat _›)
    (try have : BitVec.toNat _ < (65 : Nat) := ‹_›)
    (try have : (65 : Nat) ≤ BitVec.toNat _ := Nat.not_lt.mp ‹¬ BitVec.toNat _ < 65›)
    (try have : (73 : Nat) < BitVec.toNat _ := ‹_›)
    (try have : BitVec.toNat _ ≤ (73 : Nat) := Nat.not_lt.mp ‹¬ 73 < BitVec.toNat _›)
    (try have : BitVec.toNat _ < (74 : Nat) := ‹_›)
    (try have : (74 : Nat) ≤ BitVec.toNat _ := Nat.not_lt.mp ‹¬ BitVec.toNat _ < 74›)
    (try have : (82 : Nat) < BitVec.toNat _ := ‹_›)
    (try have : BitVec.toNat _ ≤ (82 : Nat) := Nat.not_lt.mp ‹¬ 82 < BitVec.toNat _›)
    (try have : BitVec.toNat _ < (112 : Nat) := ‹_›)
    (try have : (112 : Nat) ≤ BitVec.toNat _ := Nat.not_lt.mp ‹¬ BitVec.toNat _ < 112›)
    (try have : (121 : Nat) < BitVec.toNat _ := ‹_›)
    (try have : BitVec.toNat _ ≤ (121 : Nat) := Nat.not_lt.mp ‹¬ 121 < BitVec.toNat _›)
    (try have : BitVec.toNat _ = (123 : Nat) := ‹_›)
    (try have : BitVec.toNat _ ≠ (123 : Nat) := ‹¬ BitVec.toNat _ = 123›)
    (try have : BitVec.toNat _ = (125 : Nat) := ‹_›)
    (try have : BitVec.toNat _ ≠ (125 : Nat) := ‹¬ BitVec.toNat _ = 125›)))

end EquivLean.Modernize.Cbstm03a.Java.Dz
