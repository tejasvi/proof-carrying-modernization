import EquivLean.Modernize.Cbstm03a.Java.Dz.Lem

/-!
# CBSTM03A → Java `decodeZoned`: closers of the last character's paths (cut point 16)

The last character `c` at `k` (`k + 1 = t.length`), not a digit: `zAcc t t.length` is `zAcc t k` with `zLast c`'s
digit and sign (`last_len`); the cases of `zLast` (`{`, `A`–`I`, `}`, `J`–`R`, `p`–`y`, any other) and the
goals at the join in the form `jvc` leaves them (`d = 0`, `c - 65 + 1`, `c - 74 + 1`, `c - 112`, `(c & 15) % 10`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

theorem last_len (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hk : k + 1 = t.length) :
    zAcc t t.length = ((zAcc t k).1 * 10 + (zLast c (zAcc t k).2).1, (zLast c (zAcc t k).2).2) := by
  rw [← hk]; exact zAcc_last t k c hd hnd hk

theorem zLast_123 (c : JChar) (b : Bool) (h : c.toNat = 123) : zLast c b = (0, b) := by
  unfold zLast; rw [if_pos h]

theorem zLast_AI (c : JChar) (b : Bool) (h0 : ¬ c.toNat = 123) (h1 : 65 ≤ c.toNat) (h2 : c.toNat ≤ 73) :
    zLast c b = (c.toNat - 64, b) := by
  unfold zLast; rw [if_neg h0, if_pos ⟨h1, h2⟩]

theorem zLast_125 (c : JChar) (b : Bool) (h0 : ¬ c.toNat = 123) (h1 : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73))
    (h : c.toNat = 125) : zLast c b = (0, true) := by
  unfold zLast; rw [if_neg h0, if_neg h1, if_pos h]

theorem zLast_JR (c : JChar) (b : Bool) (h0 : ¬ c.toNat = 123) (h1 : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73))
    (h3 : ¬ c.toNat = 125) (h4 : 74 ≤ c.toNat) (h5 : c.toNat ≤ 82) : zLast c b = (c.toNat - 73, true) := by
  unfold zLast; rw [if_neg h0, if_neg h1, if_neg h3, if_pos ⟨h4, h5⟩]

theorem zLast_py (c : JChar) (b : Bool) (h0 : ¬ c.toNat = 123) (h1 : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73))
    (h3 : ¬ c.toNat = 125) (h4 : ¬ (74 ≤ c.toNat ∧ c.toNat ≤ 82)) (h6 : 112 ≤ c.toNat) (h7 : c.toNat ≤ 121) :
    zLast c b = (c.toNat - 112, true) := by
  unfold zLast; rw [if_neg h0, if_neg h1, if_neg h3, if_neg h4, if_pos ⟨h6, h7⟩]

theorem zLast_oth (c : JChar) (b : Bool) (h0 : ¬ c.toNat = 123) (h1 : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73))
    (h3 : ¬ c.toNat = 125) (h4 : ¬ (74 ≤ c.toNat ∧ c.toNat ≤ 82)) (h6 : ¬ (112 ≤ c.toNat ∧ c.toNat ≤ 121)) :
    zLast c b = (lowDigit c, b) := by
  unfold zLast; rw [if_neg h0, if_neg h1, if_neg h3, if_neg h4, if_neg h6]

/-! ## The values at the join -/

/-- `{` or `}`: `d = 0`. -/
theorem last_v0 (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hk : k + 1 = t.length)
    (hc : c.toNat = 123 ∨ c.toNat = 125) : (zAcc t t.length).1 = (zAcc t k).1 * 10 := by
  rw [last_len t k c hd (by omega) hk]
  rcases hc with hc | hc
  · simp only [zLast_123 c _ hc, Nat.add_zero]
  · simp only [zLast_125 c _ (by omega) (by omega) hc, Nat.add_zero]

/-- `A` … `I`: `d = c - 65 + 1`. -/
theorem last_vAI (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hk : k + 1 = t.length)
    (h : ¬ c.toNat = 123 ∧ 65 ≤ c.toNat ∧ c.toNat ≤ 73) :
    (zAcc t t.length).1 = (zAcc t k).1 * 10 + (4294967231 + c.toNat + 1) % 4294967296 := by
  rw [last_len t k c hd (by omega) hk, zLast_AI c _ h.1 h.2.1 h.2.2]
  dsimp only
  omega

/-- `J` … `R`: `d = c - 74 + 1`. -/
theorem last_vJR (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hk : k + 1 = t.length)
    (h : ¬ c.toNat = 123 ∧ ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73) ∧ ¬ c.toNat = 125 ∧ 74 ≤ c.toNat ∧ c.toNat ≤ 82) :
    (zAcc t t.length).1 = (zAcc t k).1 * 10 + (4294967222 + c.toNat + 1) % 4294967296 := by
  rw [last_len t k c hd (by omega) hk, zLast_JR c _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2]
  dsimp only
  omega

/-- `p` … `y`: `d = c - 112`. -/
theorem last_vpy (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hk : k + 1 = t.length)
    (h : ¬ c.toNat = 123 ∧ ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73) ∧ ¬ c.toNat = 125 ∧ ¬ (74 ≤ c.toNat ∧ c.toNat ≤ 82) ∧
      112 ≤ c.toNat ∧ c.toNat ≤ 121) :
    (zAcc t t.length).1 = (zAcc t k).1 * 10 + (4294967184 + c.toNat) % 4294967296 := by
  rw [last_len t k c hd (by omega) hk, zLast_py c _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2]
  dsimp only
  omega

/-- Any other character: `d = (c & 15) % 10`. -/
theorem last_voth (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hk : k + 1 = t.length)
    (h : ¬ c.toNat = 123 ∧ ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 73) ∧ ¬ c.toNat = 125 ∧ ¬ (74 ≤ c.toNat ∧ c.toNat ≤ 82) ∧
      ¬ (112 ≤ c.toNat ∧ c.toNat ≤ 121)) :
    (zAcc t t.length).1 =
      (zAcc t k).1 * 10 + (BitVec.srem (BitVec.setWidth 32 c &&& 15#32) 10#32).toNat := by
  rw [last_len t k c hd hnd hk, zLast_oth c _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2, lowd_toNat]

/-! ## The signs at the join -/

theorem zLast_keep (c : JChar) (b : Bool)
    (h : ¬ c.toNat = 125 ∧ ¬ (74 ≤ c.toNat ∧ c.toNat ≤ 82) ∧ ¬ (112 ≤ c.toNat ∧ c.toNat ≤ 121)) :
    (zLast c b).2 = b := by
  unfold zLast
  split_ifs <;> first | rfl | (exfalso; omega)

theorem zLast_neg (c : JChar) (b : Bool)
    (h : c.toNat = 125 ∨ (74 ≤ c.toNat ∧ c.toNat ≤ 82) ∨ (112 ≤ c.toNat ∧ c.toNat ≤ 121)) :
    (zLast c b).2 = true := by
  unfold zLast
  split_ifs <;> first | rfl | (exfalso; omega)

theorem last_s (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hk : k + 1 = t.length) : (zAcc t t.length).2 = (zLast c (zAcc t k).2).2 := by
  rw [last_len t k c hd hnd hk]

/-- `}`, `J` … `R`, `p` … `y`: negative. -/
theorem last_s_neg (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hk : k + 1 = t.length)
    (h : c.toNat = 125 ∨ (74 ≤ c.toNat ∧ c.toNat ≤ 82) ∨ (112 ≤ c.toNat ∧ c.toNat ≤ 121)) :
    (zAcc t t.length).2 = true := by
  rw [last_s t k c hd hnd hk, zLast_neg c _ h]

/-- Otherwise the sign so far. -/
theorem last_s_keep (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c)
    (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57)) (hk : k + 1 = t.length)
    (h : ¬ c.toNat = 125 ∧ ¬ (74 ≤ c.toNat ∧ c.toNat ≤ 82) ∧ ¬ (112 ≤ c.toNat ∧ c.toNat ≤ 121)) :
    (zAcc t t.length).2 = (zAcc t k).2 := by
  rw [last_s t k c hd hnd hk, zLast_keep c _ h]

end EquivLean.Modernize.Cbstm03a.Java.Dz
