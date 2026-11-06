import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-!
# CBSTM03A → Java: `decodeZoned`'s invariants, its paths and its arithmetic

`decodeZoned(String)`'s statements, numbered from 0 (the labels are not statements): 0 `s := @parameter0`,
1 `v = 0L`, 2 `neg = 0`, 3 `n = s.length()`, 4 `i = 0`, 5 `if i >= n goto label10` (the loop head),
6 `c = s.charAt(i)`, 7 `d = (int) c`, 8–13 the digit, 14–15 `if i != n - 1 goto label08`, 16–53 the last
character (overpunch), 54–56 `(c & 15) % 10`, 57–61 `v = v * 10 + d; i++` (label09), 62–64 the sign and `return v`.
Locals: `c` 0, `v` 1, `$l6` 2, `n` 3, `d` 4, `i` 5, `s` 6, `neg` 7.

The invariants are cbA-num's (`HDecodeZoned.lean`): 5 the loop head, 7 after `charAt`, 16 the last character
(not a digit), 57 the join. `dzWP` is the paths' weakest precondition (irreducible); each cut point's paths are
proved in their own module and assembled in `CbADz.Sat`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows argText)

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

/-! ## Arithmetic -/

theorem zAcc_succN (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) :
    zAcc t (k + 1) =
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then ((zAcc t k).1 * 10 + (c.toNat - 48), (zAcc t k).2)
      else if k + 1 = t.length then ((zAcc t k).1 * 10 + (zLast c (zAcc t k).2).1, (zLast c (zAcc t k).2).2)
      else ((zAcc t k).1 * 10 + lowDigit c, (zAcc t k).2) := by
  have g : t.getD k 0 = c := by rw [List.getD_eq_getElem?_getD, hd]; rfl
  rw [zAcc, g]

/-- A digit. -/
theorem zAcc_digit (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (h1 : 48 ≤ c.toNat)
    (h2 : c.toNat ≤ 57) : zAcc t (k + 1) = ((zAcc t k).1 * 10 + (c.toNat - 48), (zAcc t k).2) := by
  rw [zAcc_succN t k c hd, if_pos ⟨h1, h2⟩]

/-- Not a digit, not the last character. -/
theorem zAcc_mid (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hne : k + 1 ≠ t.length) : zAcc t (k + 1) = ((zAcc t k).1 * 10 + lowDigit c, (zAcc t k).2) := by
  rw [zAcc_succN t k c hd, if_neg hnd, if_neg hne]

/-- The last character, not a digit. -/
theorem zAcc_last (t : JStr) (k : Nat) (c : JChar) (hd : t[k]? = some c) (hnd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hk : k + 1 = t.length) :
    zAcc t (k + 1) = ((zAcc t k).1 * 10 + (zLast c (zAcc t k).2).1, (zLast c (zAcc t k).2).2) := by
  rw [zAcc_succN t k c hd, if_neg hnd, if_pos hk]

/-- `v = v * 10 + (long) d` for a digit `d`. -/
theorem step64 (A : Nat) (d : BitVec 32) (hd : d.toNat < 10) :
    BitVec.ofNat 64 A * 10#64 + JInt.toLong d = BitVec.ofNat 64 (A * 10 + d.toNat) := by
  have hmsb : d.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.2 (by simp only [Nat.reducePow]; omega)
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.toLong, BitVec.signExtend_eq_setWidth_of_msb_false hmsb, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reducePow]
  omega

theorem ofNat64_neg (A : Nat) : -BitVec.ofNat 64 A = BitVec.ofInt 64 (-(A : Int)) := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]

/-- `(c & 0x0F) % 10` on the `int` value of a character. -/
theorem lowd_toNat (c : JChar) : (BitVec.srem (BitVec.setWidth 32 c &&& 15#32) 10#32).toNat = lowDigit c := by
  have hc := c.isLt
  have h1 : (BitVec.setWidth 32 c &&& 15#32).toNat = c.toNat % 16 := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (15 : Nat) % 2 ^ 32 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    simp only [Nat.reducePow]
    omega
  have hm : (BitVec.setWidth 32 c &&& 15#32).msb = false :=
    BitVec.msb_eq_false_iff_two_mul_lt.2 (by rw [h1]; simp only [Nat.reducePow]; omega)
  have h10 : (10#32 : BitVec 32).msb = false := by decide
  rw [BitVec.srem_eq, hm, h10]
  simp only [BitVec.toNat_umod, h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, lowDigit]

theorem lowDigit_lt (c : JChar) : lowDigit c < 10 := Nat.mod_lt _ (by decide)

theorem dz_exit_neg (t : JStr) (k : Nat) (h : k = t.length) :
    -BitVec.ofNat 64 (zAcc t k).1 = BitVec.ofInt 64 (-((zAcc t t.length).1 : Int)) := by
  subst h
  exact ofNat64_neg _

theorem dz_exit_pos (t : JStr) (k : Nat) (h : k = t.length) :
    BitVec.ofNat 64 (zAcc t k).1 = BitVec.ofInt 64 ((zAcc t t.length).1 : Int) := by
  subst h
  rw [BitVec.ofInt_natCast]

theorem toInt_ofNat_sub_one (L : Nat) (h1 : 1 ≤ L) (h2 : L < 2147483648) :
    (BitVec.ofNat 32 L - 1#32).toInt = (L : Int) - 1 := by
  have := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 L - 1#32)
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at this
  split at this <;> omega

theorem sw32_eq (c : JChar) (n : Nat) (hn : n < 65536) :
    (BitVec.setWidth 32 c = BitVec.ofNat 32 n) ↔ c.toNat = n := by
  have hc := c.isLt
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega

theorem toInt_ofNat32z (L : Nat) (h : L < 2147483648) : (BitVec.ofNat 32 L).toInt = L := by
  have := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 L)
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
  split at this <;> omega

theorem last_iff (i : BitVec 32) (L : Nat) (h1 : 1 ≤ L) (h2 : L < 2147483648) :
    (i = BitVec.ofNat 32 L - 1#32) ↔ i.toInt = (L : Int) - 1 :=
  ⟨fun e => by rw [e, toInt_ofNat_sub_one L h1 h2],
   fun e => BitVec.eq_of_toInt_eq (by rw [e, toInt_ofNat_sub_one L h1 h2])⟩

theorem toInt_setWidth32 (c : JChar) : (BitVec.setWidth 32 c).toInt = c.toNat := by
  have hc := c.isLt
  have := BitVec.toInt_eq_toNat_cond (BitVec.setWidth 32 c)
  simp only [BitVec.toNat_setWidth, Nat.reducePow] at this
  split at this <;> omega

/-! ## Invariants (cbA-num's) -/

/-- At the loop head (statement 5): the text `t` (local `s` 6, its length local `n` 3), the index `i` (local 5),
the value so far (local `v` 1) and the sign (local `neg` 7); the state is unchanged. -/
def dzHead (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ sv, args = [sv] → ∃ (sa : Addr) (t : JStr) (i : I32), sv = .ref sa ∧ σ.heap sa = some (.str t) ∧
    t.length < 2147483648 ∧ fr.get 6 = some (.ref sa) ∧ fr.get 3 = some (.int (BitVec.ofNat 32 t.length)) ∧
    fr.get 5 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ t.length ∧
    fr.get 1 = some (.long (BitVec.ofNat 64 (zAcc t i.toInt.toNat).1)) ∧
    fr.get 7 = some (.int (if (zAcc t i.toInt.toNat).2 then 1#32 else 0#32)) ∧ σ = σ0

/-- After reading the character at `i` (statement 7): the character `ch` (local `c` 0). -/
def dzChar (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ sv, args = [sv] → ∃ (sa : Addr) (t : JStr) (i : I32) (ch : JChar), sv = .ref sa ∧
    σ.heap sa = some (.str t) ∧
    t.length < 2147483648 ∧ fr.get 6 = some (.ref sa) ∧ fr.get 3 = some (.int (BitVec.ofNat 32 t.length)) ∧
    fr.get 5 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt < t.length ∧
    fr.get 1 = some (.long (BitVec.ofNat 64 (zAcc t i.toInt.toNat).1)) ∧
    fr.get 7 = some (.int (if (zAcc t i.toInt.toNat).2 then 1#32 else 0#32)) ∧
    fr.get 0 = some (.int (BitVec.setWidth 32 ch)) ∧ t[i.toInt.toNat]? = some ch ∧ σ = σ0

/-- At the last character, not a digit (statement 16): the character `ch` (local `c` 0). -/
def dzLast (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ sv, args = [sv] → ∃ (sa : Addr) (t : JStr) (i : I32) (ch : JChar), sv = .ref sa ∧
    σ.heap sa = some (.str t) ∧
    t.length < 2147483648 ∧ fr.get 6 = some (.ref sa) ∧ fr.get 3 = some (.int (BitVec.ofNat 32 t.length)) ∧
    fr.get 5 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt.toNat + 1 = t.length ∧
    fr.get 1 = some (.long (BitVec.ofNat 64 (zAcc t i.toInt.toNat).1)) ∧
    fr.get 7 = some (.int (if (zAcc t i.toInt.toNat).2 then 1#32 else 0#32)) ∧
    fr.get 0 = some (.int (BitVec.setWidth 32 ch)) ∧ t[i.toInt.toNat]? = some ch ∧
    ¬ (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) ∧ σ = σ0

/-- At the join (statement 57): the digit `d` (local 4) of the character at `i` and the sign after it. -/
def dzJoin (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ sv, args = [sv] → ∃ (sa : Addr) (t : JStr) (i d : I32), sv = .ref sa ∧ σ.heap sa = some (.str t) ∧
    t.length < 2147483648 ∧ fr.get 6 = some (.ref sa) ∧ fr.get 3 = some (.int (BitVec.ofNat 32 t.length)) ∧
    fr.get 5 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt < t.length ∧
    fr.get 1 = some (.long (BitVec.ofNat 64 (zAcc t i.toInt.toNat).1)) ∧
    fr.get 4 = some (.int d) ∧ d.toNat < 10 ∧
    (zAcc t (i.toInt.toNat + 1)).1 = (zAcc t i.toInt.toNat).1 * 10 + d.toNat ∧
    fr.get 7 = some (.int (if (zAcc t (i.toInt.toNat + 1)).2 then 1#32 else 0#32)) ∧ σ = σ0

def decodeZonedInv : Invariants :=
  [(5, fun args σ0 fr σ => dzHead args σ0 fr σ), (7, fun args σ0 fr σ => dzChar args σ0 fr σ),
   (16, fun args σ0 fr σ => dzLast args σ0 fr σ),
   (57, fun args σ0 fr σ => dzJoin args σ0 fr σ)]

/-! ## The paths -/

abbrev dzBody : Body := Gen.Cbstm03a.«decodeZoned(java.lang.String)»

/-- The paths of `decodeZoned` from statement `pc`. -/
@[irreducible] def dzWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog (fun _ => none) 0) dzBody (decodeZonedInv.inst args σ0)
    (decodeZonedSpec.post args σ0) 80 pc fr σ

/-- The entry path (statements 0 … 5). -/
def DzEntryVC : Prop :=
  ∀ args σ0, decodeZonedSpec.pre args σ0 → dzWP args σ0 0 (Frame.init true args) σ0

/-- The paths from cut point `pc` with invariant `I`. -/
def DzCutVC (pc : Nat) (I : List Value → State → Frame → State → Prop) : Prop :=
  ∀ args σ0, decodeZonedSpec.pre args σ0 → ∀ fr σ, I args σ0 fr σ → dzWP args σ0 pc fr σ

end EquivLean.Modernize.Cbstm03a.Java.Dz
