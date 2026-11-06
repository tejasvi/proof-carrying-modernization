import EquivLean.Modernize.Cbact04c.JavaSpec

/-!
# CBACT04C → Java: lemmas for the proof of `run`

The heap relation `Grows`, the hiding wrapper `Hide`, the strings the helpers build (`spJ`,
`zpadJ`), machine arithmetic of the digit loops, and the linking of static-method contracts.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The heap grows -/

/-- The heap only grows: objects that existed are unchanged. -/
def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

theorem grows_refl (σ : State) : Grows σ σ := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_trans {σ1 σ2 σ3 : State} (h1 : Grows σ1 σ2) (h2 : Grows σ2 σ3) : Grows σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem heap_of_grows {σ0 σ : State} {x : Addr} {o : Obj} (hg : Grows σ0 σ)
    (h : σ0.heap x = some o) : σ.heap x = some o := by
  rw [hg.2 x (State.lt_next_of_heap h), h]

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 := by
  refine ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => ?_⟩
  rw [State.heap_alloc, ite_eq_right (Nat.ne_of_lt hx)]

theorem grows_setObj {σ0 σ : State} {l : Addr} {o : Obj} (hg : Grows σ0 σ) (hl : σ0.next ≤ l) :
    Grows σ0 (σ.setObj l o) := by
  refine ⟨by rw [State.next_setObj]; exact hg.1, fun x hx => ?_⟩
  have hxl : x ≠ l := by intro h; subst h; exact absurd hx (Nat.not_lt.mpr hl)
  rw [State.heap_setObj, ite_eq_right hxl, hg.2 x hx]

/-! ## Field lists -/

theorem fields_get_cons (k k' : FieldKey) (v : Value) (fs : List (FieldKey × Value)) :
    Fields.get ((k, v) :: fs) k' = if k' = k then some v else Fields.get fs k' := by
  simp only [Fields.get, List.lookup]
  by_cases h : k' = k
  · subst h; simp
  · have : (k' == k) = false := by simp [h]
    simp [this, h]

theorem fields_get_nil (k' : FieldKey) : Fields.get [] k' = none := rfl

theorem fields_get_filter (fs : List (FieldKey × Value)) (k k' : FieldKey) :
    Fields.get (fs.filter (fun p => p.1 != k)) k' = if k' = k then none else Fields.get fs k' := by
  induction fs with
  | nil => simp [Fields.get]
  | cons p fs ih =>
    obtain ⟨k0, v0⟩ := p
    by_cases h0 : k0 = k
    · subst h0
      have : (k0 != k0) = false := by simp
      simp only [List.filter_cons, this, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      by_cases h : k' = k0
      · simp [h]
      · simp only [h, ↓reduceIte, fields_get_cons]
    · have : (k0 != k) = true := by simp [h0]
      simp only [List.filter_cons, this, ↓reduceIte, fields_get_cons, ih]
      by_cases h : k' = k
      · subst h; simp [Ne.symm h0]
      · simp [h]

theorem fields_get_set (fs : List (FieldKey × Value)) (k k' : FieldKey) (v : Value) :
    Fields.get (Fields.set fs k v) k' = if k' = k then some v else Fields.get fs k' := by
  simp only [Fields.set, fields_get_cons, fields_get_filter]
  by_cases h : k' = k <;> simp [h]

theorem narrow_long (v : Value) : (JType.prim .long).narrow v = v := by cases v <;> rfl
theorem narrow_cls (c : ClassName) (v : Value) : (JType.cls c).narrow v = v := by cases v <;> rfl

/-! ## Hiding hypotheses from `jvc` -/

/-- A hypothesis hidden from the `jvc` preprocessing (destructuring, forward instantiation). -/
@[irreducible] def Hide (p : Prop) : Prop := p

theorem Hide.intro {p : Prop} (h : p) : Hide p := by unfold Hide; exact h
theorem Hide.elim {p : Prop} (h : Hide p) : p := by unfold Hide at h; exact h

/-! ## Strings -/

def space : JChar := BitVec.ofNat 16 32

/-- `n` spaces. -/
def spJ (n : Nat) : JStr := List.replicate n space

theorem spJ_succ (n : Nat) : spJ (n + 1) = spJ n ++ [space] := by
  simp [spJ, List.replicate_succ']

theorem spJ_length (n : Nat) : (spJ n).length = n := by simp [spJ]

/-- The digit `d` as a UTF-16 unit. -/
def digitJ (d : Nat) : JChar := BitVec.ofNat 16 (48 + d)

/-- The last `m` decimal digits of `c`, zero-padded (`fmtU`). -/
def zpadJ (c : Nat) : Nat → JStr
  | 0 => []
  | m + 1 => zpadJ (c / 10) m ++ [digitJ (c % 10)]

theorem zpadJ_length (c m : Nat) : (zpadJ c m).length = m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih => simp [zpadJ, ih]

/-- `zpadJ` sees only the last `m` digits. -/
theorem zpadJ_mod (c m : Nat) : zpadJ (c % 10 ^ m) m = zpadJ c m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    simp only [zpadJ]
    have h1 : c % 10 ^ (m + 1) / 10 = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ m) 10, Nat.mod_mul_right_div_self]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 := by
      rw [Nat.pow_succ]
      exact Nat.mod_mul_left_mod c (10 ^ m) 10
    rw [h1, h2, ih]

/-- `StringBuilder.append(char)`: the character as a one-unit string. -/
theorem valueOfArg_char (P : Program) (c : I32) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfArg P (.prim .char) (.int c) σ k = k [c.setWidth 16] σ := rfl

/-! ## Machine arithmetic -/

theorem pow10_lt (k : Nat) (hk : k ≤ 18) : 10 ^ k < 2 ^ 63 := by
  have : 10 ^ k ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hk
  have h2 : (10 : Nat) ^ 18 < 2 ^ 63 := by decide
  omega

theorem pow10_pos (k : Nat) : 0 < 10 ^ k := Nat.pow_pos (by decide)

theorem ofNat_pow10_ne_zero (k : Nat) (hk : k ≤ 18) : BitVec.ofNat 64 (10 ^ k) ≠ 0#64 := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := pow10_lt k hk; omega)] at h1
  have := pow10_pos k
  simp at h1

theorem toInt_ofNat_pow10 (k : Nat) (hk : k ≤ 18) :
    (BitVec.ofNat 64 (10 ^ k)).toInt = ((10 ^ k : Nat) : Int) := by
  have h := pow10_lt k hk
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

theorem msb_false_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : l.msb = false := by
  have := BitVec.toInt_eq_toNat_cond l
  have hl := l.isLt
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  by_cases hc : 2 * l.toNat < 2 ^ 64
  · omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)] at this
    · omega

theorem toNat_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : (l.toNat : Int) = l.toInt := by
  have := BitVec.toInt_eq_toNat_cond l
  split at this <;> omega

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

/-- The character `fmtU` stores: `(char) ('0' + (int) (a % 10))`. -/
theorem digit_char (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (JInt.toChar (48#32 + JLong.toInt (l.srem 10#64))).setWidth 16 = digitJ (l.toNat % 10) := by
  rw [srem10_of_nonneg l h]
  apply BitVec.eq_of_toNat_eq
  simp only [digitJ, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem drop_set_self {α : Type} : ∀ (xs : List α) (k : Nat) (e : α), k < xs.length →
    (xs.set k e).drop k = e :: xs.drop (k + 1)
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, k + 1, e, h => by
    simp only [List.set_cons_succ, List.drop_succ_cons]
    exact drop_set_self xs k e (by simpa using h)

/-- `lcmp` against 0, as the sign of the value. -/
theorem cmp_zero_nonneg_iff (a : I64) : 0 ≤ (JLong.cmp a 0#64).toInt ↔ 0 ≤ a.toInt := by
  unfold JLong.cmp
  by_cases h1 : a.slt 0#64
  · have : a.toInt < 0 := by
      rw [BitVec.slt_iff_toInt_lt] at h1; simpa using h1
    simp only [h1, ite_true]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; omega
  · have : 0 ≤ a.toInt := by
      rw [BitVec.slt_iff_toInt_lt] at h1; simp at h1; omega
    simp only [h1]
    constructor
    · intro _; exact this
    · intro _
      by_cases h2 : a = 0#64
      · simp [h2]
      · simp only [h2, ite_false]; decide

/-- `|v| mod 10^k`, as Java's `fmtU` computes it (`v > Long.MIN_VALUE`). -/
theorem srem_abs_toNat (v : I64) (k : Nat) (hk : k ≤ 18) (hv : -9223372036854775808 < v.toInt) :
    ((if 0 ≤ v.toInt then v else -v).srem (BitVec.ofNat 64 (10 ^ k))).toNat =
      v.toInt.natAbs % 10 ^ k ∧
    0 ≤ ((if 0 ≤ v.toInt then v else -v).srem (BitVec.ofNat 64 (10 ^ k))).toInt := by
  have hp := toInt_ofNat_pow10 k hk
  have hpl := pow10_lt k hk
  have hpp := pow10_pos k
  -- the absolute value as a machine integer
  have habs : (if 0 ≤ v.toInt then v else -v).toInt = (v.toInt.natAbs : Int) := by
    split
    · next h => omega
    · next h =>
      rw [BitVec.toInt_neg_of_ne_intMin]
      · omega
      · intro he
        have := congrArg BitVec.toInt he
        rw [BitVec.toInt_intMin] at this
        simp at this
        omega
  have hr : ((if 0 ≤ v.toInt then v else -v).srem (BitVec.ofNat 64 (10 ^ k))).toInt =
      ((v.toInt.natAbs % 10 ^ k : Nat) : Int) := by
    rw [BitVec.toInt_srem, habs, hp, Int.tmod_eq_emod_of_nonneg (by omega), Int.natCast_emod]
  have hnn : 0 ≤ ((if 0 ≤ v.toInt then v else -v).srem (BitVec.ofNat 64 (10 ^ k))).toInt := by
    rw [hr]; omega
  refine ⟨?_, hnn⟩
  have := toNat_of_toInt_nonneg _ hnn
  omega

/-! ### Rewrites for the residual goals of `fmtU` -/

theorem ofNat_pow10_eq_zero_iff (k : Nat) (hk : k ≤ 18) : BitVec.ofNat 64 (10 ^ k) = 0#64 ↔ False :=
  ⟨ofNat_pow10_ne_zero k hk, False.elim⟩

theorem zpadJ_srem_pos (v : I64) (k : Nat) (hv : 0 ≤ v.toInt) (hk : k ≤ 18) :
    zpadJ (v.srem (BitVec.ofNat 64 (10 ^ k))).toNat k = zpadJ v.toInt.natAbs k := by
  have h := (srem_abs_toNat v k hk (by omega)).1
  simp only [hv, ↓reduceIte] at h
  rw [h, zpadJ_mod]

theorem zpadJ_srem_neg (v : I64) (k : Nat) (hv : ¬ 0 ≤ v.toInt)
    (hm : -9223372036854775808 < v.toInt) (hk : k ≤ 18) :
    zpadJ ((-v).srem (BitVec.ofNat 64 (10 ^ k))).toNat k = zpadJ v.toInt.natAbs k := by
  have h := (srem_abs_toNat v k hk hm).1
  simp only [hv, ↓reduceIte] at h
  rw [h, zpadJ_mod]

theorem srem_pow10_nonneg_pos (v : I64) (k : Nat) (hv : 0 ≤ v.toInt) (hk : k ≤ 18) :
    0 ≤ v.toInt.tmod (BitVec.ofNat 64 (10 ^ k)).toInt := by
  have h := (srem_abs_toNat v k hk (by omega)).2
  simp only [hv, ↓reduceIte, BitVec.toInt_srem] at h
  exact h

theorem srem_pow10_nonneg_neg (v : I64) (k : Nat) (hv : ¬ 0 ≤ v.toInt)
    (hm : -9223372036854775808 < v.toInt) (hk : k ≤ 18) :
    0 ≤ (-v).toInt.tmod (BitVec.ofNat 64 (10 ^ k)).toInt := by
  have h := (srem_abs_toNat v k hk hm).2
  simp only [hv, ↓reduceIte, BitVec.toInt_srem] at h
  exact h

theorem toNat_add_one_of_neg (x : Int) (h1 : -1 ≤ x) (h2 : x < 0) : (x + 1).toNat = 0 := by omega

theorem int_add_neg_one_add_one (x : Int) : x + -1 + 1 = x := by omega

theorem toChar_toChar (x : I32) : JInt.toChar (JInt.toChar x) = JInt.toChar x := by
  unfold JInt.toChar
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem charsOf_cons (x : Value) (xs : List Value) :
    Native.charsOf (x :: xs) = (match x with | .int c => c.setWidth 16 | _ => 0) :: Native.charsOf xs := rfl

theorem charsOf_nil : Native.charsOf [] = [] := rfl

end EquivLean.Modernize.Cbact04c.Java
