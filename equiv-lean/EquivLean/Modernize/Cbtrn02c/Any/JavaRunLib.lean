import EquivLean.Modernize.Cbtrn02c.JavaSpec

/-!
# CBTRN02C → Java: lemmas for the proof of `run`

The heap relation `Grows`, the hiding wrapper `Hide`, the strings the helpers build (`spJ`,
`zpadJ`), machine arithmetic of the digit loop (`long` division and remainder by 10, `lcmp`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ## Simp helpers -/

theorem fields_get_cons (k k' : FieldKey) (v : Value) (fs : List (FieldKey × Value)) :
    Fields.get ((k, v) :: fs) k' = if k' = k then some v else Fields.get fs k' := by
  simp only [Fields.get, List.lookup]
  by_cases h : k' = k
  · subst h; simp
  · have : (k' == k) = false := by simp [h]
    simp [this, h]

theorem fields_get_nil (k' : FieldKey) : Fields.get [] k' = none := rfl

open Lean Meta in
/-- `JStr.ofString "…"` on a literal as its explicit list of UTF-16 code units (as `JStr.ofChar`
builds it), so that string constants and concatenation recipes compute (as `jstrLit` of
`Bridge/Jimple/SpecAuto.lean`). -/
dsimproc jstrLitT (JStr.ofString _) := fun e => do
  let_expr JStr.ofString s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let units := JStr.ofString str
  let elems := units.map fun (c : BitVec 16) =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 16) (mkNatLit c.toNat)
  return .done (← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) elems)

/-- An array index `BitVec.ofNat 32 i` read back (`toNat`) for `i < 2^32`. -/
theorem nat_mod_2_32 {i : Nat} (h : i < 4294967296) : i % 4294967296 = i := Nat.mod_eq_of_lt h

/-! ## `String.valueOf` of a string argument -/

/-- `valueOfObjN` folded: the cases other than a string object (never taken for the arguments of
these proofs). -/
@[irreducible] def vobjSlow (P : Program) (n : Nat) (v : Value) (σ : State)
    (k : JStr → State → NRes) : NRes := Native.valueOfObjN P n v σ k

/-- `String.valueOf` of a reference: a string object's text; every other case folded into
`vobjSlow` (so that symbolic execution never unfolds the `toString` machinery). -/
theorem valueOfObjN_ref (P : Program) (n : Nat) (a : Addr) (σ : State)
    (k : JStr → State → NRes) :
    Native.valueOfObjN P (n + 1) (.ref a) σ k =
      match σ.heap a with
      | some (.str s) => k s σ
      | _ => vobjSlow P (n + 1) (.ref a) σ k := by
  unfold vobjSlow
  cases h : σ.heap a with
  | none => rfl
  | some o =>
    cases o <;> first | rfl | (simp only [Native.valueOfObjN, h, Native.nObjStr])

theorem valueOfObj_eq (P : Program) (v : Value) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfObj P v σ k = Native.valueOfObjN P 8 v σ k := rfl

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

/-- The last `m` decimal digits of `c`, zero-padded (`digits`). -/
def zpadJ (c : Nat) : Nat → JStr
  | 0 => []
  | m + 1 => zpadJ (c / 10) m ++ [digitJ (c % 10)]

theorem zpadJ_length (c m : Nat) : (zpadJ c m).length = m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih => simp [zpadJ, ih]

/-- `StringBuilder.append(char)`: the character as a one-unit string. -/
theorem valueOfArg_char (P : Program) (c : I32) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfArg P (.prim .char) (.int c) σ k = k [c.setWidth 16] σ := rfl

/-! ## Machine arithmetic -/

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

/-- The character `digits` stores: `(char) ('0' + (int) (v % 10))`. -/
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

/-- `lcmp` is 0 exactly on equal values. -/
theorem jlong_cmp_eq_zero (a b : I64) : (JLong.cmp a b = 0#32) ↔ a = b := by
  unfold JLong.cmp
  by_cases h1 : a.slt b
  · have hne : a ≠ b := by
      intro h; subst h; simp [BitVec.slt, Int.lt_irrefl] at h1
    simp only [h1, ite_true, hne, iff_false]
    decide
  · simp only [h1]
    by_cases h2 : a = b
    · simp [h2]
    · simp only [h2, ite_false, iff_false]; decide

/-- The absolute value of a `long` other than `Long.MIN_VALUE`, as `digits` computes it. -/
theorem abs_toNat (v : I64) (hv : -9223372036854775808 < v.toInt) :
    (if 0 ≤ v.toInt then v else -v).toNat = v.toInt.natAbs ∧
    0 ≤ (if 0 ≤ v.toInt then v else -v).toInt := by
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
  have hnn : 0 ≤ (if 0 ≤ v.toInt then v else -v).toInt := by rw [habs]; omega
  refine ⟨?_, hnn⟩
  have := toNat_of_toInt_nonneg _ hnn
  omega

theorem neg_toNat (v : I64) (hv : -9223372036854775808 < v.toInt) (hneg : v.toInt < 0) :
    (-v).toNat = v.toInt.natAbs ∧ 0 ≤ (-v).toInt := by
  have h := abs_toNat v hv
  simp only [show ¬ (0 ≤ v.toInt) by omega, ↓reduceIte] at h
  exact h

theorem pos_toNat (v : I64) (hpos : 0 ≤ v.toInt) : v.toNat = v.toInt.natAbs := by
  have := toNat_of_toInt_nonneg v hpos
  omega

theorem negNat (v : I64) (h1 : ¬ 0 ≤ v.toInt) (h2 : -9223372036854775808 < v.toInt) :
    (18446744073709551616 - v.toNat) % 18446744073709551616 = v.toInt.natAbs := by
  have := BitVec.toInt_eq_toNat_cond v
  have hl := v.isLt
  split at this <;> omega

theorem toNat_add_one_of_neg (x : Int) (h1 : -1 ≤ x) (h2 : x < 0) : (x + 1).toNat = 0 := by omega

theorem int_add_neg_one_add_one (x : Int) : x + -1 + 1 = x := by omega

theorem charsOf_cons_int (c : I32) (xs : List Value) :
    Native.charsOf (.int c :: xs) = c.setWidth 16 :: Native.charsOf xs := rfl

theorem toChar_toChar (x : I32) : JInt.toChar (JInt.toChar x) = JInt.toChar x := by
  unfold JInt.toChar
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

/-- The character `digits` stores, as the jvc simp set presents it. -/
theorem digit_char2 (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (JInt.toChar (JInt.toChar (48#32 + JLong.toInt (BitVec.srem l 10#64)))).setWidth 16 =
      BitVec.ofNat 16 (48 + l.toInt.natAbs % 10) := by
  rw [toChar_toChar, digit_char l h, digitJ, pos_toNat l h]

theorem charsOf_replicate_drop (n : Nat) :
    Native.charsOf ((List.replicate n (Value.int 0)).drop n) = [] := by
  simp [Native.charsOf]

/-! ## `signedZoned`: the last digit and the overpunch -/

theorem zpadJ_getElem?_pred (c N : Nat) (h : 1 ≤ N) :
    (zpadJ c N)[N - 1]? = some (digitJ (c % 10)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp only [zpadJ, Nat.add_sub_cancel]
  rw [List.getElem?_append_right (by rw [zpadJ_length]; exact Nat.le_refl _)]
  simp [zpadJ_length]

theorem zpadJ_take_pred (c N : Nat) (h : 1 ≤ N) :
    (zpadJ c N).take (N - 1) = zpadJ (c / 10) (N - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp only [zpadJ, Nat.add_sub_cancel]
  rw [List.take_append_of_le_length (by rw [zpadJ_length]; exact Nat.le_refl _),
    List.take_of_length_le (by rw [zpadJ_length]; exact Nat.le_refl _)]

theorem i32_toNat_eq (i : I32) (h0 : 0 ≤ i.toInt) : i.toNat = i.toInt.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at h0 <;> omega

theorem i32_toNat_sub_one (n : I32) (h0 : 1 ≤ n.toInt) : (n - 1#32).toNat = n.toInt.toNat - 1 := by
  have h1 : (n - 1#32).toInt = n.toInt - 1 := by
    rw [BitVec.toInt_sub]
    have : (1#32).toInt = 1 := by decide
    rw [this, Int.bmod_def]
    have := BitVec.toInt_lt (x := n)
    split <;> simp_all <;> omega
  rw [i32_toNat_eq _ (by omega), h1]
  omega

/-- The code point of an overpunched last digit, as a UTF-16 unit. -/
def overJ (neg : Bool) (d : Nat) : JChar := BitVec.ofNat 16 (EquivLean.Cobol.Rec.overpunch neg d)

theorem digit_sub48 (d : Nat) (h : d < 10) :
    (BitVec.ofNat 16 (48 + d)).setWidth 32 - 48#32 = BitVec.ofNat 32 d := by
  revert d; decide

theorem over_pos_char (d : Nat) (h : d < 10) :
    BitVec.setWidth 16 (JInt.toChar (65#32 + (BitVec.ofNat 32 (48 + d) - 48#32) - 1#32)) =
      BitVec.ofNat 16 (64 + d) := by
  revert d; decide

theorem over_neg_char (d : Nat) (h : d < 10) :
    BitVec.setWidth 16 (JInt.toChar (74#32 + (BitVec.ofNat 32 (48 + d) - 48#32) - 1#32)) =
      BitVec.ofNat 16 (73 + d) := by
  revert d; decide

theorem idx_pred (N : Nat) (h : 1 ≤ N) (h2 : N < 2147483647) :
    (4294967295 + N) % 4294967296 = N - 1 := by
  omega

theorem ofNat32_digit_eq_zero (d : Nat) (h : d < 10) : (BitVec.ofNat 32 d = 0#32) ↔ d = 0 := by
  revert d; decide

/-! ## Powers of ten, `trunc`, `norm` -/

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

theorem pow10_step (k : Nat) : BitVec.ofNat 64 (10 ^ k) * 10#64 = BitVec.ofNat 64 (10 ^ (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.pow_succ, Nat.mul_mod]

theorem ofNat_pow10_eq_zero_iff (k : Nat) (hk : k ≤ 18) : BitVec.ofNat 64 (10 ^ k) = 0#64 ↔ False :=
  ⟨ofNat_pow10_ne_zero k hk, False.elim⟩

theorem toNat_add_one_of_nonneg (x : Int) (h : 0 ≤ x) : (x + 1).toNat = x.toNat + 1 := by omega

/-- `norm(v, n)`: `|v| mod 10^n`, as Java computes it. -/
def normR (v : I64) (n : Nat) : I64 := (if 0 ≤ v.toInt then v else -v).srem (BitVec.ofNat 64 (10 ^ n))

/-- `|v| mod 10^k`, as Java's `norm` computes it (`v > Long.MIN_VALUE`). -/
theorem normR_toNat (v : I64) (k : Nat) (hk : k ≤ 18) (hv : -9223372036854775808 < v.toInt) :
    (normR v k).toNat = v.toInt.natAbs % 10 ^ k ∧ 0 ≤ (normR v k).toInt := by
  unfold normR
  have hp := toInt_ofNat_pow10 k hk
  have hpl := pow10_lt k hk
  have hpp := pow10_pos k
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

theorem zpadJ_normR (v : I64) (k : Nat) (hk : k ≤ 18) (hv : -9223372036854775808 < v.toInt) :
    zpadJ (normR v k).toNat k = zpadJ v.toInt.natAbs k := by
  rw [(normR_toNat v k hk hv).1, zpadJ_mod]

theorem normR_nonneg (v : I64) (k : Nat) (hk : k ≤ 18) (hv : -9223372036854775808 < v.toInt) :
    0 ≤ (normR v k).toInt := (normR_toNat v k hk hv).2

/-! ## v2 string helpers -/

/-- A char read by `charAt` and appended again. -/
theorem jchar_rt (c : JChar) : (c.zeroExtend 32).setWidth 16 = c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
  have := c.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `fit(s, n)`: the first `n` characters of `s`, padded with spaces. -/
def fitJ (cs : JStr) (n : Nat) : JStr := (List.range n).map fun i => cs.getD i space

theorem fitJ_zero (cs : JStr) : fitJ cs 0 = [] := rfl

theorem fitJ_succ_lt (cs : JStr) (i : Nat) (c : JChar) (h : cs[i]? = some c) :
    fitJ cs (i + 1) = fitJ cs i ++ [c] := by
  simp [fitJ, List.range_succ, List.getD_eq_getElem?_getD, h]

theorem fitJ_succ_ge (cs : JStr) (i : Nat) (h : cs.length ≤ i) :
    fitJ cs (i + 1) = fitJ cs i ++ [space] := by
  simp [fitJ, List.range_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- The digits of `c`, least significant first, `i` of them. -/
def revD (c : Nat) (i : Nat) : JStr := (List.range i).map fun k => digitJ (c / 10 ^ k % 10)

theorem revD_succ (c i : Nat) : revD c (i + 1) = revD c i ++ [digitJ (c / 10 ^ i % 10)] := by
  simp [revD, List.range_succ]

theorem revD_length (c i : Nat) : (revD c i).length = i := by simp [revD]

theorem revD_cons (c i : Nat) : revD c (i + 1) = digitJ (c % 10) :: revD (c / 10) i := by
  simp only [revD, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro k _
    simp only [Function.comp, Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (10 ^ k) 10]

theorem revD_reverse (c i : Nat) : (revD c i).reverse = zpadJ c i := by
  induction i generalizing c with
  | zero => rfl
  | succ i ih => rw [revD_cons, List.reverse_cons, ih, zpadJ]

/-- The character `padNum` appends: `(char) (int) (48L + a % 10)`. -/
theorem digit_char3 (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (JInt.toChar (JLong.toInt (48#64 + l.srem 10#64))).setWidth 16 = digitJ (l.toNat % 10) := by
  rw [srem10_of_nonneg l h]
  apply BitVec.eq_of_toNat_eq
  simp only [digitJ, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem rev_drop_step {α : Type} (R : List α) (i : Nat) (c : α) (h : R[i]? = some c) :
    (R.drop (i + 1)).reverse ++ [c] = (R.drop i).reverse := by
  have hi : i < R.length := by
    rcases Nat.lt_or_ge i R.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at h; cases h
  rw [List.drop_eq_getElem_cons hi, List.reverse_cons]
  rw [List.getElem?_eq_getElem hi] at h
  cases h; rfl

theorem jchar_rt' (c : JChar) : (c.setWidth 32).setWidth 16 = c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := c.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The index `zonedSigned` reads the overpunch strings at: the last digit's code minus 48. -/
theorem idx_sub48 (d : Nat) : (4294967248 + (48 + d % 10)) % 4294967296 = d % 10 := by omega

/-- `"{ABCDEFGHI".charAt(d)`: the positive overpunch of digit `d`. -/
theorem over_pos_lit (d : Nat) {h} :
    ([123#16, 65#16, 66#16, 67#16, 68#16, 69#16, 70#16, 71#16, 72#16, 73#16] : List (BitVec 16))[d % 10]'h =
      overJ false (d % 10) := by
  have : d % 10 < 10 := Nat.mod_lt _ (by decide)
  generalize d % 10 = e at this h ⊢
  revert e; decide

/-- `"}JKLMNOPQR".charAt(d)`: the negative overpunch of digit `d`. -/
theorem over_neg_lit (d : Nat) {h} :
    ([125#16, 74#16, 75#16, 76#16, 77#16, 78#16, 79#16, 80#16, 81#16, 82#16] : List (BitVec 16))[d % 10]'h =
      overJ true (d % 10) := by
  have : d % 10 < 10 := Nat.mod_lt _ (by decide)
  generalize d % 10 = e at this h ⊢
  revert e; decide

/-! ## Searches -/

/-- The first index `j` with `p xs[j]`, or `-1`. -/
def firstIdx {α : Type} (p : α → Bool) (xs : List α) : Int :=
  match xs.findIdx? p with
  | some j => j
  | none => -1

theorem findIdx?_eq_some_of {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length), p xs[i] = true →
      (∀ j (hj : j < i), p (xs[j]'(Nat.lt_trans hj hi)) = false) → xs.findIdx? p = some i
  | [], _, hi, _, _ => by simp at hi
  | x :: xs, 0, _, hp, _ => by simp at hp; simp [List.findIdx?_cons, hp]
  | x :: xs, i + 1, hi, hp, hlt => by
    have h0 := hlt 0 (by omega)
    simp only [List.getElem_cons_zero] at h0
    rw [List.findIdx?_cons, h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [findIdx?_eq_some_of p xs i (by simp at hi; omega) (by simpa using hp)
      (fun j hj => by simpa using hlt (j + 1) (by omega))]
    rfl

theorem findIdx?_eq_none_of {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ j (hj : j < xs.length), p xs[j] = false) → xs.findIdx? p = none
  | [], _ => rfl
  | x :: xs, h => by
    have h0 := h 0 (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_zero] at h0
    rw [List.findIdx?_cons, h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [findIdx?_eq_none_of p xs (fun j hj => by
      have := h (j + 1) (by simp; omega)
      simpa only [List.getElem_cons_succ] using this)]
    rfl

theorem firstIdx_of_found {α : Type} (p : α → Bool) (xs : List α) (i : Nat) (hi : i < xs.length)
    (hp : p xs[i] = true) (hlt : ∀ j (hj : j < i), p (xs[j]'(Nat.lt_trans hj hi)) = false) :
    firstIdx p xs = i := by
  unfold firstIdx; rw [findIdx?_eq_some_of p xs i hi hp hlt]

theorem firstIdx_of_none {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ j (hj : j < xs.length), p xs[j] = false) : firstIdx p xs = -1 := by
  unfold firstIdx; rw [findIdx?_eq_none_of p xs h]

/-- The text of the string field `k` of the object `v`. -/
def strFieldOf (σ : State) (k : FieldKey) : Value → Option JStr
  | .ref x => match σ.heap x with
    | some (.plain _ fs) => match Fields.get fs k with
      | some (.ref s) => match σ.heap s with
        | some (.str cs) => some cs
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The value of the `long` field `k` of the object `v`. -/
def longFieldOf (σ : State) (k : FieldKey) : Value → Option I64
  | .ref x => match σ.heap x with
    | some (.plain _ fs) => match Fields.get fs k with
      | some (.long l) => some l
      | _ => none
    | _ => none
  | _ => none

/-- The text of the string `v`. -/
def strOfV (σ : State) : Value → Option JStr
  | .ref s => match σ.heap s with
    | some (.str cs) => some cs
    | _ => none
  | _ => none

/-- No element before index `n` satisfies `p` (a search's loop invariant). -/
def NoMatch {α : Type} (p : α → Bool) (xs : List α) (n : Nat) : Prop :=
  ∀ j (hj : j < xs.length), j < n → p xs[j] = false

theorem noMatch_zero {α : Type} (p : α → Bool) (xs : List α) : NoMatch p xs 0 ↔ True :=
  ⟨fun _ => trivial, fun _ j _ h => absurd h (Nat.not_lt_zero j)⟩

theorem noMatch_succ {α : Type} (p : α → Bool) (xs : List α) (i : I32) (h0 : 0 ≤ i.toInt)
    (h : NoMatch p xs i.toInt.toNat) (hc : ∀ hi, p (xs[i.toInt.toNat]'hi) = false) :
    NoMatch p xs (i.toInt.toNat + 1) := by
  intro j hj hji
  by_cases hlt : j < i.toInt.toNat
  · exact h j hj hlt
  · have : j = i.toInt.toNat := by omega
    subst this; exact hc hj

/-- The loop of a search ends without a match: the result `-1`. -/
theorem exit_idx {α : Type} (p : α → Bool) (xs : List α) (i : I32) (h0 : 0 ≤ i.toInt)
    (hle : (xs.length : Int) ≤ i.toInt) (hinv : NoMatch p xs i.toInt.toNat) :
    4294967295#32 = BitVec.ofInt 32 (firstIdx p xs) := by
  rw [firstIdx_of_none p xs (fun j hj => hinv j hj (by omega))]; rfl

/-- A search finds its first match at `i`. -/
theorem found_idx {α : Type} (p : α → Bool) (xs : List α) (i : I32) (h0 : 0 ≤ i.toInt)
    (hlt : i.toInt < (xs.length : Int)) (hp : ∀ h, p (xs[i.toInt.toNat]'h) = true)
    (hinv : NoMatch p xs i.toInt.toNat) :
    i = BitVec.ofInt 32 (firstIdx p xs) := by
  have hi : i.toInt.toNat < xs.length := by omega
  rw [firstIdx_of_found p xs i.toInt.toNat hi (hp hi) (fun j hj => hinv j _ hj)]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt]
  have := i.toInt_lt; have := i.le_toInt
  simp only [Int.toNat_of_nonneg h0]
  rw [Int.bmod_eq_of_le] <;> omega

/-! ## CP037 -/

theorem cp037Char_toNat_lt (b : UInt8) : (Cobol.Codepage.cp037Char b).toNat < 256 := by
  have h := (Cobol.Codepage.cp037_check b.toNat b.toNat_lt).2.2.1
  unfold Cobol.Codepage.cp037Char
  rw [Cobol.Codepage.Char.toNat_ofNat_lt256 _ h]
  exact h

theorem cp037Unit_inj {a b : UInt8} (h : EquivLean.Cobol.Rec.cp037Unit a = EquivLean.Cobol.Rec.cp037Unit b) :
    a = b := by
  unfold EquivLean.Cobol.Rec.cp037Unit at h
  have ha := cp037Char_toNat_lt a
  have hb := cp037Char_toNat_lt b
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  have e1 := Cobol.Codepage.cp037Byte_cp037Char a
  have e2 := Cobol.Codepage.cp037Byte_cp037Char b
  unfold Cobol.Codepage.cp037Byte at e1 e2
  rw [h2] at e1
  rw [e1] at e2
  exact Option.some.inj e2

theorem cp037Str_inj : ∀ {a b : List UInt8},
    EquivLean.Cobol.Rec.cp037Str a = EquivLean.Cobol.Rec.cp037Str b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [EquivLean.Cobol.Rec.cp037Str] at h
  | _ :: _, [], h => by simp [EquivLean.Cobol.Rec.cp037Str] at h
  | x :: xs, y :: ys, h => by
    simp only [EquivLean.Cobol.Rec.cp037Str, List.map_cons, List.cons.injEq] at h
    rw [cp037Unit_inj h.1, cp037Str_inj (a := xs) (b := ys) h.2]

theorem cp037Unit_setWidth_iff (a b : UInt8) :
    (EquivLean.Cobol.Rec.cp037Unit a).setWidth 32 = (EquivLean.Cobol.Rec.cp037Unit b).setWidth 32 ↔
      a = b := by
  constructor
  · intro h
    apply cp037Unit_inj
    have h2 := congrArg (BitVec.setWidth 16) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq, BitVec.setWidth_eq] at h2
  · intro h; rw [h]

theorem uint8_ofNat_eq_iff (k : Nat) (b : UInt8) (hk : k < 256) : UInt8.ofNat k = b ↔ k = b.toNat := by
  constructor
  · intro h; subst h; simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hk]
  · intro h; subst h; simp

theorem map_cp037Unit_iff (a b : List UInt8) :
    List.map EquivLean.Cobol.Rec.cp037Unit a = List.map EquivLean.Cobol.Rec.cp037Unit b ↔ a = b :=
  ⟨fun h => cp037Str_inj h, fun h => h ▸ rfl⟩

theorem narrow_long (v : Value) : (JType.prim .long).narrow v = v := rfl
theorem narrow_cls (c : ClassName) (v : Value) : (JType.cls c).narrow v = v := rfl

theorem setObj_setObj (σ : State) (a : Addr) (o1 o2 : Obj) :
    (σ.setObj a o1).setObj a o2 = σ.setObj a o2 := by
  simp only [State.setObj, Array.setIfInBounds_setIfInBounds]

/-! ## Folded field facts -/

/-- The fields `keys` of `fs1` are those of `fs2` (kept folded during symbolic execution). -/
def SameFields (keys : List FieldKey) (fs1 fs2 : List (FieldKey × Value)) : Prop :=
  ∀ k ∈ keys, Fields.get fs1 k = Fields.get fs2 k

/-- All the fields `keys` are present in `fs`. -/
def AllSome (keys : List FieldKey) (fs : List (FieldKey × Value)) : Prop :=
  ∀ k ∈ keys, (Fields.get fs k).isSome

theorem allSome_set {keys : List FieldKey} {fs : List (FieldKey × Value)} (k : FieldKey) (v : Value)
    (h : AllSome keys fs) : AllSome keys (Fields.set fs k v) := by
  intro k' hk'
  rw [Fields.get_set]
  split
  · rfl
  · exact h k' hk'

theorem allSome_of_same {keys : List FieldKey} {fs1 fs2 : List (FieldKey × Value)}
    (h : SameFields keys fs1 fs2) (h2 : AllSome keys fs2) : AllSome keys fs1 := by
  intro k hk; rw [h k hk]; exact h2 k hk

end EquivLean.Modernize.Cbtrn02c.Java
