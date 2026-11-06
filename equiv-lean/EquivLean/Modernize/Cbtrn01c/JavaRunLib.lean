import EquivLean.Modernize.Cbtrn01c.JavaProof

/-!
# CBTRN01C → Java: lemmas for the proof of `run`

The heap relation `Grows`, the hiding wrapper `Hide`, the strings the helpers build (`spJ`,
`zpadJ`), machine arithmetic of the digit loop (`long` division and remainder by 10, `lcmp`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

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
    (JInt.toChar (48#32 + JLong.toInt (BitVec.srem l 10#64))).setWidth 16 =
      BitVec.ofNat 16 (48 + l.toInt.natAbs % 10) := by
  rw [digit_char l h, digitJ, pos_toNat l h]

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

end EquivLean.Modernize.Cbtrn01c.Java
