import EquivLean.Modernize.Cbtrn03c.JavaGen
import EquivLean.Modernize.Cbtrn03c.Model
import EquivLean.Bridge.Jimple.CobolRec

/-!
# CBTRN03C → Java: lemmas for the helper contracts and the proof of `run`

The heap relation `Grows`, the hiding wrapper `Hide`, the strings the helpers build (`repJ`,
`spJ`, `padJ`, `zpadJ`), machine arithmetic of the digit loops (`long` division and remainder,
`lcmp`).  Most of these are CBTRN01C's (`Cbtrn01c/JavaRunLib.lean`), for this program.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

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
builds it), so that string constants and concatenation recipes compute. -/
dsimproc jstrLitT (JStr.ofString _) := fun e => do
  let_expr JStr.ofString s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let units := JStr.ofString str
  let elems := units.map fun (c : BitVec 16) =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 16) (mkNatLit c.toNat)
  return .done (← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) elems)

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

/-- `StringBuilder.append(char)`: the character as a one-unit string. -/
theorem valueOfArg_char (P : Program) (c : I32) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfArg P (.prim .char) (.int c) σ k = k [c.setWidth 16] σ := rfl

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

/-! ## String arguments -/

/-- The text of a string argument: its characters, `""` for `null` (and for a non-string). -/
def argText (σ : State) (v : Value) : JStr := (strOf σ v).getD []

/-- A string argument (not `null`), of `int` length as every Java string. -/
def StrArg (σ : State) (v : Value) : Prop :=
  ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-! ## Strings -/

def space : JChar := BitVec.ofNat 16 32

/-- `n` copies of the character `c` (`repeat`). -/
def repJ (c : JChar) (n : Nat) : JStr := List.replicate n c

theorem repJ_succ (c : JChar) (n : Nat) : repJ c (n + 1) = repJ c n ++ [c] := by
  simp [repJ, List.replicate_succ']

theorem repJ_length (c : JChar) (n : Nat) : (repJ c n).length = n := by simp [repJ]

/-- `n` spaces. -/
def spJ (n : Nat) : JStr := repJ space n

theorem spJ_length (n : Nat) : (spJ n).length = n := by simp [spJ, repJ]

/-- `s` in a field of width `n`: its first `n` characters, padded with spaces (`pad`). -/
def padJ (s : JStr) (n : Nat) : JStr := s.take n ++ spJ (n - s.length)

theorem padJ_of_le {s : JStr} {n : Nat} (h : n ≤ s.length) : padJ s n = s.take n := by
  simp [padJ, spJ, repJ, Nat.sub_eq_zero_of_le h]

theorem padJ_of_lt {s : JStr} {n : Nat} (h : s.length < n) : padJ s n = s ++ spJ (n - s.length) := by
  simp [padJ, List.take_of_length_le (Nat.le_of_lt h)]

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

/-- Only the last `m` digits count. -/
theorem zpadJ_mod (c m : Nat) : zpadJ (c % 10 ^ m) m = zpadJ c m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    have h1 : c % 10 ^ (m + 1) / 10 = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ m) 10, Nat.mod_mul_right_div_self]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 := by
      rw [Nat.pow_succ]; exact Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left 10 _)
    simp only [zpadJ, h1, h2, ih]

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

/-- `sdiv` of non-negative `long`s is the natural quotient. -/
theorem sdiv_toNat_of_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    (l.sdiv p).toNat = l.toNat / p.toNat := by
  rw [BitVec.sdiv_eq, msb_false_of_toInt_nonneg l hl, msb_false_of_toInt_nonneg p hp]
  simp [BitVec.toNat_udiv]

theorem sdiv_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    0 ≤ (l.sdiv p).toInt := by
  have hn := sdiv_toNat_of_nonneg l p hl hp
  have hl2 := l.isLt
  have hlt : 2 * l.toNat < 2 ^ 64 := by
    have := BitVec.toInt_eq_toNat_cond l; split at this <;> omega
  have hq : (l.sdiv p).toNat ≤ l.toNat := by rw [hn]; exact Nat.div_le_self _ _
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

/-- `srem` of non-negative `long`s is the natural remainder. -/
theorem srem_toNat_of_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    (l.srem p).toNat = l.toNat % p.toNat := by
  rw [BitVec.srem_eq, msb_false_of_toInt_nonneg l hl, msb_false_of_toInt_nonneg p hp]
  simp [BitVec.toNat_umod]

theorem srem_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    0 ≤ (l.srem p).toInt := by
  have hn := srem_toNat_of_nonneg l p hl hp
  have hl2 := l.isLt
  have hlt : 2 * l.toNat < 2 ^ 64 := by
    have := BitVec.toInt_eq_toNat_cond l; split at this <;> omega
  have hq : (l.srem p).toNat ≤ l.toNat := by rw [hn]; exact Nat.mod_le _ _
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

/-- `10 ^ k` as a `long` times 10. -/
theorem pow10_mul (k : Nat) : BitVec.ofNat 64 (10 ^ k) * 10#64 = BitVec.ofNat 64 (10 ^ (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.pow_succ, Nat.mod_mul_mod]

theorem pow10_toNat {k : Nat} (h : k ≤ 18) : (BitVec.ofNat 64 (10 ^ k)).toNat = 10 ^ k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  calc 10 ^ k ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) h
    _ < 2 ^ 64 := by decide

theorem pow10_toInt {k : Nat} (h : k ≤ 18) : (BitVec.ofNat 64 (10 ^ k)).toInt = (10 ^ k : Nat) := by
  rw [BitVec.toInt_eq_toNat_cond, pow10_toNat h]
  have : 2 * 10 ^ k < 2 ^ 64 := by
    calc 2 * 10 ^ k ≤ 2 * 10 ^ 18 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)
      _ < 2 ^ 64 := by decide
  simp [this]

/-- The character `(char) ('0' + (int) d)` of a `long` digit `0 ≤ d < 10`. -/
theorem digit_char_of_lt (l : BitVec 64) (h : l.toNat < 10) :
    (JInt.toChar (48#32 + JLong.toInt l)).setWidth 16 = digitJ l.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [digitJ, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

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

/-- The absolute value of a `long` other than `Long.MIN_VALUE`, as the helpers compute it. -/
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

/-! ## Allocation chains -/

/-- Overwriting the object just allocated. -/
theorem alloc_setObj_self (σ : State) (o o' : Obj) :
    (σ.alloc o).2.setObj σ.next o' = (σ.alloc o').2 := by
  simp only [State.alloc, State.setObj, State.next]
  congr 1
  apply Array.toList_inj.mp
  simp [Array.toList_setIfInBounds]

/-- Overwriting an older object commutes with an allocation. -/
theorem alloc_setObj_lt (σ : State) (o o' : Obj) {a : Addr} (h : a < σ.next) :
    (σ.alloc o).2.setObj a o' = ((σ.setObj a o').alloc o).2 := by
  simp only [State.alloc, State.setObj, State.next] at *
  congr 1
  apply Array.toList_inj.mp
  simp only [Array.toList_setIfInBounds, Array.toList_push]
  have h' : a < σ.mem.toList.length := by rw [Array.length_toList]; exact h
  rw [List.set_append_left _ _ h']

theorem nat_self_eq_add (n k : Nat) : (n = n + k) = (k = 0) := by apply propext; omega
theorem nat_add_eq_self (n k : Nat) : (n + k = n) = (k = 0) := by apply propext; omega

theorem eq_add_false_of_lt {a b : Nat} (k : Nat) (h : a < b) : (a = b + k) = False :=
  eq_false (by omega)
theorem add_eq_false_of_lt {a b : Nat} (k : Nat) (h : a < b) : (b + k = a) = False :=
  eq_false (by omega)

end EquivLean.Modernize.Cbtrn03c.Java
