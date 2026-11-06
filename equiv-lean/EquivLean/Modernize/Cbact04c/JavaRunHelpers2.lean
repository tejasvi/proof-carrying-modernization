import EquivLean.Modernize.Cbact04c.JavaRunHelpers1

/-!
# CBACT04C → Java: `fmtZoned`, the searches and the record copies
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## `fmtZoned` -/

/-- The overpunched last character of a signed DISPLAY field (`EquivLean.Cobol.Rec.overpunch`). -/
def opJ (neg : Bool) (d : Nat) : JChar :=
  BitVec.ofNat 16 (if neg then (if d = 0 then 125 else 73 + d) else (if d = 0 then 123 else 64 + d))

/-- `fmtZoned v n`: the last `n` digits of `|v|`, the last one overpunched with the sign. -/
def zonedJ (v : Int) (n : Nat) : JStr :=
  zpadJ (v.natAbs / 10) (n - 1) ++ [opJ (decide (v < 0)) (v.natAbs % 10)]

abbrev fmtZonedRef : MethodRef := Gen.Cbact04c.«fmtZoned(long,int)».ref

def fmtZonedSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 2 ≤ n.toInt ∧ n.toInt ≤ 18 ∧
     -9223372036854775808 < v.toInt ∧ σ.initOf "Cbact04c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zonedJ v.toInt n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def fmtUSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "java.lang.String", name := "fmtU",
    params := [.prim .long, .prim .int] }

def fmtZonedC : Contracts := [(fmtUSig, fmtUSpec)]

theorem zpadJ_getElem_last (c m : Nat) (h : m < (zpadJ c (m + 1)).length) :
    (zpadJ c (m + 1))[m] = digitJ (c % 10) := by
  simp only [zpadJ]
  rw [List.getElem_append_right (by rw [zpadJ_length]; omega)]
  simp [zpadJ_length]

/-- `charAt(n - 1)` of `fmtU`'s result: its last digit. -/
theorem charAtIdx_zpadJ_pred (c : Nat) (w : I32) (σ : State) (k : JChar → NRes)
    (h1 : 2 ≤ w.toInt) (h2 : w.toInt ≤ 18) :
    Native.charAtIdx (zpadJ c w.toInt.toNat) (w - 1#32) σ k = k (digitJ (c % 10)) := by
  have hw : (w - 1#32).toInt = w.toInt - 1 := by
    rw [BitVec.toInt_sub]
    have : (1#32).toInt = 1 := by decide
    rw [this, Int.bmod_def]; split <;> omega
  obtain ⟨m, hm⟩ : ∃ m, w.toInt.toNat = m + 1 := ⟨w.toInt.toNat - 1, by omega⟩
  unfold Native.charAtIdx
  rw [hm, zpadJ_length, hw]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  have hi : (w - 1#32).toNat = m := by
    have := BitVec.toInt_eq_toNat_cond (w - 1#32)
    split at this <;> omega
  rw [hi, List.getElem?_eq_getElem (by rw [zpadJ_length]; omega), zpadJ_getElem_last]

theorem digit_sub48 (d : Nat) (hd : d < 10) :
    BitVec.setWidth 32 (digitJ d) - 48#32 = BitVec.ofNat 32 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [digitJ, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem lit_pos_get (d : Nat) (hd : d < 10) :
    (JStr.ofString "{ABCDEFGHI")[d]? = some (opJ false d) := by
  match d, hd with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide

theorem lit_neg_get (d : Nat) (hd : d < 10) :
    (JStr.ofString "}JKLMNOPQR")[d]? = some (opJ true d) := by
  match d, hd with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide

theorem lit_length_pos : (JStr.ofString "{ABCDEFGHI").length = 10 := by decide
theorem lit_length_neg : (JStr.ofString "}JKLMNOPQR").length = 10 := by decide

theorem charAtIdx_digit (s : JStr) (d : Nat) (σ : State) (k : JChar → NRes) (hd : d < 10)
    (hs : s.length = 10) :
    Native.charAtIdx s (BitVec.setWidth 32 (digitJ d) - 48#32) σ k =
      match s[d]? with
      | some c => k c
      | none => Native.bad "index" := by
  unfold Native.charAtIdx
  rw [digit_sub48 d hd]
  have h1 : (BitVec.ofNat 32 d).toInt = d := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]; split <;> omega
  have h2 : (BitVec.ofNat 32 d).toNat = d := by
    rw [BitVec.toNat_ofNat]; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [h1, hs]; omega)), h2]
  rfl

theorem charAtIdx_lit_pos (d : Nat) (σ : State) (k : JChar → NRes) (hd : d < 10) :
    Native.charAtIdx (JStr.ofString "{ABCDEFGHI") (BitVec.setWidth 32 (digitJ d) - 48#32) σ k =
      k (opJ false d) := by
  rw [charAtIdx_digit _ d σ k hd lit_length_pos, lit_pos_get d hd]

theorem charAtIdx_lit_neg (d : Nat) (σ : State) (k : JChar → NRes) (hd : d < 10) :
    Native.charAtIdx (JStr.ofString "}JKLMNOPQR") (BitVec.setWidth 32 (digitJ d) - 48#32) σ k =
      k (opJ true d) := by
  rw [charAtIdx_digit _ d σ k hd lit_length_neg, lit_neg_get d hd]

theorem zpadJ_getElem?_pred (c k : Nat) (hk : 1 ≤ k) :
    (zpadJ c k)[k - 1]? = some (digitJ (c % 10)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, List.getElem?_eq_getElem (by rw [zpadJ_length]; omega), zpadJ_getElem_last]

theorem digitJ_toNat (d : Nat) (hd : d < 10) : (digitJ d).toNat = 48 + d := by
  simp only [digitJ, BitVec.toNat_ofNat]; omega

theorem lit_pos_getElem (d : Nat) (hd : d < 10) (h : d < (JStr.ofString "{ABCDEFGHI").length) :
    (JStr.ofString "{ABCDEFGHI")[d] = opJ false d := by
  have := lit_pos_get d hd
  rw [List.getElem?_eq_getElem h] at this
  exact Option.some.inj this

theorem lit_neg_getElem (d : Nat) (hd : d < 10) (h : d < (JStr.ofString "}JKLMNOPQR").length) :
    (JStr.ofString "}JKLMNOPQR")[d] = opJ true d := by
  have := lit_neg_get d hd
  rw [List.getElem?_eq_getElem h] at this
  exact Option.some.inj this

theorem mod32_sub48 (d : Nat) (hd : d < 10) : (4294967248 + (48 + d)) % 4294967296 = d := by omega

theorem recipe2 : JStr.ofString "\x01\x01" = [1#16, 1#16] := by decide

theorem take_zpadJ_pred (c k : Nat) (hk : 1 ≤ k) : (zpadJ c k).take (k - 1) = zpadJ (c / 10) (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [zpadJ, Nat.add_sub_cancel]
  rw [List.take_append_of_le_length (by rw [zpadJ_length]; exact Nat.le_refl _),
    List.take_of_length_le (by rw [zpadJ_length]; exact Nat.le_refl _)]

theorem mod32_pred (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 18) : (4294967295 + k) % 4294967296 = k - 1 := by
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem fmtZoned_vc : MethodVC Gen.prog fmtZonedC.env 0 fmtZonedRef fmtZonedSpec [] 60 := by
  jverify [fmtZonedSpec, fmtZonedC, fmtUSig, fmtUSpec, Grows, zonedJ, cmp_zero_nonneg_iff,
    charAtIdx_zpadJ_pred, charAtIdx_lit_pos, charAtIdx_lit_neg, evalDynamic, concatRecipe,
    Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, strOf, recipe2,
    valueOfArg_char, zpadJ_length, take_zpadJ_pred, mod32_pred, zpadJ_getElem?_pred, digitJ_toNat,
    lit_pos_getElem, lit_neg_getElem, mod32_sub48, lit_length_pos, lit_length_neg, lit_pos_get,
    lit_neg_get]
  all_goals (first | exact targets_static rfl rfl | skip)

end EquivLean.Modernize.Cbact04c.Java
