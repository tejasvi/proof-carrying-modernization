import EquivLean.Modernize.Cbtrn03c.JavaTop.CalNum

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contract of `zoned`

`zoned(v, n)`: the leading `n - 1` digits of `|v|`, zero-padded, then the last digit overpunched
with the sign (`{`, `A`…`I` for `+0`…`+9`, `}`, `J`…`R` for `-0`…`-9`), against the contract of
`digits`.  Ported from cir-repin's `T3/Zoned.lean` (`Agree` as the frame); `zoned_ok` (the model's
`zoned`) by the rule of consequence and cir-repin's `zonedJ_eq` (`T3/Lines.lean`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-! ### The last digit and the overpunch -/

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

/-! ### `zoned` -/

/-- What `zoned(v, n)` returns. -/
def zonedJ (v : I64) (n : Nat) : JStr :=
  zpadJ (v.toInt.natAbs / 10) (n - 1) ++ [overJ (decide (v.toInt < 0)) (v.toInt.natAbs % 10)]

/-- `zoned` builds the model's signed DISPLAY field. -/
theorem zonedJ_eq (v : I64) (n : Nat) : zonedJ v n = jline (Model.zoned n v.toInt) := by
  rw [zonedJ, Model.zoned, jline, List.map_append, ← jline, zpadJ_eq]
  rfl

abbrev zonedRef : MethodRef := Gen.Cbtrn03c.«zoned(long,int)».ref

def zonedCallees : Contracts := [(digitsSig, digitsSpec)]

/-- `zoned` (cir-repin's `zonedSpec`, a new string, `Agree` as the frame). -/
def zonedSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 1 ≤ n.toInt ∧ n.toInt ≤ 18 ∧
     σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zonedJ v n.toInt.toNat)) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zoned_vc : MethodVC Gen.prog zonedCallees.env 0 zonedRef zonedSpec [] 60 := by
  jverify [zonedSpec, zonedCallees, digitsSig, digitsSpec, Agree, zonedJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, ofNat32_digit_eq_zero, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, Native.valueOfArg, Native.primStr, JType.isRef,
    over_pos_char, over_neg_char]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | (intro h; subst h; jomega)
    | skip

theorem zoned_sat : Sat Gen.prog zonedRef zonedSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [zonedCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact digitsC_ok)) zoned_vc

set_option maxHeartbeats 0 in
theorem zonedC_ok : ContractOK Gen.prog zonedSig zonedSpec := by
  jcontract_ok [zoned_sat]

/-- `zoned` on the model's `zoned`. -/
theorem zonedT_sat : Sat Gen.prog zonedRef zonedSpecT := by
  intro args σ o hp hx
  have ho := zoned_sat args σ o hp hx
  cases o with
  | normal r σ' =>
    intro v n heq
    obtain ⟨x, hr, hxs, -, h2, h3, h4, h5⟩ := ho v n heq
    refine ⟨x, hr, ?_, h2, h3, h4, h5⟩
    rw [hxs, zonedJ_eq]
  | exc e σ' => exact ho
  | wrong m => exact ho

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem zoned_ok : ContractOK Gen.prog zonedSig zonedSpecT := by
  jcontract_ok [Cal.zonedT_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.zonedC_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.zoned_ok
