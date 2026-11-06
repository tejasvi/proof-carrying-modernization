import EquivLean.Modernize.Cbtrn03c.JavaW.EditDefs
import EquivLean.Modernize.Cbtrn03c.JavaW.Spaces

/-!
# CBTRN03C → Java: the helper `edit`

`edit(v, plus)`: the numeric-edited amount `[+|-]ZZZ,ZZZ,ZZZ.ZZ` of `|v| % 10 ^ 11` (15 spaces
for 0), against the contracts of `spaces` and `digits`.  The loop runs 9 times; symbolic
execution unrolls it (no invariant).
-/

open Jimple


namespace EquivLean.Modernize.Cbtrn03c.Java


/-! The value `m = |v| % 10 ^ 11` of `edit`, for `v ≥ 0` and for `v < 0`. -/

theorem srem11_pos (v : I64) (h1 : 0 ≤ v.toInt) :
    (BitVec.srem v 100000000000#64).toInt.natAbs = v.toInt.natAbs % 100000000000 := by
  have h11 : 0 ≤ (100000000000#64 : BitVec 64).toInt := by decide
  have hn := srem_toNat_of_nonneg v _ h1 h11
  have hq := srem_nonneg v _ h1 h11
  have := toNat_of_toInt_nonneg _ hq
  rw [pos_toNat v h1] at hn
  have h2 : (100000000000#64 : BitVec 64).toNat = 100000000000 := by decide
  rw [h2] at hn
  omega

theorem srem11_neg (v : I64) (h1 : v.toInt < 0) (h2 : -9223372036854775808 < v.toInt) :
    (BitVec.srem (-v) 100000000000#64).toInt.natAbs = v.toInt.natAbs % 100000000000 := by
  obtain ⟨hn0, hnn⟩ := neg_toNat v h2 h1
  have h11 : 0 ≤ (100000000000#64 : BitVec 64).toInt := by decide
  have hn := srem_toNat_of_nonneg (-v) _ hnn h11
  have hq := srem_nonneg (-v) _ hnn h11
  have := toNat_of_toInt_nonneg _ hq
  rw [hn0] at hn
  have h3 : (100000000000#64 : BitVec 64).toNat = 100000000000 := by decide
  rw [h3] at hn
  omega

theorem srem11_eq_zero_pos (v : I64) (h1 : 0 ≤ v.toInt) :
    (BitVec.srem v 100000000000#64 = 0#64) = (v.toInt.natAbs % 100000000000 = 0) := by
  have h11 : 0 ≤ (100000000000#64 : BitVec 64).toInt := by decide
  have hn := srem_toNat_of_nonneg v _ h1 h11
  rw [pos_toNat v h1] at hn
  have h2 : (100000000000#64 : BitVec 64).toNat = 100000000000 := by decide
  rw [h2] at hn
  apply propext
  rw [BitVec.toNat_eq, hn]
  simp

theorem srem11_eq_zero_neg (v : I64) (h1 : v.toInt < 0) (h2 : -9223372036854775808 < v.toInt) :
    (BitVec.srem (-v) 100000000000#64 = 0#64) = (v.toInt.natAbs % 100000000000 = 0) := by
  obtain ⟨hn0, hnn⟩ := neg_toNat v h2 h1
  have h11 : 0 ≤ (100000000000#64 : BitVec 64).toInt := by decide
  have hn := srem_toNat_of_nonneg (-v) _ hnn h11
  rw [hn0] at hn
  have h3 : (100000000000#64 : BitVec 64).toNat = 100000000000 := by decide
  rw [h3] at hn
  apply propext
  rw [BitVec.toNat_eq, hn]
  simp

/-! The loop's tests, as conditions on `int` values and characters. -/

theorem i32_eq_3 (i : I32) : (i = 3#32) = (i.toInt = 3) := by
  apply propext; constructor
  · intro h; subst h; decide
  · intro h; apply BitVec.eq_of_toInt_eq; rw [h]; decide

theorem i32_eq_6 (i : I32) : (i = 6#32) = (i.toInt = 6) := by
  apply propext; constructor
  · intro h; subst h; decide
  · intro h; apply BitVec.eq_of_toInt_eq; rw [h]; decide

theorem char_eq_48 (c : JChar) : (c.setWidth 32 = 48#32) = (c = BitVec.ofNat 16 48) := by
  apply propext
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := c.isLt; omega)] at h1
    exact BitVec.eq_of_toNat_eq (by rw [h1]; rfl)
  · rintro rfl; rfl

theorem i32_toNat_of_nonneg (i : I32) (h0 : 0 ≤ i.toInt) : i.toNat = i.toInt.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at h0 <;> omega

/-- The digits `edit` reads: the 11 digits of `|v| % 10 ^ 11`. -/
def edDigits (v : I64) : JStr := zpadJ (v.toInt.natAbs % 100000000000) 11

theorem edDigits_fold (v : I64) : zpadJ (v.toInt.natAbs % 100000000000) 11 = edDigits v := rfl

theorem edDigits_length (v : I64) : (edDigits v).length = 11 := zpadJ_length _ _

theorem edDigits_neg (v : I64) : edDigits (-v) = edDigits v := by
  unfold edDigits
  by_cases h : v = BitVec.intMin 64
  · subst h; rw [BitVec.neg_intMin]
  · rw [BitVec.toInt_neg_of_ne_intMin h, Int.natAbs_neg]

theorem editJ_zero {neg plus : Bool} {m : Nat} (h : m = 0) : editJ neg plus m = spJ 15 := by
  simp [editJ, h]

theorem editJ_pos (neg plus : Bool) (v : I64) (h : ¬ v.toInt.natAbs % 100000000000 = 0) :
    editJ neg plus (v.toInt.natAbs % 100000000000) =
      signJ neg plus :: (edS (edDigits v) 9 ++
        [BitVec.ofNat 16 46, (edDigits v).getD 9 0, (edDigits v).getD 10 0]) := by
  simp [editJ, h, edDigits]

/-- One step of the loop, at the index `x.toNat` of an `int` (not at a literal). -/
theorem edS_stepN (D : JStr) (x : Int) :
    edS D (x.toNat + 1) = edS D x.toNat ++
      (if x.toNat = 3 ∨ x.toNat = 6 then [if edB D x.toNat then comma else space] else []) ++
      [if edB D (x.toNat + 1) then D.getD x.toNat 0 else space] := rfl

theorem edB_stepN (D : JStr) (x : Int) :
    edB D (x.toNat + 1) = (edB D x.toNat || D.getD x.toNat 0 != digitJ 0) := rfl

/-- The steps at the separators (the index is a literal there). -/
theorem edS_four (D : JStr) : edS D 4 = edS D 3 ++ [if edB D 3 then comma else space] ++
    [if edB D 4 then D.getD 3 0 else space] := rfl

theorem edS_seven (D : JStr) : edS D 7 = edS D 6 ++ [if edB D 6 then comma else space] ++
    [if edB D 7 then D.getD 6 0 else space] := rfl

theorem edB_four (D : JStr) : edB D 4 = (edB D 3 || D.getD 3 0 != digitJ 0) := rfl

theorem edB_seven (D : JStr) : edB D 7 = (edB D 6 || D.getD 6 0 != digitJ 0) := rfl

theorem edS_zero (D : JStr) : edS D 0 = [] := rfl
theorem edB_zero (D : JStr) : edB D 0 = false := rfl

abbrev editRef : MethodRef := Gen.Cbtrn03c.«edit(long,boolean)».ref

def editCallees : Contracts := [(spacesSig, spacesSpec), (digitsSig, digitsSpec)]

def editSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (z : I32), args = [.long v, .int z] ∧
     -9223372036854775808 < v.toInt ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (z : I32), args = [.long v, .int z] →
     ∃ x, r = some (.ref x) ∧
       σ'.heap x = some (.str (editJ (decide (v.toInt < 0)) (z != 0#32)
         (v.toInt.natAbs % 100000000000))) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

/-- At the loop head (statement 29): the sign and `i` steps of the loop in the builder; both
flags (locals 8, 9) say whether a nonzero digit has been seen. -/
def editInv : Invariants := [(29, fun args σ0 fr σ => ∀ (v : I64) (z : I32), args = [.long v, .int z] →
  ∃ i sb ds, fr.get 0 = some (.long v) ∧ fr.get 4 = some (.int i) ∧ fr.get 6 = some (.ref sb) ∧
    fr.get 7 = some (.ref ds) ∧ σ.heap ds = some (.str (edDigits v)) ∧
    fr.get 8 = some (.int (JInt.ofBool (edB (edDigits v) i.toInt.toNat))) ∧
    fr.get 9 = some (.int (JInt.ofBool (edB (edDigits v) i.toInt.toNat))) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder"
      (signJ (decide (v.toInt < 0)) (z != 0#32) :: edS (edDigits v) i.toInt.toNat)) ∧
    ¬ v.toInt.natAbs % 100000000000 = 0 ∧ -9223372036854775808 < v.toInt ∧
    0 ≤ i.toInt ∧ i.toInt ≤ 9 ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn03c" = σ0.initOf "Cbtrn03c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem edit_vc : MethodVC Gen.prog editCallees.env 0 editRef editSpec editInv 80 := by
  jverify [editSpec, editInv, editCallees, spacesSig, spacesSpec, digitsSig, digitsSpec, Grows,
    signJ, edDigits_fold, edDigits_length, edDigits_neg, editJ_zero, editJ_pos, edS_stepN, edB_stepN,
    edS_four, edS_seven, edB_four, edB_seven, edS_zero, edB_zero, comma, space,
    spJ, valueOfArg_char, srem11_pos, srem11_neg, srem11_eq_zero_pos, srem11_eq_zero_neg, i32_eq_3,
    i32_eq_6, char_eq_48, i32_toNat_of_nonneg, Native.valueOfArg, Native.valueOfObj,
    valueOfObjN_ref, JType.isRef]
  -- the remaining paths read a digit past the end of the 11 digits: infeasible
  all_goals (simp only [List.getElem?_eq_none_iff, edDigits_length] at hd; omega)

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.spaces_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.edit_vc
