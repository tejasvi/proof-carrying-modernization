import EquivLean.Modernize.Cbstm03a.Java.Iface1

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 20000 in
theorem cp037Table_length : cp037Table.length = 256 := by decide

set_option maxRecDepth 20000 in
theorem num_cp037Arr_length : cp037Arr.length = 256 := by simp [cp037Arr, cp037Table_length]

set_option maxRecDepth 20000 in
theorem cp037_all_lt : ∀ x ∈ cp037Table, x < 256 := by decide

theorem cp037_lt (i : Nat) : cp037Table.getD i 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : cp037Table[i]? with
  | none => simp
  | some x => exact cp037_all_lt x (List.mem_of_getElem? h)

theorem cp037Arr_getElem? (i : Nat) (h : i < 256) :
    cp037Arr[i]? = some (.int (BitVec.ofNat 32 (cp037Table.getD i 0))) := by
  rw [cp037Arr, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < cp037Table.length by rw [cp037Table_length]; exact h)]
  rfl

theorem drop_cp037 (i : Nat) (h : i < 256) :
    cp037Table.drop i = cp037Table.getD i 0 :: cp037Table.drop (i + 1) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < cp037Table.length by rw [cp037Table_length]; exact h)]
  exact List.drop_eq_getElem_cons _

theorem ebc_hit (c i : Nat) (hi : i < 256) (h : cp037Table.getD i 0 = c) :
    ebcGo c (cp037Table.drop i) i = i := by
  rw [drop_cp037 i hi, ebcGo, if_pos h]

theorem ebc_miss (c i : Nat) (hi : i < 256) (h : ¬ cp037Table.getD i 0 = c) :
    ebcGo c (cp037Table.drop i) i = ebcGo c (cp037Table.drop (i + 1)) (i + 1) := by
  rw [drop_cp037 i hi, ebcGo, if_neg h]

set_option maxRecDepth 20000 in
theorem ebc_end (c : Nat) : ebcGo c (cp037Table.drop 256) 256 = 256 + c := by
  rw [List.drop_eq_nil_of_le (by rw [cp037Table_length])]; rfl

theorem ebc_hit' (i : Nat) (hi : i < 256) :
    ebcGo (cp037Table[i]?.getD 0 % 4294967296) (cp037Table.drop i) i = i := by
  have h := cp037_lt i
  rw [List.getD_eq_getElem?_getD] at h
  rw [Nat.mod_eq_of_lt (by omega)]
  exact ebc_hit _ i hi (by rw [List.getD_eq_getElem?_getD])

theorem ebc_miss' (c : BitVec 32) (i : Nat) (hi : i < 256)
    (h : ¬ BitVec.ofNat 32 (cp037Table[i]?.getD 0) = c) :
    ebcGo c.toNat (cp037Table.drop i) i = ebcGo c.toNat (cp037Table.drop (i + 1)) (i + 1) := by
  apply ebc_miss c.toNat i hi
  intro e
  rw [List.getD_eq_getElem?_getD] at e
  exact h (by rw [e]; exact BitVec.ofNat_toNat 32 c |>.trans (BitVec.setWidth_eq c))

theorem ofNat_toInt_toNat (w : BitVec 32) (h : 0 ≤ w.toInt) : BitVec.ofNat 32 w.toInt.toNat = w := by
  apply BitVec.eq_of_toNat_eq
  have := BitVec.toInt_eq_toNat_cond w
  have hl := w.isLt
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  split at this <;> omega

/-- At the loop head (statement 2): no entry before `i` is `c`; the state is unchanged.
Locals: `i` 2, `c` 4. -/
def ebcInv : Invariants := [(2, fun args σ0 fr σ => ∀ c : I32, args = [.int c] →
  ∃ i : I32, fr.get 4 = some (.int c) ∧ fr.get 2 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ 256 ∧
    ebcIdx c.toNat = ebcGo c.toNat (cp037Table.drop i.toInt.toNat) i.toInt.toNat ∧ σ = σ0 ∧ CP037At σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ebc_vc : MethodVC Gen.prog (fun _ => none) 0 ebcRef ebcSpec ebcInv 40 := by
  jverify [ebcSpec, ebcInv, CP037At, num_cp037Arr_length, cp037Arr_getElem?]
  all_goals first
    | rfl
    | (rw [ebc_hit' _ (by omega), ofNat_toInt_toNat _ (by omega)])
    | exact ebc_miss' _ _ (by omega) ‹_›

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.ebc_vc
