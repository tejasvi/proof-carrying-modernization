import EquivLean.Modernize.Cbtrn03c.JavaTop.CalFind

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `ebcdic` and `compareEbcdic`

`ebcdic(c)`: the index of `c` in the string constant CP037 (0x6F if absent); one loop
invariant (statement 2).  `compareEbcdic(a, b)` for strings of equal length: the sign of the
first difference of their EBCDIC codes, against the contract of `ebcdic`; one loop invariant
(statement 9), the loops for unequal lengths are not reached.  Ported from cir-repin's
`T3/Ebc.lean` (`Agree` as the frame).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-- Java's `CP037` constant: the character of each EBCDIC byte.  Irreducible, so that symbolic
execution keeps it folded (evaluating the 256 units makes the kernel check recurse too deeply). -/
@[irreducible] def cpJ : JStr := JStr.ofString "\x00\x01\x02\x03\x9c\x09\x86\x7f\x97\x8d\x8e\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x9d\x85\x08\x87\x18\x19\x92\x8f\x1c\x1d\x1e\x1f\x80\x81\x82\x83\x84\x0a\x17\x1b\x88\x89\x8a\x8b\x8c\x05\x06\x07\x90\x91\x16\x93\x94\x95\x96\x04\x98\x99\x9a\x9b\x14\x15\x9e\x1a\x20\xa0\xe2\xe4\xe0\xe1\xe3\xe5\xe7\xf1\xa2\x2e\x3c\x28\x2b\x7c\x26\xe9\xea\xeb\xe8\xed\xee\xef\xec\xdf\x21\x24\x2a\x29\x3b\xac\x2d\x2f\xc2\xc4\xc0\xc1\xc3\xc5\xc7\xd1\xa6\x2c\x25\x5f\x3e\x3f\xf8\xc9\xca\xcb\xc8\xcd\xce\xcf\xcc\x60\x3a\x23\x40\x27\x3d\x22\xd8abcdefghi\xab\xbb\xf0\xfd\xfe\xb1\xb0jklmnopqr\xaa\xba\xe6\xb8\xc6\xa4\xb5\x7estuvwxyz\xa1\xbf\xd0\xdd\xde\xae\x5e\xa3\xa5\xb7\xa9\xa7\xb6\xbc\xbd\xbe\x5b\x5d\xaf\xa8\xb4\xd7\x7bABCDEFGHI\xad\xf4\xf6\xf2\xf3\xf5\x7dJKLMNOPQR\xb9\xfb\xfc\xf9\xfa\xff\x5c\xf7STUVWXYZ\xb2\xd4\xd6\xd2\xd3\xd50123456789\xb3\xdb\xdc\xd9\xda\x9f"

/-- The constant as the program holds it, folded before simplification looks inside it. -/
@[jsimp ↓] theorem cpJ_fold : JStr.ofString "\x00\x01\x02\x03\x9c\x09\x86\x7f\x97\x8d\x8e\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x9d\x85\x08\x87\x18\x19\x92\x8f\x1c\x1d\x1e\x1f\x80\x81\x82\x83\x84\x0a\x17\x1b\x88\x89\x8a\x8b\x8c\x05\x06\x07\x90\x91\x16\x93\x94\x95\x96\x04\x98\x99\x9a\x9b\x14\x15\x9e\x1a\x20\xa0\xe2\xe4\xe0\xe1\xe3\xe5\xe7\xf1\xa2\x2e\x3c\x28\x2b\x7c\x26\xe9\xea\xeb\xe8\xed\xee\xef\xec\xdf\x21\x24\x2a\x29\x3b\xac\x2d\x2f\xc2\xc4\xc0\xc1\xc3\xc5\xc7\xd1\xa6\x2c\x25\x5f\x3e\x3f\xf8\xc9\xca\xcb\xc8\xcd\xce\xcf\xcc\x60\x3a\x23\x40\x27\x3d\x22\xd8abcdefghi\xab\xbb\xf0\xfd\xfe\xb1\xb0jklmnopqr\xaa\xba\xe6\xb8\xc6\xa4\xb5\x7estuvwxyz\xa1\xbf\xd0\xdd\xde\xae\x5e\xa3\xa5\xb7\xa9\xa7\xb6\xbc\xbd\xbe\x5b\x5d\xaf\xa8\xb4\xd7\x7bABCDEFGHI\xad\xf4\xf6\xf2\xf3\xf5\x7dJKLMNOPQR\xb9\xfb\xfc\xf9\xfa\xff\x5c\xf7STUVWXYZ\xb2\xd4\xd6\xd2\xd3\xd50123456789\xb3\xdb\xdc\xd9\xda\x9f" = cpJ := by unfold cpJ; rfl

set_option maxRecDepth 100000 in
theorem cpJ_length : cpJ.length = 256 := by unfold cpJ; decide +kernel

/-- `ebcdic` from index `i` on: the first index at or after `i` holding `u`, else 111. -/
def ebcFrom (u : JChar) (i : Nat) : Int :=
  match (cpJ.drop i).findIdx? (· == u) with
  | some j => i + j
  | none => 111

theorem ebcFrom_ne {u : JChar} {i : Nat} (h : i < 256) (hne : ¬ cpJ.getD i 0 = u) :
    ebcFrom u i = ebcFrom u (i + 1) := by
  have hi : i < cpJ.length := by rw [cpJ_length]; exact h
  unfold ebcFrom
  rw [List.drop_eq_getElem_cons hi, List.findIdx?_cons]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hne
  simp only [beq_iff_eq, hne, ite_false]
  cases hf : (cpJ.drop (i + 1)).findIdx? (· == u) with
  | none => simp
  | some j => simp; omega

theorem ebcFrom_eq {u : JChar} {i : Nat} (h : i < 256) (he : cpJ.getD i 0 = u) :
    ebcFrom u i = i := by
  have hi : i < cpJ.length := by rw [cpJ_length]; exact h
  unfold ebcFrom
  rw [List.drop_eq_getElem_cons hi, List.findIdx?_cons]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at he
  simp [he]

theorem ebcFrom_ge {u : JChar} {i : Nat} (h : 256 ≤ i) : ebcFrom u i = 111 := by
  unfold ebcFrom
  rw [List.drop_of_length_le (by rw [cpJ_length]; exact h)]
  rfl

theorem setWidth32_inj (a b : JChar) : (a.setWidth 32 = b.setWidth 32) = (a = b) := by
  apply propext
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
    exact this
  · rintro rfl; rfl

theorem setWidth_16_32 (u : JChar) : (u.setWidth 32).setWidth 16 = u := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := u.isLt
  omega

abbrev ebcdicRef : MethodRef := Gen.Cbtrn03c.«ebcdic(char)».ref

def ebcdicSig : MethodSig := ⟨"Cbtrn03c", .prim .int, "ebcdic", [.prim .char]⟩

def ebcdicSpec : Spec := Spec.of
  (fun args _ => ∃ u : JChar, args = [.int (u.setWidth 32)])
  (fun args σ r σ' => ∀ c : I32, args = [.int c] →
     r = some (.int (BitVec.ofInt 32 (ebcFrom (c.setWidth 16) 0))) ∧ σ.next ≤ σ'.next ∧
     Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 2): the search continues at `i`.  Locals: `i2` 0, `c0` 3. -/
def ebcdicInv : Invariants := [(2, fun args σ0 fr σ => ∀ u : JChar, args = [.int (u.setWidth 32)] →
  ∃ i, fr.get 0 = some (.int i) ∧ fr.get 3 = some (.int (u.setWidth 32)) ∧ 0 ≤ i.toInt ∧
    i.toInt ≤ 256 ∧ ebcFrom u 0 = ebcFrom u i.toInt.toNat ∧ σ0.next ≤ σ.next ∧ Agree σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem ebcdic_vc : MethodVC Gen.prog (fun _ => none) 0 ebcdicRef ebcdicSpec ebcdicInv 40 := by
  jverify [ebcdicSpec, ebcdicInv, Agree, cpJ_length, setWidth32_inj, setWidth_16_32, ebcFrom_ne,
    ebcFrom_eq, ebcFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt', List.getD_eq_getElem?_getD]
  all_goals first
    | (simp only [List.getElem?_eq_none_iff, cpJ_length] at hd; omega)
    | ((rw [ebcFrom_ne] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD]; done));
       done)
    | ((rw [ebcFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD]; done));
       done)
    | (intro h; subst h; jomega)
    | skip

theorem ebcdic_sat : Sat Gen.prog ebcdicRef ebcdicSpec := ebcdic_vc.sat

set_option maxHeartbeats 0 in
theorem ebcdic_ok : ContractOK Gen.prog ebcdicSig ebcdicSpec := by
  jcontract_ok [ebcdic_sat]

/-! ### `compareEbcdic` -/

/-- The value `ebcdic` returns for `u`. -/
def ebcV (u : JChar) : I32 := BitVec.ofInt 32 (ebcFrom u 0)

/-- `compareEbcdic` from index `i` on, for strings of equal length: the loop's tests. -/
def cmpFrom (a b : JStr) (i : Nat) : I32 :=
  if i < a.length then
    (if ebcV (a.getD i 0) = ebcV (b.getD i 0) then cmpFrom a b (i + 1)
     else if (ebcV (b.getD i 0)).toInt ≤ (ebcV (a.getD i 0)).toInt then 1 else -1)
  else 0
termination_by a.length - i
decreasing_by omega

theorem cmpFrom_eq {a b : JStr} {i : Nat} (h : i < a.length)
    (he : ebcV (a.getD i 0) = ebcV (b.getD i 0)) : cmpFrom a b i = cmpFrom a b (i + 1) := by
  rw [cmpFrom, if_pos h, if_pos he]

theorem cmpFrom_gt {a b : JStr} {i : Nat} (h : i < a.length)
    (hne : ¬ ebcV (a.getD i 0) = ebcV (b.getD i 0))
    (hge : (ebcV (b.getD i 0)).toInt ≤ (ebcV (a.getD i 0)).toInt) : cmpFrom a b i = 1 := by
  rw [cmpFrom, if_pos h, if_neg hne, if_pos hge]

theorem cmpFrom_lt {a b : JStr} {i : Nat} (h : i < a.length)
    (hne : ¬ ebcV (a.getD i 0) = ebcV (b.getD i 0))
    (hlt : ¬ (ebcV (b.getD i 0)).toInt ≤ (ebcV (a.getD i 0)).toInt) : cmpFrom a b i = -1 := by
  rw [cmpFrom, if_pos h, if_neg hne, if_neg hlt]

theorem cmpFrom_ge {a b : JStr} {i : Nat} (h : a.length ≤ i) : cmpFrom a b i = 0 := by
  rw [cmpFrom, if_neg (by omega)]

abbrev compareEbcdicRef : MethodRef :=
  Gen.Cbtrn03c.«compareEbcdic(java.lang.String,java.lang.String)».ref

def compareCallees : Contracts := [(ebcdicSig, ebcdicSpec)]

/-- `compareEbcdic` (cir-repin's `compareEbcdicSpec`, `Agree` as the frame). -/
def compareEbcdicSpec : Spec := Spec.of
  (fun args σ => ∃ (xa xb : Addr) (sa sb : JStr), args = [.ref xa, .ref xb] ∧
     σ.heap xa = some (.str sa) ∧ σ.heap xb = some (.str sb) ∧ sa.length = sb.length ∧
     sa.length < 2147483648 ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (xa xb : Addr), args = [.ref xa, .ref xb] →
     r = some (.int (cmpFrom (argText σ (.ref xa)) (argText σ (.ref xb)) 0)) ∧
     σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 9): the comparison continues at `i`.  Locals: `$i0` 2, `i12` 4,
`r0` 6, `r1` 7. -/
def compareEbcdicInv : Invariants := [(9, fun args σ0 fr σ => ∀ (xa xb : Addr) (sa sb : JStr),
  args = [.ref xa, .ref xb] → σ0.heap xa = some (.str sa) → σ0.heap xb = some (.str sb) →
  ∃ i, fr.get 4 = some (.int i) ∧ fr.get 2 = some (.int (BitVec.ofInt 32 (sa.length : Int))) ∧
    fr.get 6 = some (.ref xa) ∧ fr.get 7 = some (.ref xb) ∧ σ.heap xa = some (.str sa) ∧
    σ.heap xb = some (.str sb) ∧ xa < σ.next ∧ xb < σ.next ∧ 0 ≤ i.toInt ∧
    i.toInt ≤ sa.length ∧ sa.length = sb.length ∧ sa.length < 2147483648 ∧
    cmpFrom sa sb 0 = cmpFrom sa sb i.toInt.toNat ∧ σ0.next ≤ σ.next ∧ Agree σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn03c" = σ0.initOf "Cbtrn03c" ∧
    σ0.initOf "Cbtrn03c" = .done)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem compareEbcdic_vc :
    MethodVC Gen.prog compareCallees.env 0 compareEbcdicRef compareEbcdicSpec compareEbcdicInv 60 := by
  jverify [compareEbcdicSpec, compareEbcdicInv, compareCallees, ebcdicSig, ebcdicSpec, Agree,
    cmpFrom_eq, cmpFrom_gt, cmpFrom_lt, cmpFrom_ge, List.getD_eq_getElem?_getD, argText, strOf,
    setWidth_16_32]
  all_goals first
    | ((rw [cmpFrom_eq] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD, ebcV]; done));
       done)
    | ((rw [cmpFrom_gt] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD, ebcV]; done));
       done)
    | ((rw [cmpFrom_lt] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD, ebcV]; done));
       done)
    | (intro h; subst h; jomega)
    | skip

theorem compareEbcdic_sat : Sat Gen.prog compareEbcdicRef compareEbcdicSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [compareCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ebcdic_ok)) compareEbcdic_vc

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.cpJ_length
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.ebcdic_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.compareEbcdic_sat
