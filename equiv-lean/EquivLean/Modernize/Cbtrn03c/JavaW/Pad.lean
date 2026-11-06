import EquivLean.Modernize.Cbtrn03c.JavaW.Str

/-!
# CBTRN03C → Java: the helpers `spaces` and `pad`

`spaces(n)`: `repeat(' ', n)`, against the contract of `repeat`.  `pad(s, n)`: the first `n`
characters of `s`, padded with spaces; the loop appends the spaces after `s` (statement 10).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

def repeatSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "repeat", [.prim .char, .prim .int]⟩

theorem repeat_sat : Sat Gen.prog repeatRef repeatSpec := repeat_vc.sat

set_option maxHeartbeats 0 in
theorem repeat_ok : ContractOK Gen.prog repeatSig repeatSpec := by
  jcontract_ok [repeat_sat]

/-! ### `spaces` -/

abbrev spacesRef : MethodRef := Gen.Cbtrn03c.«spaces(int)».ref

def spacesCallees : Contracts := [(repeatSig, repeatSpec)]

def spacesSpec : Spec := Spec.of
  (fun args σ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (spJ n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

theorem setWidth_32 : BitVec.setWidth 16 (32#32) = space := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog spacesCallees.env 0 spacesRef spacesSpec [] 20 := by
  jverify [spacesSpec, spacesCallees, repeatSig, repeatSpec, Grows, spJ, setWidth_32]

/-! ### `pad` -/

/-- `fixJ s n`: the first `n` characters of `s`, padded with spaces, in the loop's order. -/
def fixJ (s : JStr) : Nat → JStr
  | 0 => []
  | i + 1 => fixJ s i ++ [s.getD i space]

theorem fixJ_eq_take : ∀ (s : JStr) (n : Nat), n ≤ s.length → fixJ s n = s.take n
  | _, 0, _ => by simp [fixJ]
  | s, n + 1, h => by
    rw [fixJ, fixJ_eq_take s n (by omega), List.take_add_one]
    simp [List.getD, List.getElem?_eq_getElem (show n < s.length by omega)]

theorem fixJ_length_self (s : JStr) : fixJ s s.length = s := by
  rw [fixJ_eq_take s s.length (Nat.le_refl _), List.take_length]

theorem padJ_of_ge {s : JStr} {n : Nat} (h : s.length ≤ n) : padJ s n = s ++ spJ (n - s.length) := by
  simp [padJ, List.take_of_length_le h]

theorem fixJ_eq_padJ : ∀ (s : JStr) (n : Nat), fixJ s n = padJ s n
  | s, 0 => by simp [fixJ, padJ, spJ, repJ]
  | s, n + 1 => by
    rw [fixJ, fixJ_eq_padJ s n]
    by_cases h : n < s.length
    · rw [padJ_of_le (Nat.le_of_lt h), padJ_of_le h, List.take_add_one]
      simp [List.getD, List.getElem?_eq_getElem h]
    · have h' : s.length ≤ n := Nat.le_of_not_lt h
      rw [padJ_of_ge h', padJ_of_ge (Nat.le_succ_of_le h')]
      simp only [List.getD, List.getElem?_eq_none h', Option.getD_none, List.append_assoc, spJ,
        repJ]
      rw [show n + 1 - s.length = (n - s.length) + 1 by omega, List.replicate_succ']

abbrev padRef : MethodRef := Gen.Cbtrn03c.«pad(java.lang.String,int)».ref

def padSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (s : JStr) (n : I32), args = [.ref x, .int n] ∧
     σ.heap x = some (.str s) ∧ s.length < 2147483648 ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ (x : Addr) (s : JStr) (n : I32), args = [.ref x, .int n] →
     σ.heap x = some (.str s) →
     ∃ y, r = some (.ref y) ∧ σ'.heap y = some (.str (fixJ s n.toInt.toNat)) ∧ σ.next ≤ y ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

/-- At the loop head (statement 10): the builder holds `s` and the spaces up to `i`. -/
def padInv : Invariants := [(10, fun args σ0 fr σ => ∀ (x : Addr) (s : JStr) (n : I32),
  args = [.ref x, .int n] → σ0.heap x = some (.str s) →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixJ s i.toInt.toNat)) ∧
    (s.length : Int) ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn03c" = σ0.initOf "Cbtrn03c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pad_vc : MethodVC Gen.prog (fun _ => none) 0 padRef padSpec padInv 60 := by
  jverify [padSpec, padInv, Grows, fixJ, fixJ_length_self, fixJ_eq_take,
    setWidth_32, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef]
  all_goals first
    | omega
    | (rw [List.getElem?_eq_none] <;> first | rfl | omega)
    | skip

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.repeat_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.spaces_vc
#print axioms EquivLean.Modernize.Cbtrn03c.Java.fixJ_eq_padJ
#print axioms EquivLean.Modernize.Cbtrn03c.Java.pad_vc
