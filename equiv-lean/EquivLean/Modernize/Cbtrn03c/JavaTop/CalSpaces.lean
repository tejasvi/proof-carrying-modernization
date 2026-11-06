import EquivLean.Modernize.Cbtrn03c.JavaTop.Callees

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contracts of `repeat` and `spaces`

`repeat(c, n)`: `n` copies of `c` (one loop invariant, statement 5); `spaces(n)`: `repeat(' ', n)`,
against the contract of `repeat`.  Ported from cir-repin's `T3/Str.lean`, `T3/Pad.lean`, with a new
string (`σ.next ≤ x`) and `Agree` as the frame.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

def space : JChar := BitVec.ofNat 16 32

/-- `n` copies of the character `c` (`repeat`). -/
def repJ (c : JChar) (n : Nat) : JStr := List.replicate n c

theorem repJ_succ (c : JChar) (n : Nat) : repJ c (n + 1) = repJ c n ++ [c] := by
  simp [repJ, List.replicate_succ']

theorem repJ_length (c : JChar) (n : Nat) : (repJ c n).length = n := by simp [repJ]

/-- `StringBuilder.append(char)`: the character as a one-unit string. -/
theorem valueOfArg_char (P : Program) (c : I32) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfArg P (.prim .char) (.int c) σ k = k [c.setWidth 16] σ := rfl

/-! ### `repeat` -/

abbrev repeatRef : MethodRef := Gen.Cbtrn03c.«repeat(char,int)».ref

def repeatSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "repeat", [.prim .char, .prim .int]⟩

def repeatSpec : Spec := Spec.of
  (fun args _ => ∃ c n : I32, args = [.int c, .int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ c n : I32, args = [.int c, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (repJ (c.setWidth 16) n.toInt.toNat)) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 5): the builder holds `i` copies.  Locals: `i1` 0, `i2` 1,
`c0` 2, `$r0` 3. -/
def repeatInv : Invariants := [(5, fun args σ0 fr σ => ∀ c n : I32, args = [.int c, .int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.int c) ∧
    fr.get 3 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (repJ (c.setWidth 16) i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ σ0.next ≤ σ.next ∧ Agree σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem repeat_vc : MethodVC Gen.prog (fun _ => none) 0 repeatRef repeatSpec repeatInv 60 := by
  jverify [repeatSpec, repeatInv, Agree, repJ_succ, valueOfArg_char]

theorem repeat_sat : Sat Gen.prog repeatRef repeatSpec := repeat_vc.sat

set_option maxHeartbeats 0 in
theorem repeat_ok : ContractOK Gen.prog repeatSig repeatSpec := by
  jcontract_ok [repeat_sat]

/-! ### `spaces` -/

abbrev spacesRef : MethodRef := Gen.Cbtrn03c.«spaces(int)».ref

def spacesCallees : Contracts := [(repeatSig, repeatSpec)]

theorem setWidth_32 : BitVec.setWidth 16 (32#32) = space := by decide

set_option maxRecDepth 100000 in
theorem cp037Unit_64 : cp037Unit 64 = space := by decide +kernel

/-- `n` EBCDIC spaces as a Java string. -/
theorem cp037Str_sp (k : Nat) : cp037Str (Model.sp k) = repJ space k := by
  simp only [cp037Str, Model.sp, repJ, List.map_replicate, cp037Unit_64]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog spacesCallees.env 0 spacesRef spacesSpecT [] 20 := by
  jverify [spacesSpecT, spacesCallees, repeatSig, repeatSpec, Agree, cp037Str_sp, setWidth_32]

theorem spaces_sat : Sat Gen.prog spacesRef spacesSpecT :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [spacesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact repeat_ok)) spaces_vc

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem spaces_ok : ContractOK Gen.prog spacesSig spacesSpecT := by
  jcontract_ok [Cal.spaces_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.repeat_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.spaces_ok
