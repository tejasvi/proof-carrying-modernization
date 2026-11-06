import EquivLean.Modernize.Cbtrn03c.JavaW.Lib

/-!
# CBTRN03C → Java: the helpers `repeat`, `spaces`, `pad`, `pow10`, `add11`

`repeat(c, n)`: `n` copies of `c`; `spaces(n)`: `repeat(' ', n)`; `pad(s, n)`: the first `n`
characters of `s`, padded with spaces; `pow10(n)`: `10 ^ n` (as a `long`); `add11(a, b)`:
`(a + b) % 10 ^ 11`.  One loop invariant each for the loops.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-! ### `repeat` -/

abbrev repeatRef : MethodRef := Gen.Cbtrn03c.«repeat(char,int)».ref

def repeatSpec : Spec := Spec.of
  (fun args _ => ∃ c n : I32, args = [.int c, .int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ c n : I32, args = [.int c, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (repJ (c.setWidth 16) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

/-- At the loop head (statement 5): the builder holds `i` copies. -/
def repeatInv : Invariants := [(5, fun args σ0 fr σ => ∀ c n : I32, args = [.int c, .int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.int c) ∧
    fr.get 3 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (repJ (c.setWidth 16) i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn03c" = σ0.initOf "Cbtrn03c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem repeat_vc : MethodVC Gen.prog (fun _ => none) 0 repeatRef repeatSpec repeatInv 60 := by
  jverify [repeatSpec, repeatInv, Grows, repJ_succ, valueOfArg_char]

/-! ### `pow10` -/

abbrev pow10Ref : MethodRef := Gen.Cbtrn03c.«pow10(int)».ref

def pow10Spec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     r = some (.long (BitVec.ofNat 64 (10 ^ n.toInt.toNat))) ∧ σ' = σ)

/-- At the loop head (statement 3): the product is `10 ^ i`. -/
def pow10Inv : Invariants := [(3, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧
    fr.get 2 = some (.long (BitVec.ofNat 64 (10 ^ i.toInt.toNat))) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pow10_vc : MethodVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv 40 := by
  jverify [pow10Spec, pow10Inv, pow10_mul]

/-! ### `add11` -/

abbrev add11Ref : MethodRef := Gen.Cbtrn03c.«add11(long,long)».ref

def add11Spec : Spec := Spec.of
  (fun args _ => ∃ a b : I64, args = [.long a, .long b])
  (fun args σ r σ' => ∀ a b : I64, args = [.long a, .long b] →
     r = some (.long ((a + b).srem (BitVec.ofInt 64 100000000000))) ∧ σ' = σ)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem add11_vc : MethodVC Gen.prog (fun _ => none) 0 add11Ref add11Spec [] 20 := by
  jverify [add11Spec]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.repeat_vc
#print axioms EquivLean.Modernize.Cbtrn03c.Java.pow10_vc
#print axioms EquivLean.Modernize.Cbtrn03c.Java.add11_vc
