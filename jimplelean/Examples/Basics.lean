/-
  Examples/Basics.lean

  Arithmetic routines of `examples_java/basics/src/Basics.java`, verified on the Jimple
  that Soot 4.7.1 produced from `javac --release 8` bytecode (`examples_java/basics/jimple`).
  Every proof is `jverify` with the loop invariant (if any) as the only manual input.
-/
import Jimple

open Jimple

jimple_import "examples_java/basics/jimple" as B

namespace Examples.Basics

/-- The method of class `cls` named `name`. -/
def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

/-! ### `max(int, int)` -/

def maxSpec : Spec := Spec.of
  (fun args _ => ∃ a b : I32, args = [.int a, .int b])
  (fun args _ r _ => ∀ a b : I32, args = [.int a, .int b] →
     ∃ x : I32, r = some (.int x) ∧ x.toInt = max a.toInt b.toInt)

theorem max_ok : MethodVC B.prog (fun _ => none) 0 (mref B.prog "Basics" "max") maxSpec [] 20 := by
  jverify

/-- What `max_ok` means: every terminating execution of `max` on two `int`s returns their
    maximum (`Sat` is partial correctness over the big-step semantics `MExec`). -/
theorem max_sat : Sat B.prog (mref B.prog "Basics" "max") maxSpec := max_ok.sat

/-! ### `clamp(int, int, int)` -/

def clampSpec : Spec := Spec.of
  (fun args _ => ∃ x lo hi : I32, args = [.int x, .int lo, .int hi] ∧ lo.toInt ≤ hi.toInt)
  (fun args _ r _ => ∀ x lo hi : I32, args = [.int x, .int lo, .int hi] →
     ∃ y : I32, r = some (.int y) ∧ lo.toInt ≤ y.toInt ∧ y.toInt ≤ hi.toInt ∧
       (lo.toInt ≤ x.toInt → x.toInt ≤ hi.toInt → y = x))

theorem clamp_ok : MethodVC B.prog (fun _ => none) 0 (mref B.prog "Basics" "clamp") clampSpec [] 20 := by
  jverify

/-! ### `sumTo(int)`: a loop; 32-bit overflow is excluded by the proof itself -/

def sumToSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1000)
  (fun args _ r _ => ∀ n : I32, args = [.int n] →
     ∃ x : I32, r = some (.int x) ∧ 2 * x.toInt = n.toInt * (n.toInt + 1))

/-- Loop head (statement 3, `if i > n goto exit`): `2 s = (i - 1) i`. Locals: `i0 = n`,
    `i1 = s`, `i2 = i`. -/
def sumToInv : Invariants := [(3, fun args _ fr _ => ∀ n : I32, args = [.int n] →
  ∃ s i : I32, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int s) ∧ fr.get 2 = some (.int i) ∧
    1 ≤ i.toInt ∧ i.toInt ≤ n.toInt + 1 ∧ 2 * s.toInt = (i.toInt - 1) * i.toInt ∧ n.toInt ≤ 1000)]

theorem sumTo_ok :
    MethodVC B.prog (fun _ => none) 0 (mref B.prog "Basics" "sumTo") sumToSpec sumToInv 20 := by
  jverify

/-! ### `countPositive(int[])`: a loop over an array -/

/-- Number of positive `int` values in a list. -/
def countPos (xs : List Value) : Nat :=
  (xs.filter fun v => match v with | .int x => decide (0 < x.toInt) | _ => false).length

def countPositiveSpec : Spec := Spec.of
  (fun args σ => ∃ a xs, args = [.ref a] ∧ σ.heap a = some (.array (.prim .int) xs) ∧
     xs.length < 2147483647 ∧ ∀ v ∈ xs, ∃ x : I32, v = .int x)
  (fun args σ r _ => ∀ a xs, args = [.ref a] → σ.heap a = some (.array (.prim .int) xs) →
     ∃ c : I32, r = some (.int c) ∧ c.toInt = countPos xs)

/-- Loop head (statement 3, before `lengthof`): the count of the first `i` elements.
    Locals: `r0 = xs`, `i2 = count`, `i3 = i`. -/
def countPositiveInv : Invariants := [(3, fun args σ0 fr σ => ∀ a xs, args = [.ref a] →
  σ0.heap a = some (.array (.prim .int) xs) →
  ∃ c i : I32, fr.get 0 = some (.ref a) ∧ fr.get 2 = some (.int c) ∧ fr.get 3 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ c.toInt = countPos (xs.take i.toNat) ∧ σ = σ0)]

theorem countPositive_ok :
    MethodVC B.prog (fun _ => none) 0 (mref B.prog "Basics" "countPositive")
      countPositiveSpec countPositiveInv 30 := by
  jverify [countPos]

end Examples.Basics

#print axioms Examples.Basics.max_ok
#print axioms Examples.Basics.max_sat
#print axioms Examples.Basics.clamp_ok
#print axioms Examples.Basics.sumTo_ok
#print axioms Examples.Basics.countPositive_ok
