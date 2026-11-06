/-
  Examples/Termination.lean

  Total correctness: `sumTo(int)` of `examples_java/basics` terminates (`Jimple/Termination.lean`).
  The termination VC needs only the loop's bounds and a variant; `jterm` proves it like `jverify`.
-/
import Jimple

open Jimple

jimple_import "examples_java/basics/jimple" as BT

namespace Examples.Termination

def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

/-- The precondition of `Examples.Basics.sumToSpec`; termination needs no postcondition. -/
def sumToPre : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1000)
  (fun _ _ _ _ => True)

/-- Loop head (statement 3, `if i > n goto exit`): `1 ≤ i ≤ n + 1`; variant `n + 1 - i`. Locals:
    `i0 = n`, `i2 = i`. -/
def sumToTerm : TermCuts := [(3,
  (fun args _ fr _ => ∀ n : I32, args = [.int n] →
    ∃ i : I32, fr.get 0 = some (.int n) ∧ fr.get 2 = some (.int i) ∧
      1 ≤ i.toInt ∧ i.toInt ≤ n.toInt + 1 ∧ n.toInt ≤ 1000),
  (fun _ _ fr _ => match fr.get 0, fr.get 2 with
    | some (.int n), some (.int i) => (n.toInt + 1 - i.toInt).toNat
    | _, _ => 0))]

theorem sumTo_term :
    TermVC BT.prog (fun _ => none) (fun _ => 0) 0 0 (mref BT.prog "Basics" "sumTo") sumToPre sumToTerm 20 := by
  jterm

/-- **`sumTo` terminates** on every argument of its precondition (no callees: the empty contract
    environment holds trivially). -/
theorem sumTo_terminates :
    ∀ args σ, sumToPre.pre args σ → MTerm BT.prog (mref BT.prog "Basics" "sumTo") args σ :=
  TermVC.mterm (Γ := fun _ => none) (rank := fun _ => 0) (r := 0)
    (fun _ _ h => by simp at h) (fun _ _ h => by simp [SpecEnv.below] at h) sumTo_term

end Examples.Termination

#print axioms Examples.Termination.sumTo_term
#print axioms Examples.Termination.sumTo_terminates
