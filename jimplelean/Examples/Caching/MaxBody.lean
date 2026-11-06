/-
  Examples/Caching/MaxBody.lean

  Per-method proofs independent of the rest of the program. This module imports only the
  class `Basics` (one `jimple_import` of one `.jimple` file), and the theorem holds for every
  program that contains this method: changing or adding other classes does not touch it.
-/
import Jimple

open Jimple

jimple_import "examples_java/basics/jimple/Basics.jimple" as BB

namespace Examples.Caching

def maxSpec : Spec := Spec.of
  (fun args _ => ∃ a b : I32, args = [.int a, .int b])
  (fun args _ r _ => ∀ a b : I32, args = [.int a, .int b] →
     ∃ x : I32, r = some (.int x) ∧ x.toInt = max a.toInt b.toInt)

/-- `Basics.max` in every program (no facts needed: its body consults no class). -/
theorem max_body : BodyVC (fun _ => True) (fun _ => none) 0 BB.Basics.«max(int,int)».ref maxSpec [] 20 := by
  jverify_body

end Examples.Caching

#print axioms Examples.Caching.max_body
