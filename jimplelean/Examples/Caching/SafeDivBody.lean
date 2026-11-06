/-
  Examples/Caching/SafeDivBody.lean

  A body that consults the program: `Hello.safeDiv` reads the static field `cnt`, initializes
  its class and dispatches exceptions through its trap table. Its proof holds for every
  program that contains the class `Hello` and shadows no library class (`Contains`). Finer
  facts, mentioning only the lookups the body makes, can be found with `jfacts` (see
  `Jimple/Verify.lean`).
-/
import Jimple

open Jimple

jimple_import "examples_java/hello/jimple/Hello.jimple" as HH

namespace Examples.Caching

def safeDivSpec : Spec := Spec.of
  (fun args σ => ∃ a b c : I32, args = [.int a, .int b] ∧ σ.initOf "Hello" = .done ∧
     σ.static ("Hello", "cnt") = some (.int c))
  (fun args σ r σ' => ∀ a b c : I32, args = [.int a, .int b] → σ.static ("Hello", "cnt") = some (.int c) →
     r = some (.int (if b = 0 then -1 else a.sdiv b)) ∧ σ'.static ("Hello", "cnt") = some (.int (c + 1)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `Hello.safeDiv` in every program that contains `Hello` and shadows no library class. -/
theorem safeDiv_body : BodyVC (Contains · [HH.Hello]) (fun _ => none) 0
    HH.Hello.«safeDiv(int,int)».ref safeDivSpec [] 60 := by
  jverify_body [Contains]

end Examples.Caching

#print axioms Examples.Caching.safeDiv_body
