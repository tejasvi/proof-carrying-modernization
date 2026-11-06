/-
  Examples/Methods/Sq.lean

  Method-level modules: this module imports the single method `Calc.sq` (`jimple_method`) and
  the contracts; its theorem holds in every program. It does not change when another method of
  `Calc` does.
-/
import Examples.Methods.Contracts

open Jimple

jimple_method "examples_java/calc/jimple/Calc.jimple" "sq(int)" as CQ

namespace Examples.Methods

/-- `Calc.sq` in every program. -/
theorem sq_body : BodyVC (fun _ => True) (fun _ => none) 0 CQ.Calc.«sq(int)».ref sqSpec [] 20 := by
  jverify_body [sqSpec]

end Examples.Methods

#print axioms Examples.Methods.sq_body
