/-
  Examples/Methods/SumSq.lean

  `Calc.sumSq` calls `Calc.sq` twice. Its proof imports its own method (`jimple_method`), the
  shape of `Calc` (`jimple_shape`: signatures, fields, hierarchy, no bodies) and the contracts;
  the facts `Shapes P [CS.Calc]` mention no method body. Editing the body of another method of
  `Calc` (`sq` too, while its contract holds) changes none of these modules: the proof is
  checked once and reused (`Link.lean` links it into the original and into an edited program).
-/
import Examples.Methods.Shape
import Examples.Methods.Contracts

open Jimple

jimple_method "examples_java/calc/jimple/Calc.jimple" "sumSq(int,int)" as CM

namespace Examples.Methods

/-- The callee contracts of `sumSq`. -/
def sumSqCallees : Contracts := [(sqSig, sqSpec)]

/-- `Calc.sumSq` in every program in which `Calc` has this shape, against `sq`'s contract. -/
theorem sumSq_body : BodyVC (Shapes · [CS.Calc]) sumSqCallees.env 0
    CM.Calc.«sumSq(int,int)».ref sumSqSpec [] 40 := by
  jverify_body [sumSqSpec, sumSqCallees, sqSig, sqSpec]

end Examples.Methods

#print axioms Examples.Methods.sumSq_body
