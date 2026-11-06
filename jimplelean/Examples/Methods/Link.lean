/-
  Examples/Methods/Link.lean

  The link step for the method-level modules: the whole class is imported here (only here),
  the shape facts are checked by evaluation, and the per-method proofs are instantiated.
  `jcontract_ok` matches the method of `jimple_method` with the one of the program by unfolding
  (same body). The same proof `sumSq_body` is linked into a second program in which the body
  of `Calc.add` was edited (`examples_java/calc/jimple_edit`): the shape is unchanged.
-/
import Examples.Methods.SumSq
import Examples.Methods.Sq

open Jimple

jimple_import "examples_java/calc/jimple/Calc.jimple" as CC
jimple_import "examples_java/calc/jimple_edit/Calc.jimple" as CE

namespace Examples.Methods

/-- The program has the shape the body proofs assumed. -/
theorem cc_shapes : Shapes CC.prog [CS.Calc] :=
  Shapes.of_check (by decide) (by
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact ⟨_, rfl, rfl⟩)

theorem sq_sat : Sat CC.prog CQ.Calc.«sq(int)».ref sqSpec := sq_body.sat trivial (valid_none _)

theorem sq_ok : ContractOK CC.prog sqSig sqSpec := by
  jcontract_ok [sq_sat]

theorem sumSq_sat : Sat CC.prog CM.Calc.«sumSq(int,int)».ref sumSqSpec :=
  sumSq_body.sat cc_shapes (Contracts.valid_of_ok (by
    intro p hp
    simp only [sumSqCallees, List.mem_singleton] at hp
    subst hp
    exact sq_ok))

/-- The edited program (another body of `add`) has the same shape. -/
theorem ce_shapes : Shapes CE.prog [CS.Calc] :=
  Shapes.of_check (by decide) (by
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact ⟨_, rfl, rfl⟩)

theorem sq_ok_edit : ContractOK CE.prog sqSig sqSpec := by
  jcontract_ok [(sq_body.sat trivial (valid_none _) : Sat CE.prog CQ.Calc.«sq(int)».ref sqSpec)]

/-- `sumSq_body`, checked once, linked into the edited program. -/
theorem sumSq_sat_edit : Sat CE.prog CM.Calc.«sumSq(int,int)».ref sumSqSpec :=
  sumSq_body.sat ce_shapes (Contracts.valid_of_ok (by
    intro p hp
    simp only [sumSqCallees, List.mem_singleton] at hp
    subst hp
    exact sq_ok_edit))

end Examples.Methods

#print axioms Examples.Methods.cc_shapes
#print axioms Examples.Methods.sq_ok
#print axioms Examples.Methods.sumSq_sat
#print axioms Examples.Methods.sumSq_sat_edit
