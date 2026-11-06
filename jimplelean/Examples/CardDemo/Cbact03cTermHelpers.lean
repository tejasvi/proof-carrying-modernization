/-
  Examples/CardDemo/Cbact03cTermHelpers.lean

  Termination of CBACT03C's helpers by the split VC (`Jimple/TermSplit.lean`): `spaces`, `zeroPad`
  and `fixLen` take the variants of their CBACT02C and CBCUS01C twins (`spacesVar`, `zeroPadVar`,
  `fitVar`); `recordText` has no loop. `run` is in `Cbact03cTermRun`.
-/
import Examples.CardDemo.Cbact03cLink
import Examples.CardDemo.Cbcus01cTermHelpers

open Jimple

namespace Examples.CardDemo

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_spaces_thin : ThinVC C3.prog (fun _ => none) 0 c3SpacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [ite_nat_ne, spacesSpec, spacesInv, spacesVar, Grows, fixStr]

theorem c3_spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm C3.prog c3SpacesRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) c3_spaces_vc c3_spaces_thin)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_zeroPad_thin : ThinVC C3.prog (fun _ => none) 0 c3ZeroPadRef zeroPadSpec zeroPadInv9 (fun _ => zeroPadVar) 80 := by
  jthin [ite_nat_ne, zeroPadSpec, zeroPadInv9, zeroPadVar, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg,
    sdiv10_nonneg, digit_char, drop_set_self]

theorem c3_zeroPad_term : ∀ args σ, zeroPadSpec.pre args σ → MTerm C3.prog c3ZeroPadRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) c3_zeroPad_vc c3_zeroPad_thin)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.hypHeapFacts true in
theorem c3_fixLen_thin : ThinVC C3.prog (fun _ => none) 0 c3FixLenRef fixLenSpec fitInv (fun _ => fitVar) 60 := by
  jthin [ite_nat_ne, fixLenSpec, fitInv, fitVar, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some]

theorem c3_fixLen_term : ∀ args σ, fixLenSpec.pre args σ → MTerm C3.prog c3FixLenRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) c3_fixLen_vc c3_fixLen_thin)

theorem c3_spaces_cterm : ContractTerm C3.prog c3SpacesSig spacesSpec := by jcontract_term [c3_spaces_term]
theorem c3_zeroPad_cterm : ContractTerm C3.prog c3ZeroPadSig zeroPadSpec := by jcontract_term [c3_zeroPad_term]
theorem c3_fixLen_cterm : ContractTerm C3.prog c3FixLenSig fixLenSpec := by jcontract_term [c3_fixLen_term]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_recordText_thin :
    ThinVC C3.prog rtCallees.env 0 c3RecordTextRef recordTextSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [ite_nat_ne, recordTextSpec, rtCallees, c3ZeroPadSig, StateRecOk, stateLine, sfieldOf, sfieldLong,
    argText, Grows, stCls]

theorem c3_recordText_term : ∀ args σ, recordTextSpec.pre args σ → MTerm C3.prog c3RecordTextRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [rtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact c3_zeroPad_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [rtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact c3_zeroPad_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) c3_recordText_vc c3_recordText_thin)

theorem c3_recordText_cterm : ContractTerm C3.prog c3RecordTextSig recordTextSpec := by
  jcontract_term [c3_recordText_term]

end Examples.CardDemo

#print axioms Examples.CardDemo.c3_spaces_cterm
#print axioms Examples.CardDemo.c3_fixLen_cterm
#print axioms Examples.CardDemo.c3_recordText_cterm
