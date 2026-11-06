-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cTermHelpers.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cTermHelpers.lean

  Termination of CBCUS01C's helpers by the split VC (`Jimple/TermSplit.lean`): each partial-correctness
  VC of `Cbcus01cHelpers`/`Cbcus01cFormat` with a thin VC. `spaces` and `fmtNum` take the variants of
  their CBACT02C twins (`spacesVar`, `zeroPadVar`), `fit` pads up to `n` (variant `n - k`), and
  `fmtRecordInitial` and `fmtRecord` have no loop. `run` is in `Cbcus01cTermRun`.
-/
import EquivLean.Modernize.JL.Cbcus01cLink
import EquivLean.Modernize.JL.Cbact02cTermHelpers

open Jimple

namespace EquivLean.Modernize.JL

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_spaces_thin : ThinVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog (fun _ => none) 0 cuSpacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [ite_nat_ne, spacesSpec, spacesInv, spacesVar, Grows, fixStr]

theorem cu_spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuSpacesRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cu_spaces_vc cu_spaces_thin)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_fmtNum_thin : ThinVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog (fun _ => none) 0 cuFmtNumRef zeroPadSpec zeroPadInv (fun _ => zeroPadVar) 80 := by
  jthin [ite_nat_ne, zeroPadSpec, zeroPadInv, zeroPadVar, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg,
    sdiv10_nonneg, digit_char, drop_set_self]

theorem cu_fmtNum_term : ∀ args σ, zeroPadSpec.pre args σ → MTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtNumRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cu_fmtNum_vc cu_fmtNum_thin)

/-- `fit`'s loop pads the builder up to `n` characters: `n - k` (locals `i0` 0, `$i1` 1). -/
def fitVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int k) => (n.toInt - k.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.hypHeapFacts true in
theorem cu_fit_thin : ThinVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog (fun _ => none) 0 cuFitRef fitSpec fitInv (fun _ => fitVar) 60 := by
  jthin [ite_nat_ne, fitSpec, fitInv, fitVar, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some]

theorem cu_fit_term : ∀ args σ, fitSpec.pre args σ → MTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFitRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cu_fit_vc cu_fit_thin)

theorem cu_spaces_cterm : ContractTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuSpacesSig spacesSpec := by jcontract_term [cu_spaces_term]
theorem cu_fmtNum_cterm : ContractTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtNumSig zeroPadSpec := by jcontract_term [cu_fmtNum_term]
theorem cu_fit_cterm : ContractTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFitSig fitSpec := by jcontract_term [cu_fit_term]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_fmtRecordInitial_thin :
    ThinVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog friCallees.env 0 cuFmtRecordInitialRef fmtRecordInitialSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [ite_nat_ne, fmtRecordInitialSpec, friCallees, cuFmtNumSig, cuSpacesSig, Grows]

theorem cu_fmtRecordInitial_term :
    ∀ args σ, fmtRecordInitialSpec.pre args σ → MTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordInitialRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [friCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact cu_fmtNum_ok
      · exact cu_spaces_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [friCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact cu_fmtNum_cterm
      · exact cu_spaces_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cu_fmtRecordInitial_vc cu_fmtRecordInitial_thin)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_fmtRecord_thin :
    ThinVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog frCallees.env 0 cuFmtRecordRef fmtRecordSpec [] (fun _ _ _ _ _ => 0) 120 := by
  jthin [ite_nat_ne, fmtRecordSpec, frCallees, cuFmtNumSig, cuFitSig, CustOk, CStrField, CLongField, StrOk,
    custLine, ctext, cfieldOf, cfieldLong, argText, Grows, custCls]

theorem cu_fmtRecord_term : ∀ args σ, fmtRecordSpec.pre args σ → MTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [frCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact cu_fmtNum_ok
      · exact cu_fit_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [frCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact cu_fmtNum_cterm
      · exact cu_fit_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cu_fmtRecord_vc cu_fmtRecord_thin)

theorem cu_fmtRecordInitial_cterm : ContractTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordInitialSig fmtRecordInitialSpec := by
  jcontract_term [cu_fmtRecordInitial_term]
theorem cu_fmtRecord_cterm : ContractTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordSig fmtRecordSpec := by
  jcontract_term [cu_fmtRecord_term]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.cu_fmtRecordInitial_cterm
#print axioms EquivLean.Modernize.JL.cu_fmtRecord_cterm
