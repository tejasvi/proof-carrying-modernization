-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermLink.lean (sha256 4b7d7c73be8fa19a...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaRun
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalFindOK
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalRecOK
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalEbcOK
import EquivLean.Modernize.Cbtrn03c.JavaW.WsM
import EquivLean.Modernize.Cbtrn03c.JavaW.WsM3
import EquivLean.Modernize.Cbtrn03c.JavaW.WsM4
import EquivLean.Modernize.Cbtrn03c.JavaW.W5
import EquivLean.Modernize.Cbtrn03c.JavaW.PadF
import EquivLean.Modernize.Cbtrn03c.JavaTermCal
import EquivLean.Modernize.Cbtrn03c.JavaTermWHelpers
import EquivLean.Modernize.Cbtrn03c.JavaTermWThin
import EquivLean.Modernize.Cbtrn03c.JavaTermTop

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run` terminates, and is totally correct

Every method's termination from its `MethodVC` and its thin VC (`Jimple.TermVC.of_thin`); the
contracts of the callee tables terminate (`ContractTerm`): the helpers' (`Cal.*`), the writers'
for given ghost values (`*_termG`) and on the model state (the `…SpecM` and `…SpecR` contracts, their
preconditions destructured as in the originals' `…M_sat`), the stronger `…SpecT`/`…SpecC`/`…SpecF`
preconditions by `ContractTerm.mono`. Then `Top.run_term_of` and `total_of_sat_mterm`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

/-! ## The helpers of the top layer -/

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

theorem repeat_term : ∀ args σ, repeatSpec.pre args σ → MTerm Gen.prog repeatRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) repeat_vc repeat_thin)
theorem ebcdic_term : ∀ args σ, ebcdicSpec.pre args σ → MTerm Gen.prog ebcdicRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ebcdic_vc ebcdic_thin)
theorem pow10_term : ∀ args σ, pow10Spec.pre args σ → MTerm Gen.prog pow10Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) pow10_vc pow10_thin)
theorem findXref_term : ∀ args σ, findXrefSpec.pre args σ → MTerm Gen.prog findXrefRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findXref_vc findXref_thin)
theorem findTranType_term : ∀ args σ, findTranTypeSpec.pre args σ → MTerm Gen.prog findTranTypeRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findTranType_vc findTranType_thin)
theorem findTranCat_term : ∀ args σ, findTranCatSpec.pre args σ → MTerm Gen.prog findTranCatRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findTranCat_vc findTranCat_thin)
theorem ioStatusLine_term : ∀ args σ, ioStatusLineSpecT.pre args σ → MTerm Gen.prog ioStatusLineRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ioStatusLine_vc ioStatusLine_thin)
theorem add11_term : ∀ args σ, add11SpecT.pre args σ → MTerm Gen.prog add11Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) add11_vc add11_thin)

set_option maxHeartbeats 0 in
theorem repeat_cterm : ContractTerm Gen.prog repeatSig repeatSpec := by jcontract_term [repeat_term]
set_option maxHeartbeats 0 in
theorem ebcdic_cterm : ContractTerm Gen.prog ebcdicSig ebcdicSpec := by jcontract_term [ebcdic_term]
set_option maxHeartbeats 0 in
theorem pow10_cterm : ContractTerm Gen.prog pow10Sig pow10Spec := by jcontract_term [pow10_term]
set_option maxHeartbeats 0 in
theorem findXref_cterm : ContractTerm Gen.prog findXrefSig findXrefSpec := by
  jcontract_term [findXref_term]
set_option maxHeartbeats 0 in
theorem findTranType_cterm : ContractTerm Gen.prog findTranTypeSig findTranTypeSpec := by
  jcontract_term [findTranType_term]
set_option maxHeartbeats 0 in
theorem findTranCat_cterm : ContractTerm Gen.prog findTranCatSig findTranCatSpec := by
  jcontract_term [findTranCat_term]
set_option maxHeartbeats 0 in
theorem ioStatusLine_cterm : ContractTerm Gen.prog ioStatusLineSig ioStatusLineSpecT := by
  jcontract_term [ioStatusLine_term]
set_option maxHeartbeats 0 in
theorem add11_cterm : ContractTerm Gen.prog add11Sig add11SpecT := by jcontract_term [add11_term]

theorem spaces_term : ∀ args σ, spacesSpecT.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [spacesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact repeat_ok))
    (Contracts.term_of_ok (by
      simp only [spacesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact repeat_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)
set_option maxHeartbeats 0 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpecT := by jcontract_term [spaces_term]

theorem blankTran_term : ∀ args σ, blankTranSpecT.pre args σ → MTerm Gen.prog blankTranRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [blankCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact spaces_ok))
    (Contracts.term_of_ok (by
      simp only [blankCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact spaces_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) blankTran_vc blankTran_thin)
set_option maxHeartbeats 0 in
theorem blankTran_cterm : ContractTerm Gen.prog blankTranSig blankTranSpecT := by
  jcontract_term [blankTran_term]

theorem compareEbcdic_term :
    ∀ args σ, compareEbcdicSpec.pre args σ → MTerm Gen.prog compareEbcdicRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [compareCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ebcdic_ok))
    (Contracts.term_of_ok (by
      simp only [compareCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ebcdic_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) compareEbcdic_vc compareEbcdic_thin)
set_option maxHeartbeats 0 in
theorem compareEbcdic_cterm : ContractTerm Gen.prog compareEbcdicSig compareEbcdicSpec := by
  jcontract_term [compareEbcdic_term]

theorem digits_term : ∀ args σ, digitsSpec.pre args σ → MTerm Gen.prog digitsRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [digitsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact pow10_ok))
    (Contracts.term_of_ok (by
      simp only [digitsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact pow10_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) digits_vc digits_thin)
set_option maxHeartbeats 0 in
theorem digits_cterm : ContractTerm Gen.prog digitsSig digitsSpec := by jcontract_term [digits_term]

theorem zoned_term : ∀ args σ, zonedSpec.pre args σ → MTerm Gen.prog zonedRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [zonedCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact digitsC_ok))
    (Contracts.term_of_ok (by
      simp only [zonedCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact digits_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) zoned_vc zoned_thin)
set_option maxHeartbeats 0 in
theorem zoned_cterm : ContractTerm Gen.prog zonedSig zonedSpec := by jcontract_term [zoned_term]

theorem tranRecordText_term :
    ∀ args σ, tranRecordTextSpec.pre args σ → MTerm Gen.prog tranRecordTextRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [trCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ⟨digitsC_ok, zonedC_ok⟩))
    (Contracts.term_of_ok (by
      simp only [trCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ⟨digits_cterm, zoned_cterm⟩) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) tranRecordText_vc tranRecordText_thin)
set_option maxHeartbeats 0 in
theorem tranRecordText_cterm : ContractTerm Gen.prog tranRecordTextSig tranRecordTextSpec := by
  jcontract_term [tranRecordText_term]

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-! ## The contracts of the callee tables (stronger preconditions, as in `Cal*OK`) -/

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem findXrefT_cterm : ContractTerm Gen.prog findXrefSig findXrefSpecT :=
  ContractTerm.mono Cal.findXref_cterm (by
    intro args σ hp
    obtain ⟨a, y, xs, k, rfl, hf, hv, hy⟩ := hp
    obtain ⟨et, es, ha, hlen, h2⟩ := hf
    exact ⟨a, y, cp037Str k, et, es, rfl, hy, ha, hlen, (Cal.xref_elems h2 hv).2⟩)

theorem findTranTypeT_cterm : ContractTerm Gen.prog findTranTypeSig findTranTypeSpecT :=
  ContractTerm.mono Cal.findTranType_cterm (by
    intro args σ hp
    obtain ⟨a, y, ys, k, rfl, hf, hv, hy⟩ := hp
    obtain ⟨et, es, ha, hlen, h2⟩ := hf
    exact ⟨a, y, cp037Str k, et, es, rfl, hy, ha, hlen, (Cal.type_elems h2 hv).2⟩)

theorem findTranCatT_cterm : ContractTerm Gen.prog findTranCatSig findTranCatSpecT :=
  ContractTerm.mono Cal.findTranCat_cterm (by
    intro args σ hp
    obtain ⟨a, y, cs, k, v, rfl, hf, hv, hy, -⟩ := hp
    obtain ⟨et, es, ha, hlen, h2⟩ := hf
    exact ⟨a, y, cp037Str k, v, et, es, rfl, hy, ha, hlen, (Cal.cat_elems h2 hv).2⟩)

theorem digitsT_cterm : ContractTerm Gen.prog digitsSig digitsSpecT :=
  ContractTerm.mono Cal.digits_cterm fun _ _ h => h

theorem zonedT_cterm : ContractTerm Gen.prog zonedSig zonedSpecT :=
  ContractTerm.mono Cal.zoned_cterm fun _ _ h => h

theorem tranRecordTextT_cterm : ContractTerm Gen.prog tranRecordTextSig tranRecordTextSpecT :=
  ContractTerm.mono Cal.tranRecordText_cterm (by
    intro args σ hp
    obtain ⟨c, t, rfl, hf, hv, hi⟩ := hp
    have hf' : TranFields σ c t := by unfold TranFieldsI at hf; exact hf
    exact ⟨c, rfl, (Cal.tran_glue hf' hv).1, hi⟩)

theorem compareEbcdicC_cterm : ContractTerm Gen.prog compareEbcdicSig compareEbcdicSpecC :=
  ContractTerm.mono Cal.compareEbcdic_cterm (by
    intro args σ hp
    obtain ⟨xa, xb, ba, bb, rfl, ha, hb, hl, hlen, hi⟩ := hp
    exact ⟨xa, xb, cp037Str ba, cp037Str bb, rfl, ha, hb,
      by rw [cp037Str_length, cp037Str_length, hl], by rw [cp037Str_length]; exact hlen, hi⟩)

end EquivLean.Modernize.Cbtrn03c.Java.Top

/-! ## The working-state writers -/

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem repeat_term : ∀ args σ, repeatSpec.pre args σ → MTerm Gen.prog repeatRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) repeat_vc repeat_thin)
theorem pow10_term : ∀ args σ, pow10Spec.pre args σ → MTerm Gen.prog pow10Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) pow10_vc pow10_thin)
theorem add11_term : ∀ args σ, add11Spec.pre args σ → MTerm Gen.prog add11Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) add11_vc add11_thin)
theorem incLine_term : ∀ args σ, incLineSpec.pre args σ → MTerm Gen.prog incLineRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) incLine_vc incLine_thin)
theorem pad_term : ∀ args σ, padSpec.pre args σ → MTerm Gen.prog padRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) pad_vc pad_thin)

set_option maxHeartbeats 0 in
theorem repeat_cterm : ContractTerm Gen.prog repeatSig repeatSpec := by jcontract_term [repeat_term]
set_option maxHeartbeats 0 in
theorem pow10_cterm : ContractTerm Gen.prog pow10Sig pow10Spec := by jcontract_term [pow10_term]
set_option maxHeartbeats 0 in
theorem add11_cterm : ContractTerm Gen.prog add11Sig add11Spec := by jcontract_term [add11_term]
set_option maxHeartbeats 0 in
theorem incLine_cterm : ContractTerm Gen.prog incLineSig incLineSpec := by jcontract_term [incLine_term]
set_option maxHeartbeats 0 in
theorem pad_cterm : ContractTerm Gen.prog padSig padSpec := by jcontract_term [pad_term]
theorem padF_cterm : ContractTerm Gen.prog padSig padSpecF := ContractTerm.mono pad_cterm fun _ _ h => h

theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [spacesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact repeat_ok))
    (Contracts.term_of_ok (by
      simp only [spacesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact repeat_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)
set_option maxHeartbeats 0 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec := by jcontract_term [spaces_term]

theorem digits_term : ∀ args σ, digitsSpec.pre args σ → MTerm Gen.prog digitsRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [digitsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact pow10_ok))
    (Contracts.term_of_ok (by
      simp only [digitsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact pow10_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) digits_vc digits_thin)
set_option maxHeartbeats 0 in
theorem digits_cterm : ContractTerm Gen.prog digitsSig digitsSpec := by jcontract_term [digits_term]

theorem edit_term : ∀ args σ, editSpec.pre args σ → MTerm Gen.prog editRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [editCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ⟨spaces_ok, digits_ok⟩))
    (Contracts.term_of_ok (by
      simp only [editCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ⟨spaces_cterm, digits_cterm⟩) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) edit_vc edit_thin)
set_option maxHeartbeats 0 in
theorem edit_cterm : ContractTerm Gen.prog editSig editSpec := by jcontract_term [edit_term]

theorem writeLine_term : ∀ args σ, writeLineSpec.pre args σ → MTerm Gen.prog writeLineRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [writeLineCallees, List.forall_mem_cons, List.not_mem_nil, false_implies,
        implies_true, and_true]
      exact padF_ok))
    (Contracts.term_of_ok (by
      simp only [writeLineCallees, List.forall_mem_cons, List.not_mem_nil, false_implies,
        implies_true, and_true]
      exact padF_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) writeLine_vc writeLine_thin)
set_option maxHeartbeats 0 in
theorem writeLine_cterm : ContractTerm Gen.prog writeLineSig writeLineSpec := by
  jcontract_term [writeLine_term]

theorem totalsCallees_term :
    ∀ sig S, (totalsCallees.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [totalsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨padF_cterm, repeat_cterm, edit_cterm, add11_cterm, writeLine_cterm, incLine_cterm⟩) _ _

theorem linesCallees_term :
    ∀ sig S, (linesCallees.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [linesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨padF_cterm, spaces_cterm, repeat_cterm, digits_cterm, edit_cterm, writeLine_cterm,
      incLine_cterm⟩) _ _

theorem writePageTotals_termG (w ld lr : Addr) (v : WsV) :
    ∀ args σ, (writePageTotalsSpecG w ld lr v).pre args σ → MTerm Gen.prog writePageTotalsRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) totalsCallees_valid totalsCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writePageTotals_vcG w ld lr v)
      (writePageTotals_thinG w ld lr v))

theorem writeAccountTotals_termG (w ld lr : Addr) (v : WsV) :
    ∀ args σ, (writeAccountTotalsSpecG w ld lr v).pre args σ →
      MTerm Gen.prog writeAccountTotalsRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) totalsCallees_valid totalsCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeAccountTotals_vcG w ld lr v)
      (writeAccountTotals_thinG w ld lr v))

theorem writeGrandTotals_termG (w ld lr : Addr) (v : WsV) :
    ∀ args σ, (writeGrandTotalsSpecG w ld lr v).pre args σ →
      MTerm Gen.prog writeGrandTotalsRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) totalsCallees_valid totalsCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeGrandTotals_vcG w ld lr v)
      (writeGrandTotals_thinG w ld lr v))

theorem writeHeaders_termG (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) :
    ∀ args σ, (writeHeadersSpecG w ld lr v xs xe rs re).pre args σ →
      MTerm Gen.prog writeHeadersRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) linesCallees_valid linesCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeHeaders_vcG w ld lr v xs xe rs re)
      (writeHeaders_thinG w ld lr v xs xe rs re))

theorem writeDetail_termG (w ld lr : Addr) (v : WsV) (c yx cx : Addr)
    (t : List EquivLean.Cobol.Rec.FVal) (ys cs : JStr) :
    ∀ args σ, (writeDetailSpecG w ld lr v c yx cx t ys cs).pre args σ →
      MTerm Gen.prog writeDetailRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) linesCallees_valid linesCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeDetail_vcG w ld lr v c yx cx t ys cs)
      (writeDetail_thinG w ld lr v c yx cx t ys cs))

/-! ### On the model state (preconditions destructured as in `WsM*`, `W5v`) -/

theorem writePageTotalsM_term :
    ∀ args σ, Top.writePageTotalsSpecM.pre args σ → MTerm Gen.prog writePageTotalsRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, d, s, hargs, hR, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, -, hp, -, -⟩ := wsAt_of_wsRel hR
  exact writePageTotals_termG w ld lr v args σ ⟨hargs, hA, hp, hi1, hi2⟩

theorem writeAccountTotalsM_term :
    ∀ args σ, Top.writeAccountTotalsSpecM.pre args σ → MTerm Gen.prog writeAccountTotalsRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, d, s, hargs, hR, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, -, -, ha, -⟩ := wsAt_of_wsRel hR
  exact writeAccountTotals_termG w ld lr v args σ ⟨hargs, hA, ha, hi1, hi2⟩

theorem writeGrandTotalsM_term :
    ∀ args σ, Top.writeGrandTotalsSpecM.pre args σ → MTerm Gen.prog writeGrandTotalsRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, d, s, hargs, hR, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, -, -, -, hg⟩ := wsAt_of_wsRel hR
  exact writeGrandTotals_termG w ld lr v args σ ⟨hargs, hA, hg, hi1, hi2⟩

theorem writeHeadersM_term :
    ∀ args σ, writeHeadersSpecM.pre args σ → MTerm Gen.prog writeHeadersRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, d, s, h1, h2, -, h3, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, hV⟩ := wsRel_iff.1 h2
  have hV0 := hV
  obtain ⟨-, -, ⟨rx, hrx, hrxs⟩, ⟨ex, hex, hexs⟩, -⟩ := hV0
  obtain ⟨l1, l2⟩ := dateparm_len h3
  refine writeHeaders_termG w ld lr v rx ex _ _ args σ
    ⟨h1, hA, hrx, hrxs, hex, hexs, ?_, ?_, hi1, hi2⟩
  · rw [cp037Str_length]; omega
  · rw [cp037Str_length]; omega

theorem writeDetailM_term :
    ∀ args σ, writeDetailSpecM.pre args σ → MTerm Gen.prog writeDetailRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, c, ty, ca, d, s, t, y, cc, h1, h2, h3, h4, h5, h6, h7, h8, h9, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, hV⟩ := wsRel_iff.1 h2
  have hV0 := hV
  obtain ⟨-, -, -, -, ha, -⟩ := hV0
  obtain ⟨id, tty, cat, src, desc, amt, _, _, _, _, _, _, _, _, rfl, hid, htt, hcat, -, hsrc, -,
    hamt, -⟩ := Glue.tran_shape h4
  obtain ⟨_, ydesc, _, rfl, -, hyd, -⟩ := Glue.type_shape h5
  obtain ⟨_, _, cdesc, _, rfl, -, -, -, hcd, -⟩ := Glue.catg_shape h6
  refine writeDetail_termG w ld lr v c ty ca _ _ _ args σ
    ⟨h1, hA, ?_, detailFields_of h3, ?_, ?_, ?_, ?_, ?_, h8, ?_, h9, ?_, hi1, hi2⟩
  · rw [ha, trunc11_small (by omega)]; omega
  · show id.length < 1000; omega
  · show tty.length < 1000; omega
  · show src.length < 1000; omega
  · show -9223372036854775808 < (BitVec.ofInt 64 cat).toInt
    rw [trunc11_small (by omega)]; omega
  · show -9223372036854775808 < (BitVec.ofInt 64 amt).toInt
    rw [trunc11_small (by omega)]; omega
  · show (cp037Str ydesc).length < 1000
    rw [cp037Str_length]; omega
  · show (cp037Str cdesc).length < 1000
    rw [cp037Str_length]; omega

set_option maxHeartbeats 0 in
theorem writePageTotalsM_cterm : ContractTerm Gen.prog Top.writePageTotalsSig Top.writePageTotalsSpecM := by
  jcontract_term [writePageTotalsM_term]
set_option maxHeartbeats 0 in
theorem writeAccountTotalsM_cterm :
    ContractTerm Gen.prog Top.writeAccountTotalsSig Top.writeAccountTotalsSpecM := by
  jcontract_term [writeAccountTotalsM_term]
set_option maxHeartbeats 0 in
theorem writeGrandTotalsM_cterm :
    ContractTerm Gen.prog Top.writeGrandTotalsSig Top.writeGrandTotalsSpecM := by
  jcontract_term [writeGrandTotalsM_term]
set_option maxHeartbeats 0 in
theorem writeHeadersM_cterm : ContractTerm Gen.prog writeHeadersSig writeHeadersSpecM := by
  jcontract_term [writeHeadersM_term]
set_option maxHeartbeats 0 in
theorem writeDetailM_cterm : ContractTerm Gen.prog writeDetailSig writeDetailSpecM := by
  jcontract_term [writeDetailM_term]

theorem headersR_cterm : ContractTerm Gen.prog writeHeadersSig headersSpecR :=
  ContractTerm.mono writeHeadersM_cterm fun _ _ h => h
theorem pageR_cterm : ContractTerm Gen.prog Top.writePageTotalsSig pageSpecR :=
  ContractTerm.mono writePageTotalsM_cterm fun _ _ h => h
theorem detailR_cterm : ContractTerm Gen.prog writeDetailSig detailSpecR :=
  ContractTerm.mono writeDetailM_cterm fun _ _ h => h

theorem reportCalleesR_term :
    ∀ sig S, (reportCalleesR.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [reportCalleesR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨headersR_cterm, pageR_cterm, detailR_cterm, add11_cterm⟩) _ _

theorem wtr_termG (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (hd : WsDateparmRecord.Valid d)
    (ht : TranRecord.Valid t) (hy : TranTypeRecord.Valid y) (hc : TranCatRecord.Valid cc)
    (hx : (Model.xAcct s.xref).natAbs < 100000000000) :
    ∀ args σ, (wtrSpecG w ld lr c ty ca d s t y cc).pre args σ →
      MTerm Gen.prog writeTransactionReportRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) reportCalleesR_valid reportCalleesR_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (wtr_vcG w ld lr c ty ca d s t y cc hd ht hy hc hx)
      (wtr_thinG w ld lr c ty ca d s t y cc hd ht hy hc hx))

theorem writeTransactionReportM_term :
    ∀ args σ, Top.writeTransactionReportSpecM.pre args σ →
      MTerm Gen.prog writeTransactionReportRef args σ := by
  intro args σ hpre
  obtain ⟨w, ld, lr, c, ty, ca, d, s, t, y, cc, h1, h2, h3, h4, h5, h6, h7, h8, h9, hi1, hi2⟩ := hpre
  exact wtr_termG w ld lr c ty ca d s t y cc h5 h4 h6 h7 (xacct_of_wsRel h2) args σ
    ⟨h1, h2, h3, h8, h9, hi1, hi2⟩

set_option maxHeartbeats 0 in
theorem writeTransactionReportM_cterm :
    ContractTerm Gen.prog Top.writeTransactionReportSig Top.writeTransactionReportSpecM := by
  jcontract_term [writeTransactionReportM_term]

end EquivLean.Modernize.Cbtrn03c.Java

/-! ## `run` -/

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem pdCallees_valid : Valid Gen.prog Top.pdCallees.env := by
  apply Contracts.valid_of_ok
  simp only [Top.pdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨Top.tranRecordText_ok, writeAccountTotalsM_ok, Top.findXref_ok, Top.ioStatusLine_ok,
    Top.findTranType_ok, Top.findTranCat_ok, Top.digits_ok, writeTransactionReportM_ok⟩

theorem peCallees_valid : Valid Gen.prog Top.peCallees.env := by
  apply Contracts.valid_of_ok
  simp only [Top.peCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨Top.zoned_ok, Top.add11_ok, writePageTotalsM_ok, writeGrandTotalsM_ok⟩

theorem pdCallees_term : ∀ p ∈ Top.pdCallees, ContractTerm Gen.prog p.1 p.2 := by
  simp only [Top.pdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨Top.tranRecordTextT_cterm, writeAccountTotalsM_cterm, Top.findXrefT_cterm,
    Top.Cal.ioStatusLine_cterm, Top.findTranTypeT_cterm, Top.findTranCatT_cterm, Top.digitsT_cterm,
    writeTransactionReportM_cterm⟩

theorem peCallees_term : ∀ p ∈ Top.peCallees, ContractTerm Gen.prog p.1 p.2 := by
  simp only [Top.peCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨Top.zonedT_cterm, Top.Cal.add11_cterm, writePageTotalsM_cterm, writeGrandTotalsM_cterm⟩

theorem runCallees_valid : Valid Gen.prog Top.runCallees.env := by
  apply Contracts.valid_of_ok
  simp only [Top.runCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨Top.spaces_ok, Top.blankTran_ok, Top.compareEbcdicC_ok, Top.pd_ok pdCallees_valid,
    Top.pe_ok peCallees_valid⟩

theorem runCallees_term : ∀ p ∈ Top.runCallees, ContractTerm Gen.prog p.1 p.2 := by
  simp only [Top.runCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨Top.Cal.spaces_cterm, Top.Cal.blankTran_cterm, Top.compareEbcdicC_cterm,
    Top.pd_cterm pdCallees_valid pdCallees_term, Top.pe_cterm peCallees_valid peCallees_term⟩

/-- **`run` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ :=
  Top.run_term_of runCallees_valid runCallees_term

/-- **CBTRN03C → Java, total correctness**: on every input of `runSpec`, `run` has an outcome, and
    every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm run_sat run_term

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.run_term
#print axioms EquivLean.Modernize.Cbtrn03c.Java.run_total
