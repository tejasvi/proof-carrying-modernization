import EquivLean.Modernize.Cbact01c.Model
import EquivLean.Demo.Cobol.Cbact01c.Prog
import EquivLean.Modernize.Cbact04c.Glue

/-!
# CBACT01C: coblean's model and the translations' model

coblean's `cbact01c_extracts` describes the COBOL run of CBACT01C for every account file given as
coblean's account records (`Acct`), by its model `model`: a fold over the records (`step`, the
events of one record).  `Model.run` is the fold the translations perform on field values.

* `acctOf` builds coblean's account record from the field values of the statements' records: a
  valid record (`acctOf_valid`) with the record's bytes (`acctOf_bytes`).
* The records the run writes are those of `Model.run`, decoded: the OUT-FILE copy
  (`decode_outRec`, with the two spaces of COBDATFT's output date after the eight characters it
  sets), the ARRY-FILE record (`decode_arrRec`, with the schema `ArrArrayRec` of the `OCCURS`
  record, the occurrences expanded in storage order), the two VBRC-FILE records (`vb1_text`,
  `vb2_text`, as text); and the displayed lines are `lines` (`step_lines`).
* The proof is a simulation, one account record at a time (`step_corr`).  Its invariant `Corr`:
  coblean's bytes of `OUT-ACCT-CURR-CYC-DEBIT` encode the translations' value, and the outputs
  are those of coblean's events.
* `cobol_outputs`: with coblean's theorem, the COBOL run of the statements ends with GOBACK, and
  its displays and the records it writes are `Model.run`'s.  The harness storage holds spaces
  after the eight characters COBDATFT sets (`initMem_rf`) and a packed zero in
  `OUT-ACCT-CURR-CYC-DEBIT` (`initMem_cd`), as `Model.run` has it.
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbact01c.Model
open CardDemo.Cbact01c (Acct)
open EquivLean.Modernize.Cbact04c.Glue (num_of_valid str_of_valid holds_display)

namespace EquivLean.Modernize.Cbact01c.Glue

-- The record of ARRY-FILE, its `OCCURS` items expanded in storage order (as `arrVals`).
cobol_schema ArrArrayRec from "../../../examples/cobol/carddemo/cbact01c.ir.json" record "ARR-ARRAY-REC"

/-! ## The account records as coblean's structures -/

/-- coblean's account record of a record's field values. -/
def acctOf (a : List FVal) : Acct :=
  ⟨aId a, aStatus a, aBal a, aLimit a, numOf (a.getD 4 default), strOf (a.getD 5 default),
    strOf (a.getD 6 default), aReissue a, numOf (a.getD 8 default), aCycDebit a,
    strOf (a.getD 10 default), strOf (a.getD 11 default), strOf (a.getD 12 default)⟩

theorem acct_shape {A : List FVal} (hA : AccountRecord.Valid A) :
    ∃ id s bal cl ccl od ed rd cc cd zip grp af,
      A = [.num id, .str s, .num bal, .num cl, .num ccl, .str od, .str ed, .str rd, .num cc,
        .num cd, .str zip, .str grp, .str af] ∧
      id.natAbs < 100000000000 ∧ 0 ≤ id ∧ s.length = 1 ∧ bal.natAbs < 1000000000000 ∧
      cl.natAbs < 1000000000000 ∧ ccl.natAbs < 1000000000000 ∧ od.length = 10 ∧
      ed.length = 10 ∧ rd.length = 10 ∧ cc.natAbs < 1000000000000 ∧
      cd.natAbs < 1000000000000 ∧ zip.length = 10 ∧ grp.length = 10 ∧ af.length = 178 := by
  have hl : A.length = 13 := hA.length_eq.symm
  match A, hl, hA with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], _,
      .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
        (.cons h9 (.cons h10 (.cons h11 (.cons h12 .nil)))))))))))) =>
    obtain ⟨id, rfl, hid⟩ := num_of_valid rfl h0
    obtain ⟨s, rfl, hs⟩ := str_of_valid rfl h1
    obtain ⟨bal, rfl, hbal⟩ := num_of_valid rfl h2
    obtain ⟨cl, rfl, hcl⟩ := num_of_valid rfl h3
    obtain ⟨ccl, rfl, hccl⟩ := num_of_valid rfl h4
    obtain ⟨od, rfl, hod⟩ := str_of_valid rfl h5
    obtain ⟨ed, rfl, hed⟩ := str_of_valid rfl h6
    obtain ⟨rd, rfl, hrd⟩ := str_of_valid rfl h7
    obtain ⟨cc, rfl, hcc⟩ := num_of_valid rfl h8
    obtain ⟨cd, rfl, hcd⟩ := num_of_valid rfl h9
    obtain ⟨zip, rfl, hzip⟩ := str_of_valid rfl h10
    obtain ⟨grp, rfl, hgrp⟩ := str_of_valid rfl h11
    obtain ⟨af, rfl, haf⟩ := str_of_valid rfl h12
    obtain ⟨_, k0, -, -, n0, -⟩ := hid
    obtain ⟨_, k2, -, -, n2, -⟩ := hbal
    obtain ⟨_, k3, -, -, n3, -⟩ := hcl
    obtain ⟨_, k4, -, -, n4, -⟩ := hccl
    obtain ⟨_, k8, -, -, n8, -⟩ := hcc
    obtain ⟨_, k9, -, -, n9, -⟩ := hcd
    cases k0; cases k2; cases k3; cases k4; cases k8; cases k9
    rw [holds_display rfl] at n0 n2 n3 n4 n8 n9
    refine ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, ?_⟩
    simp_all

theorem acctOf_valid {A : List FVal} (hA : AccountRecord.Valid A) : (acctOf A).valid := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, h⟩ := acct_shape hA
  exact h

theorem acctOf_bytes {A : List FVal} (hA : AccountRecord.Valid A) :
    (acctOf A).bytes = AccountRecord.encode A := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, cd, zip, grp, af, rfl, -⟩ := acct_shape hA
  have e : AccountRecord.encode [.num id, .str s, .num bal, .num cl, .num ccl, .str od, .str ed,
      .str rd, .num cc, .num cd, .str zip, .str grp, .str af] =
      encodeNum {} CardDemo.Cbact01c.ACCT_ID.fmt id ++ (s ++
      (encodeNum {} CardDemo.Cbact01c.ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact01c.ACCT_CREDIT_LIMIT.fmt cl ++
      (encodeNum {} CardDemo.Cbact01c.ACCT_CASH_CREDIT_LIMIT.fmt ccl ++ (od ++ (ed ++ (rd ++
      (encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_CREDIT.fmt cc ++
      (encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_DEBIT.fmt cd ++
      (zip ++ (grp ++ (af ++ [])))))))))))) := rfl
  rw [e]
  simp [Acct.bytes, acctOf, aId, aStatus, aBal, aLimit, aReissue, aCycDebit, strOf, numOf,
    List.append_assoc]

/-! ## The records written -/

/-- A value a packed (COMP-3) or zoned picture holds. -/
theorem holds_dec {f : NumFmt} (hf : f.fullBinary {} = false) {v : Int} :
    f.Holds {} v ↔ v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v) := by
  unfold NumFmt.Holds
  simp [hf]

/-- The OUT-FILE copy of an account record is coblean's `outRec`, with the two spaces of
COBDATFT's output date after the eight characters it sets. -/
theorem outVals_encode {A : List FVal} (hA : AccountRecord.Valid A) (cd : Int) :
    OutAcctRec.encode (outVals A cd) = CardDemo.Cbact01c.outRec (sp 2)
      (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt cd) (acctOf A) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, -⟩ := acct_shape hA
  have e : OutAcctRec.encode (outVals [.num id, .str s, .num bal, .num cl, .num ccl, .str od,
      .str ed, .str rd, .num cc, .num d, .str zip, .str grp, .str af] cd) =
      encodeNum {} CardDemo.Cbact01c.OUT_ACCT_ID.fmt id ++ (s ++
      (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CREDIT_LIMIT.fmt cl ++
      (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CASH_CREDIT_LIMIT.fmt ccl ++ (od ++ (ed ++
      (reissueOut rd ++ (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_CREDIT.fmt cc ++
      (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt cd ++ (grp ++ [])))))))))) :=
    rfl
  rw [e]
  simp [CardDemo.Cbact01c.outRec, CardDemo.Cbact01c.reisOut, reissueOut, acctOf, aId, aStatus,
    aBal, aLimit, aReissue, strOf, numOf, List.append_assoc]

theorem outVals_valid {A : List FVal} (hA : AccountRecord.Valid A) {cd : Int}
    (hcd : cd.natAbs < 1000000000000) : OutAcctRec.Valid (outVals A cd) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, hid, hid0, hs, hbal, hcl,
    hccl, hod, hed, hrd, hcc, -, -, hgrp, -⟩ := acct_shape hA
  have hr : (reissueOut rd).length = 10 := by simp [reissueOut, sp, hrd]
  exact .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hid, fun _ => hid0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hs⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hbal, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcl, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hccl, fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hod⟩ (.cons ⟨⟨_, rfl⟩, hed⟩ (.cons ⟨⟨_, rfl⟩, hr⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcc, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_dec rfl).2 ⟨hcd, fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hgrp⟩ .nil))))))))))

theorem decode_outRec {A : List FVal} (hA : AccountRecord.Valid A) {cd : Int}
    (hcd : cd.natAbs < 1000000000000) :
    OutAcctRec.decode (CardDemo.Cbact01c.outRec (sp 2)
      (encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt cd) (acctOf A)) =
      some (outVals A cd) := by
  rw [← outVals_encode hA cd]
  exact Schema.decode_encode (by decide) (outVals_valid hA hcd)

/-- The ARRY-FILE record of an account record is coblean's `arrRec`. -/
theorem arrVals_encode {A : List FVal} (hA : AccountRecord.Valid A) :
    ArrArrayRec.encode (arrVals A) = CardDemo.Cbact01c.arrRec (acctOf A) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, -⟩ := acct_shape hA
  have e : ArrArrayRec.encode (arrVals [.num id, .str s, .num bal, .num cl, .num ccl, .str od,
      .str ed, .str rd, .num cc, .num d, .str zip, .str grp, .str af]) =
      encodeNum {} CardDemo.Cbact01c.ARR_ACCT_ID.fmt id ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_CYC_DEBIT.fmt 100500 ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_CYC_DEBIT.fmt 152500 ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_BAL.fmt (-102500) ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_CYC_DEBIT.fmt (-250000) ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_BAL.fmt 0 ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_CYC_DEBIT.fmt 0 ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_BAL.fmt 0 ++
      (encodeNum {} CardDemo.Cbact01c.ARR_ACCT_CURR_CYC_DEBIT.fmt 0 ++ (sp 4 ++ []))))))))))) :=
    rfl
  rw [e]
  simp [CardDemo.Cbact01c.arrRec, acctOf, aId, aBal, numOf, sp, List.append_assoc]

theorem arrVals_valid {A : List FVal} (hA : AccountRecord.Valid A) :
    ArrArrayRec.Valid (arrVals A) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, hid, hid0, -, hbal, -⟩ :=
    acct_shape hA
  exact .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hid, fun _ => hid0⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hbal, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hbal, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨⟨_, rfl⟩, by simp [sp]⟩ .nil)))))))))))

theorem decode_arrRec {A : List FVal} (hA : AccountRecord.Valid A) :
    ArrArrayRec.decode (CardDemo.Cbact01c.arrRec (acctOf A)) = some (arrVals A) := by
  rw [← arrVals_encode hA]
  exact Schema.decode_encode (by decide) (arrVals_valid hA)

theorem vb1_valid {A : List FVal} (hA : AccountRecord.Valid A) : VbrcRec1.Valid (vb1 A) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, hid, hid0, hs, -⟩ :=
    acct_shape hA
  exact .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hid, fun _ => hid0⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, hs⟩ .nil)

theorem vb2_valid {A : List FVal} (hA : AccountRecord.Valid A) : VbrcRec2.Valid (vb2 A) := by
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, hid, hid0, -, hbal, hcl, -,
    -, -, hrd, -⟩ := acct_shape hA
  exact .cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hid, fun _ => hid0⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hbal, fun h => by cases h⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, (holds_display rfl).2 ⟨hcl, fun h => by cases h⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, by simp [aReissue, strOf, hrd]⟩ .nil)))

/-- The text of VBRC-REC1 is that of coblean's record. -/
theorem vb1_text {A : List FVal} (hA : AccountRecord.Valid A) :
    VbrcRec1.textS (vb1 A) = (CardDemo.Cbact01c.vb1 (acctOf A)).map cp037Code := by
  rw [Schema.textS_eq (by decide) (vb1_valid hA)]
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, -⟩ := acct_shape hA
  have e : VbrcRec1.encode (vb1 [.num id, .str s, .num bal, .num cl, .num ccl, .str od, .str ed,
      .str rd, .num cc, .num d, .str zip, .str grp, .str af]) =
      encodeNum {} CardDemo.Cbact01c.VB1_ACCT_ID.fmt id ++ (s ++ []) := rfl
  rw [e]
  simp [CardDemo.Cbact01c.vb1, acctOf, aId, aStatus, strOf, numOf]

/-- The text of VBRC-REC2 is that of coblean's record. -/
theorem vb2_text {A : List FVal} (hA : AccountRecord.Valid A) :
    VbrcRec2.textS (vb2 A) = (CardDemo.Cbact01c.vb2 (acctOf A)).map cp037Code := by
  rw [Schema.textS_eq (by decide) (vb2_valid hA)]
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, -⟩ := acct_shape hA
  have e : VbrcRec2.encode (vb2 [.num id, .str s, .num bal, .num cl, .num ccl, .str od, .str ed,
      .str rd, .num cc, .num d, .str zip, .str grp, .str af]) =
      encodeNum {} CardDemo.Cbact01c.VB2_ACCT_ID.fmt id ++
      (encodeNum {} CardDemo.Cbact01c.VB2_ACCT_CURR_BAL.fmt bal ++
      (encodeNum {} CardDemo.Cbact01c.VB2_ACCT_CREDIT_LIMIT.fmt cl ++ (rd.take 4 ++ []))) := rfl
  rw [e]
  simp [CardDemo.Cbact01c.vb2, acctOf, aId, aBal, aLimit, aReissue, strOf, numOf]

/-! ## The lines displayed -/

theorem lblId_text : CardDemo.Cbact01c.lblId.map cp037Code = txt "ACCT-ID                 :" := by
  decide +kernel
theorem lblStatus_text :
    CardDemo.Cbact01c.lblStatus.map cp037Code = txt "ACCT-ACTIVE-STATUS      :" := by decide +kernel
theorem lblBal_text :
    CardDemo.Cbact01c.lblBal.map cp037Code = txt "ACCT-CURR-BAL           :" := by decide +kernel
theorem lblLimit_text :
    CardDemo.Cbact01c.lblLimit.map cp037Code = txt "ACCT-CREDIT-LIMIT       :" := by decide +kernel
theorem lblCash_text :
    CardDemo.Cbact01c.lblCash.map cp037Code = txt "ACCT-CASH-CREDIT-LIMIT  :" := by decide +kernel
theorem lblOpen_text :
    CardDemo.Cbact01c.lblOpen.map cp037Code = txt "ACCT-OPEN-DATE          :" := by decide +kernel
theorem lblExp_text :
    CardDemo.Cbact01c.lblExp.map cp037Code = txt "ACCT-EXPIRAION-DATE     :" := by decide +kernel
theorem lblReis_text :
    CardDemo.Cbact01c.lblReis.map cp037Code = txt "ACCT-REISSUE-DATE       :" := by decide +kernel
theorem lblCc_text :
    CardDemo.Cbact01c.lblCc.map cp037Code = txt "ACCT-CURR-CYC-CREDIT    :" := by decide +kernel
theorem lblCd_text :
    CardDemo.Cbact01c.lblCd.map cp037Code = txt "ACCT-CURR-CYC-DEBIT     :" := by decide +kernel
theorem lblGrp_text :
    CardDemo.Cbact01c.lblGrp.map cp037Code = txt "ACCT-GROUP-ID           :" := by decide +kernel
theorem dashes_text : CardDemo.Cbact01c.dashes.map cp037Code =
    txt "-------------------------------------------------" := by decide +kernel
theorem vb1Lbl_text : CardDemo.Cbact01c.vb1Lbl.map cp037Code = txt "VBRC-REC1:" := by decide +kernel
theorem vb2Lbl_text : CardDemo.Cbact01c.vb2Lbl.map cp037Code = txt "VBRC-REC2:" := by decide +kernel
theorem startMsg_text : CardDemo.Cbact01c.startMsg.map cp037Code =
    txt "START OF EXECUTION OF PROGRAM CBACT01C" := by decide +kernel
theorem endMsg_text : CardDemo.Cbact01c.endMsg.map cp037Code =
    txt "END OF EXECUTION OF PROGRAM CBACT01C" := by decide +kernel

/-- The text of a field of a valid account record is the CP037 text of its bytes. -/
theorem fld_eq {A : List FVal} (hA : AccountRecord.Valid A) (k : Nat)
    (hk : k < AccountRecord.fields.length) :
    fld A k = ((AccountRecord.fields.getD k default).encode (A.getD k default)).map cp037Code := by
  have hd : ∀ f ∈ AccountRecord.fields, DisplayNumeric f := by decide
  exact fieldTextS_eq (hd _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]))
    (Forall2.getD hA k (by simpa using hk))

/-- The lines coblean's events display for an account record are `lines`. -/
theorem step_lines {A : List FVal} (hA : AccountRecord.Valid A) :
    [CardDemo.Cbact01c.lblId ++ encodeNum {} CardDemo.Cbact01c.ACCT_ID.fmt (acctOf A).id,
      CardDemo.Cbact01c.lblStatus ++ (acctOf A).st,
      CardDemo.Cbact01c.lblBal ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_BAL.fmt (acctOf A).bal,
      CardDemo.Cbact01c.lblLimit ++
        encodeNum {} CardDemo.Cbact01c.ACCT_CREDIT_LIMIT.fmt (acctOf A).limit,
      CardDemo.Cbact01c.lblCash ++
        encodeNum {} CardDemo.Cbact01c.ACCT_CASH_CREDIT_LIMIT.fmt (acctOf A).cash,
      CardDemo.Cbact01c.lblOpen ++ (acctOf A).openDt, CardDemo.Cbact01c.lblExp ++ (acctOf A).exp,
      CardDemo.Cbact01c.lblReis ++ (acctOf A).reis,
      CardDemo.Cbact01c.lblCc ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_CREDIT.fmt (acctOf A).cc,
      CardDemo.Cbact01c.lblCd ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_DEBIT.fmt (acctOf A).cd,
      CardDemo.Cbact01c.lblGrp ++ (acctOf A).grp, CardDemo.Cbact01c.dashes,
      CardDemo.Cbact01c.vb1Lbl ++ CardDemo.Cbact01c.vb1 (acctOf A),
      CardDemo.Cbact01c.vb2Lbl ++ CardDemo.Cbact01c.vb2 (acctOf A), (acctOf A).bytes].map
      (·.map cp037Code) = lines A := by
  have hb := acctOf_bytes hA
  have h1 := vb1_text hA
  have h2 := vb2_text hA
  have ht := Schema.textS_eq (s := AccountRecord) (by decide) hA
  simp only [lines, fld_eq hA _ (by decide : 0 < 13), fld_eq hA _ (by decide : 1 < 13),
    fld_eq hA _ (by decide : 2 < 13), fld_eq hA _ (by decide : 3 < 13),
    fld_eq hA _ (by decide : 4 < 13), fld_eq hA _ (by decide : 5 < 13),
    fld_eq hA _ (by decide : 6 < 13), fld_eq hA _ (by decide : 7 < 13),
    fld_eq hA _ (by decide : 8 < 13), fld_eq hA _ (by decide : 9 < 13),
    fld_eq hA _ (by decide : 11 < 13), h1, h2, ht, ← hb, List.map_cons, List.map_nil,
    List.map_append, lblId_text, lblStatus_text, lblBal_text, lblLimit_text, lblCash_text,
    lblOpen_text, lblExp_text, lblReis_text, lblCc_text, lblCd_text, lblGrp_text, dashes_text,
    vb1Lbl_text, vb2Lbl_text]
  obtain ⟨id, s, bal, cl, ccl, od, ed, rd, cc, d, zip, grp, af, rfl, -⟩ := acct_shape hA
  rfl

/-! ## The simulation -/

/-- The lines displayed by the events `l` (oldest first). -/
def dispL (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .display bs => some bs | _ => none

/-- The records written to file `f` by the events `l`. -/
def wrL (f : Nat) (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .write g bs => if g = f then some bs else none | _ => none

theorem dispL_append (l l' : List Event) : dispL (l ++ l') = dispL l ++ dispL l' := by
  simp [dispL, List.filterMap_append]
theorem wrL_append (f : Nat) (l l' : List Event) : wrL f (l ++ l') = wrL f l ++ wrL f l' := by
  simp [wrL, List.filterMap_append]
theorem dispL_display (bs : List UInt8) (l : List Event) :
    dispL (.display bs :: l) = bs :: dispL l := rfl
theorem wrL_display (f : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.display bs :: l) = wrL f l := rfl
theorem dispL_nil : dispL [] = [] := rfl
theorem wrL_nil (f : Nat) : wrL f [] = [] := rfl

/-- The events of one account record, oldest first. -/
theorem step_out (rf : List UInt8) (s : CardDemo.Cbact01c.Model) (a : Acct) :
    (CardDemo.Cbact01c.step rf s a).out.reverse = s.out.reverse ++
      [.display (CardDemo.Cbact01c.lblId ++ encodeNum {} CardDemo.Cbact01c.ACCT_ID.fmt a.id),
        .display (CardDemo.Cbact01c.lblStatus ++ a.st),
        .display (CardDemo.Cbact01c.lblBal ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_BAL.fmt a.bal),
        .display (CardDemo.Cbact01c.lblLimit ++
          encodeNum {} CardDemo.Cbact01c.ACCT_CREDIT_LIMIT.fmt a.limit),
        .display (CardDemo.Cbact01c.lblCash ++
          encodeNum {} CardDemo.Cbact01c.ACCT_CASH_CREDIT_LIMIT.fmt a.cash),
        .display (CardDemo.Cbact01c.lblOpen ++ a.openDt), .display (CardDemo.Cbact01c.lblExp ++ a.exp),
        .display (CardDemo.Cbact01c.lblReis ++ a.reis),
        .display (CardDemo.Cbact01c.lblCc ++
          encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_CREDIT.fmt a.cc),
        .display (CardDemo.Cbact01c.lblCd ++
          encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_DEBIT.fmt a.cd),
        .display (CardDemo.Cbact01c.lblGrp ++ a.grp), .display CardDemo.Cbact01c.dashes,
        .call "COBDATFT", .write 2 (CardDemo.Cbact01c.outRec rf (CardDemo.Cbact01c.step rf s a).cd a),
        .write 3 (CardDemo.Cbact01c.arrRec a),
        .display (CardDemo.Cbact01c.vb1Lbl ++ CardDemo.Cbact01c.vb1 a),
        .display (CardDemo.Cbact01c.vb2Lbl ++ CardDemo.Cbact01c.vb2 a),
        .write 4 (CardDemo.Cbact01c.vb1 a), .write 4 (CardDemo.Cbact01c.vb2 a), .display a.bytes] := by
  simp [CardDemo.Cbact01c.step]

/-- The lines one account record displays. -/
theorem step_disp (rf : List UInt8) (s : CardDemo.Cbact01c.Model) (a : Acct) :
    dispL (CardDemo.Cbact01c.step rf s a).out.reverse = dispL s.out.reverse ++
    [CardDemo.Cbact01c.lblId ++ encodeNum {} CardDemo.Cbact01c.ACCT_ID.fmt a.id,
      CardDemo.Cbact01c.lblStatus ++ a.st,
      CardDemo.Cbact01c.lblBal ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_BAL.fmt a.bal,
      CardDemo.Cbact01c.lblLimit ++ encodeNum {} CardDemo.Cbact01c.ACCT_CREDIT_LIMIT.fmt a.limit,
      CardDemo.Cbact01c.lblCash ++ encodeNum {} CardDemo.Cbact01c.ACCT_CASH_CREDIT_LIMIT.fmt a.cash,
      CardDemo.Cbact01c.lblOpen ++ a.openDt, CardDemo.Cbact01c.lblExp ++ a.exp,
      CardDemo.Cbact01c.lblReis ++ a.reis,
      CardDemo.Cbact01c.lblCc ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_CREDIT.fmt a.cc,
      CardDemo.Cbact01c.lblCd ++ encodeNum {} CardDemo.Cbact01c.ACCT_CURR_CYC_DEBIT.fmt a.cd,
      CardDemo.Cbact01c.lblGrp ++ a.grp, CardDemo.Cbact01c.dashes,
      CardDemo.Cbact01c.vb1Lbl ++ CardDemo.Cbact01c.vb1 a,
      CardDemo.Cbact01c.vb2Lbl ++ CardDemo.Cbact01c.vb2 a, a.bytes] := by
  rw [step_out, dispL_append]
  rfl

/-- The records one account record writes. -/
theorem step_wr2 (rf : List UInt8) (s : CardDemo.Cbact01c.Model) (a : Acct) :
    wrL 2 (CardDemo.Cbact01c.step rf s a).out.reverse = wrL 2 s.out.reverse ++
      [CardDemo.Cbact01c.outRec rf (CardDemo.Cbact01c.step rf s a).cd a] := by
  rw [step_out, wrL_append]
  rfl
theorem step_wr3 (rf : List UInt8) (s : CardDemo.Cbact01c.Model) (a : Acct) :
    wrL 3 (CardDemo.Cbact01c.step rf s a).out.reverse = wrL 3 s.out.reverse ++
      [CardDemo.Cbact01c.arrRec a] := by
  rw [step_out, wrL_append]
  rfl
theorem step_wr4 (rf : List UInt8) (s : CardDemo.Cbact01c.Model) (a : Acct) :
    wrL 4 (CardDemo.Cbact01c.step rf s a).out.reverse = wrL 4 s.out.reverse ++
      [CardDemo.Cbact01c.vb1 a, CardDemo.Cbact01c.vb2 a] := by
  rw [step_out, wrL_append]
  rfl

/-- The translations' state `S` after the same account records as coblean's model state `M`:
coblean's bytes of `OUT-ACCT-CURR-CYC-DEBIT` encode the translations' value, and the outputs are
those of `M`'s events. -/
structure Corr (S : St) (M : CardDemo.Cbact01c.Model) : Prop where
  cd : M.cd = encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt S.cd
  cdb : S.cd.natAbs < 1000000000000
  disp : S.disp = txt "START OF EXECUTION OF PROGRAM CBACT01C" ::
    (dispL M.out.reverse).map (·.map cp037Code)
  outW : (wrL 2 M.out.reverse).map OutAcctRec.decode = S.outWrites.map some
  arryW : (wrL 3 M.out.reverse).map ArrArrayRec.decode = S.arryWrites.map some
  vbrcW : (wrL 4 M.out.reverse).map (·.map cp037Code) = S.vbrcWrites

/-- **One account record**: the translations' step and coblean's `step` keep `Corr`. -/
theorem step_corr {S : St} {M : CardDemo.Cbact01c.Model} {A : List FVal} (hC : Corr S M)
    (hA : AccountRecord.Valid A) :
    Corr (Model.step S A) (CardDemo.Cbact01c.step (sp 2) M (acctOf A)) := by
  obtain ⟨hcd, hcdb, hdisp, hout, harr, hvb⟩ := hC
  have hcd' : (CardDemo.Cbact01c.step (sp 2) M (acctOf A)).cd =
      encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt (Model.step S A).cd := by
    by_cases h : aCycDebit A = 0
    · simp [CardDemo.Cbact01c.step, Model.step, acctOf, h]
    · simp [CardDemo.Cbact01c.step, Model.step, acctOf, h, hcd]
  have hcdb' : (Model.step S A).cd.natAbs < 1000000000000 := by
    by_cases h : aCycDebit A = 0
    · simp [Model.step, h]
    · simp [Model.step, h, hcdb]
  refine ⟨hcd', hcdb', ?_, ?_, ?_, ?_⟩
  · rw [step_disp, List.map_append, step_lines hA]
    simp only [Model.step, hdisp, List.cons_append]
  · rw [step_wr2, List.map_append, hout, hcd', List.map_singleton, decode_outRec hA hcdb']
    simp [Model.step]
  · rw [step_wr3, List.map_append, harr, List.map_singleton, decode_arrRec hA]
    simp [Model.step]
  · rw [step_wr4, List.map_append, hvb]
    simp [Model.step, vb1_text hA, vb2_text hA]

/-- The account records `ts`, from corresponding states. -/
theorem fold_corr : ∀ (ts : List (List FVal)) (S : St) (M : CardDemo.Cbact01c.Model), Corr S M →
    (∀ t ∈ ts, AccountRecord.Valid t) →
    Corr (ts.foldl Model.step S) (ts.foldl (fun m t => CardDemo.Cbact01c.step (sp 2) m (acctOf t)) M)
  | [], _, _, hC, _ => hC
  | t :: ts, _, _, hC, ht =>
    fold_corr ts _ _ (step_corr hC (ht t (by simp))) (fun t' h' => ht t' (by simp [h']))

/-! ## The COBOL run -/

cobol_mem_hex initMem from "init_mem.hex"

set_option maxRecDepth 10000 in
theorem initMem_size : initMem.size = 1071 := by rfl

/-- The harness storage holds spaces in the two characters of COBDATFT's output date after the
eight it sets, and a packed zero in `OUT-ACCT-CURR-CYC-DEBIT`. -/
theorem initMem_rf : initMem.read 927 2 = sp 2 := by decide +kernel
theorem initMem_cd :
    initMem.read 390 7 = encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt 0 := by
  decide +kernel

/-- The state before the first record. -/
theorem init_corr :
    Corr Model.init ⟨encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt 0, []⟩ :=
  ⟨rfl, by decide, rfl, rfl, rfl, rfl⟩

/-- **CBACT01C's COBOL run outputs what `Model.run` says**, for every account file of valid
records: the run ends with GOBACK; its displays (code points), the records it writes to OUT-FILE
and ARRY-FILE (decoded) and to VBRC-FILE (as text) are `Model.run`'s. -/
theorem cobol_outputs (vals1 : List (List FVal)) (hv1 : ∀ v ∈ vals1, AccountRecord.Valid v)
    (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbact01c.run { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])
    let o := Model.run vals1
    r.1 = .stop .goback ∧ (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 2 r.2).map OutAcctRec.decode = o.outWrites.map some ∧
      (writes 3 r.2).map ArrArrayRec.decode = o.arryWrites.map some ∧
      (writes 4 r.2).map (·.map cp037Code) = o.vbrcWrites := by
  dsimp only
  have hf : vals1.map AccountRecord.encode = (vals1.map acctOf).map Acct.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun a ha => (acctOf_bytes (hv1 a ha)).symm)
  have hx := CardDemo.Cbact01c.cbact01c_extracts initMem initMem_size (vals1.map acctOf)
    (by intro a ha; obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha; exact acctOf_valid (hv1 a0 ha0))
    n (by rw [List.length_map]; exact hn)
  simp only [initMem_rf, initMem_cd, ← hf, CardDemo.Cbact01c.model, List.foldl_map] at hx
  obtain ⟨hstop, hout⟩ := hx
  have hC := fold_corr vals1 _ _ init_corr hv1
  simp only [Model.run]
  generalize vals1.foldl (fun m t => CardDemo.Cbact01c.step (sp 2) m (acctOf t))
    ⟨encodeNum {} CardDemo.Cbact01c.OUT_ACCT_CURR_CYC_DEBIT.fmt 0, []⟩ = M at hC hout
  generalize vals1.foldl Model.step Model.init = S at hC
  refine ⟨hstop, ?_, ?_, ?_, ?_⟩
  · show (dispL _).map _ = _
    rw [hout, hC.disp]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, dispL_display, dispL_append, dispL_nil, List.map_append, List.map_cons,
      List.map_nil, startMsg_text, endMsg_text]
  · show (wrL 2 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, wrL_display, wrL_append, wrL_nil, List.append_nil]
    exact hC.outW
  · show (wrL 3 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, wrL_display, wrL_append, wrL_nil, List.append_nil]
    exact hC.arryW
  · show (wrL 4 _).map _ = _
    rw [hout]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, wrL_display, wrL_append, wrL_nil, List.append_nil]
    exact hC.vbrcW

end EquivLean.Modernize.Cbact01c.Glue
