import EquivLean.Modernize.Cbact01c.RustRun3
import EquivLean.Modernize.Cbact01c.RustProof

/-!
# CBACT01C → Rust: the equation of `run` (`RunSpec`), hence the generated statement

* `run_bytes_eq` (`RustRun3.lean`): `run` outputs the fold `rfold` over the account structs, in
  Latin-1 bytes.
* The glue (`corr_step`, `corr_fold`): after each record, the bytes are the model's outputs
  (`Model.step` on the struct's field values): a numeric field shows its low digits, the last one
  overpunched when signed (`zonedText_unsigned`, `zonedText_signed`), an alphanumeric field's
  Latin-1 bytes are the CP037 text of its EBCDIC bytes (`latin1_text`), the copy's reissue date is
  the model's `reissueOut`, the cycle debit is carried as in the model.
* `run_spec : RunSpec`, and `rust : Statement`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Rust

/-! ## Texts -/

theorem zonedText_unsigned (v : Int) (n : Nat) :
    (zonedText v n false).map UScalar.val = zpad n v.natAbs := by
  simp only [zonedText, Bool.false_eq_true, _root_.ite_false, zeroPad_val]

theorem zonedText_signed (v : Int) (n : Nat) :
    (zonedText v n true).map UScalar.val =
      zpad (n - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)] := by
  simp only [zonedText, _root_.ite_true, List.map_append, zeroPad_val, List.map_cons,
    List.map_nil]
  rw [byteOf_val _ (overpunch_lt _ _ (Nat.mod_lt _ (by norm_num)))]

theorem lines_const :
    lblId.map UScalar.val = Model.txt "ACCT-ID                 :" ∧
    lblStatus.map UScalar.val = Model.txt "ACCT-ACTIVE-STATUS      :" ∧
    lblBal.map UScalar.val = Model.txt "ACCT-CURR-BAL           :" ∧
    lblLimit.map UScalar.val = Model.txt "ACCT-CREDIT-LIMIT       :" ∧
    lblCash.map UScalar.val = Model.txt "ACCT-CASH-CREDIT-LIMIT  :" ∧
    lblOpen.map UScalar.val = Model.txt "ACCT-OPEN-DATE          :" ∧
    lblExp.map UScalar.val = Model.txt "ACCT-EXPIRAION-DATE     :" ∧
    lblReis.map UScalar.val = Model.txt "ACCT-REISSUE-DATE       :" ∧
    lblCc.map UScalar.val = Model.txt "ACCT-CURR-CYC-CREDIT    :" ∧
    lblCd.map UScalar.val = Model.txt "ACCT-CURR-CYC-DEBIT     :" ∧
    lblGrp.map UScalar.val = Model.txt "ACCT-GROUP-ID           :" ∧
    dashes.map UScalar.val = Model.txt "-------------------------------------------------" ∧
    vb1Lbl.map UScalar.val = Model.txt "VBRC-REC1:" ∧ vb2Lbl.map UScalar.val = Model.txt "VBRC-REC2:" ∧
    startLine.map UScalar.val = Model.txt "START OF EXECUTION OF PROGRAM CBACT01C" ∧
    endLine.map UScalar.val = Model.txt "END OF EXECUTION OF PROGRAM CBACT01C" := by
  decide +kernel

/-- The text of each field of an account record, as the model displays it. -/
theorem fld_eq (a : cbact01c.AccountRecord) :
    Model.fld (AccountRecord.vals a) 0 = zpad 11 a.acct_id.val.natAbs ∧
    Model.fld (AccountRecord.vals a) 1 = a.acct_active_status.val.map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 2 = (zonedText a.acct_curr_bal.val 12 true).map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 3 =
      (zonedText a.acct_credit_limit.val 12 true).map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 4 =
      (zonedText a.acct_cash_credit_limit.val 12 true).map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 5 = a.acct_open_date.val.map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 6 = a.acct_expiraion_date.val.map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 7 = a.acct_reissue_date.val.map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 8 =
      (zonedText a.acct_curr_cyc_credit.val 12 true).map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 9 =
      (zonedText a.acct_curr_cyc_debit.val 12 true).map UScalar.val ∧
    Model.fld (AccountRecord.vals a) 11 = a.acct_group_id.val.map UScalar.val := by
  simp only [zonedText_signed]
  refine ⟨rfl, latin1_text _, rfl, rfl, rfl, latin1_text _, latin1_text _, latin1_text _, rfl, rfl,
    latin1_text _⟩

/-- Unfolding a record's text field by field. -/
theorem textS_cons (n t : String) (l : Nat) (f : Field) (fs : List Field) (v : FVal)
    (vs : List FVal) :
    Schema.textS ⟨n, t, l, f :: fs⟩ (v :: vs) = fieldTextS f v ++ Schema.textS ⟨n, t, l, fs⟩ vs := by
  simp [Schema.textS]

theorem textS_nil (n t : String) (l : Nat) (vs : List FVal) : Schema.textS ⟨n, t, l, []⟩ vs = [] := by
  simp [Schema.textS]

theorem vb1_text (a : cbact01c.AccountRecord) :
    Model.VbrcRec1.textS (Model.vb1 (AccountRecord.vals a)) = (vbrc1 a).map UScalar.val := by
  simp only [Model.vb1, Model.aId, Model.aStatus, AccountRecord.vals, Model.numOf, Model.strOf,
    List.getD_cons_zero, List.getD_cons_succ, vbrc1, List.map_append, zonedText_unsigned,
    Model.VbrcRec1, textS_cons, textS_nil, fieldTextS, Bool.false_eq_true, _root_.ite_false,
    latin1_text, List.append_nil]

theorem vb2_text (a : cbact01c.AccountRecord) :
    Model.VbrcRec2.textS (Model.vb2 (AccountRecord.vals a)) = (vbrc2 a).map UScalar.val := by
  simp only [Model.vb2, Model.aId, Model.aBal, Model.aLimit, Model.aReissue, AccountRecord.vals,
    Model.numOf, Model.strOf, List.getD_cons_zero, List.getD_cons_succ, vbrc2, List.map_append,
    zonedText_unsigned, zonedText_signed, Model.VbrcRec2, textS_cons, textS_nil, fieldTextS,
    Bool.false_eq_true, _root_.ite_false, _root_.ite_true, ← List.map_take, latin1_text,
    List.append_nil, List.append_assoc, Nat.reduceSub]

theorem rec_text (a : cbact01c.AccountRecord) :
    Model.AccountRecord.textS (AccountRecord.vals a) = (recText a).map UScalar.val := by
  simp only [AccountRecord.vals, recText, List.map_append, zonedText_unsigned, zonedText_signed,
    Model.AccountRecord, textS_cons, textS_nil, fieldTextS, Bool.false_eq_true, _root_.ite_false,
    _root_.ite_true, latin1_text, List.append_nil, List.append_assoc, Nat.reduceSub]

theorem lines_eq (a : cbact01c.AccountRecord) :
    (recLines a).map (·.map UScalar.val) = Model.lines (AccountRecord.vals a) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, -, -⟩ := lines_const
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f11⟩ := fld_eq a
  simp only [recLines, Model.lines, List.map_cons, List.map_nil, List.map_append, l1, l2, l3, l4,
    l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f11,
    zonedText_unsigned, vb1_text, vb2_text, rec_text]

theorem ebc_space : ebcdicOfLatin1 32 = 64 := by decide +kernel

theorem out_eq (a : cbact01c.AccountRecord) (cd : I64) :
    OutAcctRec.vals (outRec a cd) = Model.outVals (AccountRecord.vals a) cd.val := by
  simp only [OutAcctRec.vals, outRec, Model.outVals, AccountRecord.vals, List.getD_cons_zero,
    List.getD_cons_succ, Model.reissueOut, Model.aReissue, Model.strOf, Array.from_val, picks,
    List.map_append, List.map_take, List.map_drop, List.map_cons, List.map_nil, Model.sp,
    UScalar.ofNatCore_val_eq, ebc_space, List.append_assoc,
    List.replicate_succ, List.replicate_zero]

theorem arr_eq (a : cbact01c.AccountRecord) :
    ArrArrayRec.vals (arrRec a) = Model.arrVals (AccountRecord.vals a) := by
  simp only [ArrArrayRec.vals, arrRec, Model.arrVals, Model.aId, Model.aBal, AccountRecord.vals,
    Model.numOf, List.getD_cons_zero, List.getD_cons_succ, Array.from_val, List.map_cons,
    List.map_nil, Model.sp, ebc_space, uscalar_ofNat_val, 
    IScalar.ofInt_val_eq, List.replicate_succ, List.replicate_zero]

/-- `run`'s state in bytes against the model's state. -/
def Corr (s : RSt) (m : Model.St) : Prop :=
  s.cd.val = m.cd ∧ s.disp.map (·.map UScalar.val) = m.disp ∧
    s.outs.map OutAcctRec.vals = m.outWrites ∧ s.arrs.map ArrArrayRec.vals = m.arryWrites ∧
    s.vbrcs.map (·.map UScalar.val) = m.vbrcWrites

theorem corr_step (s : RSt) (m : Model.St) (a : cbact01c.AccountRecord) (h : Corr s m) :
    Corr (rstep s a) (Model.step m (AccountRecord.vals a)) := by
  obtain ⟨hcd, hd, ho, ha, hv⟩ := h
  have hc : (if a.acct_curr_cyc_debit = 0#i64 then 252500#i64 else s.cd).val =
      (if Model.aCycDebit (AccountRecord.vals a) = 0 then 252500 else m.cd) := by
    simp only [Model.aCycDebit, AccountRecord.vals, List.getD_cons_zero, List.getD_cons_succ,
      Model.numOf]
    by_cases h0 : a.acct_curr_cyc_debit.val = 0
    · have : a.acct_curr_cyc_debit = 0#i64 := IScalar.eq_of_val_eq (by simp [h0])
      simp [this]
    · have : ¬ a.acct_curr_cyc_debit = 0#i64 := fun h => h0 (by simp [h])
      simp [this, h0, hcd]
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · simp only [rstep, Model.step, List.map_append, hd, lines_eq]
  · simp only [rstep, Model.step, List.map_append, ho, List.map_cons, List.map_nil, out_eq, hc]
  · simp only [rstep, Model.step, List.map_append, ha, List.map_cons, List.map_nil, arr_eq]
  · simp only [rstep, Model.step, List.map_append, hv, List.map_cons, List.map_nil, vb1_text,
      vb2_text]

theorem corr_fold (l : List cbact01c.AccountRecord) :
    Corr (rfold l) ((l.map AccountRecord.vals).foldl Model.step Model.init) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, ?_, rfl, rfl, rfl⟩
    simp only [rfold, List.foldl_nil, rinit, Model.init, List.map_cons, List.map_nil]
    exact congrArg (fun x => [x]) lines_const.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | append_singleton l a ih =>
    simp only [rfold, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
      List.map_cons, List.map_nil] at *
    exact corr_step _ _ a ih

/-! ## The equation of `run` -/

/-- **The equation of `run`** (`RunSpec` of `RustSpec.lean`). -/
theorem run_spec : RunSpec := by
  intro s1 vals1 hs _hv hn
  dsimp only
  have hl : s1.val.length = vals1.length := by rw [← hs, List.length_map]
  have hU : 4294967295 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega
  have hlen : 15 * s1.val.length + 2 < Usize.max := by omega
  obtain ⟨out, hrun, hd, ho, ha, hvb, hab⟩ := run_bytes_eq s1 hU hlen
  obtain ⟨-, hcd, hco, hca, hcv⟩ := corr_fold s1.val
  rw [hs] at hcd hco hca hcv
  refine ⟨out, hrun, ?_, ?_, ?_, ?_, hab⟩
  · have := congrArg (List.map (List.map UScalar.val)) hd
    simp only [List.map_map, List.map_append, List.map_cons, List.map_nil] at this
    rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
      (fun l => l.val.map UScalar.val) from rfl] at this
    rw [this, hcd, lines_const.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    simp only [Model.run]
  · rw [ho, hco]
    simp only [Model.run]
  · rw [ha, hca]
    simp only [Model.run]
  · have := congrArg (List.map (List.map UScalar.val)) hvb
    simp only [List.map_map] at this
    rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
      (fun l => l.val.map UScalar.val) from rfl] at this
    rw [this, hcv]
    simp only [Model.run]

/-- **CBACT01C → Rust, every input.** -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbact01c.Rust

#print axioms EquivLean.Modernize.Cbact01c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbact01c.Rust.rust
