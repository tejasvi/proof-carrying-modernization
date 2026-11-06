import EquivLean.Modernize.Cbtrn02c.RustRun6
import EquivLean.Modernize.Cbtrn02c.ModelAny

/-!
# CBTRN02C → Rust on any input: the loop body at a repeated transaction id

A posted transaction whose id is already in the transaction file (`run_loop2_loop5` /
`run_loop2_loop8`, the duplicate checks of `2900-WRITE-TRANSACTION-FILE`, return true): the body
returns `done` with the outputs of `Model.runX` at the stop (`stopOut (dupSt ..)`): the category
balance and the account updated, the transaction record not written, the error line, the status
line `22` and `ABENDING PROGRAM` displayed, `abended` set.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-- `ERROR WRITING TO TRANSACTION FILE` (Latin-1). -/
def errWriteR : List U8 := [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 87#u8, 82#u8, 73#u8, 84#u8,
  73#u8, 78#u8, 71#u8, 32#u8, 84#u8, 79#u8, 32#u8, 84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8, 67#u8,
  84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 70#u8, 73#u8, 76#u8, 69#u8]

theorem dupLines_text : [errWriteR.map UScalar.val, (statusBytes 50#u8).map UScalar.val,
    abendBytes.map UScalar.val] = Model.dupLines := by decide

/-- The outputs of the Rust run are the model's. -/
def OutRel (out : cbtrn02c.Output) (o : Model.OutX) : Prop :=
  out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
    out.transact_file_writes.val.map TranRecord.vals = o.tranW ∧
    out.dalyrejs_file_writes.val.map RejectRecord.vals = o.rejW ∧
    out.account_file_rewrites.val.map AccountRecord.vals = o.acctRW ∧
    out.tcatbal_file_writes.val.map TranCatBalRecord.vals = o.catW ∧
    out.tcatbal_file_rewrites.val.map TranCatBalRecord.vals = o.catRW ∧
    out.return_code.val = o.rc ∧ out.abended = o.abended

/-- The outputs of `Model.runX` when the run stops at a duplicate id. -/
def stopOut (s : Model.St) : Model.OutX :=
  { disp := s.disp, tranW := s.tranW, rejW := s.rejW, catW := s.catW, acctRW := s.acctRW,
    catRW := s.catRW, rc := 0, abended := true }

/-- The state at the abend: `s'` (the transaction posted) without its transaction record, with the
abend lines. -/
def dupSt (s s' : Model.St) : Model.St :=
  { s' with tranW := s.tranW, disp := s'.disp ++ Model.dupLines }

theorem display_io_status_22 (out : cbtrn02c.Output) (h : out.displays.val.length < Usize.max) :
    cbtrn02c.display_io_status out (Std.Array.repeat 2#usize 50#u8) = .ok { out with
      displays := alloc.vec.Vec.from (out.displays.val ++ [alloc.vec.Vec.from (statusBytes 50#u8)
        (by have := usize_max_ge; simp [statusBytes]; omega)]) (by simp; omega) } :=
  display_io_status_eq out _ 50#u8 (by simp [Std.Array.repeat_val]) (by decide) h

set_option maxHeartbeats 4000000 in
/-- **A posted transaction with a repeated id, new category key.** -/
theorem body_post_create_dup (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64) (s : Model.St)
    (hrel : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s) (hri : RInv accounts tcatbals)
    (hpos : pos.val < file.val.length) (x : cbtrn02c.CardXrefRecord) (a : cbtrn02c.AccountRecord)
    (ja : Nat) (hja : ja < accounts.val.length) (haj : accounts.val[ja] = a)
    (hfa : accounts.val.findIdx (fun b => b.acct_id.val == a.acct_id.val) = ja)
    (hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
      .ok (file.val[pos.val], x, true))
    (has : cbtrn02c.run_loop2_loop1 accounts ar 0#usize x.xref_acct_id = .ok (a, true))
    (hamt : -100000000000 < (file.val[pos.val]).dalytran_amt.val ∧
      (file.val[pos.val]).dalytran_amt.val < 100000000000)
    (hexp : geEbc a.acct_expiraion_date.val (file.val[pos.val]).dalytran_orig_ts.val 10 = true)
    (hlim : Int.tmod (a.acct_curr_cyc_credit.val - a.acct_curr_cyc_debit.val +
      (file.val[pos.val]).dalytran_amt.val) 100000000000 ≤ a.acct_credit_limit.val)
    (hcs : cbtrn02c.run_loop2_loop2 tcatbals tcr 0#usize x.xref_acct_id
      (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd = .ok (tcr, false))
    (hdup : cbtrn02c.run_loop2_loop3 tcatbals x.xref_acct_id (file.val[pos.val]).dalytran_type_cd
      (file.val[pos.val]).dalytran_cat_cd 0#usize = .ok false)
    (hai : cbtrn02c.run_loop2_loop4 accounts a.acct_id 0#usize = .ok (usz ja, true))
    (htd : cbtrn02c.run_loop2_loop5 v1 (file.val[pos.val]).dalytran_id 0#usize = .ok true)
    (hnone : Model.findCat s.cats (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals file.val[pos.val]))
      (Model.tCat (DalytranRecord.vals file.val[pos.val])) = none)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9)
    (hl0 : v.val.length + 4 < Usize.max) (hl3 : v3.val.length < Usize.max)
    (hl4 : v4.val.length < Usize.max)
    (hlt : tcatbals.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ out, r = .ok (.done out) ∧
        OutRel out (stopOut (dupSt s (s.post clk (DalytranRecord.vals file.val[pos.val])
          (CardXrefRecord.vals x) (AccountRecord.vals a))))) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  have hal : accounts.val.length ≤ Usize.max := accounts.property
  have hge := ge_prefix_exp a file.val[pos.val] true hexp
  have hab := hri.1 a (haj ▸ List.getElem_mem hja)
  by_cases hs : 0 ≤ (file.val[pos.val]).dalytran_amt.val
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hdup, hai, htd, hs, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, digits_eq,
      vec_index_mut_eq, dite_eq_left]
    bwp [not_false_eq_true, P9_val', hs, display_io_status_22, abend_eq]
    refine ⟨_, rfl, ?_⟩
    unfold OutRel
    refine ⟨?_, hrel.tranW, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, ← hrel.disp,
        ← dupLines_text, xAcct_vals, tType_vals, tCat_vals, ← noCat_text, Std.Array.make_val,
        List.append_assoc, List.singleton_append]
      rfl
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      exact hrel.rejW
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.acctRW, List.map_cons, List.map_nil,
        tAmt_vals]
      exact congrArg (fun z => s.acctRW ++ [z]) (acctNew_vals a _ _ _ _
        (by rw [srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_left hs, srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_left hs]))
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.catW, List.map_cons, List.map_nil,
        ← hrel.fill]
      exact congrArg (fun z => s.catW ++ [z]) (catNew_vals tcr x _ _ (by
        rw [srem_val, ofIntCore_val', P11_val', zero_add]
        exact tmod_id _ _ (by norm_num) (by omega) (by omega)))
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      exact hrel.catRW
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hdup, hai, htd, hs, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, digits_eq,
      vec_index_mut_eq, dite_eq_left]
    bwp [not_false_eq_true, P9_val', hs, display_io_status_22, abend_eq]
    refine ⟨_, rfl, ?_⟩
    unfold OutRel
    refine ⟨?_, hrel.tranW, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, ← hrel.disp,
        ← dupLines_text, xAcct_vals, tType_vals, tCat_vals, ← noCat_text, Std.Array.make_val,
        List.append_assoc, List.singleton_append]
      rfl
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      exact hrel.rejW
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.acctRW, List.map_cons, List.map_nil,
        tAmt_vals]
      exact congrArg (fun z => s.acctRW ++ [z]) (acctNew_vals a _ _ _ _
        (by rw [srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_right hs]) (by rw [ite_eq_right hs, srem_val, ofIntCore_val', P12_val]))
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.catW, List.map_cons, List.map_nil,
        ← hrel.fill]
      exact congrArg (fun z => s.catW ++ [z]) (catNew_vals tcr x _ _ (by
        rw [srem_val, ofIntCore_val', P11_val', zero_add]
        exact tmod_id _ _ (by norm_num) (by omega) (by omega)))
    · simp only [stopOut, dupSt, Model.St.post, hnone]
      exact hrel.catRW

set_option maxHeartbeats 4000000 in
/-- **A posted transaction with a repeated id, existing category record.** -/
theorem body_post_rewrite_dup (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64) (s : Model.St)
    (hrel : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s) (hri : RInv accounts tcatbals)
    (hpos : pos.val < file.val.length) (x : cbtrn02c.CardXrefRecord) (a : cbtrn02c.AccountRecord)
    (ja : Nat) (hja : ja < accounts.val.length) (haj : accounts.val[ja] = a)
    (hfa : accounts.val.findIdx (fun b => b.acct_id.val == a.acct_id.val) = ja)
    (c0 : cbtrn02c.TranCatBalRecord) (jc : Nat) (hjc : jc < tcatbals.val.length)
    (hcj : tcatbals.val[jc] = c0)
    (hsome : Model.findCat s.cats (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals file.val[pos.val]))
      (Model.tCat (DalytranRecord.vals file.val[pos.val])) = some (TranCatBalRecord.vals c0))
    (hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
      .ok (file.val[pos.val], x, true))
    (has : cbtrn02c.run_loop2_loop1 accounts ar 0#usize x.xref_acct_id = .ok (a, true))
    (hamt : -100000000000 < (file.val[pos.val]).dalytran_amt.val ∧
      (file.val[pos.val]).dalytran_amt.val < 100000000000)
    (hexp : geEbc a.acct_expiraion_date.val (file.val[pos.val]).dalytran_orig_ts.val 10 = true)
    (hlim : Int.tmod (a.acct_curr_cyc_credit.val - a.acct_curr_cyc_debit.val +
      (file.val[pos.val]).dalytran_amt.val) 100000000000 ≤ a.acct_credit_limit.val)
    (hcs : cbtrn02c.run_loop2_loop2 tcatbals tcr 0#usize x.xref_acct_id
      (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd = .ok (c0, true))
    (hci : cbtrn02c.run_loop2_loop6 tcatbals c0.trancat_acct_id c0.trancat_type_cd c0.trancat_cd
      0#usize = .ok (usz jc, true))
    (hai : cbtrn02c.run_loop2_loop7 accounts a.acct_id 0#usize = .ok (usz ja, true))
    (htd : cbtrn02c.run_loop2_loop8 v1 (file.val[pos.val]).dalytran_id 0#usize = .ok true)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9)
    (hl0 : v.val.length + 4 < Usize.max) (hl3 : v3.val.length < Usize.max)
    (hl5 : v5.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ out, r = .ok (.done out) ∧
        OutRel out (stopOut (dupSt s (s.post clk (DalytranRecord.vals file.val[pos.val])
          (CardXrefRecord.vals x) (AccountRecord.vals a))))) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  have hal : accounts.val.length ≤ Usize.max := accounts.property
  have htl : tcatbals.val.length ≤ Usize.max := tcatbals.property
  have hge := ge_prefix_exp a file.val[pos.val] true hexp
  have hab := hri.1 a (haj ▸ List.getElem_mem hja)
  have hcb := hri.2 c0 (hcj ▸ List.getElem_mem hjc)
  have hia := vec_index_mut_eq accounts (usz ja) (by rw [usz_val _ (by omega)]; exact hja)
  have hic := vec_index_mut_eq tcatbals (usz jc) (by rw [usz_val _ (by omega)]; exact hjc)
  by_cases hs : 0 ≤ (file.val[pos.val]).dalytran_amt.val
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hci, hai, htd, hs, hia, hic, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, dite_eq_left]
    try bwp [not_false_eq_true, P9_val', hs, display_io_status_22, abend_eq]
    refine ⟨_, rfl, ?_⟩
    unfold OutRel
    refine ⟨?_, hrel.tranW, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, ← hrel.disp,
        ← dupLines_text, Std.Array.make_val, List.singleton_append]
      rfl
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      exact hrel.rejW
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.acctRW, List.map_cons, List.map_nil,
        tAmt_vals]
      exact congrArg (fun z => s.acctRW ++ [z]) (acctNew_vals a _ _ _ _
        (by rw [srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_left hs, srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_left hs]))
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      exact hrel.catW
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.catRW, List.map_cons, List.map_nil,
        tAmt_vals]
      exact congrArg (fun z => s.catRW ++ [z])
        (catUpd_vals c0 _ _ (by rw [srem_val, ofIntCore_val', P11_val]))
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hci, hai, htd, hs, hia, hic, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, dite_eq_left]
    try bwp [not_false_eq_true, P9_val', hs, display_io_status_22, abend_eq]
    refine ⟨_, rfl, ?_⟩
    unfold OutRel
    refine ⟨?_, hrel.tranW, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, ← hrel.disp,
        ← dupLines_text, Std.Array.make_val, List.singleton_append]
      rfl
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      exact hrel.rejW
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.acctRW, List.map_cons, List.map_nil,
        tAmt_vals]
      exact congrArg (fun z => s.acctRW ++ [z]) (acctNew_vals a _ _ _ _
        (by rw [srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_right hs]) (by rw [ite_eq_right hs, srem_val, ofIntCore_val', P12_val]))
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      exact hrel.catW
    · simp only [stopOut, dupSt, Model.St.post, hsome]
      simp only [alloc.vec.Vec.from_val, List.map_append, hrel.catRW, List.map_cons, List.map_nil,
        tAmt_vals]
      exact congrArg (fun z => s.catRW ++ [z])
        (catUpd_vals c0 _ _ (by rw [srem_val, ofIntCore_val', P11_val]))

end EquivLean.Modernize.Cbtrn02c.Rust
