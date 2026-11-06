import EquivLean.Modernize.Cbtrn02c.RustRun3
/-!
# CBTRN02C → Rust: the main loop's state against the model, and the rejects
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-! ## The relation of the loop state to the model's state -/

/-- The outputs, tables, records and reject count of `run_loop2`'s state are the model's. -/
structure SRel (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (rej : I64) (s : Model.St) : Prop where
  disp : v.val.map (fun l => l.val.map (·.val)) = s.disp
  tranW : v1.val.map TranRecord.vals = s.tranW
  rejW : v2.val.map RejectRecord.vals = s.rejW
  acctRW : v3.val.map AccountRecord.vals = s.acctRW
  catW : v4.val.map TranCatBalRecord.vals = s.catW
  catRW : v5.val.map TranCatBalRecord.vals = s.catRW
  accts : accounts.val.map AccountRecord.vals = s.accts
  cats : tcatbals.val.map TranCatBalRecord.vals = s.cats
  fill : tcr.filler1.val.map ebc = s.catFill
  tfill : tr.filler1.val = List.replicate 20 32#u8
  rej : rej.val = s.rejects

/-- A rejected transaction: the reject record (the daily record's bytes, the trailer) appended,
the reject count incremented. -/
theorem srel_reject {v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s}
    (h : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s)
    (d : cbtrn02c.DalytranRecord) (code : Int) (descR : List U8) (descM : List UInt8)
    (hd : descR.map ebc = descM ++ List.replicate (76 - descM.length) 64)
    (r : cbtrn02c.RejectRecord) (hr1 : r.reject_tran_data.val = encList d)
    (hr2 : r.validation_trailer.val = digs 4 code.natAbs ++ descR)
    (v2' : alloc.vec.Vec cbtrn02c.RejectRecord) (hv2 : v2'.val = v2.val ++ [r])
    (rej' : I64) (hrej : rej'.val = rej.val + 1) :
    SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej'
      (s.reject (DalytranRecord.vals d) code descM) where
  disp := h.disp
  tranW := h.tranW
  rejW := by
    rw [hv2, List.map_append, h.rejW]
    have e1 : r.reject_tran_data.val.map ebc = Model.DalytranRecord.encode (DalytranRecord.vals d) := by
      rw [hr1, encList_ebc]
    have e2 : r.validation_trailer.val.map ebc = CardDemo.Cbtrn02c.trailer code descM := by
      rw [hr2, trailer_ebc _ _ _ hd]
    simp only [Model.St.reject, List.map_cons, List.map_nil, Model.rejectVals, RejectRecord.vals]
    rw [← e1, ← e2]
  acctRW := h.acctRW
  catW := h.catW
  catRW := h.catRW
  accts := h.accts
  cats := h.cats
  fill := h.fill
  tfill := h.tfill
  rej := by rw [hrej, h.rej]; rfl

/-! ## The records of a posted transaction -/

theorem natAbs_lt_iff' (x : Int) (n : Nat) : x.natAbs < n ↔ -(n : Int) < x ∧ x < n := by
  rcases Int.natAbs_eq x with hx | hx <;> constructor <;> intro h <;> omega

/-- The transaction record of a posted transaction (`2000-POST-TRANSACTION`). -/
def tranOf (tr : cbtrn02c.TranRecord) (d : cbtrn02c.DalytranRecord) (ts : Std.Array U8 26#usize) :
    cbtrn02c.TranRecord :=
  { tr with tran_id := d.dalytran_id, tran_type_cd := d.dalytran_type_cd,
            tran_cat_cd := d.dalytran_cat_cd, tran_source := d.dalytran_source,
            tran_desc := d.dalytran_desc, tran_amt := d.dalytran_amt,
            tran_merchant_id := d.dalytran_merchant_id,
            tran_merchant_name := d.dalytran_merchant_name,
            tran_merchant_city := d.dalytran_merchant_city,
            tran_merchant_zip := d.dalytran_merchant_zip, tran_card_num := d.dalytran_card_num,
            tran_orig_ts := d.dalytran_orig_ts, tran_proc_ts := ts }

theorem tranOf_vals (tr : cbtrn02c.TranRecord) (htf : tr.filler1.val = List.replicate 20 32#u8)
    (d : cbtrn02c.DalytranRecord) (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21) :
    TranRecord.vals (tranOf tr d (tsArr clock)) = Model.tranVals (DalytranRecord.vals d) clk := by
  have hts : (tsArr clock).val.map ebc = CardDemo.Cbtrn02c.db2ts clk := by
    rw [tsArr, Std.Array.from_val]; exact tsList_ebc clock clk hclk hclen
  have h32 : ebc 32#u8 = 64 := by decide +kernel
  have hsp : (List.replicate 20 32#u8).map ebc = Model.sp 20 := by
    rw [List.map_replicate, h32]; rfl
  simp only [TranRecord.vals, tranOf, Model.tranVals, DalytranRecord.vals, htf]
  rw [show ((tsArr clock).val.map fun u => ebcdicOfLatin1 u.val) = CardDemo.Cbtrn02c.db2ts clk from hts,
    show ((List.replicate 20 32#u8).map fun u => ebcdicOfLatin1 u.val) = Model.sp 20 from hsp]
  rfl

/-- A new category balance record (`2700-A-CREATE-TCATBAL-REC`): the key, the amount, the
`FILLER` of the current record. -/
def catNew (tcr : cbtrn02c.TranCatBalRecord) (x : cbtrn02c.CardXrefRecord) (d : cbtrn02c.DalytranRecord)
    (bal : I64) : cbtrn02c.TranCatBalRecord :=
  { tcr with trancat_acct_id := x.xref_acct_id, trancat_type_cd := d.dalytran_type_cd,
             trancat_cd := d.dalytran_cat_cd, tran_cat_bal := bal }

theorem catNew_vals (tcr : cbtrn02c.TranCatBalRecord) (x : cbtrn02c.CardXrefRecord)
    (d : cbtrn02c.DalytranRecord) (bal : I64) (hb : bal.val = d.dalytran_amt.val) :
    TranCatBalRecord.vals (catNew tcr x d bal) =
      [.num (Model.xAcct (CardXrefRecord.vals x)), .str (Model.tType (DalytranRecord.vals d)),
        .num (Model.tCat (DalytranRecord.vals d)), .num (Model.tAmt (DalytranRecord.vals d)),
        .str (tcr.filler1.val.map ebc)] := by
  simp only [TranCatBalRecord.vals, catNew, hb]
  rfl

/-- The category balance record `c` with the amount added (`2700-B-UPDATE-TCATBAL-REC`). -/
theorem catUpd_vals (c : cbtrn02c.TranCatBalRecord) (amt : Int) (bal : I64)
    (hb : bal.val = Int.tmod (c.tran_cat_bal.val + amt) (10 ^ 11)) :
    TranCatBalRecord.vals { c with tran_cat_bal := bal } =
      (TranCatBalRecord.vals c).set 3 (.num (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt
        (Model.cBal (TranCatBalRecord.vals c) + amt)).2) := by
  have e := fitNum_tmod CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (by rfl) (by rfl)
    (c.tran_cat_bal.val + amt)
  have d1 : CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt.digits = 11 := by rfl
  rw [cBal_vals, e, d1, ← hb]
  rfl

/-- The account `a` with the amount posted (`2800-UPDATE-ACCOUNT-REC`). -/
theorem acctNew_vals (a : cbtrn02c.AccountRecord) (amt : Int) (bal cc cd : I64)
    (hbal : bal.val = Int.tmod (a.acct_curr_bal.val + amt) (10 ^ 12))
    (hcc : cc.val = if 0 ≤ amt then Int.tmod (a.acct_curr_cyc_credit.val + amt) (10 ^ 12)
      else a.acct_curr_cyc_credit.val)
    (hcd : cd.val = if 0 ≤ amt then a.acct_curr_cyc_debit.val
      else Int.tmod (a.acct_curr_cyc_debit.val + amt) (10 ^ 12)) :
    AccountRecord.vals { a with acct_curr_bal := bal, acct_curr_cyc_credit := cc, acct_curr_cyc_debit := cd } =
      Model.postAcct (AccountRecord.vals a) amt := by
  have e1 := fitNum_tmod CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt (by rfl) (by rfl)
    (a.acct_curr_bal.val + amt)
  have e2 := fitNum_tmod CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt (by rfl) (by rfl)
    (a.acct_curr_cyc_credit.val + amt)
  have e3 := fitNum_tmod CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt (by rfl) (by rfl)
    (a.acct_curr_cyc_debit.val + amt)
  have d1 : CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt.digits = 12 := by rfl
  have d2 : CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt.digits = 12 := by rfl
  have d3 : CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt.digits = 12 := by rfl
  rw [d1] at e1; rw [d2] at e2; rw [d3] at e3
  simp only [Model.postAcct, aBal_vals, aCC_vals, aCD_vals, e1, e2, e3]
  by_cases hs : 0 ≤ amt
  · simp only [hs, _root_.ite_true] at hcc hcd ⊢
    simp only [AccountRecord.vals, ← hbal, ← hcc, ← hcd]
    rfl
  · simp only [hs, _root_.ite_false] at hcc hcd ⊢
    simp only [AccountRecord.vals, ← hbal, ← hcc, ← hcd]
    rfl

/-- **A posted transaction whose category key is new** (`2700-A-CREATE-TCATBAL-REC`). -/
theorem srel_post_create {v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s}
    (h : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s) (clk : List UInt8)
    (d : cbtrn02c.DalytranRecord) (x : cbtrn02c.CardXrefRecord) (a : cbtrn02c.AccountRecord)
    (ja : Nat) (hja : ja < accounts.val.length)
    (hfa : accounts.val.findIdx (fun b => b.acct_id.val == a.acct_id.val) = ja)
    (hnone : Model.findCat s.cats (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals d)) (Model.tCat (DalytranRecord.vals d)) = none)
    (a' : cbtrn02c.AccountRecord)
    (ha' : AccountRecord.vals a' = Model.postAcct (AccountRecord.vals a) (Model.tAmt (DalytranRecord.vals d)))
    (c : cbtrn02c.TranCatBalRecord)
    (hc : TranCatBalRecord.vals c =
      [.num (Model.xAcct (CardXrefRecord.vals x)), .str (Model.tType (DalytranRecord.vals d)),
        .num (Model.tCat (DalytranRecord.vals d)), .num (Model.tAmt (DalytranRecord.vals d)),
        .str (tcr.filler1.val.map ebc)])
    (hcf : c.filler1 = tcr.filler1)
    (t : cbtrn02c.TranRecord) (ht : TranRecord.vals t = Model.tranVals (DalytranRecord.vals d) clk)
    (htf : t.filler1 = tr.filler1)
    (v' : alloc.vec.Vec (alloc.vec.Vec U8))
    (hv' : v'.val.map (fun l => l.val.map (·.val)) = v.val.map (fun l => l.val.map (·.val)) ++
      [Model.noCatLine (Model.xAcct (CardXrefRecord.vals x)) (Model.tType (DalytranRecord.vals d))
        (Model.tCat (DalytranRecord.vals d))])
    (v1' : alloc.vec.Vec cbtrn02c.TranRecord) (hv1' : v1'.val = v1.val ++ [t])
    (v3' : alloc.vec.Vec cbtrn02c.AccountRecord) (hv3' : v3'.val = v3.val ++ [a'])
    (v4' : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (hv4' : v4'.val = v4.val ++ [c])
    (accounts' : alloc.vec.Vec cbtrn02c.AccountRecord) (hacc' : accounts'.val = accounts.val.set ja a')
    (tcatbals' : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (htc' : tcatbals'.val = tcatbals.val ++ [c]) :
    SRel v' v1' v2 v3' v4' v5 accounts' tcatbals' c t rej
      (s.post clk (DalytranRecord.vals d) (CardXrefRecord.vals x) (AccountRecord.vals a)) where
  disp := by simp only [Model.St.post, hnone]; rw [hv', h.disp]
  tranW := by simp only [Model.St.post, hnone]; rw [hv1', List.map_append, h.tranW]; simp [ht]
  rejW := by simp only [Model.St.post, hnone]; exact h.rejW
  acctRW := by simp only [Model.St.post, hnone]; rw [hv3', List.map_append, h.acctRW]; simp [ha']
  catW := by
    simp only [Model.St.post, hnone]
    rw [hv4', List.map_append, h.catW, List.map_cons, List.map_nil, hc, h.fill]
  catRW := by simp only [Model.St.post, hnone]; exact h.catRW
  accts := by
    simp only [Model.St.post, hnone]
    rw [hacc', ← h.accts, ← ha']
    have hq : ((fun b => Model.aId b == Model.aId (AccountRecord.vals a)) ∘ AccountRecord.vals) =
        (fun b : cbtrn02c.AccountRecord => b.acct_id.val == a.acct_id.val) := rfl
    rw [replaceFirst_map AccountRecord.vals _ a' accounts.val (by rw [hq, hfa]; exact hja), hq, hfa]
  cats := by
    simp only [Model.St.post, hnone]
    rw [htc', List.map_append, h.cats, List.map_cons, List.map_nil, hc, h.fill]
  fill := by simp only [Model.St.post, hnone]; rw [hcf, h.fill]
  tfill := by rw [htf, h.tfill]
  rej := by simp only [Model.St.post, hnone]; exact h.rej

/-- **A posted transaction whose category record exists** (`2700-B-UPDATE-TCATBAL-REC`). -/
theorem srel_post_rewrite {v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s}
    (h : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s) (clk : List UInt8)
    (d : cbtrn02c.DalytranRecord) (x : cbtrn02c.CardXrefRecord) (a : cbtrn02c.AccountRecord)
    (ja : Nat) (hja : ja < accounts.val.length)
    (hfa : accounts.val.findIdx (fun b => b.acct_id.val == a.acct_id.val) = ja)
    (c0 : cbtrn02c.TranCatBalRecord) (jc : Nat) (hjc : jc < tcatbals.val.length)
    (hfc : tcatbals.val.findIdx (Model.catKey (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals d)) (Model.tCat (DalytranRecord.vals d)) ∘
        TranCatBalRecord.vals) = jc)
    (hsome : Model.findCat s.cats (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals d)) (Model.tCat (DalytranRecord.vals d)) =
        some (TranCatBalRecord.vals c0))
    (a' : cbtrn02c.AccountRecord)
    (ha' : AccountRecord.vals a' = Model.postAcct (AccountRecord.vals a) (Model.tAmt (DalytranRecord.vals d)))
    (c : cbtrn02c.TranCatBalRecord)
    (hc : TranCatBalRecord.vals c = (TranCatBalRecord.vals c0).set 3
      (.num (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt
        (Model.cBal (TranCatBalRecord.vals c0) + Model.tAmt (DalytranRecord.vals d))).2))
    (hcf : c.filler1 = c0.filler1)
    (t : cbtrn02c.TranRecord) (ht : TranRecord.vals t = Model.tranVals (DalytranRecord.vals d) clk)
    (htf : t.filler1 = tr.filler1)
    (v1' : alloc.vec.Vec cbtrn02c.TranRecord) (hv1' : v1'.val = v1.val ++ [t])
    (v3' : alloc.vec.Vec cbtrn02c.AccountRecord) (hv3' : v3'.val = v3.val ++ [a'])
    (v5' : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (hv5' : v5'.val = v5.val ++ [c])
    (accounts' : alloc.vec.Vec cbtrn02c.AccountRecord) (hacc' : accounts'.val = accounts.val.set ja a')
    (tcatbals' : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (htc' : tcatbals'.val = tcatbals.val.set jc c) :
    SRel v v1' v2 v3' v4 v5' accounts' tcatbals' c t rej
      (s.post clk (DalytranRecord.vals d) (CardXrefRecord.vals x) (AccountRecord.vals a)) where
  disp := by simp only [Model.St.post, hsome]; exact h.disp
  tranW := by simp only [Model.St.post, hsome]; rw [hv1', List.map_append, h.tranW]; simp [ht]
  rejW := by simp only [Model.St.post, hsome]; exact h.rejW
  acctRW := by simp only [Model.St.post, hsome]; rw [hv3', List.map_append, h.acctRW]; simp [ha']
  catW := by simp only [Model.St.post, hsome]; exact h.catW
  catRW := by
    simp only [Model.St.post, hsome]
    rw [hv5', List.map_append, h.catRW, List.map_cons, List.map_nil, hc]
  accts := by
    simp only [Model.St.post, hsome]
    rw [hacc', ← h.accts, ← ha']
    have hq : ((fun b => Model.aId b == Model.aId (AccountRecord.vals a)) ∘ AccountRecord.vals) =
        (fun b : cbtrn02c.AccountRecord => b.acct_id.val == a.acct_id.val) := rfl
    rw [replaceFirst_map AccountRecord.vals _ a' accounts.val (by rw [hq, hfa]; exact hja), hq, hfa]
  cats := by
    simp only [Model.St.post, hsome]
    rw [htc', ← h.cats, ← hc, replaceFirst_map TranCatBalRecord.vals _ c tcatbals.val
      (by rw [hfc]; exact hjc), hfc]
  fill := by simp only [Model.St.post, hsome]; rw [hcf, cFill_vals]
  tfill := by rw [htf, h.tfill]
  rej := by simp only [Model.St.post, hsome]; exact h.rej


/-! ## The reject messages -/

def badCardR : List U8 := [73#u8, 78#u8, 86#u8, 65#u8, 76#u8, 73#u8, 68#u8, 32#u8, 67#u8, 65#u8,
  82#u8, 68#u8, 32#u8, 78#u8, 85#u8, 77#u8, 66#u8, 69#u8, 82#u8, 32#u8, 70#u8, 79#u8, 85#u8, 78#u8,
  68#u8]
def noAcctR : List U8 := [65#u8, 67#u8, 67#u8, 79#u8, 85#u8, 78#u8, 84#u8, 32#u8, 82#u8, 69#u8,
  67#u8, 79#u8, 82#u8, 68#u8, 32#u8, 78#u8, 79#u8, 84#u8, 32#u8, 70#u8, 79#u8, 85#u8, 78#u8, 68#u8]
def overLimitR : List U8 := [79#u8, 86#u8, 69#u8, 82#u8, 76#u8, 73#u8, 77#u8, 73#u8, 84#u8, 32#u8,
  84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8, 67#u8, 84#u8, 73#u8, 79#u8, 78#u8]
def expiredR : List U8 := [84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8, 67#u8, 84#u8, 73#u8, 79#u8,
  78#u8, 32#u8, 82#u8, 69#u8, 67#u8, 69#u8, 73#u8, 86#u8, 69#u8, 68#u8, 32#u8, 65#u8, 70#u8, 84#u8,
  69#u8, 82#u8, 32#u8, 65#u8, 67#u8, 67#u8, 84#u8, 32#u8, 69#u8, 88#u8, 80#u8, 73#u8, 82#u8, 65#u8,
  84#u8, 73#u8, 79#u8, 78#u8]

theorem badCard_ebc : (pad76 badCardR).map ebc = CardDemo.Cbtrn02c.badCardDesc ++
    List.replicate (76 - CardDemo.Cbtrn02c.badCardDesc.length) 64 := by decide +kernel
theorem noAcct_ebc : (pad76 noAcctR).map ebc = CardDemo.Cbtrn02c.noAcctDesc ++
    List.replicate (76 - CardDemo.Cbtrn02c.noAcctDesc.length) 64 := by decide +kernel
theorem overLimit_ebc : (pad76 overLimitR).map ebc = CardDemo.Cbtrn02c.overLimitDesc ++
    List.replicate (76 - CardDemo.Cbtrn02c.overLimitDesc.length) 64 := by decide +kernel
theorem expired_ebc : (pad76 expiredR).map ebc = CardDemo.Cbtrn02c.expiredDesc ++
    List.replicate (76 - CardDemo.Cbtrn02c.expiredDesc.length) 64 := by decide +kernel

theorem P9_val' : cbtrn02c.P9.val = 1000000000 := by unfold cbtrn02c.P9; rfl
theorem P11_val' : cbtrn02c.P11.val = 100000000000 := by unfold cbtrn02c.P11; rfl
theorem P12_val' : cbtrn02c.P12.val = 1000000000000 := by unfold cbtrn02c.P12; rfl

theorem tmod_id (v : Int) (m : Int) (hm : 0 < m) (h1 : -m < v) (h2 : v < m) : Int.tmod v m = v := by
  rcases (show 0 ≤ v ∨ v < 0 by omega) with hv | hv
  · rw [Int.tmod_eq_emod_of_nonneg hv, Int.emod_eq_of_lt hv h2]
  · have : Int.tmod (-v) m = -v := by
      rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.emod_eq_of_lt (by omega) (by omega)]
    rw [← neg_neg v, Int.neg_tmod, this, neg_neg]

theorem ofIntCore_val' (x : Int) (h) : (IScalar.ofIntCore (ty := .I64) x h).val = x :=
  IScalar.ofInt_val_eq h

theorem vec_deref_val {α : Type _} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

theorem arr_to_slice_val {α : Type _} {n : Usize} (a : Std.Array α n) :
    (Std.Array.to_slice a).val = a.val := by
  simp [Std.Array.to_slice]

/-- The validation trailer built by the reject path: the reason code's digits, the message. -/
macro "rej_trailer_tac" : tactic => `(tactic| (
  simp only [Std.Array.from_val, Std.Array.make_val, Nat.zero_min, Nat.sub_zero, Nat.sub_self,
    List.replicate_zero, List.nil_append, List.append_nil, badCardR, noAcctR, overLimitR, expiredR]))

/-! ## Symbolic execution of the loop body -/

/-- Side conditions of conditional rewrites: lengths and linear arithmetic. -/
macro "side_tac" : tactic => `(tactic| (first
  | omega
  | (simp (disch := omega) only [Slice.from_val, Std.Array.from_val, Std.Array.to_slice,
      Std.Array.make_val, alloc.vec.Vec.deref, alloc.vec.Vec.from_val, List.length_append,
      List.length_take, List.length_drop, List.length_replicate, List.length_cons, List.length_nil,
      digs_length, sdigs_length, usz_val, arr_len, Std.Array.repeat_val, UScalar.ofNatCore_val_eq,
      alloc.vec.Vec.len_val, alloc.vec.Vec.length, pad76, encList_length, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceLeDiff] <;> omega)
  | fail "side_tac"))

open Lean Parser Tactic in
/-- `aeneas_wp` with conditional rewrites (side conditions by `side_tac`) and the `if`s on
linear arithmetic decided. -/
syntax (name := bwp) "bwp" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| bwp $[[$args,*]]?) => do
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    `(tactic| simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [wp_bind, wp_bind_tc, wp_ok, wp_fail, wp_div, wp_pure,
        wp_lift, wp_ite, wp_dite, wp_massert, wp_ofOption, wp_Slice_index_usize, wp_Vec_index_usize,
        wp_Vec_push, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
        alloc.vec.Vec.from_val, Slice.from_val,
        wp_UScalar_add_val, wp_UScalar_sub_val, wp_IScalar_add_val, wp_IScalar_sub_val,
        wp_IScalar_rem, UScalar.lt_equiv, UScalar.le_equiv, IScalar.lt_equiv, IScalar.le_equiv,
        UScalar.eq_equiv, IScalar.eq_equiv, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
        UScalarTy.Usize_numBits_eq, IScalarTy.I64_numBits_eq,
        UScalar.max_USize_eq, IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq,
        I64.min_eq, I64.max_eq, Prod.mk.injEq, Aeneas.Std.uncurry_apply_pair, _root_.dite_true,
        _root_.dite_false, _root_.ite_true, _root_.ite_false, and_self, and_true, true_and,
        dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right, Bool.false_eq_true, lift, Std.Array.to_slice_mut, Std.Array.repeat_val, from_slice_from,
        Std.Array.from_val, usz_val, List.take_append, List.drop_append, List.length_append,
        List.length_take, List.length_drop, List.length_replicate, digs_length, sdigs_length,
        arr_len, List.take_replicate, List.drop_replicate, List.take_of_length_le,
        List.drop_of_length_le, Nat.sub_self, List.take_zero, List.drop_zero, List.nil_append,
        List.append_nil, List.append_assoc, List.replicate_zero, put_eq, digits_eq,
        signed_digits_eq, push_bytes_eq, lit_eq, alpha76_eq, encode_dalytran_eq,
        db2_timestamp_eq, Std.Array.to_slice, alloc.vec.Vec.deref, P9_val, P11_val, P12_val, reduceIte, reduceDIte, Int.reduceEq,
        Int.reduceNe, Int.reduceLE, Int.reduceLT, Int.reducePow, Int.reduceAdd, Int.reduceNeg,
        Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceLeDiff,
        $args,*])

set_option maxHeartbeats 2000000 in
/-- **Reject 100** (the card is not in the cross-reference file). -/
theorem body_rej100 (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64) (s : Model.St)
    (hrel : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s)
    (hpos : pos.val < file.val.length)
    (hx : ¬ xrefs.val.findIdx (fun x => decide (x.xref_card_num.val =
      file.val[pos.val].dalytran_card_num.val)) < xrefs.val.length)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9) (hrj : 0 ≤ rej.val ∧ rej.val + 1 < 10 ^ 9)
    (hl2 : v2.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ v2' x' pos' tx' rej', r = .ok (.cont (v, v1, v2', v3, v4, v5, accounts, tcatbals,
          file.val[pos.val], x', ar, tcr, tr, pos', false, tx', rej')) ∧
        pos'.val = pos.val + 1 ∧ tx'.val = tx.val + 1 ∧
        SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej'
          (s.reject (DalytranRecord.vals file.val[pos.val]) 100 CardDemo.Cbtrn02c.badCardDesc)) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  have hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
      .ok (file.val[pos.val], cxr, false) := by
    rw [xref_search_eq, searchRes_nf _ _ _ _ hx]
  simp only [cbtrn02c.run_loop2.body]
  aeneas_wp [hpos, hxs, Bool.false_eq_true, reduceIte, reduceDIte, Int.reduceEq, P9_val',
    not_false_eq_true, Std.Array.to_slice, alloc.vec.Vec.deref]
  simp (disch := side_tac) only [alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
  bwp [not_false_eq_true, P9_val']
  refine ⟨_, _, _, _, _, rfl, ?_, ?_, ?_⟩
  · simp only [UScalar.ofNatCore_val_eq]
  · rw [srem_val, ofIntCore_val', P9_val']
    exact tmod_id _ _ (by norm_num) (by omega) (by omega)
  · refine srel_reject hrel _ 100 (pad76 badCardR) _ badCard_ebc ?r ?hr1 ?hr2 _ ?hv2 _ ?hrej
    case hv2 => rw [alloc.vec.Vec.from_val]
    case hr1 => simp only [Std.Array.from_val]
    case hr2 => rej_trailer_tac
    case hrej =>
      rw [srem_val, ofIntCore_val', P9_val']
      exact tmod_id _ _ (by norm_num) (by omega) (by omega)

end EquivLean.Modernize.Cbtrn02c.Rust

/-!
# CBTRN02C → Rust: the loop body on a rejected transaction (reasons 101, 102, 103)
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-- The expiration test of a found account, as the rewrite of the Rust call. -/
theorem ge_prefix_exp (a : cbtrn02c.AccountRecord) (d : cbtrn02c.DalytranRecord) (b : Bool)
    (hb : geEbc a.acct_expiraion_date.val d.dalytran_orig_ts.val 10 = b) :
    ∀ h1 h2, cbtrn02c.ge_prefix (Slice.from a.acct_expiraion_date.val h1)
      (Slice.from d.dalytran_orig_ts.val h2) 10#usize = .ok b := by
  intro h1 h2
  rw [ge_prefix_eq _ _ _ (by simp [arr_len]) (by simp [arr_len])]
  simp only [Slice.from_val, UScalar.ofNatCore_val_eq, hb]

/-- The leaf of a reject: the state after the reject record (`srel_reject`). -/
macro "rej_leaf" h:term:max code:term:max msg:term:max hmsg:term:max : tactic => `(tactic| (
  refine ⟨_, _, _, _, _, _, rfl, ?_, ?_, ?_⟩
  · simp only [UScalar.ofNatCore_val_eq]
  · rw [srem_val, ofIntCore_val', P9_val']
    exact tmod_id _ _ (by norm_num) (by omega) (by omega)
  · refine srel_reject $h _ $code (pad76 $msg) _ $hmsg ?r ?hr1 ?hr2 _ ?hv2 _ ?hrej
    case hv2 => rw [alloc.vec.Vec.from_val]
    case hr1 => simp only [Std.Array.from_val]
    case hr2 => rej_trailer_tac
    case hrej =>
      rw [srem_val, ofIntCore_val', P9_val']
      exact tmod_id _ _ (by norm_num) (by omega) (by omega)))

set_option maxHeartbeats 2000000 in
/-- **Reject 101** (the account is not in the account file). -/
theorem body_rej101 (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64) (s : Model.St)
    (hrel : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s)
    (hpos : pos.val < file.val.length) (x : cbtrn02c.CardXrefRecord)
    (hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
      .ok (file.val[pos.val], x, true))
    (has : cbtrn02c.run_loop2_loop1 accounts ar 0#usize x.xref_acct_id = .ok (ar, false))
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9) (hrj : 0 ≤ rej.val ∧ rej.val + 1 < 10 ^ 9)
    (hl2 : v2.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ v2' x' a' pos' tx' rej', r = .ok (.cont (v, v1, v2', v3, v4, v5, accounts, tcatbals,
          file.val[pos.val], x', a', tcr, tr, pos', false, tx', rej')) ∧
        pos'.val = pos.val + 1 ∧ tx'.val = tx.val + 1 ∧
        SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej'
          (s.reject (DalytranRecord.vals file.val[pos.val]) 101 CardDemo.Cbtrn02c.noAcctDesc)) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  simp only [cbtrn02c.run_loop2.body]
  aeneas_wp [hpos, hxs, has, Bool.false_eq_true, reduceIte, reduceDIte, Int.reduceEq, P9_val',
    not_false_eq_true, Std.Array.to_slice, alloc.vec.Vec.deref]
  simp (disch := side_tac) only [alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
  bwp [not_false_eq_true, P9_val']
  rej_leaf hrel 101 noAcctR noAcct_ebc

set_option maxHeartbeats 2000000 in
/-- **Reject 103** (the transaction is after the account's expiration date). -/
theorem body_rej103 (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64) (s : Model.St)
    (hrel : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s)
    (hpos : pos.val < file.val.length) (x : cbtrn02c.CardXrefRecord) (a : cbtrn02c.AccountRecord)
    (hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
      .ok (file.val[pos.val], x, true))
    (has : cbtrn02c.run_loop2_loop1 accounts ar 0#usize x.xref_acct_id = .ok (a, true))
    (hab : -1000000000000 < a.acct_curr_cyc_credit.val ∧ a.acct_curr_cyc_credit.val < 1000000000000 ∧
      -1000000000000 < a.acct_curr_cyc_debit.val ∧ a.acct_curr_cyc_debit.val < 1000000000000)
    (hamt : -100000000000 < (file.val[pos.val]).dalytran_amt.val ∧
      (file.val[pos.val]).dalytran_amt.val < 100000000000)
    (hexp : geEbc a.acct_expiraion_date.val (file.val[pos.val]).dalytran_orig_ts.val 10 = false)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9) (hrj : 0 ≤ rej.val ∧ rej.val + 1 < 10 ^ 9)
    (hl2 : v2.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ v2' x' a' pos' tx' rej', r = .ok (.cont (v, v1, v2', v3, v4, v5, accounts, tcatbals,
          file.val[pos.val], x', a', tcr, tr, pos', false, tx', rej')) ∧
        pos'.val = pos.val + 1 ∧ tx'.val = tx.val + 1 ∧
        SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej'
          (s.reject (DalytranRecord.vals file.val[pos.val]) 103 CardDemo.Cbtrn02c.expiredDesc)) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  have hge := ge_prefix_exp a file.val[pos.val] false hexp
  simp only [cbtrn02c.run_loop2.body]
  aeneas_wp [hpos, hxs, has, hge, Bool.false_eq_true, reduceIte, reduceDIte, Int.reduceEq, P9_val',
    P11_val', srem_val, ofIntCore_val', not_false_eq_true, Std.Array.to_slice, alloc.vec.Vec.deref]
  simp (disch := side_tac) only [alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
  bwp [not_false_eq_true, P9_val']
  split_ifs <;> rej_leaf hrel 103 expiredR expired_ebc

set_option maxHeartbeats 2000000 in
/-- **Reject 102** (over the credit limit, not expired). -/
theorem body_rej102 (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64) (s : Model.St)
    (hrel : SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej s)
    (hpos : pos.val < file.val.length) (x : cbtrn02c.CardXrefRecord) (a : cbtrn02c.AccountRecord)
    (hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
      .ok (file.val[pos.val], x, true))
    (has : cbtrn02c.run_loop2_loop1 accounts ar 0#usize x.xref_acct_id = .ok (a, true))
    (hab : -1000000000000 < a.acct_curr_cyc_credit.val ∧ a.acct_curr_cyc_credit.val < 1000000000000 ∧
      -1000000000000 < a.acct_curr_cyc_debit.val ∧ a.acct_curr_cyc_debit.val < 1000000000000)
    (hamt : -100000000000 < (file.val[pos.val]).dalytran_amt.val ∧
      (file.val[pos.val]).dalytran_amt.val < 100000000000)
    (hexp : geEbc a.acct_expiraion_date.val (file.val[pos.val]).dalytran_orig_ts.val 10 = true)
    (hlim : ¬ Int.tmod (a.acct_curr_cyc_credit.val - a.acct_curr_cyc_debit.val +
      (file.val[pos.val]).dalytran_amt.val) 100000000000 ≤ a.acct_credit_limit.val)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9) (hrj : 0 ≤ rej.val ∧ rej.val + 1 < 10 ^ 9)
    (hl2 : v2.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ v2' x' a' pos' tx' rej', r = .ok (.cont (v, v1, v2', v3, v4, v5, accounts, tcatbals,
          file.val[pos.val], x', a', tcr, tr, pos', false, tx', rej')) ∧
        pos'.val = pos.val + 1 ∧ tx'.val = tx.val + 1 ∧
        SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej'
          (s.reject (DalytranRecord.vals file.val[pos.val]) 102 CardDemo.Cbtrn02c.overLimitDesc)) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  have hge := ge_prefix_exp a file.val[pos.val] true hexp
  simp only [cbtrn02c.run_loop2.body]
  aeneas_wp [hpos, hxs, has, hge, hlim, Bool.false_eq_true, reduceIte, reduceDIte, Int.reduceEq,
    P9_val', P11_val', srem_val, ofIntCore_val', not_false_eq_true, Std.Array.to_slice,
    alloc.vec.Vec.deref]
  simp (disch := side_tac) only [alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
  bwp [not_false_eq_true, P9_val', hlim]
  rej_leaf hrel 102 overLimitR overLimit_ebc

end EquivLean.Modernize.Cbtrn02c.Rust
