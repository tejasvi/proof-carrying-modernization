import EquivLean.Modernize.Cbtrn02c.RustRun4
/-!
# CBTRN02C → Rust: the loop body on a posted transaction
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust


open Lean Parser Tactic in
/-- `aeneas_wp` with a larger step budget (the loop body is long). -/
syntax (name := awp) "awp" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| awp $[[$args,*]]?) => do
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    `(tactic| simp (config := { maxSteps := 4000000 }) only [wp_bind, wp_bind_tc, wp_ok, wp_fail,
        wp_div, wp_pure, wp_lift, wp_ite, wp_dite, wp_massert, wp_ofOption, wp_Slice_index_usize,
        wp_Vec_index_usize, wp_Vec_push, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len_val,
        alloc.vec.Vec.length, alloc.vec.Vec.from_val, Slice.from_val,
        wp_UScalar_add_val, wp_UScalar_sub_val, wp_IScalar_add_val, wp_IScalar_sub_val,
        wp_IScalar_rem, UScalar.lt_equiv, UScalar.le_equiv, IScalar.lt_equiv, IScalar.le_equiv,
        UScalar.eq_equiv, IScalar.eq_equiv, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
        UScalarTy.Usize_numBits_eq, IScalarTy.I64_numBits_eq,
        UScalar.max_USize_eq, IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq,
        I64.min_eq, I64.max_eq, Prod.mk.injEq, Aeneas.Std.uncurry_apply_pair, _root_.dite_true,
        _root_.dite_false, _root_.ite_true, _root_.ite_false, and_self, and_true, true_and,
        Bool.false_eq_true, lift, Std.Array.to_slice_mut, Std.Array.to_slice, alloc.vec.Vec.deref,
        reduceIte, reduceDIte, Int.reduceEq, not_false_eq_true, $args,*])

/-- Bounds on the account and category balance tables (no Rust arithmetic overflows). -/
def RInv (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) : Prop :=
  (∀ a ∈ accounts.val, -1000000000000 < a.acct_curr_bal.val ∧ a.acct_curr_bal.val < 1000000000000 ∧
    -1000000000000 < a.acct_curr_cyc_credit.val ∧ a.acct_curr_cyc_credit.val < 1000000000000 ∧
    -1000000000000 < a.acct_curr_cyc_debit.val ∧ a.acct_curr_cyc_debit.val < 1000000000000) ∧
  (∀ c ∈ tcatbals.val, -100000000000 < c.tran_cat_bal.val ∧ c.tran_cat_bal.val < 100000000000)

theorem tmod_bound (v : Int) (m : Int) (hm : 0 < m) : -m < Int.tmod v m ∧ Int.tmod v m < m := by
  have h := Int.natAbs_tmod v m
  have h2 : (Int.tmod v m).natAbs < m.natAbs := by
    rw [h]; exact Nat.mod_lt _ (by omega)
  rcases Int.natAbs_eq (Int.tmod v m) with e | e <;> omega

/-- `TCATBAL record not found for key : ` and `.. Creating.` (Latin-1). -/
def noCatHead : List U8 := [84#u8, 67#u8, 65#u8, 84#u8, 66#u8, 65#u8, 76#u8, 32#u8, 114#u8, 101#u8,
  99#u8, 111#u8, 114#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 102#u8, 111#u8, 117#u8,
  110#u8, 100#u8, 32#u8, 102#u8, 111#u8, 114#u8, 32#u8, 107#u8, 101#u8, 121#u8, 32#u8, 58#u8, 32#u8]
def creatingR : List U8 := [46#u8, 46#u8, 32#u8, 67#u8, 114#u8, 101#u8, 97#u8, 116#u8, 105#u8,
  110#u8, 103#u8, 46#u8]

theorem noCatHead_text : noCatHead.map UScalar.val = Model.txt "TCATBAL record not found for key : " := by
  decide
theorem creatingR_text : creatingR.map UScalar.val = Model.txt ".. Creating." := by decide

/-- The display line of a missing category key. -/
theorem noCat_text (acct cd : Int) (ty : List U8) :
    (noCatHead ++ (digs 11 acct.natAbs ++ (ty ++ (digs 4 cd.natAbs ++ creatingR)))).map UScalar.val =
      Model.noCatLine acct (ty.map ebc) cd := by
  simp only [List.map_append, digs_val, Model.noCatLine, latin1_text, noCatHead_text, creatingR_text,
    List.append_assoc]

set_option maxHeartbeats 4000000 in
/-- **A posted transaction, new category key** (`2700-A-CREATE-TCATBAL-REC`). -/
theorem body_post_create (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (hclk : clock.val.map (·.val) = rustLine clk)
    (hclen : clk.length = 21) (v : alloc.vec.Vec (alloc.vec.Vec U8))
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
    (htd : cbtrn02c.run_loop2_loop5 v1 (file.val[pos.val]).dalytran_id 0#usize = .ok false)
    (hnone : Model.findCat s.cats (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals file.val[pos.val]))
      (Model.tCat (DalytranRecord.vals file.val[pos.val])) = none)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9)
    (hl0 : v.val.length < Usize.max) (hl1 : v1.val.length < Usize.max)
    (hl3 : v3.val.length < Usize.max) (hl4 : v4.val.length < Usize.max)
    (hlt : tcatbals.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ v' v1' v3' v4' accounts' tcatbals' a' c t pos' tx',
        r = .ok (.cont (v', v1', v2, v3', v4', v5, accounts', tcatbals', file.val[pos.val], x, a', c, t,
          pos', false, tx', rej)) ∧
        pos'.val = pos.val + 1 ∧ tx'.val = tx.val + 1 ∧
        SRel v' v1' v2 v3' v4' v5 accounts' tcatbals' c t rej
          (s.post clk (DalytranRecord.vals file.val[pos.val]) (CardXrefRecord.vals x)
            (AccountRecord.vals a)) ∧
        RInv accounts' tcatbals' ∧ v1'.val = v1.val ++ [t] ∧
        t.tran_id = (file.val[pos.val]).dalytran_id) := by
  have hm := usize_max_ge
  have hfl : file.val.length ≤ Usize.max := by scalar_tac
  have hal : accounts.val.length ≤ Usize.max := accounts.property
  have hge := ge_prefix_exp a file.val[pos.val] true hexp
  have hab := hri.1 a (haj ▸ List.getElem_mem hja)
  by_cases hs : 0 ≤ (file.val[pos.val]).dalytran_amt.val
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hdup, hai, htd, hs, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, push_bytes_eq,
      digits_eq, vec_index_mut_eq, alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
    bwp [not_false_eq_true, P9_val', hs]
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [UScalar.ofNatCore_val_eq]
    · rw [srem_val, ofIntCore_val', P9_val']
      exact tmod_id _ _ (by norm_num) (by omega) (by omega)
    · refine srel_post_create hrel clk _ x a ja hja hfa hnone ?na ?ha' _ ?hc ?hcf _ ?ht ?htf _ ?hv' _
        ?hv1' _ ?hv3' _ ?hv4' _ ?hacc' _ ?htc'
      case hv3' => rw [alloc.vec.Vec.from_val]
      case ha' =>
        rw [tAmt_vals]
        exact acctNew_vals a _ _ _ _ (by rw [srem_val, ofIntCore_val', P12_val])
          (by rw [ite_eq_left hs, srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_left hs])
      case hc =>
        exact catNew_vals tcr x _ _ (by
          rw [srem_val, ofIntCore_val', P11_val', zero_add]
          exact tmod_id _ _ (by norm_num) (by omega) (by omega))
      case hcf => rfl
      case ht => exact tranOf_vals tr hrel.tfill _ clock clk hclk hclen
      case htf => rfl
      case hv' =>
        rw [alloc.vec.Vec.from_val, List.map_append, List.map_singleton, alloc.vec.Vec.from_val,
          Std.Array.make_val, Std.Array.make_val, xAcct_vals, tType_vals, tCat_vals, ← noCat_text]
        rfl
      case hv1' => rw [alloc.vec.Vec.from_val]
      case hv4' => rw [alloc.vec.Vec.from_val]
      case hacc' => rw [alloc.vec.Vec.set_val_eq, usz_val _ (by omega)]
      case htc' => rw [alloc.vec.Vec.from_val]
    · refine ⟨fun b hb => ?_, fun c hc => ?_⟩
      · rw [alloc.vec.Vec.set_val_eq] at hb
        rcases List.mem_or_eq_of_mem_set hb with hb | rfl
        · exact hri.1 b hb
        · simp only [srem_val, ofIntCore_val', P12_val']
          have t1 := tmod_bound (a.acct_curr_bal.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          have t2 := tmod_bound (a.acct_curr_cyc_credit.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          omega
      · rw [alloc.vec.Vec.from_val] at hc
        rcases List.mem_append.1 hc with hc | hc
        · exact hri.2 c hc
        · rw [List.mem_singleton] at hc
          subst hc
          simp only [srem_val, ofIntCore_val', P11_val', zero_add]
          rw [tmod_id _ _ (by norm_num) (by omega) (by omega)]
          omega
    · rw [alloc.vec.Vec.from_val]
    · rfl
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hdup, hai, htd, hs, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, push_bytes_eq,
      digits_eq, vec_index_mut_eq, alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
    bwp [not_false_eq_true, P9_val', hs]
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [UScalar.ofNatCore_val_eq]
    · rw [srem_val, ofIntCore_val', P9_val']
      exact tmod_id _ _ (by norm_num) (by omega) (by omega)
    · refine srel_post_create hrel clk _ x a ja hja hfa hnone ?na2 ?ha'2 _ ?hc2 ?hcf2 _ ?ht2 ?htf2 _ ?hv'2 _
        ?hv1'2 _ ?hv3'2 _ ?hv4'2 _ ?hacc'2 _ ?htc'2
      case hv3'2 => rw [alloc.vec.Vec.from_val]
      case ha'2 =>
        rw [tAmt_vals]
        exact acctNew_vals a _ _ _ _ (by rw [srem_val, ofIntCore_val', P12_val])
          (by rw [ite_eq_right hs]) (by rw [ite_eq_right hs, srem_val, ofIntCore_val', P12_val])
      case hc2 =>
        exact catNew_vals tcr x _ _ (by
          rw [srem_val, ofIntCore_val', P11_val', zero_add]
          exact tmod_id _ _ (by norm_num) (by omega) (by omega))
      case hcf2 => rfl
      case ht2 => exact tranOf_vals tr hrel.tfill _ clock clk hclk hclen
      case htf2 => rfl
      case hv'2 =>
        rw [alloc.vec.Vec.from_val, List.map_append, List.map_singleton, alloc.vec.Vec.from_val,
          Std.Array.make_val, Std.Array.make_val, xAcct_vals, tType_vals, tCat_vals, ← noCat_text]
        rfl
      case hv1'2 => rw [alloc.vec.Vec.from_val]
      case hv4'2 => rw [alloc.vec.Vec.from_val]
      case hacc'2 => rw [alloc.vec.Vec.set_val_eq, usz_val _ (by omega)]
      case htc'2 => rw [alloc.vec.Vec.from_val]
    · refine ⟨fun b hb => ?_, fun c hc => ?_⟩
      · rw [alloc.vec.Vec.set_val_eq] at hb
        rcases List.mem_or_eq_of_mem_set hb with hb | rfl
        · exact hri.1 b hb
        · simp only [srem_val, ofIntCore_val', P12_val']
          have t1 := tmod_bound (a.acct_curr_bal.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          have t2 := tmod_bound (a.acct_curr_cyc_debit.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          omega
      · rw [alloc.vec.Vec.from_val] at hc
        rcases List.mem_append.1 hc with hc | hc
        · exact hri.2 c hc
        · rw [List.mem_singleton] at hc
          subst hc
          simp only [srem_val, ofIntCore_val', P11_val', zero_add]
          rw [tmod_id _ _ (by norm_num) (by omega) (by omega)]
          omega
    · rw [alloc.vec.Vec.from_val]
    · rfl

end EquivLean.Modernize.Cbtrn02c.Rust

/-!
# CBTRN02C → Rust: the loop body on a posted transaction whose category record exists
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

set_option maxHeartbeats 4000000 in
/-- **A posted transaction, existing category record** (`2700-B-UPDATE-TCATBAL-REC`). -/
theorem body_post_rewrite (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (hclk : clock.val.map (·.val) = rustLine clk)
    (hclen : clk.length = 21) (v : alloc.vec.Vec (alloc.vec.Vec U8))
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
    (hfc : tcatbals.val.findIdx (Model.catKey (Model.xAcct (CardXrefRecord.vals x))
      (Model.tType (DalytranRecord.vals file.val[pos.val]))
      (Model.tCat (DalytranRecord.vals file.val[pos.val])) ∘ TranCatBalRecord.vals) = jc)
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
    (htd : cbtrn02c.run_loop2_loop8 v1 (file.val[pos.val]).dalytran_id 0#usize = .ok false)
    (htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9)
    (hl1 : v1.val.length < Usize.max) (hl3 : v3.val.length < Usize.max)
    (hl5 : v5.val.length < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ v1' v3' v5' accounts' tcatbals' a' c t pos' tx',
        r = .ok (.cont (v, v1', v2, v3', v4, v5', accounts', tcatbals', file.val[pos.val], x, a', c, t,
          pos', false, tx', rej)) ∧
        pos'.val = pos.val + 1 ∧ tx'.val = tx.val + 1 ∧
        SRel v v1' v2 v3' v4 v5' accounts' tcatbals' c t rej
          (s.post clk (DalytranRecord.vals file.val[pos.val]) (CardXrefRecord.vals x)
            (AccountRecord.vals a)) ∧
        RInv accounts' tcatbals' ∧ v1'.val = v1.val ++ [t] ∧
        t.tran_id = (file.val[pos.val]).dalytran_id) := by
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
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, push_bytes_eq,
      digits_eq, vec_index_mut_eq, alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
    try bwp [not_false_eq_true, P9_val', hs]
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [UScalar.ofNatCore_val_eq]
    · rw [srem_val, ofIntCore_val', P9_val']
      exact tmod_id _ _ (by norm_num) (by omega) (by omega)
    · refine srel_post_rewrite hrel clk _ x a ja hja hfa c0 jc hjc hfc hsome ?na ?ha' _ ?hc ?hcf _ ?ht
        ?htf _ ?hv1' _ ?hv3' _ ?hv5' _ ?hacc' _ ?htc'
      case hv3' => rw [alloc.vec.Vec.from_val]
      case ha' =>
        rw [tAmt_vals]
        exact acctNew_vals a _ _ _ _ (by rw [srem_val, ofIntCore_val', P12_val])
          (by rw [ite_eq_left hs, srem_val, ofIntCore_val', P12_val]) (by rw [ite_eq_left hs])
      case hc =>
        rw [tAmt_vals]
        exact catUpd_vals c0 _ _ (by rw [srem_val, ofIntCore_val', P11_val])
      case hcf => rfl
      case ht => exact tranOf_vals tr hrel.tfill _ clock clk hclk hclen
      case htf => rfl
      case hv1' => rw [alloc.vec.Vec.from_val]
      case hv5' => rw [alloc.vec.Vec.from_val]
      case hacc' => rw [alloc.vec.Vec.set_val_eq, usz_val _ (by omega)]
      case htc' => rw [alloc.vec.Vec.set_val_eq, usz_val _ (by omega)]
    · refine ⟨fun b hb => ?_, fun c hc => ?_⟩
      · rw [alloc.vec.Vec.set_val_eq] at hb
        rcases List.mem_or_eq_of_mem_set hb with hb | rfl
        · exact hri.1 b hb
        · simp only [srem_val, ofIntCore_val', P12_val']
          have t1 := tmod_bound (a.acct_curr_bal.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          have t2 := tmod_bound (a.acct_curr_cyc_credit.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          omega
      · rw [alloc.vec.Vec.set_val_eq] at hc
        rcases List.mem_or_eq_of_mem_set hc with hc | rfl
        · exact hri.2 c hc
        · simp only [srem_val, ofIntCore_val', P11_val']
          have t1 := tmod_bound (c0.tran_cat_bal.val + (file.val[pos.val]).dalytran_amt.val)
            100000000000 (by norm_num)
          omega
    · rw [alloc.vec.Vec.from_val]
    · rfl
  · simp only [cbtrn02c.run_loop2.body]
    awp [hpos, hxs, has, hge, hlim, hcs, hci, hai, htd, hs, hia, hic, P9_val', P11_val', P12_val',
      srem_val, ofIntCore_val', db2_timestamp_eq]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, push_bytes_eq,
      digits_eq, vec_index_mut_eq, alpha76_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
    try bwp [not_false_eq_true, P9_val', hs]
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [UScalar.ofNatCore_val_eq]
    · rw [srem_val, ofIntCore_val', P9_val']
      exact tmod_id _ _ (by norm_num) (by omega) (by omega)
    · refine srel_post_rewrite hrel clk _ x a ja hja hfa c0 jc hjc hfc hsome ?na2 ?ha'2 _ ?hc2 ?hcf2 _
        ?ht2 ?htf2 _ ?hv1'2 _ ?hv3'2 _ ?hv5'2 _ ?hacc'2 _ ?htc'2
      case hv3'2 => rw [alloc.vec.Vec.from_val]
      case ha'2 =>
        rw [tAmt_vals]
        exact acctNew_vals a _ _ _ _ (by rw [srem_val, ofIntCore_val', P12_val])
          (by rw [ite_eq_right hs]) (by rw [ite_eq_right hs, srem_val, ofIntCore_val', P12_val])
      case hc2 =>
        rw [tAmt_vals]
        exact catUpd_vals c0 _ _ (by rw [srem_val, ofIntCore_val', P11_val])
      case hcf2 => rfl
      case ht2 => exact tranOf_vals tr hrel.tfill _ clock clk hclk hclen
      case htf2 => rfl
      case hv1'2 => rw [alloc.vec.Vec.from_val]
      case hv5'2 => rw [alloc.vec.Vec.from_val]
      case hacc'2 => rw [alloc.vec.Vec.set_val_eq, usz_val _ (by omega)]
      case htc'2 => rw [alloc.vec.Vec.set_val_eq, usz_val _ (by omega)]
    · refine ⟨fun b hb => ?_, fun c hc => ?_⟩
      · rw [alloc.vec.Vec.set_val_eq] at hb
        rcases List.mem_or_eq_of_mem_set hb with hb | rfl
        · exact hri.1 b hb
        · simp only [srem_val, ofIntCore_val', P12_val']
          have t1 := tmod_bound (a.acct_curr_bal.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          have t2 := tmod_bound (a.acct_curr_cyc_debit.val + (file.val[pos.val]).dalytran_amt.val)
            1000000000000 (by norm_num)
          omega
      · rw [alloc.vec.Vec.set_val_eq] at hc
        rcases List.mem_or_eq_of_mem_set hc with hc | rfl
        · exact hri.2 c hc
        · simp only [srem_val, ofIntCore_val', P11_val']
          have t1 := tmod_bound (c0.tran_cat_bal.val + (file.val[pos.val]).dalytran_amt.val)
            100000000000 (by norm_num)
          omega
    · rw [alloc.vec.Vec.from_val]
    · rfl

end EquivLean.Modernize.Cbtrn02c.Rust
