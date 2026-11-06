import EquivLean.Modernize.Cbtrn02c.RustRun5
/-!
# CBTRN02C → Rust: the model's lookups in Rust terms, the loop invariant, the end of the loop
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-! ## The model's lookups in Rust terms -/

/-- The key test of the cross-reference search. -/
def xp (d : cbtrn02c.DalytranRecord) (x : cbtrn02c.CardXrefRecord) : Bool :=
  decide (x.xref_card_num.val = d.dalytran_card_num.val)

theorem findXref_eq (xrefs : List cbtrn02c.CardXrefRecord) (d : cbtrn02c.DalytranRecord) :
    Model.findXref (xrefs.map CardXrefRecord.vals) (Model.tCard (DalytranRecord.vals d)) =
      if h : xrefs.findIdx (xp d) < xrefs.length then
        some (CardXrefRecord.vals xrefs[xrefs.findIdx (xp d)]) else none := by
  rw [Model.findXref, find_map_eq, xref_pred]; rfl

theorem findAcct_eq (accounts : List cbtrn02c.AccountRecord) (id : Int) :
    Model.findAcct (accounts.map AccountRecord.vals) id =
      if h : accounts.findIdx (fun a => a.acct_id.val == id) < accounts.length then
        some (AccountRecord.vals accounts[accounts.findIdx (fun a => a.acct_id.val == id)])
      else none := by
  rw [Model.findAcct, find_map_eq, acct_pred]

theorem findCat_eq (tcatbals : List cbtrn02c.TranCatBalRecord) (acct : I64)
    (ty : Std.Array U8 2#usize) (cd : I64) :
    Model.findCat (tcatbals.map TranCatBalRecord.vals) acct.val (ty.val.map ebc) cd.val =
      if h : tcatbals.findIdx (catKeyR acct ty cd) < tcatbals.length then
        some (TranCatBalRecord.vals tcatbals[tcatbals.findIdx (catKeyR acct ty cd)]) else none := by
  rw [Model.findCat, find_map_eq, cat_pred]

/-- The expiration test: the Rust prefix comparison is the model's. -/
theorem geEbc_iff (a : cbtrn02c.AccountRecord) (d : cbtrn02c.DalytranRecord) :
    geEbc a.acct_expiraion_date.val d.dalytran_orig_ts.val 10 = true ↔
      ¬ Sem.cmpBytes (Model.aExp (AccountRecord.vals a)) ((Model.tOrig (DalytranRecord.vals d)).take 10) =
        .lt := by
  rw [aExp_vals, tOrig_vals, geEbc, List.take_of_length_le (by rw [arr_len]; rfl), List.map_take]
  simp

/-- The limit test: `WS-TEMP-BAL` is Rust's `%`. -/
theorem limit_iff (a : cbtrn02c.AccountRecord) (d : cbtrn02c.DalytranRecord) :
    Model.aLimit (AccountRecord.vals a) < (Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
      (Model.aCC (AccountRecord.vals a) - Model.aCD (AccountRecord.vals a) +
        Model.tAmt (DalytranRecord.vals d))).2 ↔
      ¬ Int.tmod (a.acct_curr_cyc_credit.val - a.acct_curr_cyc_debit.val + d.dalytran_amt.val)
        100000000000 ≤ a.acct_credit_limit.val := by
  rw [fitNum_tmod _ (by rfl) (by rfl), show CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt.digits = 11 from rfl,
    aLimit_vals, aCC_vals, aCD_vals, tAmt_vals]
  norm_num

/-! ## The model's run -/

/-- The model's state after the first `k` daily records. -/
def foldAt (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (k : Nat) : Model.St :=
  (trans.take k).foldl (Model.step xrM clk) (Model.init accts0 cats0)

theorem foldAt_succ (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (k : Nat) (h : k < trans.length) :
    foldAt xrM clk accts0 cats0 trans (k + 1) =
      Model.step xrM clk (foldAt xrM clk accts0 cats0 trans k) trans[k] := by
  simp only [foldAt, take_succ_of_lt' h, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem foldAt_lens (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (k : Nat) :
    (foldAt xrM clk accts0 cats0 trans k).disp.length ≤ 1 + k ∧
      (foldAt xrM clk accts0 cats0 trans k).tranW.length ≤ k ∧
      (foldAt xrM clk accts0 cats0 trans k).rejW.length ≤ k ∧
      (foldAt xrM clk accts0 cats0 trans k).catW.length ≤ k ∧
      (foldAt xrM clk accts0 cats0 trans k).acctRW.length ≤ k ∧
      (foldAt xrM clk accts0 cats0 trans k).catRW.length ≤ k ∧
      (foldAt xrM clk accts0 cats0 trans k).rejects ≤ k ∧
      (foldAt xrM clk accts0 cats0 trans k).cats.length ≤ cats0.length + k := by
  have h := fold_lens xrM clk (trans.take k) (Model.init accts0 cats0)
  have h4 : (trans.take k).length ≤ k := by simp
  simp only [foldAt, Model.init, List.length_cons, List.length_nil] at h ⊢
  omega

/-! ## The loop invariant -/

/-- The transactions written so far have the ids of the first `k` daily records. -/
def TIds (file : Slice cbtrn02c.DalytranRecord) (k : Nat) (v1 : alloc.vec.Vec cbtrn02c.TranRecord) :
    Prop :=
  ∀ t ∈ v1.val, ∃ j, j < k ∧ ∃ h : j < file.val.length, t.tran_id = (file.val[j]'h).dalytran_id

/-- A daily record's id is not among those written before it (the domain: distinct ids). -/
theorem tdup_false (file : Slice cbtrn02c.DalytranRecord) (k : Nat) (hk : k < file.val.length)
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (hti : TIds file k v1)
    (hnd : ((file.val.map DalytranRecord.vals).map Model.tId).Nodup) :
    ¬ v1.val.findIdx (fun t => decide (t.tran_id.val = (file.val[k]).dalytran_id.val)) <
      v1.val.length := by
  intro hlt
  have hp := findIdx_pred_true _ _ hlt
  obtain ⟨j, hjk, hj, hid⟩ := hti _ (List.getElem_mem hlt)
  simp only [decide_eq_true_eq] at hp
  rw [hid] at hp
  have e : ((file.val.map DalytranRecord.vals).map Model.tId)[j]'(by simp; omega) =
      ((file.val.map DalytranRecord.vals).map Model.tId)[k]'(by simp; omega) := by
    simp only [List.getElem_map, tId_vals, hp]
  have := (List.Nodup.getElem_inj_iff hnd).1 e
  omega

/-- The invariant of the main loop: the position, the end-of-file flag, the count, the relation
with the model's state after the records read, the bounds, the ids written. -/
def LInv (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (eof : Bool) (tx rej : I64) : Prop :=
  pos.val ≤ file.val.length ∧ (eof = true → pos.val = file.val.length) ∧ tx.val = pos.val ∧
    SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej
      (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) pos.val) ∧
    RInv accounts tcatbals ∧ TIds file pos.val v1

/-! ## The end of the loop -/

set_option maxHeartbeats 2000000 in
/-- At the end of the file the flag is set. -/
theorem body_end (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64)
    (hge : ¬ pos.val < file.val.length) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => r = .ok (.cont (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos,
        true, tx, rej))) := by
  simp only [cbtrn02c.run_loop2.body]
  awp [hge]

/-- `TRANSACTIONS PROCESSED :`, `TRANSACTIONS REJECTED  :`, `END OF EXECUTION OF PROGRAM CBTRN02C`. -/
def procR : List U8 := [84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8, 67#u8, 84#u8, 73#u8, 79#u8, 78#u8,
  83#u8, 32#u8, 80#u8, 82#u8, 79#u8, 67#u8, 69#u8, 83#u8, 83#u8, 69#u8, 68#u8, 32#u8, 58#u8]
def rejR : List U8 := [84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8, 67#u8, 84#u8, 73#u8, 79#u8, 78#u8,
  83#u8, 32#u8, 82#u8, 69#u8, 74#u8, 69#u8, 67#u8, 84#u8, 69#u8, 68#u8, 32#u8, 32#u8, 58#u8]
def endR : List U8 := [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8,
  85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8, 82#u8,
  65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 84#u8, 82#u8, 78#u8, 48#u8, 50#u8, 67#u8]

theorem procR_text : procR.map UScalar.val = Model.txt "TRANSACTIONS PROCESSED :" := by decide
theorem rejR_text : rejR.map UScalar.val = Model.txt "TRANSACTIONS REJECTED  :" := by decide
theorem endR_text : endR.map UScalar.val = Model.txt "END OF EXECUTION OF PROGRAM CBTRN02C" := by
  decide

set_option maxHeartbeats 2000000 in
/-- **The end of the run**: the two counts and the end line displayed, RETURN-CODE. -/
theorem body_done (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64)
    (hl : v.val.length + 3 < Usize.max) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos true tx rej)
      (fun r => ∃ out, r = .ok (.done out) ∧
        out.displays.val.map (fun l => l.val.map (·.val)) = v.val.map (fun l => l.val.map (·.val)) ++
          [Model.txt "TRANSACTIONS PROCESSED :" ++ zpad 9 tx.val.natAbs,
            Model.txt "TRANSACTIONS REJECTED  :" ++ zpad 9 rej.val.natAbs,
            Model.txt "END OF EXECUTION OF PROGRAM CBTRN02C"] ∧
        out.transact_file_writes = v1 ∧ out.dalyrejs_file_writes = v2 ∧
        out.account_file_rewrites = v3 ∧ out.tcatbal_file_writes = v4 ∧
        out.tcatbal_file_rewrites = v5 ∧
        out.return_code.val = (if 0 < rej.val then 4 else 0) ∧ out.abended = false) := by
  have hm := usize_max_ge
  simp only [cbtrn02c.run_loop2.body]
  by_cases hr : 0 < rej.val
  · awp [hr]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, push_bytes_eq,
      digits_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
    try bwp [hr]
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
        Std.Array.make_val, digs_val]
      rw [← procR_text, ← rejR_text, ← endR_text]
      rfl
    · simp [hr]
  · awp [hr]
    simp (config := { maxSteps := 4000000 }) (disch := side_tac) only [lit_eq, push_bytes_eq,
      digits_eq, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right]
    try bwp [hr]
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
        Std.Array.make_val, digs_val]
      rw [← procR_text, ← rejR_text, ← endR_text]
      rfl
    · simp [hr]

end EquivLean.Modernize.Cbtrn02c.Rust

/-!
# CBTRN02C → Rust: one daily record (the six cases), against the loop invariant
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-- The state of the main loop. -/
abbrev LSt := alloc.vec.Vec (alloc.vec.Vec U8) × alloc.vec.Vec cbtrn02c.TranRecord ×
  alloc.vec.Vec cbtrn02c.RejectRecord × alloc.vec.Vec cbtrn02c.AccountRecord ×
  alloc.vec.Vec cbtrn02c.TranCatBalRecord × alloc.vec.Vec cbtrn02c.TranCatBalRecord ×
  alloc.vec.Vec cbtrn02c.AccountRecord × alloc.vec.Vec cbtrn02c.TranCatBalRecord ×
  cbtrn02c.DalytranRecord × cbtrn02c.CardXrefRecord × cbtrn02c.AccountRecord ×
  cbtrn02c.TranCatBalRecord × cbtrn02c.TranRecord × Usize × Bool × I64 × I64

/-- `LInv` on the loop state. -/
def LInvT (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) : LSt → Prop
  | (v, v1, v2, v3, v4, v5, accounts, tcatbals, _, _, _, tcr, tr, pos, eof, tx, rej) =>
    LInv file xrM clk accts0 cats0 v v1 v2 v3 v4 v5 accounts tcatbals tcr tr pos eof tx rej

/-- The variant: the records left, and the end-of-file step. -/
def VarT (file : Slice cbtrn02c.DalytranRecord) : LSt → Nat
  | (_, _, _, _, _, _, _, _, _, _, _, _, _, pos, eof, _, _) =>
    file.val.length - pos.val + (if eof then 0 else 1)

/-- After a reject: the invariant at the next record. -/
theorem next_rej (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) (k : Nat) (hk : k < file.val.length)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2' : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (d : cbtrn02c.DalytranRecord) (x' : cbtrn02c.CardXrefRecord)
    (a' : cbtrn02c.AccountRecord) (pos' : Usize) (tx' rej' : I64) (s' : Model.St)
    (hs' : foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) = s')
    (hri : RInv accounts tcatbals) (hti : TIds file k v1)
    (hpos' : pos'.val = k + 1) (htx' : tx'.val = k + 1)
    (hrel' : SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej' s') :
    LInvT file xrM clk accts0 cats0
        (v, v1, v2', v3, v4, v5, accounts, tcatbals, d, x', a', tcr, tr, pos', false, tx', rej') ∧
      VarT file (v, v1, v2', v3, v4, v5, accounts, tcatbals, d, x', a', tcr, tr, pos', false, tx', rej') <
        file.val.length - k + 1 := by
  refine ⟨?_, ?_⟩
  · simp only [LInvT, LInv]
    refine ⟨by omega, (fun h => by cases h), by omega, by rw [hpos', hs']; exact hrel', hri, ?_⟩
    rw [hpos']
    intro t ht
    obtain ⟨j, hj, hjl, hid⟩ := hti t ht
    exact ⟨j, by omega, hjl, hid⟩
  · simp only [VarT, Bool.false_eq_true, _root_.ite_false]
    omega

/-- After a posted transaction: the invariant at the next record. -/
theorem next_post (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) (k : Nat) (hk : k < file.val.length)
    (v' : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 v1' : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3' : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4' v5' : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts' : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals' : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (c : cbtrn02c.TranCatBalRecord)
    (t : cbtrn02c.TranRecord) (d : cbtrn02c.DalytranRecord) (x : cbtrn02c.CardXrefRecord)
    (a' : cbtrn02c.AccountRecord) (pos' : Usize) (tx' rej : I64) (s' : Model.St)
    (hs' : foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) = s')
    (hti : TIds file k v1) (hv1' : v1'.val = v1.val ++ [t])
    (htid : t.tran_id = (file.val[k]'hk).dalytran_id)
    (hpos' : pos'.val = k + 1) (htx' : tx'.val = k + 1)
    (hrel' : SRel v' v1' v2 v3' v4' v5' accounts' tcatbals' c t rej s')
    (hri' : RInv accounts' tcatbals') :
    LInvT file xrM clk accts0 cats0
        (v', v1', v2, v3', v4', v5', accounts', tcatbals', d, x, a', c, t, pos', false, tx', rej) ∧
      VarT file (v', v1', v2, v3', v4', v5', accounts', tcatbals', d, x, a', c, t, pos', false, tx', rej) <
        file.val.length - k + 1 := by
  refine ⟨?_, ?_⟩
  · simp only [LInvT, LInv]
    refine ⟨by omega, (fun h => by cases h), by omega, by rw [hpos', hs']; exact hrel', hri', ?_⟩
    rw [hpos']
    intro t' ht'
    rw [hv1'] at ht'
    rcases List.mem_append.1 ht' with h | h
    · obtain ⟨j, hj, hjl, hid⟩ := hti t' h
      exact ⟨j, by omega, hjl, hid⟩
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨k, by omega, hk, htid⟩
  · simp only [VarT, Bool.false_eq_true, _root_.ite_false]
    omega

set_option maxHeartbeats 4000000 in
/-- **One daily record**: from the invariant at record `k`, the body continues with the
invariant at record `k + 1` (the model's six cases). -/
theorem body_next (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (hclk : clock.val.map (·.val) = rustLine clk)
    (hclen : clk.length = 21) (accts0 cats0 : List (List FVal))
    (hv1 : ∀ d ∈ file.val, DalytranRecord.Valid (DalytranRecord.vals d))
    (hnd : ((file.val.map DalytranRecord.vals).map Model.tId).Nodup)
    (hsz : file.val.length + cats0.length < 2 ^ 28)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64)
    (hinv : LInv file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 v v1 v2 v3 v4 v5 accounts
      tcatbals tcr tr pos false tx rej)
    (hlt : pos.val < file.val.length) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => ∃ st', r = .ok (.cont st') ∧
        LInvT file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 st' ∧
        VarT file st' < file.val.length - pos.val + 1) := by
  obtain ⟨-, -, htxk, hrel, hri, hti⟩ := hinv
  have hm := usize_max_ge
  have hd := List.getElem_mem hlt
  have hfs := foldAt_succ (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
    (file.val.map DalytranRecord.vals) pos.val (by simp; exact hlt)
  rw [List.getElem_map] at hfs
  have hlens := foldAt_lens (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
    (file.val.map DalytranRecord.vals) pos.val
  have e0 := congrArg List.length hrel.disp
  have e1 := congrArg List.length hrel.tranW
  have e2 := congrArg List.length hrel.rejW
  have e3 := congrArg List.length hrel.acctRW
  have e4 := congrArg List.length hrel.catW
  have e5 := congrArg List.length hrel.catRW
  have e6 := congrArg List.length hrel.cats
  simp only [List.length_map] at e0 e1 e2 e3 e4 e5 e6
  have hrj := hrel.rej
  have hl0 : v.val.length < Usize.max := by omega
  have hl1 : v1.val.length < Usize.max := by omega
  have hl2 : v2.val.length < Usize.max := by omega
  have hl3 : v3.val.length < Usize.max := by omega
  have hl4 : v4.val.length < Usize.max := by omega
  have hl5 : v5.val.length < Usize.max := by omega
  have hlt' : tcatbals.val.length < Usize.max := by omega
  have htx : 0 ≤ tx.val ∧ tx.val + 1 < 10 ^ 9 := by omega
  have hrj' : 0 ≤ rej.val ∧ rej.val + 1 < 10 ^ 9 := by omega
  have hamt := (natAbs_lt_iff' _ _).1 (tran_amt_bound _ (hv1 _ hd))
  norm_num at hamt
  by_cases hx : xrefs.val.findIdx (xp file.val[pos.val]) < xrefs.val.length
  · -- the card is known
    have hxs : cbtrn02c.run_loop2_loop0 xrefs file.val[pos.val] cxr 0#usize =
        .ok (file.val[pos.val], xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])], true) := by
      rw [xref_search_eq, show (fun x : cbtrn02c.CardXrefRecord =>
        decide (x.xref_card_num.val = (file.val[pos.val]).dalytran_card_num.val)) =
          xp file.val[pos.val] from rfl, searchRes_found _ _ _ _ hx]
    by_cases ha : accounts.val.findIdx (fun b => b.acct_id.val ==
        (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val) < accounts.val.length
    · -- the account is known
      have has := acct_search_eq accounts ar
        (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
      rw [searchRes_found _ _ _ _ ha] at has
      have hab := hri.1 _ (List.getElem_mem ha)
      have hpa := findIdx_pred_true _ _ ha
      simp only [beq_iff_eq] at hpa
      have hstep0 : ∀ (P : Model.St),
          (Model.step (xrefs.val.map CardXrefRecord.vals) clk
            (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
              (file.val.map DalytranRecord.vals) pos.val) (DalytranRecord.vals file.val[pos.val]) = P) ↔
          ((if Sem.cmpBytes (Model.aExp (AccountRecord.vals accounts.val[accounts.val.findIdx
                (fun b => b.acct_id.val ==
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]))
              ((Model.tOrig (DalytranRecord.vals file.val[pos.val])).take 10) = .lt then
            (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
              (file.val.map DalytranRecord.vals) pos.val).reject
              (DalytranRecord.vals file.val[pos.val]) 103 CardDemo.Cbtrn02c.expiredDesc
          else if Model.aLimit (AccountRecord.vals accounts.val[accounts.val.findIdx
                (fun b => b.acct_id.val ==
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]) <
              (Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
                (Model.aCC (AccountRecord.vals accounts.val[accounts.val.findIdx
                  (fun b => b.acct_id.val ==
                    (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]) -
                  Model.aCD (AccountRecord.vals accounts.val[accounts.val.findIdx
                  (fun b => b.acct_id.val ==
                    (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]) +
                  Model.tAmt (DalytranRecord.vals file.val[pos.val]))).2 then
            (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
              (file.val.map DalytranRecord.vals) pos.val).reject
              (DalytranRecord.vals file.val[pos.val]) 102 CardDemo.Cbtrn02c.overLimitDesc
          else
            (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
              (file.val.map DalytranRecord.vals) pos.val).post clk
              (DalytranRecord.vals file.val[pos.val])
              (CardXrefRecord.vals xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])])
              (AccountRecord.vals accounts.val[accounts.val.findIdx (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)])) = P) := by
        intro P
        unfold Model.step
        rw [findXref_eq, dite_eq_left hx]
        dsimp only
        rw [xAcct_vals, ← hrel.accts, findAcct_eq, dite_eq_left ha]
      by_cases hc : Sem.cmpBytes (Model.aExp (AccountRecord.vals accounts.val[accounts.val.findIdx
          (fun b => b.acct_id.val ==
            (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]))
          ((Model.tOrig (DalytranRecord.vals file.val[pos.val])).take 10) = .lt
      · -- reject 103
        have hexp : geEbc (accounts.val[accounts.val.findIdx (fun b => b.acct_id.val ==
            (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]).acct_expiraion_date.val
            (file.val[pos.val]).dalytran_orig_ts.val 10 = false := by
          rw [Bool.eq_false_iff]; intro h; exact (geEbc_iff _ _).1 h hc
        have hstep := (hstep0 _).2 (by rw [ite_eq_left hc])
        refine wp_mono (body_rej103 file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
          pos tx rej _ hrel hlt _ _ hxs has ⟨hab.2.2.1, hab.2.2.2.1, hab.2.2.2.2.1, hab.2.2.2.2.2⟩ hamt
          hexp htx hrj' hl2) ?_
        rintro r ⟨v2', x', a', pos', tx', rej', rfl, hp, ht, hr⟩
        exact ⟨_, rfl, next_rej file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
          tcr tr _ x' a' pos' tx' rej' _ (by rw [hfs, hstep]) hri hti hp (by omega) hr⟩
      · have hexp : geEbc (accounts.val[accounts.val.findIdx (fun b => b.acct_id.val ==
            (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]).acct_expiraion_date.val
            (file.val[pos.val]).dalytran_orig_ts.val 10 = true := (geEbc_iff _ _).2 hc
        by_cases hl : Model.aLimit (AccountRecord.vals accounts.val[accounts.val.findIdx
              (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]) <
            (Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
              (Model.aCC (AccountRecord.vals accounts.val[accounts.val.findIdx
                (fun b => b.acct_id.val ==
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]) -
                Model.aCD (AccountRecord.vals accounts.val[accounts.val.findIdx
                (fun b => b.acct_id.val ==
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]) +
                Model.tAmt (DalytranRecord.vals file.val[pos.val]))).2
        · -- reject 102
          have hstep := (hstep0 _).2 (by rw [ite_eq_right hc, ite_eq_left hl])
          refine wp_mono (body_rej102 file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr
            tr pos tx rej _ hrel hlt _ _ hxs has ⟨hab.2.2.1, hab.2.2.2.1, hab.2.2.2.2.1, hab.2.2.2.2.2⟩
            hamt hexp ((limit_iff _ _).1 hl) htx hrj' hl2) ?_
          rintro r ⟨v2', x', a', pos', tx', rej', rfl, hp, ht, hr⟩
          exact ⟨_, rfl, next_rej file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
            tcr tr _ x' a' pos' tx' rej' _ (by rw [hfs, hstep]) hri hti hp (by omega) hr⟩
        · -- posted
          have hstep := (hstep0 _).2 (by rw [ite_eq_right hc, ite_eq_right hl])
          have hlim := not_not.1 (fun h => hl ((limit_iff _ _).2 h))
          have hai : cbtrn02c.run_loop2_loop4 accounts (accounts.val[accounts.val.findIdx
              (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]).acct_id 0#usize =
              .ok (usz (accounts.val.findIdx (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)), true) := by
            rw [acct_idx_eq, hpa, searchRes_found _ _ _ _ ha]
          have hai' : cbtrn02c.run_loop2_loop7 accounts (accounts.val[accounts.val.findIdx
              (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]).acct_id 0#usize =
              .ok (usz (accounts.val.findIdx (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)), true) := by
            rw [acct_idx_eq', hpa, searchRes_found _ _ _ _ ha]
          have hfa : accounts.val.findIdx (fun b => b.acct_id.val ==
              (accounts.val[accounts.val.findIdx (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)]).acct_id.val) =
              accounts.val.findIdx (fun b => b.acct_id.val ==
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val) := by
            rw [hpa]
          have htd := tran_dup_eq v1 (file.val[pos.val]).dalytran_id
          rw [searchRes_nf _ _ _ _ (tdup_false file pos.val hlt v1 hti hnd)] at htd
          have htd' := tran_dup_eq' v1 (file.val[pos.val]).dalytran_id
          rw [searchRes_nf _ _ _ _ (tdup_false file pos.val hlt v1 hti hnd)] at htd'
          by_cases hcf : tcatbals.val.findIdx (catKeyR
              (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
              (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd) <
              tcatbals.val.length
          · -- the category record exists: rewritten
            have hcs := cat_search_eq tcatbals tcr
              (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
              (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd
            rw [searchRes_found _ _ _ _ hcf] at hcs
            have hpc := findIdx_pred_true _ _ hcf
            simp only [catKeyR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpc
            have hkey : catKeyR (tcatbals.val[tcatbals.val.findIdx (catKeyR
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                  (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]).trancat_acct_id
                (tcatbals.val[tcatbals.val.findIdx (catKeyR
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                  (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]).trancat_type_cd
                (tcatbals.val[tcatbals.val.findIdx (catKeyR
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                  (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]).trancat_cd =
                catKeyR (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                  (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd := by
              funext e
              simp only [catKeyR, hpc.1.1, hpc.1.2, hpc.2]
            have hci := cat_idx_eq tcatbals
              (tcatbals.val[tcatbals.val.findIdx (catKeyR
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]).trancat_acct_id
              (tcatbals.val[tcatbals.val.findIdx (catKeyR
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]).trancat_type_cd
              (tcatbals.val[tcatbals.val.findIdx (catKeyR
                (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]).trancat_cd
            rw [hkey, searchRes_found _ _ _ _ hcf] at hci
            have hsome : Model.findCat
                (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
                  (file.val.map DalytranRecord.vals) pos.val).cats
                (Model.xAcct (CardXrefRecord.vals xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]))
                (Model.tType (DalytranRecord.vals file.val[pos.val]))
                (Model.tCat (DalytranRecord.vals file.val[pos.val])) =
                some (TranCatBalRecord.vals tcatbals.val[tcatbals.val.findIdx (catKeyR
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                  (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd)]) := by
              rw [xAcct_vals, tType_vals, tCat_vals, ← hrel.cats, findCat_eq, dite_eq_left hcf]
            have hfc : tcatbals.val.findIdx (Model.catKey
                (Model.xAcct (CardXrefRecord.vals xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]))
                (Model.tType (DalytranRecord.vals file.val[pos.val]))
                (Model.tCat (DalytranRecord.vals file.val[pos.val])) ∘ TranCatBalRecord.vals) =
                tcatbals.val.findIdx (catKeyR
                  (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
                  (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd) := by
              rw [xAcct_vals, tType_vals, tCat_vals, cat_pred]
            refine wp_mono (body_post_rewrite file xrefs clock clk hclk hclen v v1 v2 v3 v4 v5 accounts
              tcatbals dr cxr ar tcr tr pos tx rej _ hrel hri hlt _ _ _ ha rfl hfa _ _ hcf rfl hfc hsome
              hxs has hamt hexp hlim hcs hci hai' htd' htx hl1 hl3 hl5) ?_
            rintro r ⟨v1', v3', v5', accounts', tcatbals', a', c, t, pos', tx', rfl, hp, ht, hr, hri',
              hv1', htid⟩
            exact ⟨_, rfl, next_post file _ clk accts0 cats0 pos.val hlt v v1 v1' v2 v3' v4 v5' accounts'
              tcatbals' c t _ _ a' pos' tx' rej _ (by rw [hfs, hstep]) hti hv1' htid hp (by omega) hr
              hri'⟩
          · -- a new category record
            have hcs := cat_search_eq tcatbals tcr
              (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
              (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd
            rw [searchRes_nf _ _ _ _ hcf] at hcs
            have hdup := cat_dup_eq tcatbals
              (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
              (file.val[pos.val]).dalytran_type_cd (file.val[pos.val]).dalytran_cat_cd
            rw [searchRes_nf _ _ _ _ hcf] at hdup
            have hnone : Model.findCat
                (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
                  (file.val.map DalytranRecord.vals) pos.val).cats
                (Model.xAcct (CardXrefRecord.vals xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]))
                (Model.tType (DalytranRecord.vals file.val[pos.val]))
                (Model.tCat (DalytranRecord.vals file.val[pos.val])) = none := by
              rw [xAcct_vals, tType_vals, tCat_vals, ← hrel.cats, findCat_eq, dite_eq_right hcf]
            refine wp_mono (body_post_create file xrefs clock clk hclk hclen v v1 v2 v3 v4 v5 accounts
              tcatbals dr cxr ar tcr tr pos tx rej _ hrel hri hlt _ _ _ ha rfl hfa hxs has hamt hexp
              hlim hcs hdup hai htd hnone htx hl0 hl1 hl3 hl4 hlt') ?_
            rintro r ⟨v', v1', v3', v4', accounts', tcatbals', a', c, t, pos', tx', rfl, hp, ht, hr,
              hri', hv1', htid⟩
            exact ⟨_, rfl, next_post file _ clk accts0 cats0 pos.val hlt v' v1 v1' v2 v3' v4' v5
              accounts' tcatbals' c t _ _ a' pos' tx' rej _ (by rw [hfs, hstep]) hti hv1' htid hp
              (by omega) hr hri'⟩
    · -- reject 101
      have has := acct_search_eq accounts ar
        (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id
      rw [searchRes_nf _ _ _ _ ha] at has
      have hstep : Model.step (xrefs.val.map CardXrefRecord.vals) clk
          (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
            (file.val.map DalytranRecord.vals) pos.val) (DalytranRecord.vals file.val[pos.val]) =
          (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
            (file.val.map DalytranRecord.vals) pos.val).reject (DalytranRecord.vals file.val[pos.val]) 101
            CardDemo.Cbtrn02c.noAcctDesc := by
        unfold Model.step
        rw [findXref_eq, dite_eq_left hx]
        dsimp only
        rw [xAcct_vals, ← hrel.accts, findAcct_eq, dite_eq_right ha]
      refine wp_mono (body_rej101 file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos tx rej _ hrel hlt _ hxs has htx hrj' hl2) ?_
      rintro r ⟨v2', x', a', pos', tx', rej', rfl, hp, ht, hr⟩
      exact ⟨_, rfl, next_rej file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
        tcr tr _ x' a' pos' tx' rej' _ (by rw [hfs, hstep]) hri hti hp (by omega) hr⟩
  · -- reject 100
    have hstep : Model.step (xrefs.val.map CardXrefRecord.vals) clk
        (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
          (file.val.map DalytranRecord.vals) pos.val) (DalytranRecord.vals file.val[pos.val]) =
        (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
          (file.val.map DalytranRecord.vals) pos.val).reject (DalytranRecord.vals file.val[pos.val]) 100
          CardDemo.Cbtrn02c.badCardDesc := by
      unfold Model.step
      rw [findXref_eq, dite_eq_right hx]
    refine wp_mono (body_rej100 file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
      pos tx rej _ hrel hlt hx htx hrj' hl2) ?_
    rintro r ⟨v2', x', pos', tx', rej', rfl, hp, ht, hr⟩
    exact ⟨_, rfl, next_rej file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
      tcr tr _ x' ar pos' tx' rej' _ (by rw [hfs, hstep]) hri hti hp (by omega) hr⟩

end EquivLean.Modernize.Cbtrn02c.Rust
