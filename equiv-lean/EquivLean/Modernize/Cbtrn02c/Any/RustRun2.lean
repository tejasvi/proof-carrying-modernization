import EquivLean.Modernize.Cbtrn02c.Any.RustRun1
import EquivLean.Modernize.Cbtrn02c.RustRun

/-!
# CBTRN02C → Rust on any input: the main loop

`Model.runX`'s state before the stop is `Model.run`'s (`foldAtX` = `⟨foldAt, false⟩`); the loop
invariant `LInvX` is the old `LInv` with that equation for the ids written (no distinct ids
assumed). At a posted transaction with a written id, the body returns `runX`'s outputs at the stop
(`body_post_create_dup`, `body_post_rewrite_dup`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-! ## The model on any input -/

/-- `Model.runX`'s state after the first `k` daily records. -/
def foldAtX (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (k : Nat) : Model.StX :=
  (trans.take k).foldl (Model.stepX xrM clk) ⟨Model.init accts0 cats0, false⟩

theorem foldAtX_succ (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (k : Nat) (h : k < trans.length) :
    foldAtX xrM clk accts0 cats0 trans (k + 1) =
      Model.stepX xrM clk (foldAtX xrM clk accts0 cats0 trans k) trans[k] := by
  simp only [foldAtX, take_succ_of_lt' h, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem post_posted (clk : List UInt8) (s : Model.St) (t x a : List FVal) :
    (s.post clk t x a).posted = s.posted + 1 := by
  unfold Model.St.post
  split <;> rfl

theorem reject_not_dup {xrM : List (List FVal)} {clk : List UInt8} {s : Model.St} {t : List FVal}
    {code : Int} {desc : List UInt8} (h : Model.step xrM clk s t = s.reject t code desc) :
    ¬ ((Model.step xrM clk s t).posted = s.posted + 1 ∧ Model.tId t ∈ s.tranW.map Model.tId) := by
  rw [h]
  simp [Model.St.reject]

/-- Before the stop, a record without a repeated written id: `stepX` is `step`. -/
theorem foldAtX_next (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal))
    (clk : List UInt8) (accts0 cats0 : List (List FVal)) (k : Nat) (hk : k < file.val.length)
    (hX : foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k =
      ⟨foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k, false⟩)
    (h : ¬ ((Model.step xrM clk (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k)
        (DalytranRecord.vals file.val[k])).posted =
        (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k).posted + 1 ∧
      Model.tId (DalytranRecord.vals file.val[k]) ∈
        (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k).tranW.map Model.tId)) :
    foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) =
      ⟨Model.step xrM clk (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k)
        (DalytranRecord.vals file.val[k]), false⟩ := by
  rw [foldAtX_succ _ _ _ _ _ _ (by simp; exact hk), hX, List.getElem_map]
  simp only [Model.stepX, Bool.false_eq_true, ↓reduceIte]
  rw [ite_eq_right h]

/-- A posted record with a written id: the stop. -/
theorem foldAtX_dup (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal))
    (clk : List UInt8) (accts0 cats0 : List (List FVal)) (k : Nat) (hk : k < file.val.length)
    (hX : foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k =
      ⟨foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k, false⟩)
    (h : (Model.step xrM clk (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k)
        (DalytranRecord.vals file.val[k])).posted =
        (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k).posted + 1 ∧
      Model.tId (DalytranRecord.vals file.val[k]) ∈
        (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k).tranW.map Model.tId) :
    foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) =
      ⟨dupSt (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k)
        (Model.step xrM clk (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) k)
          (DalytranRecord.vals file.val[k])), true⟩ := by
  rw [foldAtX_succ _ _ _ _ _ _ (by simp; exact hk), hX, List.getElem_map]
  simp only [Model.stepX, Bool.false_eq_true, ↓reduceIte]
  rw [ite_eq_left h]
  rfl

theorem foldl_stepX_stopped (xrM : List (List FVal)) (clk : List UInt8) :
    ∀ (ts : List (List FVal)) (x : Model.StX), x.stop = true → ts.foldl (Model.stepX xrM clk) x = x
  | [], _, _ => rfl
  | t :: ts, x, h => by
    rw [List.foldl_cons, show Model.stepX xrM clk x t = x by simp [Model.stepX, h]]
    exact foldl_stepX_stopped xrM clk ts x h

/-- After the stop nothing changes. -/
theorem foldAtX_stopped (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 trans : List (List FVal)) (k : Nat)
    (h : (foldAtX xrM clk accts0 cats0 trans k).stop = true) :
    foldAtX xrM clk accts0 cats0 trans trans.length = foldAtX xrM clk accts0 cats0 trans k := by
  have e : trans.take trans.length = trans.take k ++ trans.drop k := by
    rw [List.take_of_length_le (le_refl _), List.take_append_drop]
  simp only [foldAtX] at h ⊢
  rw [e, List.foldl_append]
  exact foldl_stepX_stopped xrM clk _ _ h

theorem runX_stop (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (sd : Model.St) (h : foldAtX xrM clk accts0 cats0 trans trans.length = ⟨sd, true⟩) :
    Model.runX trans xrM accts0 cats0 clk = stopOut sd := by
  have e : trans.foldl (Model.stepX xrM clk) ⟨Model.init accts0 cats0, false⟩ = ⟨sd, true⟩ := by
    rw [← h, foldAtX, List.take_of_length_le (le_refl _)]
  simp only [Model.runX, e, ↓reduceIte]
  rfl

theorem runX_nostop (xrM : List (List FVal)) (clk : List UInt8) (accts0 cats0 trans : List (List FVal))
    (s : Model.St) (h : foldAtX xrM clk accts0 cats0 trans trans.length = ⟨s, false⟩) :
    Model.runX trans xrM accts0 cats0 clk =
      { disp := s.disp ++ [Model.txt "TRANSACTIONS PROCESSED :" ++ zpad 9 trans.length,
          Model.txt "TRANSACTIONS REJECTED  :" ++ zpad 9 s.rejects,
          Model.txt "END OF EXECUTION OF PROGRAM CBTRN02C"],
        tranW := s.tranW, rejW := s.rejW, catW := s.catW, acctRW := s.acctRW, catRW := s.catRW,
        rc := if 0 < s.rejects then 4 else 0, abended := false } := by
  have e : trans.foldl (Model.stepX xrM clk) ⟨Model.init accts0 cats0, false⟩ = ⟨s, false⟩ := by
    rw [← h, foldAtX, List.take_of_length_le (le_refl _)]
  simp only [Model.runX, e, Bool.false_eq_true, ↓reduceIte]

/-- The Rust duplicate check finds the id exactly when the model's transaction file holds it. -/
theorem tdup_iff {v1 : alloc.vec.Vec cbtrn02c.TranRecord} {s : Model.St}
    (hw : v1.val.map TranRecord.vals = s.tranW) (d : cbtrn02c.DalytranRecord) :
    v1.val.findIdx (fun t => decide (t.tran_id.val = d.dalytran_id.val)) < v1.val.length ↔
      Model.tId (DalytranRecord.vals d) ∈ s.tranW.map Model.tId := by
  rw [← hw, List.map_map, List.findIdx_lt_length]
  simp only [List.mem_map, Function.comp_apply, tranId_vals, tId_vals, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, by rw [he]⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, map_ebc_inj.1 he⟩

/-! ## The loop invariant -/

/-- The invariant of the main loop on any input: `LInv` without the ids, and no stop so far. -/
def LInvX (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (v1 : alloc.vec.Vec cbtrn02c.TranRecord) (v2 : alloc.vec.Vec cbtrn02c.RejectRecord)
    (v3 : alloc.vec.Vec cbtrn02c.AccountRecord) (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (eof : Bool) (tx rej : I64) : Prop :=
  pos.val ≤ file.val.length ∧ (eof = true → pos.val = file.val.length) ∧ tx.val = pos.val ∧
    SRel v v1 v2 v3 v4 v5 accounts tcatbals tcr tr rej
      (foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) pos.val) ∧
    RInv accounts tcatbals ∧
    foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) pos.val =
      ⟨foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) pos.val, false⟩

/-- `LInvX` on the loop state. -/
def LInvTX (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) : LSt → Prop
  | (v, v1, v2, v3, v4, v5, accounts, tcatbals, _, _, _, tcr, tr, pos, eof, tx, rej) =>
    LInvX file xrM clk accts0 cats0 v v1 v2 v3 v4 v5 accounts tcatbals tcr tr pos eof tx rej

/-- The outputs of `Model.runX`. -/
def FinalX (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8) (out : cbtrn02c.Output) :
    Prop :=
  OutRel out (Model.runX vals1 vals2 vals3 vals4 clk)

/-- After a reject: the invariant at the next record. -/
theorem next_rejX (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) (k : Nat) (hk : k < file.val.length)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2' : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (d : cbtrn02c.DalytranRecord) (x' : cbtrn02c.CardXrefRecord)
    (a' : cbtrn02c.AccountRecord) (pos' : Usize) (tx' rej' : I64) (s' : Model.St)
    (hs' : foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) = s')
    (hri : RInv accounts tcatbals)
    (hX' : foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) = ⟨s', false⟩)
    (hpos' : pos'.val = k + 1) (htx' : tx'.val = k + 1)
    (hrel' : SRel v v1 v2' v3 v4 v5 accounts tcatbals tcr tr rej' s') :
    LInvTX file xrM clk accts0 cats0
        (v, v1, v2', v3, v4, v5, accounts, tcatbals, d, x', a', tcr, tr, pos', false, tx', rej') ∧
      VarT file (v, v1, v2', v3, v4, v5, accounts, tcatbals, d, x', a', tcr, tr, pos', false, tx', rej') <
        file.val.length - k + 1 := by
  refine ⟨?_, ?_⟩
  · simp only [LInvTX, LInvX]
    refine ⟨by omega, (fun h => by cases h), by omega, by rw [hpos', hs']; exact hrel', hri, ?_⟩
    rw [hpos', hX', hs']
  · simp only [VarT, Bool.false_eq_true, _root_.ite_false]
    omega

/-- After a posted transaction (its id new): the invariant at the next record. -/
theorem next_postX (file : Slice cbtrn02c.DalytranRecord) (xrM : List (List FVal)) (clk : List UInt8)
    (accts0 cats0 : List (List FVal)) (k : Nat) (hk : k < file.val.length)
    (v' : alloc.vec.Vec (alloc.vec.Vec U8)) (v1' : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3' : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4' v5' : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts' : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals' : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (c : cbtrn02c.TranCatBalRecord)
    (t : cbtrn02c.TranRecord) (d : cbtrn02c.DalytranRecord) (x : cbtrn02c.CardXrefRecord)
    (a' : cbtrn02c.AccountRecord) (pos' : Usize) (tx' rej : I64) (s' : Model.St)
    (hs' : foldAt xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) = s')
    (hX' : foldAtX xrM clk accts0 cats0 (file.val.map DalytranRecord.vals) (k + 1) = ⟨s', false⟩)
    (hpos' : pos'.val = k + 1) (htx' : tx'.val = k + 1)
    (hrel' : SRel v' v1' v2 v3' v4' v5' accounts' tcatbals' c t rej s')
    (hri' : RInv accounts' tcatbals') :
    LInvTX file xrM clk accts0 cats0
        (v', v1', v2, v3', v4', v5', accounts', tcatbals', d, x, a', c, t, pos', false, tx', rej) ∧
      VarT file (v', v1', v2, v3', v4', v5', accounts', tcatbals', d, x, a', c, t, pos', false, tx', rej) <
        file.val.length - k + 1 := by
  refine ⟨?_, ?_⟩
  · simp only [LInvTX, LInvX]
    refine ⟨by omega, (fun h => by cases h), by omega, by rw [hpos', hs']; exact hrel', hri', ?_⟩
    rw [hpos', hX', hs']
  · simp only [VarT, Bool.false_eq_true, _root_.ite_false]
    omega

set_option maxHeartbeats 4000000 in
/-- **One daily record, any input**: from the invariant at record `k`, the body continues with
the invariant at record `k + 1`, or (a posted transaction whose id was already written) returns
`Model.runX`'s outputs. -/
theorem body_nextX (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (hclk : clock.val.map (·.val) = rustLine clk)
    (hclen : clk.length = 21) (accts0 cats0 : List (List FVal))
    (hv1 : ∀ d ∈ file.val, DalytranRecord.Valid (DalytranRecord.vals d))
    (hsz : file.val.length + cats0.length < 2 ^ 28)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (tx rej : I64)
    (hinv : LInvX file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 v v1 v2 v3 v4 v5 accounts
      tcatbals tcr tr pos false tx rej)
    (hlt : pos.val < file.val.length) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos false tx rej)
      (fun r => (∃ st', r = .ok (.cont st') ∧
        LInvTX file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 st' ∧
        VarT file st' < file.val.length - pos.val + 1) ∨
        (∃ out, r = .ok (.done out) ∧ FinalX (file.val.map DalytranRecord.vals)
          (xrefs.val.map CardXrefRecord.vals) accts0 cats0 clk out)) := by
  obtain ⟨-, -, htxk, hrel, hri, hX⟩ := hinv
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
  have hl0' : v.val.length + 4 < Usize.max := by omega
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
        exact .inl ⟨_, rfl, next_rejX file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
          tcr tr _ x' a' pos' tx' rej' _ (by rw [hfs, hstep]) hri
          (by rw [foldAtX_next file _ clk accts0 cats0 pos.val hlt hX (reject_not_dup hstep), hstep]) hp
          (by omega) hr⟩
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
          exact .inl ⟨_, rfl, next_rejX file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
            tcr tr _ x' a' pos' tx' rej' _ (by rw [hfs, hstep]) hri
          (by rw [foldAtX_next file _ clk accts0 cats0 pos.val hlt hX (reject_not_dup hstep), hstep]) hp
          (by omega) hr⟩
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
          have hfin : v1.val.findIdx (fun t => decide (t.tran_id.val = (file.val[pos.val]).dalytran_id.val)) <
              v1.val.length → ∀ out, OutRel out (stopOut (dupSt
                (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
                  (file.val.map DalytranRecord.vals) pos.val)
                ((foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
                  (file.val.map DalytranRecord.vals) pos.val).post clk
                  (DalytranRecord.vals file.val[pos.val])
                  (CardXrefRecord.vals xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])])
                  (AccountRecord.vals accounts.val[accounts.val.findIdx (fun b => b.acct_id.val ==
                    (xrefs.val[xrefs.val.findIdx (xp file.val[pos.val])]).xref_acct_id.val)])))) →
              FinalX (file.val.map DalytranRecord.vals) (xrefs.val.map CardXrefRecord.vals) accts0 cats0
                clk out := by
            intro hdx out hout
            have hX1 := foldAtX_dup file _ clk accts0 cats0 pos.val hlt hX
              ⟨by rw [hstep, post_posted], (tdup_iff hrel.tranW _).1 hdx⟩
            have hXn := (foldAtX_stopped _ _ _ _ _ (pos.val + 1) (by rw [hX1])).trans hX1
            unfold FinalX
            rw [runX_stop _ _ _ _ _ _ hXn, hstep]
            exact hout
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
            by_cases hdx : v1.val.findIdx
                (fun t => decide (t.tran_id.val = (file.val[pos.val]).dalytran_id.val)) < v1.val.length
            · -- a repeated id: the abend
              have htd' := tran_dup_eq' v1 (file.val[pos.val]).dalytran_id
              rw [searchRes_found _ _ _ _ hdx] at htd'
              refine wp_mono (body_post_rewrite_dup file xrefs clock clk v v1 v2 v3 v4 v5 accounts
                tcatbals dr cxr ar tcr tr pos tx rej _ hrel hri hlt _ _ _ ha rfl hfa _ _ hcf rfl hsome
                hxs has hamt hexp hlim hcs hci hai' htd' htx hl0' hl3 hl5) ?_
              rintro r ⟨out, rfl, hout⟩
              exact .inr ⟨out, rfl, hfin hdx out hout⟩
            · have htd' := tran_dup_eq' v1 (file.val[pos.val]).dalytran_id
              rw [searchRes_nf _ _ _ _ hdx] at htd'
              refine wp_mono (body_post_rewrite file xrefs clock clk hclk hclen v v1 v2 v3 v4 v5 accounts
                tcatbals dr cxr ar tcr tr pos tx rej _ hrel hri hlt _ _ _ ha rfl hfa _ _ hcf rfl hfc hsome
                hxs has hamt hexp hlim hcs hci hai' htd' htx hl1 hl3 hl5) ?_
              rintro r ⟨v1', v3', v5', accounts', tcatbals', a', c, t, pos', tx', rfl, hp, ht, hr, hri',
                hv1', htid⟩
              exact .inl ⟨_, rfl, next_postX file _ clk accts0 cats0 pos.val hlt v v1' v2 v3' v4 v5'
                accounts' tcatbals' c t _ _ a' pos' tx' rej _ (by rw [hfs, hstep])
                (by rw [foldAtX_next file _ clk accts0 cats0 pos.val hlt hX
                  (fun hh => hdx ((tdup_iff hrel.tranW _).2 hh.2)), hstep])
                hp (by omega) hr hri'⟩
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
            by_cases hdx : v1.val.findIdx
                (fun t => decide (t.tran_id.val = (file.val[pos.val]).dalytran_id.val)) < v1.val.length
            · -- a repeated id: the abend
              have htd := tran_dup_eq v1 (file.val[pos.val]).dalytran_id
              rw [searchRes_found _ _ _ _ hdx] at htd
              refine wp_mono (body_post_create_dup file xrefs clock clk v v1 v2 v3 v4 v5 accounts
                tcatbals dr cxr ar tcr tr pos tx rej _ hrel hri hlt _ _ _ ha rfl hfa hxs has hamt hexp
                hlim hcs hdup hai htd hnone htx hl0' hl3 hl4 hlt') ?_
              rintro r ⟨out, rfl, hout⟩
              exact .inr ⟨out, rfl, hfin hdx out hout⟩
            · have htd := tran_dup_eq v1 (file.val[pos.val]).dalytran_id
              rw [searchRes_nf _ _ _ _ hdx] at htd
              refine wp_mono (body_post_create file xrefs clock clk hclk hclen v v1 v2 v3 v4 v5 accounts
                tcatbals dr cxr ar tcr tr pos tx rej _ hrel hri hlt _ _ _ ha rfl hfa hxs has hamt hexp
                hlim hcs hdup hai htd hnone htx hl0 hl1 hl3 hl4 hlt') ?_
              rintro r ⟨v', v1', v3', v4', accounts', tcatbals', a', c, t, pos', tx', rfl, hp, ht, hr,
                hri', hv1', htid⟩
              exact .inl ⟨_, rfl, next_postX file _ clk accts0 cats0 pos.val hlt v' v1' v2 v3' v4' v5
                accounts' tcatbals' c t _ _ a' pos' tx' rej _ (by rw [hfs, hstep])
                (by rw [foldAtX_next file _ clk accts0 cats0 pos.val hlt hX
                  (fun hh => hdx ((tdup_iff hrel.tranW _).2 hh.2)), hstep])
                hp (by omega) hr hri'⟩
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
      exact .inl ⟨_, rfl, next_rejX file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
        tcr tr _ x' a' pos' tx' rej' _ (by rw [hfs, hstep]) hri
          (by rw [foldAtX_next file _ clk accts0 cats0 pos.val hlt hX (reject_not_dup hstep), hstep]) hp
          (by omega) hr⟩
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
    exact .inl ⟨_, rfl, next_rejX file _ clk accts0 cats0 pos.val hlt v v1 v2' v3 v4 v5 accounts tcatbals
      tcr tr _ x' ar pos' tx' rej' _ (by rw [hfs, hstep]) hri
          (by rw [foldAtX_next file _ clk accts0 cats0 pos.val hlt hX (reject_not_dup hstep), hstep]) hp
          (by omega) hr⟩

/-! ## The main loop -/

set_option maxHeartbeats 1000000 in
/-- One iteration of the main loop on any input, against the invariant and the variant. -/
theorem loop_stepX (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (hclk : clock.val.map (·.val) = rustLine clk)
    (hclen : clk.length = 21) (accts0 cats0 : List (List FVal))
    (hv1 : ∀ d ∈ file.val, DalytranRecord.Valid (DalytranRecord.vals d))
    (hsz : file.val.length + cats0.length < 2 ^ 28)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (eof : Bool) (tx rej : I64)
    (hst : LInvX file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 v v1 v2 v3 v4 v5 accounts
      tcatbals tcr tr pos eof tx rej) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos eof tx rej)
      (fun r => match loopCls r with
        | .inl o => (∃ out, o = .ok out ∧ FinalX (file.val.map DalytranRecord.vals)
            (xrefs.val.map CardXrefRecord.vals) accts0 cats0 clk out)
        | .inr s' => LInvTX file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 s' ∧
            VarT file s' < VarT file (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr,
              pos, eof, tx, rej)) := by
  cases eof
  · have hV : VarT file (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos, false,
        tx, rej) = file.val.length - pos.val + 1 := by
      simp only [VarT, Bool.false_eq_true, _root_.ite_false]
    rw [hV]
    by_cases hlt : pos.val < file.val.length
    · refine wp_mono (body_nextX file xrefs clock clk hclk hclen accts0 cats0 hv1 hsz v v1 v2 v3 v4
        v5 accounts tcatbals dr cxr ar tcr tr pos tx rej hst hlt) ?_
      rintro r (⟨st', rfl, hinv', hvar⟩ | ⟨out, rfl, hfin⟩)
      · simp only [loopCls_cont]
        exact ⟨hinv', hvar⟩
      · simp only [loopCls_done]
        exact ⟨out, rfl, hfin⟩
    · refine wp_mono (body_end file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr pos
        tx rej hlt) ?_
      rintro r rfl
      simp only [loopCls_cont]
      obtain ⟨h1, -, h3, h4, h5, h6⟩ := hst
      refine ⟨⟨h1, fun _ => by omega, h3, h4, h5, h6⟩, ?_⟩
      simp only [VarT, _root_.ite_true]
      omega
  · obtain ⟨h1, h2, h3, hrel, -, hX⟩ := hst
    have hpos : pos.val = file.val.length := h2 rfl
    have hlens := foldAt_lens (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
      (file.val.map DalytranRecord.vals) pos.val
    have e0 := congrArg List.length hrel.disp
    simp only [List.length_map] at e0
    have hm := usize_max_ge
    refine wp_mono (body_done file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr pos
      tx rej (by omega)) ?_
    rintro r ⟨out, rfl, hdisp, h1', h2', h3', h4', h5', hrc, hab⟩
    simp only [loopCls_done]
    refine ⟨out, rfl, ?_⟩
    have hXn : foldAtX (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
        (file.val.map DalytranRecord.vals) (file.val.map DalytranRecord.vals).length =
        ⟨foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
          (file.val.map DalytranRecord.vals) pos.val, false⟩ := by
      rw [List.length_map, ← hpos]
      exact hX
    have hrj := hrel.rej
    unfold FinalX
    rw [runX_nostop _ _ _ _ _ _ hXn]
    unfold OutRel
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hab⟩
    · rw [hdisp, hrel.disp, List.length_map]
      have e1 : tx.val.natAbs = file.val.length := by omega
      have e2 : rej.val.natAbs = (foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
          (file.val.map DalytranRecord.vals) pos.val).rejects := by
        omega
      rw [e1, e2]
    · rw [h1', hrel.tranW]
    · rw [h2', hrel.rejW]
    · rw [h3', hrel.acctRW]
    · rw [h4', hrel.catW]
    · rw [h5', hrel.catRW]
    · rw [hrc, hrj]
      simp

/-- **The main loop on any input**: from the invariant, `run_loop2` returns `Model.runX`'s
outputs. -/
theorem loop_specX (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (hclk : clock.val.map (·.val) = rustLine clk)
    (hclen : clk.length = 21) (accts0 cats0 : List (List FVal))
    (hv1 : ∀ d ∈ file.val, DalytranRecord.Valid (DalytranRecord.vals d))
    (hsz : file.val.length + cats0.length < 2 ^ 28)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (v1 : alloc.vec.Vec cbtrn02c.TranRecord)
    (v2 : alloc.vec.Vec cbtrn02c.RejectRecord) (v3 : alloc.vec.Vec cbtrn02c.AccountRecord)
    (v4 v5 : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (tcatbals : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (dr : cbtrn02c.DalytranRecord)
    (cxr : cbtrn02c.CardXrefRecord) (ar : cbtrn02c.AccountRecord) (tcr : cbtrn02c.TranCatBalRecord)
    (tr : cbtrn02c.TranRecord) (pos : Usize) (eof : Bool) (tx rej : I64)
    (h0 : LInvX file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 v v1 v2 v3 v4 v5 accounts
      tcatbals tcr tr pos eof tx rej) :
    wp (cbtrn02c.run_loop2 file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr pos eof
        tx rej)
      (fun o => ∃ out, o = .ok out ∧ FinalX (file.val.map DalytranRecord.vals)
        (xrefs.val.map CardXrefRecord.vals) accts0 cats0 clk out) := by
  simp only [cbtrn02c.run_loop2]
  refine wp_loop (loop_shape _) (LInvTX file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0)
    (VarT file) ?_ (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos, eof, tx, rej) h0
  rintro ⟨v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos, eof, tx, rej⟩ hst
  refine wp_mono (loop_stepX file xrefs clock clk hclk hclen accts0 cats0 hv1 hsz v v1 v2 v3 v4 v5
    accounts tcatbals dr cxr ar tcr tr pos eof tx rej hst) ?_
  intro r hr
  rcases r with e | c
  · simp only [loopCls_error] at hr ⊢; exact hr
  · rcases c with s' | o
    · simp only [loopCls_cont] at hr ⊢; exact hr
    · simp only [loopCls_done] at hr ⊢; exact hr

set_option maxHeartbeats 2000000 in
/-- **CBTRN02C on any input, Rust side**: `cbtrn02c.run` returns `Model.runX`'s outputs (no
domain assumed: repeated transaction ids included). -/
theorem run_specX (s1 : Slice cbtrn02c.DalytranRecord) (s2 : Slice cbtrn02c.CardXrefRecord)
    (s3 : Slice cbtrn02c.AccountRecord) (s4 : Slice cbtrn02c.TranCatBalRecord)
    (rclk : Std.Array Std.U8 21#usize)
    (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8)
    (hs1 : s1.val.map DalytranRecord.vals = vals1) (hs2 : s2.val.map CardXrefRecord.vals = vals2)
    (hs3 : s3.val.map AccountRecord.vals = vals3) (hs4 : s4.val.map TranCatBalRecord.vals = vals4)
    (hclk : rclk.val.map (·.val) = rustLine clk) (hcd : CurrentDate clk)
    (hv1 : ∀ v ∈ vals1, DalytranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatBalRecord.Valid v)
    (hsz : vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28) :
    ∃ out, cbtrn02c.run s1 s2 s3 s4 rclk = .ok out ∧
      OutRel out (Model.runX vals1 vals2 vals3 vals4 clk) := by
  subst hs1 hs2 hs3 hs4
  apply exists_ok_of_wp
  have hm := usize_max_ge
  have hclen : clk.length = 21 := hcd.1
  simp only [cbtrn02c.run, cbtrn02c.blank_dalytran, cbtrn02c.blank_xref, cbtrn02c.blank_account,
    cbtrn02c.blank_tcatbal, cbtrn02c.blank_tran]
  awp [run_loop0_eq, run_loop1_eq, lit_eq]
  simp (disch := omega) only [List.length_nil, dite_eq_left]
  refine loop_specX s1 s2 rclk clk hclk hclen (s3.val.map AccountRecord.vals)
    (s4.val.map TranCatBalRecord.vals) (fun d hd => hv1 _ (List.mem_map_of_mem hd))
    (by simp only [List.length_map] at hsz ⊢; omega)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
  refine ⟨by simp, (fun h => by cases h), by simp, ?_, ?_, ?_⟩
  · simp only [foldAt, UScalar.ofNatCore_val_eq, List.take_zero, List.foldl_nil]
    exact {
      disp := by
        simp only [alloc.vec.Vec.from_val, List.nil_append, List.map_cons,
          List.map_nil, Model.init, Std.Array.make_val]
        rw [← startR_text]; rfl
      tranW := by simp [Model.init]
      rejW := by simp [Model.init]
      acctRW := by simp [Model.init]
      catW := by simp [Model.init]
      catRW := by simp [Model.init]
      accts := by simp [Model.init]
      cats := by simp [Model.init]
      fill := by simp only [Std.Array.repeat_val, UScalar.ofNatCore_val_eq, Model.init]; exact sp22_ebc
      tfill := by simp
      rej := by simp [Model.init] }
  · refine ⟨fun a ha => ?_, fun c hc => ?_⟩
    · simp only [alloc.vec.Vec.from_val] at ha
      have hb := acct_bounds a (hv3 _ (List.mem_map_of_mem ha))
      rw [natAbs_lt_iff', natAbs_lt_iff', natAbs_lt_iff'] at hb
      norm_num at hb
      omega
    · simp only [alloc.vec.Vec.from_val] at hc
      have hb := (natAbs_lt_iff' _ _).1 (cat_bal_bound c (hv4 _ (List.mem_map_of_mem hc)))
      norm_num at hb
      omega
  · simp only [foldAtX, foldAt, UScalar.ofNatCore_val_eq, List.take_zero, List.foldl_nil]

end EquivLean.Modernize.Cbtrn02c.Rust
