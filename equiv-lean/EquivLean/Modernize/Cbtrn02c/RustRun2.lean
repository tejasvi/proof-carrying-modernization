import EquivLean.Modernize.Cbtrn02c.RustRun1
/-!
# CBTRN02C → Rust: the keyed lookups (searches with an early exit)
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-- The outcome of a search for the first element satisfying `p`: `found` of its index and
value, or `notfound`. -/
def searchRes {α β : Type _} (xs : List α) (p : α → Bool) (found : Nat → α → β) (notfound : β) : β :=
  if h : xs.findIdx p < xs.length then found (xs.findIdx p) (xs[xs.findIdx p]) else notfound

/-- **A search loop with an early exit**: each iteration either stops at a match, or goes on
to the next index, or stops at the end. -/
theorem early_search {α β : Type} (xs : List α) (p : α → Bool) (found : Nat → α → β)
    (notfound : β) (B : Usize → Result (ControlFlow Usize β))
    (hB : ∀ k : Usize, k.val ≤ xs.length →
      wp (B k) (fun r =>
        (∃ (h : k.val < xs.length), p xs[k.val] = true ∧ r = .ok (.done (found k.val xs[k.val]))) ∨
        (∃ (h : k.val < xs.length), p xs[k.val] = false ∧ ∃ k' : Usize, r = .ok (.cont k') ∧
          k'.val = k.val + 1) ∨
        (k.val = xs.length ∧ r = .ok (.done notfound)))) :
    wp (loop B 0#usize) (fun o => o = .ok (searchRes xs p found notfound)) := by
  refine wp_loop (loop_shape _)
    (fun k => k.val ≤ xs.length ∧ ∀ j (hj : j < k.val) (hj' : j < xs.length), p xs[j] = false)
    (fun k => xs.length - k.val) ?_ _ ?_
  · intro k hinv
    obtain ⟨hk, hnot⟩ := hinv
    refine wp_mono (hB k hk) ?_
    rintro r (⟨h, hp, rfl⟩ | ⟨h, hp, k', rfl, hk'⟩ | ⟨he, rfl⟩)
    · simp only [loopCls_done, Except.ok.injEq, searchRes]
      have hfi : xs.findIdx p = k.val := by
        rw [List.findIdx_eq h]; exact ⟨hp, fun j hj => hnot j hj (by omega)⟩
      rw [dite_eq_left_of_eq_true (eq_true (by rw [hfi]; exact h))]
      simp only [hfi]
    · simp only [loopCls_cont]
      refine ⟨⟨by omega, fun j hj hj2 => ?_⟩, by omega⟩
      rcases Nat.lt_or_ge j k.val with hj' | hj'
      · exact hnot j hj' hj2
      · have : j = k.val := by omega
        subst this; exact hp
    · simp only [loopCls_done, Except.ok.injEq, searchRes]
      have hfi : xs.findIdx p = xs.length := by
        rw [List.findIdx_eq_length]
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        exact hnot j (by omega) hj
      rw [dite_eq_right_of_eq_false (eq_false (by omega))]
  · refine ⟨by simp, fun j hj _ => ?_⟩
    simp at hj

/-- The xref search (`1500-A-LOOKUP-XREF`): the first record with the card number. -/
theorem xref_search_eq (xrefs : Slice cbtrn02c.CardXrefRecord) (d : cbtrn02c.DalytranRecord)
    (x0 : cbtrn02c.CardXrefRecord) :
    cbtrn02c.run_loop2_loop0 xrefs d x0 0#usize =
      .ok (searchRes xrefs.val (fun x => decide (x.xref_card_num.val = d.dalytran_card_num.val))
        (fun _ x => (d, x, true)) (d, x0, false)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop0]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop0.body]
  aeneas_wp [same_eq, lift, Std.Array.to_slice, usz_lit_val]
  have hm := usize_max_ge
  have hlen : xrefs.val.length ≤ Usize.max := by scalar_tac
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/-- The account search (`1500-B-LOOKUP-ACCT`): the first record with the id. -/
theorem acct_search_eq (accounts : alloc.vec.Vec cbtrn02c.AccountRecord)
    (a0 : cbtrn02c.AccountRecord) (key : I64) :
    cbtrn02c.run_loop2_loop1 accounts a0 0#usize key =
      .ok (searchRes accounts.val (fun a => a.acct_id.val == key.val) (fun _ a => (a, true))
        (a0, false)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop1]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop1.body]
  aeneas_wp [usz_lit_val]
  have hm := usize_max_ge
  have hlen : accounts.val.length ≤ Usize.max := accounts.property
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/-- The key test of the category balance searches: account, type, category. -/
def catKeyR (acct : I64) (ty : Std.Array U8 2#usize) (cd : I64) (e : cbtrn02c.TranCatBalRecord) : Bool :=
  e.trancat_acct_id.val == acct.val && decide (e.trancat_type_cd.val = ty.val) &&
    e.trancat_cd.val == cd.val

/-- The category balance search of `2700-UPDATE-TCATBAL`. -/
theorem cat_search_eq (tcs : alloc.vec.Vec cbtrn02c.TranCatBalRecord) (c0 : cbtrn02c.TranCatBalRecord)
    (acct : I64) (ty : Std.Array U8 2#usize) (cd : I64) :
    cbtrn02c.run_loop2_loop2 tcs c0 0#usize acct ty cd =
      .ok (searchRes tcs.val (catKeyR acct ty cd) (fun _ e => (e, true)) (c0, false)) := by
  have hlen : tcs.val.length ≤ Usize.max := tcs.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop2]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop2.body]
  aeneas_wp [same_eq, lift, Std.Array.to_slice, usz_lit_val, catKeyR]
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/-- The duplicate check before a new category balance record (`WRITE` with `INVALID KEY`). -/
theorem cat_dup_eq (tcs : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (acct : I64) (ty : Std.Array U8 2#usize) (cd : I64) :
    cbtrn02c.run_loop2_loop3 tcs acct ty cd 0#usize =
      .ok (searchRes tcs.val (catKeyR acct ty cd) (fun _ _ => true) false) := by
  have hlen : tcs.val.length ≤ Usize.max := tcs.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop3]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop3.body]
  aeneas_wp [same_eq, lift, Std.Array.to_slice, usz_lit_val, catKeyR]
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/-- The index of the category balance record to rewrite (`REWRITE`). -/
theorem cat_idx_eq (tcs : alloc.vec.Vec cbtrn02c.TranCatBalRecord)
    (acct : I64) (ty : Std.Array U8 2#usize) (cd : I64) :
    cbtrn02c.run_loop2_loop6 tcs acct ty cd 0#usize =
      .ok (searchRes tcs.val (catKeyR acct ty cd) (fun j _ => (usz j, true)) (0#usize, false)) := by
  have hlen : tcs.val.length ≤ Usize.max := tcs.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop6]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop6.body]
  aeneas_wp [same_eq, lift, Std.Array.to_slice, usz_lit_val, catKeyR]
  have hku : usz k.val = k := UScalar.eq_of_val_eq (usz_val _ (by omega))
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/-- The index of the account to rewrite (`2800-UPDATE-ACCOUNT-REC`). -/
theorem acct_idx_eq (accounts : alloc.vec.Vec cbtrn02c.AccountRecord) (key : I64) :
    cbtrn02c.run_loop2_loop4 accounts key 0#usize =
      .ok (searchRes accounts.val (fun a => a.acct_id.val == key.val) (fun j _ => (usz j, true))
        (0#usize, false)) := by
  have hlen : accounts.val.length ≤ Usize.max := accounts.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop4]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop4.body]
  aeneas_wp [usz_lit_val]
  have hku : usz k.val = k := UScalar.eq_of_val_eq (usz_val _ (by omega))
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

theorem acct_idx_eq' (accounts : alloc.vec.Vec cbtrn02c.AccountRecord) (key : I64) :
    cbtrn02c.run_loop2_loop7 accounts key 0#usize =
      .ok (searchRes accounts.val (fun a => a.acct_id.val == key.val) (fun j _ => (usz j, true))
        (0#usize, false)) := by
  have hlen : accounts.val.length ≤ Usize.max := accounts.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop7]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop7.body]
  aeneas_wp [usz_lit_val]
  have hku : usz k.val = k := UScalar.eq_of_val_eq (usz_val _ (by omega))
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

/-- The duplicate check of `2900-WRITE-TRANSACTION-FILE` (`WRITE` with `INVALID KEY`). -/
theorem tran_dup_eq (v : alloc.vec.Vec cbtrn02c.TranRecord) (id : Std.Array U8 16#usize) :
    cbtrn02c.run_loop2_loop5 v id 0#usize =
      .ok (searchRes v.val (fun t => decide (t.tran_id.val = id.val)) (fun _ _ => true) false) := by
  have hlen : v.val.length ≤ Usize.max := v.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop5]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop5.body]
  aeneas_wp [same_eq, lift, Std.Array.to_slice, usz_lit_val]
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

theorem tran_dup_eq' (v : alloc.vec.Vec cbtrn02c.TranRecord) (id : Std.Array U8 16#usize) :
    cbtrn02c.run_loop2_loop8 v id 0#usize =
      .ok (searchRes v.val (fun t => decide (t.tran_id.val = id.val)) (fun _ _ => true) false) := by
  have hlen : v.val.length ≤ Usize.max := v.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop2_loop8]
  apply early_search
  intro k hk
  simp only [cbtrn02c.run_loop2_loop8.body]
  aeneas_wp [same_eq, lift, Std.Array.to_slice, usz_lit_val]
  have hm := usize_max_ge
  split_ifs <;> first | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

end EquivLean.Modernize.Cbtrn02c.Rust

/-!
# CBTRN02C → Rust: the records' field values against the model
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-! ## Field access on the Rust records -/

theorem tId_vals (d : cbtrn02c.DalytranRecord) :
    Model.tId (DalytranRecord.vals d) = d.dalytran_id.val.map ebc := rfl
theorem tType_vals (d : cbtrn02c.DalytranRecord) :
    Model.tType (DalytranRecord.vals d) = d.dalytran_type_cd.val.map ebc := rfl
theorem tCat_vals (d : cbtrn02c.DalytranRecord) :
    Model.tCat (DalytranRecord.vals d) = d.dalytran_cat_cd.val := rfl
theorem tAmt_vals (d : cbtrn02c.DalytranRecord) :
    Model.tAmt (DalytranRecord.vals d) = d.dalytran_amt.val := rfl
theorem tCard_vals (d : cbtrn02c.DalytranRecord) :
    Model.tCard (DalytranRecord.vals d) = d.dalytran_card_num.val.map ebc := rfl
theorem tOrig_vals (d : cbtrn02c.DalytranRecord) :
    Model.tOrig (DalytranRecord.vals d) = d.dalytran_orig_ts.val.map ebc := rfl
theorem xCard_vals (x : cbtrn02c.CardXrefRecord) :
    Model.xCard (CardXrefRecord.vals x) = x.xref_card_num.val.map ebc := rfl
theorem xAcct_vals (x : cbtrn02c.CardXrefRecord) :
    Model.xAcct (CardXrefRecord.vals x) = x.xref_acct_id.val := rfl
theorem aId_vals (a : cbtrn02c.AccountRecord) :
    Model.aId (AccountRecord.vals a) = a.acct_id.val := rfl
theorem aBal_vals (a : cbtrn02c.AccountRecord) :
    Model.aBal (AccountRecord.vals a) = a.acct_curr_bal.val := rfl
theorem aLimit_vals (a : cbtrn02c.AccountRecord) :
    Model.aLimit (AccountRecord.vals a) = a.acct_credit_limit.val := rfl
theorem aExp_vals (a : cbtrn02c.AccountRecord) :
    Model.aExp (AccountRecord.vals a) = a.acct_expiraion_date.val.map ebc := rfl
theorem aCC_vals (a : cbtrn02c.AccountRecord) :
    Model.aCC (AccountRecord.vals a) = a.acct_curr_cyc_credit.val := rfl
theorem aCD_vals (a : cbtrn02c.AccountRecord) :
    Model.aCD (AccountRecord.vals a) = a.acct_curr_cyc_debit.val := rfl
theorem cAcct_vals (c : cbtrn02c.TranCatBalRecord) :
    Model.cAcct (TranCatBalRecord.vals c) = c.trancat_acct_id.val := rfl
theorem cType_vals (c : cbtrn02c.TranCatBalRecord) :
    Model.cType (TranCatBalRecord.vals c) = c.trancat_type_cd.val.map ebc := rfl
theorem cCd_vals (c : cbtrn02c.TranCatBalRecord) :
    Model.cCd (TranCatBalRecord.vals c) = c.trancat_cd.val := rfl
theorem cBal_vals (c : cbtrn02c.TranCatBalRecord) :
    Model.cBal (TranCatBalRecord.vals c) = c.tran_cat_bal.val := rfl
theorem cFill_vals (c : cbtrn02c.TranCatBalRecord) :
    Model.cFill (TranCatBalRecord.vals c) = c.filler1.val.map ebc := rfl

theorem tranId_vals (r : cbtrn02c.TranRecord) :
    Model.tId (TranRecord.vals r) = r.tran_id.val.map ebc := rfl

/-! ## Bytes compared through CP037 -/

theorem beq_map_ebc (a b : List U8) : (a.map ebc == b.map ebc) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : a.map ebc ≠ b.map ebc := fun e => h (map_ebc_inj.1 e)
    simp [h, h']

/-! ## The searches against the model's lookups -/

theorem searchRes_found {α β : Type _} (xs : List α) (p : α → Bool) (found : Nat → α → β) (nf : β)
    (h : xs.findIdx p < xs.length) : searchRes xs p found nf = found (xs.findIdx p) xs[xs.findIdx p] := by
  unfold searchRes; rw [dite_eq_left h]

theorem searchRes_nf {α β : Type _} (xs : List α) (p : α → Bool) (found : Nat → α → β) (nf : β)
    (h : ¬ xs.findIdx p < xs.length) : searchRes xs p found nf = nf := by
  unfold searchRes; rw [dite_eq_right h]

/-- A first-match lookup on the field values is the record at the Rust search's index. -/
theorem find_map_eq {α β : Type _} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).find? q =
      if h : l.findIdx (q ∘ f) < l.length then some (f l[l.findIdx (q ∘ f)]) else none := by
  rw [List.find?_map, List.find?_eq_getElem?_findIdx]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem?_eq_none (by omega)]; rfl

theorem findIdx_pred_true {α : Type _} (l : List α) (p : α → Bool) (h : l.findIdx p < l.length) :
    p l[l.findIdx p] = true := (List.findIdx_eq h).1 rfl |>.1

/-- The keyed `REWRITE` of the first match is the Rust update at the search's index. -/
theorem replaceFirst_map {α β : Type _} (f : α → β) (q : β → Bool) (y : α) :
    ∀ (l : List α), l.findIdx (q ∘ f) < l.length →
      Model.replaceFirst q (f y) (l.map f) = (l.set (l.findIdx (q ∘ f)) y).map f
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : q (f a) = true
    · have : (a :: l).findIdx (q ∘ f) = 0 := by simp [List.findIdx_cons, ha]
      rw [this]
      simp [Model.replaceFirst, ha]
    · have e : (a :: l).findIdx (q ∘ f) = l.findIdx (q ∘ f) + 1 := by
        simp [List.findIdx_cons, ha]
      rw [e] at h ⊢
      have ih := replaceFirst_map f q y l (by simp only [List.length_cons] at h; omega)
      simp only [List.map_cons, Model.replaceFirst, ha, Bool.false_eq_true, _root_.ite_false,
        List.set_cons_succ, ih]

theorem replaceFirst_length {α : Type _} (q : α → Bool) (y : α) :
    ∀ l : List α, (Model.replaceFirst q y l).length = l.length
  | [] => rfl
  | a :: l => by
    simp only [Model.replaceFirst]
    split_ifs <;> simp [replaceFirst_length q y l]

/-- The key tests of the Rust searches are the model's. -/
theorem xref_pred (d : cbtrn02c.DalytranRecord) :
    ((fun x => Model.xCard x == Model.tCard (DalytranRecord.vals d)) ∘ CardXrefRecord.vals) =
      (fun x : cbtrn02c.CardXrefRecord => decide (x.xref_card_num.val = d.dalytran_card_num.val)) := by
  funext x
  simp only [Function.comp_apply, xCard_vals, tCard_vals, beq_map_ebc]

theorem acct_pred (id : Int) :
    ((fun a => Model.aId a == id) ∘ AccountRecord.vals) =
      (fun a : cbtrn02c.AccountRecord => a.acct_id.val == id) := rfl

theorem cat_pred (acct : I64) (ty : Std.Array U8 2#usize) (cd : I64) :
    (Model.catKey acct.val (ty.val.map ebc) cd.val ∘ TranCatBalRecord.vals) = catKeyR acct ty cd := by
  funext e
  simp only [Function.comp_apply, Model.catKey, cAcct_vals, cType_vals, cCd_vals, catKeyR, beq_map_ebc]

/-! ## Field bounds of valid records -/

/-- A DISPLAY numeric field's value has at most `digits` digits. -/
theorem valid_num_bound {f : Field} {v : Int} (hv : f.Valid (.num v)) {fmt : NumFmt}
    (hk : f.desc.kind = .num fmt) (hd : fmt.usage = .display) : v.natAbs < 10 ^ fmt.digits := by
  obtain ⟨fmt', hk', -, -, hh, -⟩ := hv
  rw [hk] at hk'
  cases hk'
  unfold NumFmt.Holds at hh
  have : fmt.fullBinary {} = false := by simp [NumFmt.fullBinary, hd]
  simp only [this, Bool.false_eq_true, _root_.ite_false] at hh
  exact hh.1

theorem tran_amt_bound (d : cbtrn02c.DalytranRecord)
    (hv : DalytranRecord.Valid (DalytranRecord.vals d)) : d.dalytran_amt.val.natAbs < 10 ^ 11 := by
  simp only [Schema.Valid, DalytranRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h5, -⟩⟩⟩⟩⟩⟩
  exact valid_num_bound h5 rfl rfl

theorem acct_bounds (a : cbtrn02c.AccountRecord) (hv : AccountRecord.Valid (AccountRecord.vals a)) :
    a.acct_curr_bal.val.natAbs < 10 ^ 12 ∧ a.acct_curr_cyc_credit.val.natAbs < 10 ^ 12 ∧
      a.acct_curr_cyc_debit.val.natAbs < 10 ^ 12 := by
  simp only [Schema.Valid, AccountRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨h2, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h8, _ |
    ⟨h9, -⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  exact ⟨valid_num_bound h2 rfl rfl, valid_num_bound h8 rfl rfl, valid_num_bound h9 rfl rfl⟩

theorem cat_bal_bound (c : cbtrn02c.TranCatBalRecord)
    (hv : TranCatBalRecord.Valid (TranCatBalRecord.vals c)) : c.tran_cat_bal.val.natAbs < 10 ^ 11 := by
  simp only [Schema.Valid, TranCatBalRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩⟩
  exact valid_num_bound h3 rfl rfl

/-! ## Lengths along the model's run -/

theorem step_lens (xr : List (List FVal)) (clk : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr clk s t).disp.length ≤ s.disp.length + 1 ∧
      (Model.step xr clk s t).tranW.length ≤ s.tranW.length + 1 ∧
      (Model.step xr clk s t).rejW.length ≤ s.rejW.length + 1 ∧
      (Model.step xr clk s t).catW.length ≤ s.catW.length + 1 ∧
      (Model.step xr clk s t).acctRW.length ≤ s.acctRW.length + 1 ∧
      (Model.step xr clk s t).catRW.length ≤ s.catRW.length + 1 ∧
      (Model.step xr clk s t).rejects ≤ s.rejects + 1 ∧
      (Model.step xr clk s t).cats.length ≤ s.cats.length + 1 ∧
      (Model.step xr clk s t).accts.length = s.accts.length := by
  have hrej : ∀ code desc, (s.reject t code desc).disp.length ≤ s.disp.length + 1 ∧
      (s.reject t code desc).tranW.length ≤ s.tranW.length + 1 ∧
      (s.reject t code desc).rejW.length ≤ s.rejW.length + 1 ∧
      (s.reject t code desc).catW.length ≤ s.catW.length + 1 ∧
      (s.reject t code desc).acctRW.length ≤ s.acctRW.length + 1 ∧
      (s.reject t code desc).catRW.length ≤ s.catRW.length + 1 ∧
      (s.reject t code desc).rejects ≤ s.rejects + 1 ∧
      (s.reject t code desc).cats.length ≤ s.cats.length + 1 ∧
      (s.reject t code desc).accts.length = s.accts.length := by
    intro code desc
    simp [Model.St.reject]
  unfold Model.step
  split
  · exact hrej _ _
  · rename_i x _
    split
    · exact hrej _ _
    · rename_i a _
      split_ifs
      · exact hrej _ _
      · exact hrej _ _
      · simp only [Model.St.post]
        split <;> simp [replaceFirst_length]

theorem fold_lens (xr : List (List FVal)) (clk : List UInt8) :
    ∀ (l : List (List FVal)) (s : Model.St),
      (l.foldl (Model.step xr clk) s).disp.length ≤ s.disp.length + l.length ∧
      (l.foldl (Model.step xr clk) s).tranW.length ≤ s.tranW.length + l.length ∧
      (l.foldl (Model.step xr clk) s).rejW.length ≤ s.rejW.length + l.length ∧
      (l.foldl (Model.step xr clk) s).catW.length ≤ s.catW.length + l.length ∧
      (l.foldl (Model.step xr clk) s).acctRW.length ≤ s.acctRW.length + l.length ∧
      (l.foldl (Model.step xr clk) s).catRW.length ≤ s.catRW.length + l.length ∧
      (l.foldl (Model.step xr clk) s).rejects ≤ s.rejects + l.length ∧
      (l.foldl (Model.step xr clk) s).cats.length ≤ s.cats.length + l.length ∧
      (l.foldl (Model.step xr clk) s).accts.length = s.accts.length
  | [], s => by simp
  | t :: l, s => by
    have h1 := fold_lens xr clk l (Model.step xr clk s t)
    have h2 := step_lens xr clk s t
    simp only [List.foldl_cons, List.length_cons]
    omega

end EquivLean.Modernize.Cbtrn02c.Rust
