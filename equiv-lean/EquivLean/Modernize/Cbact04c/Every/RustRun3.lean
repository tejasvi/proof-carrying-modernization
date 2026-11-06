import EquivLean.Modernize.Cbact04c.Every.RustRun2
/-!
# CBACT04C → Rust on every input: `process_record`, a new account after the first
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

theorem preAcct_some (s : Model.St) (t : List FVal) (h : s.lastId.isSome) :
    preAcct s t =
      { s with
        disp := s.disp ++ [Model.TranCatBalRecord.textS t],
        accts := Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
          (Model.posted s.acct s.total) s.accts,
        rewrites := s.rewrites ++ [Model.posted s.acct s.total] } := by
  simp [preAcct, h]

set_option maxHeartbeats 4000000 in
/-- A new account (the previous one rewritten), its account record missing. -/
theorem process_record_change_amiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s)
    (id : Int) (hold : s.lastId = some id) (hne : id ≠ r.trancat_acct_id.val)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length)
    (hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
      st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807)
    (hl3 : out.account_file_rewrites.val.length < Usize.max)
    (hfa : ¬ (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (acctsAfter st).length)
    (hl1 : out.displays.val.length + 5 < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (false, st', out') ∧
        ORel out' (Model.stepE (xrefs.val.map CardXrefRecord.vals)
          (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk
          (ofSt s false) (TranCatBalRecord.vals r)) ∧
        (Model.stepE (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk (ofSt s false)
          (TranCatBalRecord.vals r)).stop = true) := by
  have hm := usize_max_ge
  have hsome : s.lastId.isSome := by rw [hold]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hfirst : st.first_time = false := by rw [hrel.first, hsome]; rfl
  have hlast : st.last_acct.val = id := hrel.last _ hold
  have hne' : (r.trancat_acct_id != st.last_acct) = true := by
    rw [bne_iff_ne, ne_eq]; intro h; apply hne; rw [← hlast, h]
  have hneq : s.lastId ≠ some (Model.tAcct (TranCatBalRecord.vals r)) := by
    rw [hold, tAcct_vals]; intro h; apply hne; exact Option.some.inj h
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hl1' : out.displays.val.length < Usize.max := by omega
  have hf0i := usz_val _ (le_trans (Nat.le_of_lt hf0) hal)
  have hv1 : (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val = acctsAfter st := by
    rw [alloc.vec.Vec.set_val_eq, hf0i]; rfl
  have hl1a : (acctsAfter st).length = st.accounts.val.length := by simp [acctsAfter]
  have hU := update_account_eq
    { st with tran_cat_bal_record := r, last_acct_set := true, first_time := false }
    { out with displays := alloc.vec.Vec.from (out.displays.val ++
        [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (push_le _ _ hl1') }
    hbt ⟨_, List.getElem_mem hf0, by simpa using List.findIdx_getElem (w := hf0)⟩ hl3
  dsimp only at hU
  have haccts := acctsAfter_vals st out s hrel hsome hf0
  rw [stepE_new _ _ _ _ _ _ hneq, preAcct_some _ _ hsome]
  dsimp only
  have hmA : Model.findAcctO (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r)) = none := by
    rw [← haccts, tAcct_vals, findAcctO_eq, dite_eq_right hfa]
  rw [hmA]
  dsimp only
  refine (fun h => ?_) (show ∀ X : Model.St, ∀ l, (Model.StE.abend (ofSt X false) l).stop = true
    from fun _ _ => rfl)
  simp only [h, and_true]
  have hge1 : usz ((acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)) := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' (acctsAfter st) _) (by omega)),
      alloc.vec.Vec.len_val, alloc.vec.Vec.length, hv1]; omega
  have hpd := push_digits_eq (alloc.vec.Vec.from notFoundBytes (msg_le _ (by decide)))
    r.trancat_acct_id 11#usize (by simp) (by simp [notFoundBytes]; omega)
  simp only [cbact04c_t.process_record, hset, hne', hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, bind_ok]
  simp only [wp_bind, wp_Vec_push, hl1', _root_.dite_true]
  simp only [hU, wp_ok, Aeneas.Std.uncurry_apply_pair]
  simp only [_root_.ite_true, find_account_eq, bind_ok, hv1]
  simp only [hge1, _root_.ite_true, m_acct_not_found_eq, m_err_read_acct_eq, bind_ok, hpd]
  aeneas_wp []
  simp (disch := abend_len) only [abend_eq]
  aeneas_wp []
  ifs_omega2
  refine ⟨_, _, rfl, ?_⟩
  refine orel_abend2 _ _ _ ?_ ?_ ?_ rfl
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text, notFound_text, digs_val, nfLine, tAcct_vals, errAcct_text, status23_text,
      abending_text, List.append_assoc, List.cons_append, List.nil_append]
  · exact hrel.writes
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
      hrel.rewrites, postedR_vals, hrel.acct hsome, hrel.total]

set_option maxHeartbeats 4000000 in
/-- A new account (the previous one rewritten), its account found, its cross-reference missing. -/
theorem process_record_change_xmiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s)
    (id : Int) (hold : s.lastId = some id) (hne : id ≠ r.trancat_acct_id.val)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length)
    (hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
      st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807)
    (hl3 : out.account_file_rewrites.val.length < Usize.max)
    (hfa : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (acctsAfter st).length)
    (hfx : ¬ xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
      xrefs.val.length)
    (hl1 : out.displays.val.length + 5 < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (false, st', out') ∧
        ORel out' (Model.stepE (xrefs.val.map CardXrefRecord.vals)
          (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk
          (ofSt s false) (TranCatBalRecord.vals r)) ∧
        (Model.stepE (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk (ofSt s false)
          (TranCatBalRecord.vals r)).stop = true) := by
  have hm := usize_max_ge
  have hsome : s.lastId.isSome := by rw [hold]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hfirst : st.first_time = false := by rw [hrel.first, hsome]; rfl
  have hlast : st.last_acct.val = id := hrel.last _ hold
  have hne' : (r.trancat_acct_id != st.last_acct) = true := by
    rw [bne_iff_ne, ne_eq]; intro h; apply hne; rw [← hlast, h]
  have hneq : s.lastId ≠ some (Model.tAcct (TranCatBalRecord.vals r)) := by
    rw [hold, tAcct_vals]; intro h; apply hne; exact Option.some.inj h
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hl1' : out.displays.val.length < Usize.max := by omega
  have hf0i := usz_val _ (le_trans (Nat.le_of_lt hf0) hal)
  have hv1 : (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val = acctsAfter st := by
    rw [alloc.vec.Vec.set_val_eq, hf0i]; rfl
  have hl1a : (acctsAfter st).length = st.accounts.val.length := by simp [acctsAfter]
  have hU := update_account_eq
    { st with tran_cat_bal_record := r, last_acct_set := true, first_time := false }
    { out with displays := alloc.vec.Vec.from (out.displays.val ++
        [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (push_le _ _ hl1') }
    hbt ⟨_, List.getElem_mem hf0, by simpa using List.findIdx_getElem (w := hf0)⟩ hl3
  dsimp only at hU
  have haccts := acctsAfter_vals st out s hrel hsome hf0
  rw [stepE_new _ _ _ _ _ _ hneq, preAcct_some _ _ hsome]
  dsimp only
  have hmA : Model.findAcctO (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r)) =
      some (AccountRecord.vals ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])) := by
    rw [← haccts, tAcct_vals, findAcctO_eq, dite_eq_left hfa]
  have hmX : Model.findXrefO (xrefs.val.map CardXrefRecord.vals)
      (Model.tAcct (TranCatBalRecord.vals r)) = none := by
    rw [tAcct_vals, findXrefO_eq, dite_eq_right hfx]
  rw [hmA]
  dsimp only
  rw [hmX]
  dsimp only
  refine (fun h => ?_) (show ∀ X : Model.St, ∀ l, (Model.StE.abend (ofSt X false) l).stop = true
    from fun _ _ => rfl)
  simp only [h, and_true]
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) (by omega))
  have hge1 : ¬ (usz ((acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int))) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length, hv1,
      not_le]; omega
  have hfa' : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val.length := by rw [hv1]; exact hfa
  have hge2 : usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' _ _) hxl),
      Slice.len_val, Slice.length]; omega
  have hpd := push_digits_eq (alloc.vec.Vec.from notFoundBytes (msg_le _ (by decide)))
    r.trancat_acct_id 11#usize (by simp) (by simp [notFoundBytes]; omega)
  simp only [cbact04c_t.process_record, hset, hne', hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, bind_ok]
  simp only [wp_bind, wp_Vec_push, hl1', _root_.dite_true]
  simp only [hU, wp_ok, Aeneas.Std.uncurry_apply_pair]
  simp only [_root_.ite_true, find_account_eq, bind_ok, hv1]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa', bind_ok, find_xref_eq]
  simp only [hv1]
  simp only [hge2, _root_.ite_true, m_acct_not_found_eq, m_err_read_xref_eq, bind_ok, hpd]
  aeneas_wp []
  simp (disch := abend_len) only [abend_eq]
  aeneas_wp []
  ifs_omega2
  refine ⟨_, _, rfl, ?_⟩
  refine orel_abend2 _ _ _ ?_ ?_ ?_ rfl
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text, notFound_text, digs_val, nfLine, tAcct_vals, errXref_text, status23_text,
      abending_text, List.append_assoc, List.cons_append, List.nil_append]
  · exact hrel.writes
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
      hrel.rewrites, postedR_vals, hrel.acct hsome, hrel.total]

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: `process_record`, a new account after the first (`DEFAULT`)
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

set_option maxHeartbeats 4000000 in
/-- A new account (the previous one rewritten), found with its cross-reference, its group missing,
`DEFAULT` found. -/
theorem process_record_change_dflt (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s)
    (id : Int) (hold : s.lastId = some id) (hne : id ≠ r.trancat_acct_id.val)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length)
    (hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
      st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807)
    (hl3 : out.account_file_rewrites.val.length < Usize.max)
    (hfa : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (acctsAfter st).length)
    (hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
      xrefs.val.length)
    (hdn : ¬ discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd) < discs.val.length)
    (hdd : discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd) < discs.val.length)
    (hb : MBounds s) (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hl1 : out.displays.val.length + 3 < Usize.max)
    (hl2 : out.transact_file_writes.val.length < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (true, st', out') ∧
        SRel st' out' (toSt (Model.stepE (xrefs.val.map CardXrefRecord.vals)
          (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk
          (ofSt s false) (TranCatBalRecord.vals r))) ∧
        (Model.stepE (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk (ofSt s false)
          (TranCatBalRecord.vals r)).stop = false) := by
  have hm := usize_max_ge
  have hsome : s.lastId.isSome := by rw [hold]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hfirst : st.first_time = false := by rw [hrel.first, hsome]; rfl
  have hlast : st.last_acct.val = id := hrel.last _ hold
  have hne' : (r.trancat_acct_id != st.last_acct) = true := by
    rw [bne_iff_ne, ne_eq]; intro h; apply hne; rw [← hlast, h]
  have hneq : s.lastId ≠ some (Model.tAcct (TranCatBalRecord.vals r)) := by
    rw [hold, tAcct_vals]; intro h; apply hne; exact Option.some.inj h
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hl1' : out.displays.val.length < Usize.max := by omega
  have hf0i := usz_val _ (le_trans (Nat.le_of_lt hf0) hal)
  have hv1 : (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val = acctsAfter st := by
    rw [alloc.vec.Vec.set_val_eq, hf0i]; rfl
  have hl1a : (acctsAfter st).length = st.accounts.val.length := by simp [acctsAfter]
  have hU := update_account_eq
    { st with tran_cat_bal_record := r, last_acct_set := true, first_time := false }
    { out with displays := alloc.vec.Vec.from (out.displays.val ++
        [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (push_le _ _ hl1') }
    hbt ⟨_, List.getElem_mem hf0, by simpa using List.findIdx_getElem (w := hf0)⟩ hl3
  dsimp only at hU
  have haccts := acctsAfter_vals st out s hrel hsome hf0
  rw [stepE_new _ _ _ _ _ _ hneq, preAcct_some _ _ hsome]
  dsimp only
  have hmA : Model.findAcctO (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r)) =
      some (AccountRecord.vals ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])) := by
    rw [← haccts, tAcct_vals, findAcctO_eq, dite_eq_left hfa]
  have hmX : Model.findXrefO (xrefs.val.map CardXrefRecord.vals)
      (Model.tAcct (TranCatBalRecord.vals r)) =
      some (CardXrefRecord.vals (xrefs.val[xrefs.val.findIdx
        (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)])) := by
    rw [tAcct_vals, findXrefO_eq, dite_eq_left hfx]
  have hm1 : Model.findRateO (discs.val.map DisGroupRecord.vals)
      (Model.aGrp (AccountRecord.vals ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])))
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [aGrp_vals, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdn]
  rw [hmA]
  dsimp only
  rw [hmX]
  dsimp only
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) (by omega))
  have hfxi := usz_val _ (le_trans (Nat.le_of_lt hfx) hxl)
  have hge1 : ¬ (usz ((acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int))) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length, hv1,
      not_le]; omega
  have hfa' : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val.length := by rw [hv1]; exact hfa
  have hge2 : ¬ (usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfxi, Slice.len_val, Slice.length, not_le]; omega
  have hnlt : ¬ (usz (discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd)) < discs.len) := by
    simp only [UScalar.lt_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]
    exact hdn
  obtain ⟨dgr, hdgr⟩ : ∃ d, discs.val[discs.val.findIdx
      (discKey defR r.trancat_type_cd r.trancat_cd)]'hdd = d := ⟨_, rfl⟩
  have hm2 : Model.findRateO (discs.val.map DisGroupRecord.vals) Model.defaultGrp
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) =
      some dgr.dis_int_rate.val := by
    rw [← defR_ebc, tType_vals, tCat_vals, findRateO_eq, dite_eq_left hdd, hdgr]
  rw [rate_dflt _ _ _ _ _ _ hm1 hm2]
  simp only [toSt_ofSt, ofSt_stop, and_true]
  have hdi := usz_val _ (le_trans (Nat.le_of_lt hdd) hdl)
  have hge3 : ¬ (usz (discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd)) ≥
      discs.len) := by
    simp only [ge_iff_le, UScalar.le_equiv, hdi, Slice.len_val, Slice.length]; omega
  have ht11 : ∀ v, cbact04c_t.trunc_digits v 11#u32 = .ok (tmodI v 11) := fun v => by
    rw [trunc_digits_eq v 11#u32 (by simp)]; rfl
  simp only [cbact04c_t.process_record, hset, hne', hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, bind_ok]
  simp only [wp_bind, wp_Vec_push, hl1', _root_.dite_true]
  simp only [hU, wp_ok, Aeneas.Std.uncurry_apply_pair]
  simp only [_root_.ite_true, find_account_eq, bind_ok, hv1]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa', bind_ok, find_xref_eq]
  simp only [hv1]
  simp only [hge2, _root_.ite_false, slice_index_usz _ _ hfx, bind_ok, find_disc_eq]
  simp only [hnlt, _root_.ite_false, m_disc_missing_eq, m_try_default_eq, find_disc_eq, bind_ok,
    defR_fold]
  simp only [hge3, _root_.ite_false]
  aeneas_wp [hdi, hdd, hdgr, ht11, build_tran_eq, isz_lit_val]
  have hdmem : dgr ∈ discs.val := hdgr ▸ List.getElem_mem hdd
  have hrate := hrates dgr hdmem
  have hmb := mul_bound _ _ hbal hrate
  have hamt := tmod11_bound ((r.tran_cat_bal.val * dgr.dis_int_rate.val).tdiv 120000)
  have hk : st.tranid_suffix.val < 1000000 ∧ 0 ≤ st.tranid_suffix.val := by
    rw [hrel.k]; have := hb.k; omega
  have hd1 := srel_change st out s hrel hsome r xrefs.val _ hv1 hfa hfx hf0 hl1' hl3
  have eA : Model.findAcct (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r)) =
      AccountRecord.vals ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]) := by
    rw [← haccts, tAcct_vals, findAcct_eq _ _ hfa]
  have eX : Model.findXref (xrefs.val.map CardXrefRecord.vals) (Model.tAcct (TranCatBalRecord.vals r)) =
      CardXrefRecord.vals (xrefs.val[xrefs.val.findIdx
        (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)]) := by
    rw [tAcct_vals, findXref_eq _ _ hfx]
  rw [eA, eX] at hd1
  have hd2 := srel_lines _ _ { out with
      displays := alloc.vec.Vec.from (out.displays.val ++
        [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)] ++
        [alloc.vec.Vec.from missingBytes (msg_le _ (by decide))] ++
        [alloc.vec.Vec.from tryDefaultBytes (msg_le _ (by decide))]) (by simp; omega),
      account_file_rewrites := alloc.vec.Vec.from (out.account_file_rewrites.val ++
        [postedR st.account_record st.total_int]) (push_le _ _ hl3) } _ hd1 dfltLines
    (by simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
          missing_text, tryDefault_text, dfltLines, List.append_assoc, List.cons_append,
          List.nil_append])
    rfl rfl rfl
  simp only [tmodI11_val, IScalar.ofInt_val_eq]
  by_cases hr0 : dgr.dis_int_rate.val = 0
  · ifs_omega2
    refine ⟨_, _, rfl, ?_⟩
    unfold mpostR
    simp only [hr0, _root_.ite_true]
    exact srel_norate _ _ _ hd2 dgr
  · ifs_omega2
    refine ⟨_, _, rfl, ?_⟩
    unfold mpostR
    simp only [hr0, _root_.ite_false]
    refine srel_post _ _ _ hd2 rfl dgr parms clock clk hclk hclen _ _ _ _ ?_ ?_ ?_ hl2
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals, isz_lit_val]
    · rw [srem_val, IScalar.ofInt_val_eq, isz_lit_val, Int.tmod_eq_emod_of_nonneg (by omega), hrel.k]
      dsimp only
      omega

set_option maxHeartbeats 4000000 in
/-- A new account (the previous one rewritten), found with its cross-reference, its group and
`DEFAULT` missing. -/
theorem process_record_change_dmiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s)
    (id : Int) (hold : s.lastId = some id) (hne : id ≠ r.trancat_acct_id.val)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length)
    (hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
      st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807)
    (hl3 : out.account_file_rewrites.val.length < Usize.max)
    (hfa : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (acctsAfter st).length)
    (hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
      xrefs.val.length)
    (hdn : ¬ discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd) < discs.val.length)
    (hdm : ¬ discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd) < discs.val.length)
    (hl1 : out.displays.val.length + 6 < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (false, st', out') ∧
        ORel out' (Model.stepE (xrefs.val.map CardXrefRecord.vals)
          (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk
          (ofSt s false) (TranCatBalRecord.vals r)) ∧
        (Model.stepE (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk (ofSt s false)
          (TranCatBalRecord.vals r)).stop = true) := by
  have hm := usize_max_ge
  have hsome : s.lastId.isSome := by rw [hold]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hfirst : st.first_time = false := by rw [hrel.first, hsome]; rfl
  have hlast : st.last_acct.val = id := hrel.last _ hold
  have hne' : (r.trancat_acct_id != st.last_acct) = true := by
    rw [bne_iff_ne, ne_eq]; intro h; apply hne; rw [← hlast, h]
  have hneq : s.lastId ≠ some (Model.tAcct (TranCatBalRecord.vals r)) := by
    rw [hold, tAcct_vals]; intro h; apply hne; exact Option.some.inj h
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hl1' : out.displays.val.length < Usize.max := by omega
  have hf0i := usz_val _ (le_trans (Nat.le_of_lt hf0) hal)
  have hv1 : (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val = acctsAfter st := by
    rw [alloc.vec.Vec.set_val_eq, hf0i]; rfl
  have hl1a : (acctsAfter st).length = st.accounts.val.length := by simp [acctsAfter]
  have hU := update_account_eq
    { st with tran_cat_bal_record := r, last_acct_set := true, first_time := false }
    { out with displays := alloc.vec.Vec.from (out.displays.val ++
        [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (push_le _ _ hl1') }
    hbt ⟨_, List.getElem_mem hf0, by simpa using List.findIdx_getElem (w := hf0)⟩ hl3
  dsimp only at hU
  have haccts := acctsAfter_vals st out s hrel hsome hf0
  rw [stepE_new _ _ _ _ _ _ hneq, preAcct_some _ _ hsome]
  dsimp only
  have hmA : Model.findAcctO (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r)) =
      some (AccountRecord.vals ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])) := by
    rw [← haccts, tAcct_vals, findAcctO_eq, dite_eq_left hfa]
  have hmX : Model.findXrefO (xrefs.val.map CardXrefRecord.vals)
      (Model.tAcct (TranCatBalRecord.vals r)) =
      some (CardXrefRecord.vals (xrefs.val[xrefs.val.findIdx
        (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)])) := by
    rw [tAcct_vals, findXrefO_eq, dite_eq_left hfx]
  have hm1 : Model.findRateO (discs.val.map DisGroupRecord.vals)
      (Model.aGrp (AccountRecord.vals ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])))
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [aGrp_vals, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdn]
  rw [hmA]
  dsimp only
  rw [hmX]
  dsimp only
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) (by omega))
  have hfxi := usz_val _ (le_trans (Nat.le_of_lt hfx) hxl)
  have hge1 : ¬ (usz ((acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int))) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length, hv1,
      not_le]; omega
  have hfa' : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val.length := by rw [hv1]; exact hfa
  have hge2 : ¬ (usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfxi, Slice.len_val, Slice.length, not_le]; omega
  have hnlt : ¬ (usz (discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd)) < discs.len) := by
    simp only [UScalar.lt_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]
    exact hdn
  have hm2 : Model.findRateO (discs.val.map DisGroupRecord.vals) Model.defaultGrp
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [← defR_ebc, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdm]
  rw [rate_dmiss _ _ _ _ _ hm1 hm2]
  refine (fun h => ?_) (show ∀ X : Model.St, ∀ l, (Model.StE.abend (ofSt X false) l).stop = true
    from fun _ _ => rfl)
  simp only [h, and_true]
  have hge3 : usz (discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd)) ≥ discs.len := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]; omega
  simp only [cbact04c_t.process_record, hset, hne', hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, bind_ok]
  simp only [wp_bind, wp_Vec_push, hl1', _root_.dite_true]
  simp only [hU, wp_ok, Aeneas.Std.uncurry_apply_pair]
  simp only [_root_.ite_true, find_account_eq, bind_ok, hv1]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa', bind_ok, find_xref_eq]
  simp only [hv1]
  simp only [hge2, _root_.ite_false, slice_index_usz _ _ hfx, bind_ok, find_disc_eq]
  simp only [hnlt, _root_.ite_false, m_disc_missing_eq, m_try_default_eq, find_disc_eq, bind_ok,
    defR_fold]
  simp only [hge3, _root_.ite_true, m_err_default_disc_eq, bind_ok]
  aeneas_wp []
  simp (disch := abend_len) only [abend_eq]
  aeneas_wp []
  ifs_omega2
  refine ⟨_, _, rfl, ?_⟩
  refine orel_abend2 _ _ _ ?_ ?_ ?_ rfl
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text, missing_text, tryDefault_text, errDefault_text, status23_text, abending_text,
      dfltLines, withAcct, List.append_assoc, List.cons_append, List.nil_append]
  · exact hrel.writes
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
      hrel.rewrites, postedR_vals, hrel.acct hsome, hrel.total, withAcct]

end EquivLean.Modernize.Cbact04c.Rust
