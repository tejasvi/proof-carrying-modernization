import EquivLean.Modernize.Cbact04c.Every.RustRun1
/-!
# CBACT04C → Rust on every input: `process_record`, the same account, the `DEFAULT` group
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

theorem findIdx_le' {α : Type _} (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length :=
  List.findIdx_le_length

/-- Decide the `if`s of a symbolically executed goal (lengths of appended lists, linear
arithmetic). -/
macro "ifs_omega2" : tactic =>
  `(tactic| simp (disch := omega) only [List.length_append, List.length_cons, List.length_nil,
    dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right])

theorem defR_fold (h) : Std.Array.make 10#usize [68#u8, 69#u8, 70#u8, 65#u8, 85#u8, 76#u8, 84#u8,
    32#u8, 32#u8, 32#u8] h = defR := rfl

set_option maxHeartbeats 4000000 in
/-- The same account, its group missing, the `DEFAULT` group found. -/
theorem process_record_same_dflt (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hb : MBounds s)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hsame : s.lastId = some r.trancat_acct_id.val)
    (hdn : ¬ discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd
      r.trancat_cd) < discs.val.length)
    (hdd : discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd) < discs.val.length)
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
  have hsome : s.lastId.isSome := by rw [hsame]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hlast : st.last_acct.val = r.trancat_acct_id.val := hrel.last _ hsame
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hdi := usz_val _ (le_trans (Nat.le_of_lt hdd) hdl)
  have hne : (r.trancat_acct_id != st.last_acct) = false := by
    rw [bne_eq_false_iff_eq]; exact IScalar.eq_of_val_eq hlast.symm
  have hnlt : ¬ (usz (discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd
      r.trancat_cd)) < discs.len) := by
    simp only [UScalar.lt_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]
    exact hdn
  have hge2 : ¬ (usz (discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd)) ≥
      discs.len) := by
    simp only [ge_iff_le, UScalar.le_equiv, hdi, Slice.len_val, Slice.length]; omega
  have ht11 : ∀ v, cbact04c_t.trunc_digits v 11#u32 = .ok (tmodI v 11) := fun v => by
    rw [trunc_digits_eq v 11#u32 (by simp)]; rfl
  -- the model
  have hgrp : Model.aGrp s.acct = st.account_record.acct_group_id.val.map ebc := by
    rw [← hrel.acct hsome, aGrp_vals]
  have hm1 : Model.findRateO (discs.val.map DisGroupRecord.vals) (Model.aGrp s.acct)
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [hgrp, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdn]
  obtain ⟨dgr, hdgr⟩ : ∃ d, discs.val[discs.val.findIdx
      (discKey defR r.trancat_type_cd r.trancat_cd)]'hdd = d := ⟨_, rfl⟩
  have hm2 : Model.findRateO (discs.val.map DisGroupRecord.vals) Model.defaultGrp
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) =
      some dgr.dis_int_rate.val := by
    rw [← defR_ebc, tType_vals, tCat_vals, findRateO_eq, dite_eq_left hdd, hdgr]
  rw [stepE_same _ _ _ _ _ _ (by rw [hsame, tAcct_vals]),
    rate_dflt _ _ _ { s with disp := s.disp ++ [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)] }
      _ _ hm1 hm2]
  simp only [toSt_ofSt, ofSt_stop, and_true]
  -- the Rust code
  simp only [cbact04c_t.process_record, hset, hne, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_disc_eq, bind_ok]
  simp only [hnlt, _root_.ite_false, m_disc_missing_eq, m_try_default_eq, find_disc_eq, bind_ok,
    defR_fold]
  simp only [hge2, _root_.ite_false]
  aeneas_wp [hdi, hdd, hdgr, ht11, build_tran_eq, isz_lit_val]
  have hdmem : dgr ∈ discs.val := hdgr ▸ List.getElem_mem hdd
  have hrate := hrates dgr hdmem
  have hm := mul_bound _ _ hbal hrate
  have hamt := tmod11_bound ((r.tran_cat_bal.val * dgr.dis_int_rate.val).tdiv 120000)
  have htot : st.total_int.val.natAbs < 10 ^ 11 := by rw [hrel.total]; exact hb.total
  have hk : st.tranid_suffix.val < 1000000 ∧ 0 ≤ st.tranid_suffix.val := by
    rw [hrel.k]; have := hb.k; omega
  have hd1 := srel_disp st out s hrel r true (by rw [hsome]) (by omega)
  have hd2 := srel_lines _ _ { out with displays := alloc.vec.Vec.from (out.displays.val ++
      [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)] ++
      [alloc.vec.Vec.from missingBytes (msg_le _ (by decide))] ++
      [alloc.vec.Vec.from tryDefaultBytes (msg_le _ (by decide))]) (by simp; omega) } _ hd1 dfltLines
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
    refine srel_post _ _ _ hd2 hsome dgr parms clock clk hclk hclen _ _ _ _ ?_ ?_ ?_ hl2
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals, hrel.total]
    · rw [srem_val, IScalar.ofInt_val_eq, isz_lit_val, Int.tmod_eq_emod_of_nonneg (by omega), hrel.k]
      dsimp only
      omega

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: `process_record`, the abends of the first record
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-- After an abend: the outputs against the model's abended state, from the three outputs. -/
theorem orel_abend2 (out' : cbact04c_t.Output) (s' : Model.St) (lines : List (List Nat))
    (hd : out'.displays.val.map (fun l => l.val.map (·.val)) =
      s'.disp ++ lines ++ [Model.txt "FILE STATUS IS: NNNN0023", Model.txt "ABENDING PROGRAM"])
    (hw : out'.transact_file_writes.val.map TranRecord.vals = s'.writes)
    (hr : out'.account_file_rewrites.val.map AccountRecord.vals = s'.rewrites)
    (ha : out'.abended = true) :
    ORel out' ((ofSt s' false).abend lines) :=
  ⟨by rw [hd]; rfl, by rw [hw]; rfl, by rw [hr]; rfl, by rw [ha]; rfl⟩

theorem preAcct_none (s : Model.St) (t : List FVal) (h : s.lastId = none) :
    preAcct s t = { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t] } := by
  simp [preAcct, h]

theorem nf_text (id : I64) :
    (notFoundBytes ++ digs 11 id.val.natAbs).map UScalar.val = nfLine id.val := by
  rw [List.map_append, notFound_text, digs_val]; rfl

/-- The length side conditions of an abend. -/
macro "abend_len" : tactic => `(tactic|
  (simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil,
    digs_length]; omega))

set_option maxHeartbeats 4000000 in
/-- The first record, its account missing. -/
theorem process_record_first_amiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hnone : s.lastId = none)
    (hfa : ¬ st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      st.accounts.val.length)
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
  have hset : st.last_acct_set = false := by rw [hrel.set, hnone]; rfl
  have hfirst : st.first_time = true := by rw [hrel.first, hnone]; rfl
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hge1 : usz (st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len st.accounts := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' _ _) hal),
      alloc.vec.Vec.len_val, alloc.vec.Vec.length]; omega
  have hpd := push_digits_eq (alloc.vec.Vec.from notFoundBytes (msg_le _ (by decide)))
    r.trancat_acct_id 11#usize (by simp) (by simp [notFoundBytes]; omega)
  -- the model
  have hmA : Model.findAcctO (preAcct s (TranCatBalRecord.vals r)).accts
      (Model.tAcct (TranCatBalRecord.vals r)) = none := by
    rw [preAcct_none _ _ hnone]
    show Model.findAcctO s.accts _ = none
    rw [← hrel.accts, tAcct_vals, findAcctO_eq, dite_eq_right hfa]
  rw [stepE_new _ _ _ _ _ _ (by rw [hnone]; simp), hmA]
  dsimp only
  refine (fun h => ?_) (show (Model.StE.abend (ofSt (preAcct s (TranCatBalRecord.vals r)) false)
    [nfLine (Model.tAcct (TranCatBalRecord.vals r)), Model.txt "ERROR READING ACCOUNT FILE"]).stop =
      true from rfl)
  simp only [h, and_true]
  -- the Rust code
  simp only [cbact04c_t.process_record, hset, hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_account_eq, bind_ok]
  simp only [hge1, _root_.ite_true, m_acct_not_found_eq, m_err_read_acct_eq, bind_ok, hpd]
  aeneas_wp []
  simp (disch := abend_len) only [abend_eq]
  aeneas_wp []
  ifs_omega2
  refine ⟨_, _, rfl, ?_⟩
  refine orel_abend2 _ _ _ ?_ ?_ ?_ rfl
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text, preAcct_none _ _ hnone, notFound_text, digs_val, nfLine, tAcct_vals, errAcct_text, status23_text,
      abending_text, List.append_assoc, List.cons_append, List.nil_append]
  · rw [preAcct_none _ _ hnone]; exact hrel.writes
  · rw [preAcct_none _ _ hnone]; exact hrel.rewrites

set_option maxHeartbeats 4000000 in
/-- The same account, its group and the `DEFAULT` group missing. -/
theorem process_record_same_dmiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hsame : s.lastId = some r.trancat_acct_id.val)
    (hdn : ¬ discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd
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
  have hsome : s.lastId.isSome := by rw [hsame]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hlast : st.last_acct.val = r.trancat_acct_id.val := hrel.last _ hsame
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hne : (r.trancat_acct_id != st.last_acct) = false := by
    rw [bne_eq_false_iff_eq]; exact IScalar.eq_of_val_eq hlast.symm
  have hnlt : ¬ (usz (discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd
      r.trancat_cd)) < discs.len) := by
    simp only [UScalar.lt_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]
    exact hdn
  have hge2 : usz (discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd)) ≥ discs.len := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]; omega
  -- the model
  have hgrp : Model.aGrp s.acct = st.account_record.acct_group_id.val.map ebc := by
    rw [← hrel.acct hsome, aGrp_vals]
  have hm1 : Model.findRateO (discs.val.map DisGroupRecord.vals) (Model.aGrp s.acct)
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [hgrp, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdn]
  have hm2 : Model.findRateO (discs.val.map DisGroupRecord.vals) Model.defaultGrp
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [← defR_ebc, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdm]
  rw [stepE_same _ _ _ _ _ _ (by rw [hsame, tAcct_vals]),
    rate_dmiss _ _ _ { s with disp := s.disp ++ [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)] }
      _ hm1 hm2]
  refine (fun h => ?_) (show (Model.StE.abend (ofSt { { s with disp := s.disp ++
      [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)] } with disp := (s.disp ++
      [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)]) ++ dfltLines } false)
    [Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP"]).stop = true from rfl)
  simp only [h, and_true]
  -- the Rust code
  simp only [cbact04c_t.process_record, hset, hne, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_disc_eq, bind_ok]
  simp only [hnlt, _root_.ite_false, m_disc_missing_eq, m_try_default_eq, find_disc_eq, bind_ok,
    defR_fold]
  simp only [hge2, _root_.ite_true, m_err_default_disc_eq, bind_ok]
  aeneas_wp []
  simp (disch := abend_len) only [abend_eq]
  aeneas_wp []
  ifs_omega2
  refine ⟨_, _, rfl, ?_⟩
  refine orel_abend2 _ _ _ ?_ ?_ ?_ rfl
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text, missing_text, tryDefault_text, errDefault_text, status23_text, abending_text,
      dfltLines, List.append_assoc, List.cons_append, List.nil_append]
  · exact hrel.writes
  · exact hrel.rewrites

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: `process_record`, the first record (xref missing, `DEFAULT`)
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

set_option maxHeartbeats 4000000 in
/-- The first record, its account found, its cross-reference missing. -/
theorem process_record_first_xmiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hnone : s.lastId = none)
    (hfa : st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      st.accounts.val.length)
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
  have hset : st.last_acct_set = false := by rw [hrel.set, hnone]; rfl
  have hfirst : st.first_time = true := by rw [hrel.first, hnone]; rfl
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) hal)
  have hge1 : ¬ (usz (st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len st.accounts) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
      not_le]; omega
  have hge2 : usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' _ _) hxl),
      Slice.len_val, Slice.length]; omega
  have hpd := push_digits_eq (alloc.vec.Vec.from notFoundBytes (msg_le _ (by decide)))
    r.trancat_acct_id 11#usize (by simp) (by simp [notFoundBytes]; omega)
  -- the model
  have hmA : Model.findAcctO s.accts (Model.tAcct (TranCatBalRecord.vals r)) =
      some (AccountRecord.vals (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])) := by
    rw [← hrel.accts, tAcct_vals, findAcctO_eq, dite_eq_left hfa]
  have hmX : Model.findXrefO (xrefs.val.map CardXrefRecord.vals)
      (Model.tAcct (TranCatBalRecord.vals r)) = none := by
    rw [tAcct_vals, findXrefO_eq, dite_eq_right hfx]
  rw [stepE_new _ _ _ _ _ _ (by rw [hnone]; simp), preAcct_none _ _ hnone]
  dsimp only
  rw [hmA]
  dsimp only
  rw [hmX]
  dsimp only
  refine (fun h => ?_) (show (Model.StE.abend (ofSt { s with disp := s.disp ++
      [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)] } false)
    [nfLine (Model.tAcct (TranCatBalRecord.vals r)), Model.txt "ERROR READING XREF FILE"]).stop =
      true from rfl)
  simp only [h, and_true]
  -- the Rust code
  simp only [cbact04c_t.process_record, hset, hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_account_eq, bind_ok]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa, bind_ok, find_xref_eq]
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
  · exact hrel.rewrites

set_option maxHeartbeats 4000000 in
/-- The first record, its account and cross-reference found, its group missing, `DEFAULT` found. -/
theorem process_record_first_dflt (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hnone : s.lastId = none)
    (hfa : st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      st.accounts.val.length)
    (hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
      xrefs.val.length)
    (hdn : ¬ discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
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
  have hset : st.last_acct_set = false := by rw [hrel.set, hnone]; rfl
  have hfirst : st.first_time = true := by rw [hrel.first, hnone]; rfl
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) hal)
  have hfxi := usz_val _ (le_trans (Nat.le_of_lt hfx) hxl)
  have hge1 : ¬ (usz (st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len st.accounts) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
      not_le]; omega
  have hge2 : ¬ (usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfxi, Slice.len_val, Slice.length, not_le]; omega
  have hnlt : ¬ (usz (discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd)) < discs.len) := by
    simp only [UScalar.lt_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]
    exact hdn
  -- the model
  have hmA : Model.findAcctO s.accts (Model.tAcct (TranCatBalRecord.vals r)) =
      some (AccountRecord.vals (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])) := by
    rw [← hrel.accts, tAcct_vals, findAcctO_eq, dite_eq_left hfa]
  have hmX : Model.findXrefO (xrefs.val.map CardXrefRecord.vals)
      (Model.tAcct (TranCatBalRecord.vals r)) =
      some (CardXrefRecord.vals (xrefs.val[xrefs.val.findIdx
        (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)])) := by
    rw [tAcct_vals, findXrefO_eq, dite_eq_left hfx]
  have hm1 : Model.findRateO (discs.val.map DisGroupRecord.vals)
      (Model.aGrp (AccountRecord.vals (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])))
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [aGrp_vals, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdn]
  rw [stepE_new _ _ _ _ _ _ (by rw [hnone]; simp), preAcct_none _ _ hnone]
  dsimp only
  rw [hmA]
  dsimp only
  rw [hmX]
  dsimp only
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
  -- the Rust code
  simp only [cbact04c_t.process_record, hset, hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_account_eq, bind_ok]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa, bind_ok, find_xref_eq]
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
  have hd1 := srel_first st out s hrel r xrefs.val hfa hfx (by omega)
  have eA : Model.findAcct s.accts (Model.tAcct (TranCatBalRecord.vals r)) =
      AccountRecord.vals (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]) := by
    rw [← hrel.accts, tAcct_vals, findAcct_eq _ _ hfa]
  have eX : Model.findXref (xrefs.val.map CardXrefRecord.vals) (Model.tAcct (TranCatBalRecord.vals r)) =
      CardXrefRecord.vals (xrefs.val[xrefs.val.findIdx
        (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)]) := by
    rw [tAcct_vals, findXref_eq _ _ hfx]
  rw [eA, eX] at hd1
  have hd2 := srel_lines _ _ { out with displays := alloc.vec.Vec.from (out.displays.val ++
      [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)] ++
      [alloc.vec.Vec.from missingBytes (msg_le _ (by decide))] ++
      [alloc.vec.Vec.from tryDefaultBytes (msg_le _ (by decide))]) (by simp; omega) } _ hd1 dfltLines
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
/-- The first record, its account and cross-reference found, its group and `DEFAULT` missing. -/
theorem process_record_first_dmiss (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hnone : s.lastId = none)
    (hfa : st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      st.accounts.val.length)
    (hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
      xrefs.val.length)
    (hdn : ¬ discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
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
  have hset : st.last_acct_set = false := by rw [hrel.set, hnone]; rfl
  have hfirst : st.first_time = true := by rw [hrel.first, hnone]; rfl
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) hal)
  have hfxi := usz_val _ (le_trans (Nat.le_of_lt hfx) hxl)
  have hge1 : ¬ (usz (st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len st.accounts) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
      not_le]; omega
  have hge2 : ¬ (usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfxi, Slice.len_val, Slice.length, not_le]; omega
  have hnlt : ¬ (usz (discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd)) < discs.len) := by
    simp only [UScalar.lt_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]
    exact hdn
  -- the model
  have hmA : Model.findAcctO s.accts (Model.tAcct (TranCatBalRecord.vals r)) =
      some (AccountRecord.vals (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])) := by
    rw [← hrel.accts, tAcct_vals, findAcctO_eq, dite_eq_left hfa]
  have hmX : Model.findXrefO (xrefs.val.map CardXrefRecord.vals)
      (Model.tAcct (TranCatBalRecord.vals r)) =
      some (CardXrefRecord.vals (xrefs.val[xrefs.val.findIdx
        (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)])) := by
    rw [tAcct_vals, findXrefO_eq, dite_eq_left hfx]
  have hm1 : Model.findRateO (discs.val.map DisGroupRecord.vals)
      (Model.aGrp (AccountRecord.vals (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)])))
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [aGrp_vals, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdn]
  rw [stepE_new _ _ _ _ _ _ (by rw [hnone]; simp), preAcct_none _ _ hnone]
  dsimp only
  rw [hmA]
  dsimp only
  rw [hmX]
  dsimp only
  have hm2 : Model.findRateO (discs.val.map DisGroupRecord.vals) Model.defaultGrp
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) = none := by
    rw [← defR_ebc, tType_vals, tCat_vals, findRateO_eq, dite_eq_right hdm]
  rw [rate_dmiss _ _ _ _ _ hm1 hm2]
  refine (fun h => ?_) (show ∀ X : Model.St, (Model.StE.abend (ofSt X false)
    [Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP"]).stop = true from fun _ => rfl)
  simp only [h, and_true]
  have hge3 : usz (discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd)) ≥ discs.len := by
    simp only [ge_iff_le, UScalar.le_equiv, usz_val _ (le_trans (findIdx_le' _ _) hdl), Slice.len_val,
      Slice.length]; omega
  -- the Rust code
  simp only [cbact04c_t.process_record, hset, hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_account_eq, bind_ok]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa, bind_ok, find_xref_eq]
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
  · exact hrel.rewrites

end EquivLean.Modernize.Cbact04c.Rust
