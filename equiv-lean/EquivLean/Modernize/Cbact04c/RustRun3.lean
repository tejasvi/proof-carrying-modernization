import EquivLean.Modernize.Cbact04c.RustRun2

/-!
# CBACT04C → Rust: one category record (`process_record`) against the model's `step`

`SRel st out s`: the Rust state and output after some records against the model's state `s`
(outputs, the account table, the flags, the current account and cross-reference, the running
total and suffix, the spaces of the transaction record that `build_tran` keeps).

`process_record` is proved in its three cases (the generated code repeats the interest part in
each): the same account as the previous record (`process_record_same`), the first record
(`process_record_first`), a new account, after `update_account` rewrites the previous one
(`process_record_change`).  Each: select the branch, rewrite the helpers by their equations,
execute symbolically, decide the overflow tests by `omega` from the field bounds, then the
relation with the model's next state (`step_same`/`step_first`/`step_change`, `srel_post`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-- The Rust state and output after some category records, against the model's state. -/
structure SRel (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St) : Prop where
  disp : out.displays.val.map (fun l => l.val.map (·.val)) = s.disp
  writes : out.transact_file_writes.val.map TranRecord.vals = s.writes
  rewrites : out.account_file_rewrites.val.map AccountRecord.vals = s.rewrites
  abended : out.abended = false
  accts : st.accounts.val.map AccountRecord.vals = s.accts
  set : st.last_acct_set = s.lastId.isSome
  first : st.first_time = !s.lastId.isSome
  last : ∀ id, s.lastId = some id → st.last_acct.val = id
  acct : s.lastId.isSome → AccountRecord.vals st.account_record = s.acct
  xref : s.lastId.isSome → CardXrefRecord.vals st.card_xref_record = s.xref
  total : st.total_int.val = s.total
  k : st.tranid_suffix.val = s.k
  desc : st.tran_record.tran_desc.val.drop 24 = List.replicate 76 32#u8
  fill : st.tran_record.filler1.val = List.replicate 20 32#u8

/-- Bounds on the model's state (no Rust arithmetic overflows). -/
structure MBounds (s : Model.St) : Prop where
  total : s.total.natAbs < 10 ^ 11
  k : s.k < 1000000
  bal : ∀ a ∈ s.accts, (Model.aBal a).natAbs < 10 ^ 12
  acct : (Model.aBal s.acct).natAbs < 10 ^ 12

theorem srem_val (x y : I64) : (⟨BitVec.srem x.bv y.bv⟩ : I64).val = Int.tmod x.val y.val := by
  show (BitVec.srem x.bv y.bv).toInt = Int.tmod x.bv.toInt y.bv.toInt
  rw [BitVec.toInt_srem]

theorem mul_bound (a b : Int) (ha : a.natAbs < 10 ^ 11) (hb : b.natAbs < 10 ^ 6) :
    -9223372036854775808 ≤ a * b ∧ a * b ≤ 9223372036854775807 := by
  have h : (a * b).natAbs < 10 ^ 17 := by
    rw [Int.natAbs_mul]
    calc a.natAbs * b.natAbs < 10 ^ 11 * 10 ^ 6 := Nat.mul_lt_mul'' ha hb
      _ = 10 ^ 17 := by norm_num
  omega

theorem tmod11_bound (x : Int) : (Int.tmod x (10 ^ 11)).natAbs < 10 ^ 11 := by
  rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by norm_num)

/-! ## The model's step, case by case -/

/-- The interest part of the model's step (1200-GET-INTEREST-RATE to 1300-B-WRITE-TX). -/
def mpost (dv : List (List FVal)) (p c : List UInt8) (t : List FVal) (s2 : Model.St) : Model.St :=
  if Model.findRate dv (Model.aGrp s2.acct) (Model.tType t) (Model.tCat t) = 0 then s2
  else
    let amt := Int.tmod (Int.tdiv (Model.tBal t *
      Model.findRate dv (Model.aGrp s2.acct) (Model.tType t) (Model.tCat t)) 120000) (10 ^ 11)
    { s2 with total := Int.tmod (s2.total + amt) (10 ^ 11), k := (s2.k + 1) % 1000000,
              writes := s2.writes ++ [Model.tranVals p c ((s2.k + 1) % 1000000) (Model.aId s2.acct)
                (Model.xCard s2.xref) amt] }

theorem step_same (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h : s.lastId = some (Model.tAcct t)) :
    Model.step xr dv p c s t = mpost dv p c t { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t] } := by
  dsimp only [Model.step, mpost]
  simp only [h, _root_.ite_true]

theorem step_first (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h : s.lastId = none) :
    Model.step xr dv p c s t = mpost dv p c t
      { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t], lastId := some (Model.tAcct t),
               total := 0, acct := Model.findAcct s.accts (Model.tAcct t),
               xref := Model.findXref xr (Model.tAcct t) } := by
  dsimp only [Model.step, mpost]
  simp only [h, reduceCtorEq, _root_.ite_false, Option.isSome_none, Bool.false_eq_true]

theorem step_change (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (id : Int) (h : s.lastId = some id) (hne : id ≠ Model.tAcct t) :
    Model.step xr dv p c s t = mpost dv p c t
      { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t],
               accts := Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
                 (Model.posted s.acct s.total) s.accts,
               rewrites := s.rewrites ++ [Model.posted s.acct s.total],
               lastId := some (Model.tAcct t), total := 0,
               acct := Model.findAcct (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
                 (Model.posted s.acct s.total) s.accts) (Model.tAcct t),
               xref := Model.findXref xr (Model.tAcct t) } := by
  dsimp only [Model.step, mpost]
  have : ¬ (some id = some (Model.tAcct t)) := by simpa using hne
  simp only [h, this, _root_.ite_false, Option.isSome_some, _root_.ite_true]

/-! ## Lookups on the field values, from the Rust searches -/

theorem find_map_getD' {α β : Type _} (f : α → β) (q : β → Bool) (p : α → Bool) (hp : q ∘ f = p)
    (d : β) (l : List α) (h : l.findIdx p < l.length) :
    ((l.map f).find? q).getD d = f (l[l.findIdx p]) := by
  subst hp; exact find_map_getD f q d l h

theorem findAcct_eq (l : List cbact04c_t.AccountRecord) (id : Int)
    (h : l.findIdx (fun r => r.acct_id.val == id) < l.length) :
    Model.findAcct (l.map AccountRecord.vals) id =
      AccountRecord.vals (l[l.findIdx (fun r => r.acct_id.val == id)]) := by
  unfold Model.findAcct
  exact find_map_getD' AccountRecord.vals _ _ (acctKey_comp id) [] l h

theorem findXref_eq (l : List cbact04c_t.CardXrefRecord) (id : Int)
    (h : l.findIdx (fun r => r.xref_acct_id.val == id) < l.length) :
    Model.findXref (l.map CardXrefRecord.vals) id =
      CardXrefRecord.vals (l[l.findIdx (fun r => r.xref_acct_id.val == id)]) := by
  unfold Model.findXref
  exact find_map_getD' CardXrefRecord.vals _ _ (xrefKey_comp id) [] l h

theorem findRate_eq (l : List cbact04c_t.DisGroupRecord) (group : Std.Array U8 10#usize)
    (typ : Std.Array U8 2#usize) (cat : I64) (h : l.findIdx (discKey group typ cat) < l.length) :
    Model.findRate (l.map DisGroupRecord.vals) (group.val.map ebc) (typ.val.map ebc) cat.val =
      (l[l.findIdx (discKey group typ cat)]).dis_int_rate.val := by
  unfold Model.findRate
  rw [find_map_getD' DisGroupRecord.vals _ _ (discKey_comp group typ cat) [] l h]
  rfl

/-! ## The relation through the interest part -/

theorem srel_norate (st : cbact04c_t.State) (out : cbact04c_t.Output) (s2 : Model.St)
    (hrel : SRel st out s2) (dgr : cbact04c_t.DisGroupRecord) :
    SRel { st with dis_group_record := dgr } out s2 :=
  ⟨hrel.disp, hrel.writes, hrel.rewrites, hrel.abended, hrel.accts, hrel.set, hrel.first, hrel.last,
    hrel.acct, hrel.xref, hrel.total, hrel.k, hrel.desc, hrel.fill⟩

theorem tranOf_desc (prev : cbact04c_t.TranRecord) (parm : Std.Array U8 10#usize)
    (suffix acct amt : I64) (card : Std.Array U8 16#usize) (clock : Std.Array U8 21#usize) :
    (tranOf prev parm suffix acct amt card clock).tran_desc.val.drop 24 = prev.tran_desc.val.drop 24 := by
  simp only [tranOf, Std.Array.from_val]
  rw [List.drop_append_of_le_length (by simp [descPre, digs_length]), List.drop_eq_nil_of_le
    (by simp [descPre, digs_length])]
  simp

theorem srel_post (st : cbact04c_t.State) (out : cbact04c_t.Output) (s2 : Model.St)
    (hrel : SRel st out s2) (hsome : s2.lastId.isSome)
    (dgr : cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (monthly i4 i6 : I64) (amt : Int) (hmon : monthly.val = amt)
    (hi4 : i4.val = Int.tmod (s2.total + amt) (10 ^ 11))
    (hi6 : i6.val = (((s2.k + 1) % 1000000 : Nat) : Int))
    (hw : out.transact_file_writes.val.length < Usize.max) :
    SRel { st with dis_group_record := dgr,
                   tran_record := tranOf st.tran_record parms.parm_date i6 st.account_record.acct_id
                     monthly st.card_xref_record.xref_card_num clock,
                   total_int := i4, tranid_suffix := i6 }
      { out with transact_file_writes := alloc.vec.Vec.from (out.transact_file_writes.val ++
          [tranOf st.tran_record parms.parm_date i6 st.account_record.acct_id monthly
            st.card_xref_record.xref_card_num clock]) (by simp; omega) }
      { s2 with total := Int.tmod (s2.total + amt) (10 ^ 11), k := (s2.k + 1) % 1000000,
                writes := s2.writes ++ [Model.tranVals (Model.parmOf (ExternalParms.vals parms)) clk
                  ((s2.k + 1) % 1000000) (Model.aId s2.acct) (Model.xCard s2.xref) amt] } := by
  have hk0 : 0 ≤ i6.val := by rw [hi6]; positivity
  have hkn : i6.val.toNat = (s2.k + 1) % 1000000 := by rw [hi6]; omega
  refine ⟨hrel.disp, ?_, hrel.rewrites, hrel.abended, hrel.accts, hrel.set, hrel.first, hrel.last,
    hrel.acct, hrel.xref, hi4, ?_, ?_, hrel.fill⟩
  · simp only [alloc.vec.Vec.from_val, List.map_append, hrel.writes, List.map_cons, List.map_nil]
    rw [tranOf_vals _ _ _ _ _ _ _ clk hk0 hrel.desc hrel.fill hclk hclen, hkn, hmon,
      ← hrel.acct hsome, ← hrel.xref hsome, aId_vals, xCard_vals]
    rfl
  · show i6.val = ((s2.k + 1) % 1000000 : Nat)
    exact hi6
  · rw [tranOf_desc]; exact hrel.desc

theorem vec_index_usz {α : Type _} (v : alloc.vec.Vec α) (k : Nat) (h : k < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v (usz k) = .ok (v.val[k]) := by
  have hl : v.val.length ≤ Usize.max := v.property
  have hk := usz_val k (by omega)
  refine eq_ok_of_wp' ?_
  rw [alloc.vec.Vec.index_slice_index, wp_Vec_index_usize]
  simp only [hk, h, _root_.dite_true]

theorem slice_index_usz {α : Type _} (s : Slice α) (k : Nat) (h : k < s.val.length) :
    Slice.index_usize s (usz k) = .ok (s.val[k]) := by
  have hl : s.val.length ≤ Usize.max := by scalar_tac
  have hk := usz_val k (by omega)
  refine eq_ok_of_wp' ?_
  rw [wp_Slice_index_usize]
  simp only [hk, h, _root_.dite_true]

theorem push_le {α : Type _} (l : List α) (x : α) (h : l.length < Usize.max) :
    (l ++ [x]).length ≤ Usize.max := by simp; omega

theorem tcatLine_le (r : cbact04c_t.TranCatBalRecord) : (tcatLine r).length ≤ Usize.max := by
  rw [tcatLine_length]; have := usize_max_ge; omega

theorem tmodI11_val (v : I64) : (tmodI v 11).val = Int.tmod v.val (10 ^ 11) :=
  tmodI_val v 11 (by norm_num)

/-- The display line pushed: the relation with the record's text appended. -/
theorem srel_disp (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (hrel : SRel st out s) (r : cbact04c_t.TranCatBalRecord) (b : Bool) (hb : b = s.lastId.isSome)
    (h1 : out.displays.val.length < Usize.max) :
    SRel { st with tran_cat_bal_record := r, last_acct_set := b }
      { out with displays := alloc.vec.Vec.from (out.displays.val ++
          [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (by simp; omega) }
      { s with disp := s.disp ++ [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)] } := by
  refine ⟨?_, hrel.writes, hrel.rewrites, hrel.abended, hrel.accts, hb, hrel.first, hrel.last,
    hrel.acct, hrel.xref, hrel.total, hrel.k, hrel.desc, hrel.fill⟩
  simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
    tcatLine_text]

/-! ## `process_record`, case 1: the same account as the previous record -/

set_option maxHeartbeats 2000000 in
theorem process_record_same (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hb : MBounds s)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hsame : s.lastId = some r.trancat_acct_id.val)
    (hdd : discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd r.trancat_cd) <
      discs.val.length)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hl1 : out.displays.val.length < Usize.max) (hl2 : out.transact_file_writes.val.length < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (true, st', out') ∧
        SRel st' out' (Model.step (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk s (TranCatBalRecord.vals r))) := by
  have hsome : s.lastId.isSome := by rw [hsame]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hlast : st.last_acct.val = r.trancat_acct_id.val := hrel.last _ hsame
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hdi := usz_val _ (le_trans (Nat.le_of_lt hdd) hdl)
  have hne : (r.trancat_acct_id != st.last_acct) = false := by
    rw [bne_eq_false_iff_eq]; exact IScalar.eq_of_val_eq hlast.symm
  have hlt : usz (discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd
      r.trancat_cd)) < discs.len := by
    rw [UScalar.lt_equiv, hdi, Slice.len_val]; exact hdd
  have ht11 : ∀ v, cbact04c_t.trunc_digits v 11#u32 = .ok (tmodI v 11) := fun v => by
    rw [trunc_digits_eq v 11#u32 (by simp)]; rfl
  rw [step_same _ _ _ _ _ _ (by rw [hsame, tAcct_vals])]
  simp only [cbact04c_t.process_record, hset, hne, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_disc_eq, bind_ok]
  simp only [hlt, _root_.ite_true]
  aeneas_wp [hdi, hdd, ht11, build_tran_eq, isz_lit_val]
  obtain ⟨dgr, hdgr⟩ : ∃ d, discs.val[discs.val.findIdx
      (discKey st.account_record.acct_group_id r.trancat_type_cd r.trancat_cd)]'hdd = d := ⟨_, rfl⟩
  have hdmem : dgr ∈ discs.val := hdgr ▸ List.getElem_mem hdd
  simp only [hdgr]
  have hrate := hrates dgr hdmem
  have hm := mul_bound _ _ hbal hrate
  have hamt := tmod11_bound ((r.tran_cat_bal.val * dgr.dis_int_rate.val).tdiv 120000)
  have htot : st.total_int.val.natAbs < 10 ^ 11 := by rw [hrel.total]; exact hb.total
  have hk : st.tranid_suffix.val < 1000000 ∧ 0 ≤ st.tranid_suffix.val := by
    rw [hrel.k]; have := hb.k; omega
  have hfr : Model.findRate (discs.val.map DisGroupRecord.vals) (Model.aGrp s.acct)
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) =
      dgr.dis_int_rate.val := by
    rw [← hrel.acct hsome, aGrp_vals, tType_vals, tCat_vals, findRate_eq _ _ _ _ hdd, hdgr]
  have hd1 := srel_disp st out s hrel r true (by rw [hsome]) hl1
  simp only [tmodI11_val, IScalar.ofInt_val_eq]
  by_cases hr0 : dgr.dis_int_rate.val = 0
  · ifs_omega
    refine ⟨_, _, rfl, ?_⟩
    unfold mpost
    simp only [hfr, hr0, _root_.ite_true]
    exact srel_norate _ _ _ hd1 dgr
  · ifs_omega
    refine ⟨_, _, rfl, ?_⟩
    unfold mpost
    simp only [hfr, hr0, _root_.ite_false]
    refine srel_post _ _ _ hd1 hsome dgr parms clock clk hclk hclen _ _ _ _ ?_ ?_ ?_ hl2
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals, hrel.total]
    · rw [srem_val, IScalar.ofInt_val_eq, isz_lit_val, Int.tmod_eq_emod_of_nonneg (by omega), hrel.k]
      dsimp only
      omega

/-! ## `process_record`, case 2: the first record -/

/-- The relation after the account part of the first record (no rewrite). -/
theorem srel_first (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (hrel : SRel st out s) (r : cbact04c_t.TranCatBalRecord) (xrefs : List cbact04c_t.CardXrefRecord)
    (hfa : st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      st.accounts.val.length)
    (hfx : xrefs.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) < xrefs.length)
    (h1 : out.displays.val.length < Usize.max) :
    SRel { st with tran_cat_bal_record := r,
                   card_xref_record := xrefs[xrefs.findIdx (fun x => x.xref_acct_id.val ==
                     r.trancat_acct_id.val)],
                   account_record := st.accounts.val[st.accounts.val.findIdx
                     (fun a => a.acct_id.val == r.trancat_acct_id.val)],
                   last_acct_set := true, last_acct := r.trancat_acct_id, first_time := false,
                   total_int := 0#i64 }
      { out with displays := alloc.vec.Vec.from (out.displays.val ++
          [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (by simp; omega) }
      { s with disp := s.disp ++ [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)],
               lastId := some (Model.tAcct (TranCatBalRecord.vals r)), total := 0,
               acct := Model.findAcct s.accts (Model.tAcct (TranCatBalRecord.vals r)),
               xref := Model.findXref (xrefs.map CardXrefRecord.vals)
                 (Model.tAcct (TranCatBalRecord.vals r)) } := by
  refine ⟨?_, hrel.writes, hrel.rewrites, hrel.abended, hrel.accts, rfl, rfl, ?_, ?_, ?_, ?_,
    hrel.k, hrel.desc, hrel.fill⟩
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text]
  · intro id hid
    simp only [Option.some.injEq] at hid
    rw [← hid, tAcct_vals]
  · intro _
    rw [← hrel.accts, tAcct_vals, findAcct_eq _ _ hfa]
  · intro _
    rw [tAcct_vals, findXref_eq _ _ hfx]
  · simp only [isz_lit_val]

set_option maxHeartbeats 4000000 in
theorem process_record_first (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hb : MBounds s)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hnone : s.lastId = none)
    (hfa : st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      st.accounts.val.length)
    (hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) < xrefs.val.length)
    (hdd : discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd) < discs.val.length)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hl1 : out.displays.val.length < Usize.max) (hl2 : out.transact_file_writes.val.length < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (true, st', out') ∧
        SRel st' out' (Model.step (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk s (TranCatBalRecord.vals r))) := by
  have hset : st.last_acct_set = false := by rw [hrel.set, hnone]; rfl
  have hfirst : st.first_time = true := by rw [hrel.first, hnone]; rfl
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) hal)
  have hfxi := usz_val _ (le_trans (Nat.le_of_lt hfx) hxl)
  have hdi := usz_val _ (le_trans (Nat.le_of_lt hdd) hdl)
  have hge1 : ¬ (usz (st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len st.accounts) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
      not_le]; omega
  have hge2 : ¬ (usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfxi, Slice.len_val, Slice.length, not_le]; omega
  have hlt : usz (discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd)) < discs.len := by
    rw [UScalar.lt_equiv, hdi, Slice.len_val]; exact hdd
  have ht11 : ∀ v, cbact04c_t.trunc_digits v 11#u32 = .ok (tmodI v 11) := fun v => by
    rw [trunc_digits_eq v 11#u32 (by simp)]; rfl
  rw [step_first _ _ _ _ _ _ hnone]
  simp only [cbact04c_t.process_record, hset, hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, find_account_eq, bind_ok]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa, bind_ok, find_xref_eq]
  simp only [hge2, _root_.ite_false, slice_index_usz _ _ hfx, bind_ok, find_disc_eq]
  simp only [hlt, _root_.ite_true]
  aeneas_wp [hdi, hdd, ht11, build_tran_eq, isz_lit_val]
  obtain ⟨dgr, hdgr⟩ : ∃ d, discs.val[discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
      (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
      r.trancat_cd)]'hdd = d := ⟨_, rfl⟩
  have hdmem : dgr ∈ discs.val := hdgr ▸ List.getElem_mem hdd
  simp only [hdgr]
  have hrate := hrates dgr hdmem
  have hm := mul_bound _ _ hbal hrate
  have hamt := tmod11_bound ((r.tran_cat_bal.val * dgr.dis_int_rate.val).tdiv 120000)
  have hk : st.tranid_suffix.val < 1000000 ∧ 0 ≤ st.tranid_suffix.val := by
    rw [hrel.k]; have := hb.k; omega
  have hfr : Model.findRate (discs.val.map DisGroupRecord.vals)
      (Model.aGrp (Model.findAcct s.accts (Model.tAcct (TranCatBalRecord.vals r))))
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) =
      dgr.dis_int_rate.val := by
    rw [← hrel.accts, tAcct_vals, findAcct_eq _ _ hfa, aGrp_vals, tType_vals, tCat_vals,
      findRate_eq _ _ _ _ hdd, hdgr]
  have hd1 := srel_first st out s hrel r xrefs.val hfa hfx hl1
  simp only [tmodI11_val, IScalar.ofInt_val_eq]
  by_cases hr0 : dgr.dis_int_rate.val = 0
  · ifs_omega
    refine ⟨_, _, rfl, ?_⟩
    unfold mpost
    simp only [hfr, hr0, _root_.ite_true]
    exact srel_norate _ _ _ hd1 dgr
  · ifs_omega
    refine ⟨_, _, rfl, ?_⟩
    unfold mpost
    simp only [hfr, hr0, _root_.ite_false]
    refine srel_post _ _ _ hd1 rfl dgr parms clock clk hclk hclen _ _ _ _ ?_ ?_ ?_ hl2
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · rw [srem_val, IScalar.ofInt_val_eq, isz_lit_val, Int.tmod_eq_emod_of_nonneg (by omega), hrel.k]
      dsimp only
      omega

/-! ## `process_record`, case 3: a new account (the previous one is rewritten) -/

/-- The account table after the rewrite of the current account. -/
def acctsAfter (st : cbact04c_t.State) : List cbact04c_t.AccountRecord :=
  st.accounts.val.set (st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val))
    (postedR st.account_record st.total_int)

theorem acctsAfter_vals (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (hrel : SRel st out s) (hsome : s.lastId.isSome)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length) :
    (acctsAfter st).map AccountRecord.vals =
      Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct) (Model.posted s.acct s.total)
        s.accts := by
  rw [← hrel.acct hsome, ← hrel.total, ← postedR_vals, ← hrel.accts, aId_vals]
  rw [replaceFirst_map AccountRecord.vals _ _ _ (by rw [acctKey_comp]; exact hf0), acctKey_comp]
  rfl

/-- The relation after the account part of a record of a new account. -/
theorem srel_change (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (hrel : SRel st out s) (hsome : s.lastId.isSome) (r : cbact04c_t.TranCatBalRecord)
    (xrefs : List cbact04c_t.CardXrefRecord) (v : alloc.vec.Vec cbact04c_t.AccountRecord)
    (hv : v.val = acctsAfter st)
    (hfa : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (acctsAfter st).length)
    (hfx : xrefs.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) < xrefs.length)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length)
    (h1 : out.displays.val.length < Usize.max) (h3 : out.account_file_rewrites.val.length < Usize.max) :
    SRel { st with tran_cat_bal_record := r, accounts := v,
                   card_xref_record := xrefs[xrefs.findIdx (fun x => x.xref_acct_id.val ==
                     r.trancat_acct_id.val)],
                   account_record := (acctsAfter st)[(acctsAfter st).findIdx
                     (fun a => a.acct_id.val == r.trancat_acct_id.val)],
                   last_acct_set := true, last_acct := r.trancat_acct_id, first_time := false,
                   total_int := 0#i64 }
      { out with
          displays := alloc.vec.Vec.from (out.displays.val ++
            [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (push_le _ _ h1),
          account_file_rewrites := alloc.vec.Vec.from (out.account_file_rewrites.val ++
            [postedR st.account_record st.total_int]) (push_le _ _ h3) }
      { s with disp := s.disp ++ [Model.TranCatBalRecord.textS (TranCatBalRecord.vals r)],
               accts := Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
                 (Model.posted s.acct s.total) s.accts,
               rewrites := s.rewrites ++ [Model.posted s.acct s.total],
               lastId := some (Model.tAcct (TranCatBalRecord.vals r)), total := 0,
               acct := Model.findAcct (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
                 (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r)),
               xref := Model.findXref (xrefs.map CardXrefRecord.vals)
                 (Model.tAcct (TranCatBalRecord.vals r)) } := by
  have hacct := hrel.acct hsome
  have haccts := acctsAfter_vals st out s hrel hsome hf0
  refine ⟨?_, hrel.writes, ?_, hrel.abended, ?_, rfl, rfl, ?_, ?_, ?_, ?_, hrel.k, hrel.desc,
    hrel.fill⟩
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      tcatLine_text]
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.rewrites,
      postedR_vals, hacct, hrel.total]
  · rw [hv, haccts]
  · intro id hid
    simp only [Option.some.injEq] at hid
    rw [← hid, tAcct_vals]
  · intro _
    rw [← haccts, tAcct_vals, findAcct_eq _ _ hfa]
  · intro _
    rw [tAcct_vals, findXref_eq _ _ hfx]
  · simp only [isz_lit_val]

set_option maxHeartbeats 4000000 in
theorem process_record_change (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hb : MBounds s)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (id : Int) (hold : s.lastId = some id) (hne : id ≠ r.trancat_acct_id.val)
    (hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length)
    (hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
      st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807)
    (hfa : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (acctsAfter st).length)
    (hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) < xrefs.val.length)
    (hdd : discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd) < discs.val.length)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hl1 : out.displays.val.length < Usize.max) (hl2 : out.transact_file_writes.val.length < Usize.max)
    (hl3 : out.account_file_rewrites.val.length < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (true, st', out') ∧
        SRel st' out' (Model.step (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk s (TranCatBalRecord.vals r))) := by
  have hsome : s.lastId.isSome := by rw [hold]; rfl
  have hset : st.last_acct_set = true := by rw [hrel.set, hsome]
  have hfirst : st.first_time = false := by rw [hrel.first, hsome]; rfl
  have hlast : st.last_acct.val = id := hrel.last _ hold
  have hne' : (r.trancat_acct_id != st.last_acct) = true := by
    rw [bne_iff_ne, ne_eq]; intro h; apply hne; rw [← hlast, h]
  have hal : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hxl : xrefs.val.length ≤ Usize.max := by scalar_tac
  have hdl : discs.val.length ≤ Usize.max := by scalar_tac
  have hf0i := usz_val _ (le_trans (Nat.le_of_lt hf0) hal)
  have hv1 : (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val = acctsAfter st := by
    rw [alloc.vec.Vec.set_val_eq, hf0i]; rfl
  have hl1' : (acctsAfter st).length = st.accounts.val.length := by simp [acctsAfter]
  have hfai := usz_val _ (le_trans (Nat.le_of_lt hfa) (by omega))
  have hfxi := usz_val _ (le_trans (Nat.le_of_lt hfx) hxl)
  have hdi := usz_val _ (le_trans (Nat.le_of_lt hdd) hdl)
  have hge1 : ¬ (usz ((acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val)) ≥
      alloc.vec.Vec.len (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int))) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfai, alloc.vec.Vec.len_val, alloc.vec.Vec.length, hv1,
      not_le]; omega
  have hge2 : ¬ (usz (xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val)) ≥
      Slice.len xrefs) := by
    simp only [ge_iff_le, UScalar.le_equiv, hfxi, Slice.len_val, Slice.length, not_le]; omega
  have hlt : usz (discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
        (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
        r.trancat_cd)) < discs.len := by
    rw [UScalar.lt_equiv, hdi, Slice.len_val]; exact hdd
  have hfa' : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
      (st.accounts.set (usz (st.accounts.val.findIdx
      (fun a => a.acct_id.val == st.account_record.acct_id.val)))
      (postedR st.account_record st.total_int)).val.length := by rw [hv1]; exact hfa
  have ht11 : ∀ v, cbact04c_t.trunc_digits v 11#u32 = .ok (tmodI v 11) := fun v => by
    rw [trunc_digits_eq v 11#u32 (by simp)]; rfl
  have hU := update_account_eq
    { st with tran_cat_bal_record := r, last_acct_set := true, first_time := false }
    { out with displays := alloc.vec.Vec.from (out.displays.val ++
        [alloc.vec.Vec.from (tcatLine r) (tcatLine_le r)]) (push_le _ _ hl1) }
    hbt ⟨_, List.getElem_mem hf0, by simpa using List.findIdx_getElem (w := hf0)⟩ hl3
  dsimp only at hU
  rw [step_change _ _ _ _ _ _ id hold (by rw [tAcct_vals]; exact hne)]
  simp only [cbact04c_t.process_record, hset, hne', hfirst, _root_.ite_true, Bool.false_eq_true,
    _root_.ite_false, display_tcat_eq, bind_ok]
  simp only [wp_bind, wp_Vec_push, hl1, _root_.dite_true]
  simp only [hU, wp_ok, Aeneas.Std.uncurry_apply_pair]
  simp only [_root_.ite_true, find_account_eq, bind_ok, hv1]
  simp only [hge1, _root_.ite_false, vec_index_usz _ _ hfa', bind_ok, find_xref_eq]
  simp only [hv1]
  simp only [hge2, _root_.ite_false, slice_index_usz _ _ hfx, bind_ok, find_disc_eq]
  simp only [hlt, _root_.ite_true]
  aeneas_wp [hdi, hdd, ht11, build_tran_eq, isz_lit_val]
  obtain ⟨dgr, hdgr⟩ : ∃ d, discs.val[discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
      (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
      r.trancat_cd)]'hdd = d := ⟨_, rfl⟩
  have hdmem : dgr ∈ discs.val := hdgr ▸ List.getElem_mem hdd
  simp only [hdgr]
  have hrate := hrates dgr hdmem
  have hm := mul_bound _ _ hbal hrate
  have hamt := tmod11_bound ((r.tran_cat_bal.val * dgr.dis_int_rate.val).tdiv 120000)
  have hk : st.tranid_suffix.val < 1000000 ∧ 0 ≤ st.tranid_suffix.val := by
    rw [hrel.k]; have := hb.k; omega
  have hfr : Model.findRate (discs.val.map DisGroupRecord.vals)
      (Model.aGrp (Model.findAcct (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
        (Model.posted s.acct s.total) s.accts) (Model.tAcct (TranCatBalRecord.vals r))))
      (Model.tType (TranCatBalRecord.vals r)) (Model.tCat (TranCatBalRecord.vals r)) =
      dgr.dis_int_rate.val := by
    rw [← acctsAfter_vals st out s hrel hsome hf0, tAcct_vals, findAcct_eq _ _ hfa, aGrp_vals,
      tType_vals, tCat_vals, findRate_eq _ _ _ _ hdd, hdgr]
  have hd1 := srel_change st out s hrel hsome r xrefs.val _ hv1 hfa hfx hf0 hl1 hl3
  simp only [tmodI11_val, IScalar.ofInt_val_eq]
  by_cases hr0 : dgr.dis_int_rate.val = 0
  · ifs_omega
    refine ⟨_, _, rfl, ?_⟩
    unfold mpost
    simp only [hfr, hr0, _root_.ite_true]
    exact srel_norate _ _ _ hd1 dgr
  · ifs_omega
    refine ⟨_, _, rfl, ?_⟩
    unfold mpost
    simp only [hfr, hr0, _root_.ite_false]
    refine srel_post _ _ _ hd1 rfl dgr parms clock clk hclk hclen _ _ _ _ ?_ ?_ ?_ hl2
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · simp only [tmodI11_val, IScalar.ofInt_val_eq, tBal_vals]
    · rw [srem_val, IScalar.ofInt_val_eq, isz_lit_val, Int.tmod_eq_emod_of_nonneg (by omega), hrel.k]
      dsimp only
      omega

end EquivLean.Modernize.Cbact04c.Rust
