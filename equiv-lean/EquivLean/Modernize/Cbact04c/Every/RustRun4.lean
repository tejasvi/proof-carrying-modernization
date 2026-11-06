import EquivLean.Modernize.Cbact04c.Every.RustRun3
/-!
# CBACT04C → Rust on every input: the model's invariants, and the step on full success
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-! ## Lookups: the `Option` ones and the defaulting ones -/

theorem findAcct_of (l : List (List FVal)) (id : Int) (a : List FVal)
    (h : Model.findAcctO l id = some a) : Model.findAcct l id = a := by
  unfold Model.findAcctO at h; unfold Model.findAcct; rw [h]; rfl

theorem findXref_of (l : List (List FVal)) (id : Int) (x : List FVal)
    (h : Model.findXrefO l id = some x) : Model.findXref l id = x := by
  unfold Model.findXrefO at h; unfold Model.findXref; rw [h]; rfl

theorem findRate_of (l : List (List FVal)) (grp ty : List UInt8) (cat r : Int)
    (h : Model.findRateO l grp ty cat = some r) : Model.findRate l grp ty cat = r := by
  unfold Model.findRateO at h
  unfold Model.findRate
  cases hf : l.find? (fun d => Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat) with
  | none => rw [hf] at h; cases h
  | some d => rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; simp [h]

/-! ## Full success: the every-input step is the success model's step -/

theorem stepE_same_ok (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h : s.lastId = some (Model.tAcct t)) (r : Int)
    (hr : Model.findRateO dv (Model.aGrp s.acct) (Model.tType t) (Model.tCat t) = some r) :
    Model.stepE xr dv p c (ofSt s false) t = ofSt (Model.step xr dv p c s t) false := by
  rw [stepE_same _ _ _ _ _ _ h,
    rate_direct _ _ _ { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t] } _ r hr,
    step_same _ _ _ _ _ _ h, mpost_eq]
  rw [findRate_of _ _ _ _ _ hr]

theorem stepE_first_ok (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h : s.lastId = none) (a x : List FVal)
    (ha : Model.findAcctO s.accts (Model.tAcct t) = some a)
    (hx : Model.findXrefO xr (Model.tAcct t) = some x) (r : Int)
    (hr : Model.findRateO dv (Model.aGrp a) (Model.tType t) (Model.tCat t) = some r) :
    Model.stepE xr dv p c (ofSt s false) t = ofSt (Model.step xr dv p c s t) false := by
  rw [stepE_new _ _ _ _ _ _ (by rw [h]; simp), preAcct_none _ _ h]
  dsimp only
  rw [ha]
  dsimp only
  rw [hx]
  dsimp only
  rw [rate_direct _ _ _ (withAcct { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t] } t a x)
    _ r hr, step_first _ _ _ _ _ _ h, mpost_eq, findAcct_of _ _ _ ha, findXref_of _ _ _ hx]
  show ofSt (mpostR r p c t _) false = ofSt (mpostR (Model.findRate dv (Model.aGrp a) _ _) p c t _) false
  rw [findRate_of _ _ _ _ _ hr]
  rfl

theorem stepE_change_ok (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (id : Int) (h : s.lastId = some id) (hne : id ≠ Model.tAcct t) (a x : List FVal)
    (ha : Model.findAcctO (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) (Model.tAcct t) = some a)
    (hx : Model.findXrefO xr (Model.tAcct t) = some x) (r : Int)
    (hr : Model.findRateO dv (Model.aGrp a) (Model.tType t) (Model.tCat t) = some r) :
    Model.stepE xr dv p c (ofSt s false) t = ofSt (Model.step xr dv p c s t) false := by
  have hsome : s.lastId.isSome := by rw [h]; rfl
  rw [stepE_new _ _ _ _ _ _ (by rw [h]; intro e; exact hne (Option.some.inj e)),
    preAcct_some _ _ hsome]
  dsimp only
  rw [ha]
  dsimp only
  rw [hx]
  dsimp only
  rw [rate_direct _ _ _ (withAcct { s with
      disp := s.disp ++ [Model.TranCatBalRecord.textS t],
      accts := Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
        (Model.posted s.acct s.total) s.accts,
      rewrites := s.rewrites ++ [Model.posted s.acct s.total] } t a x) _ r hr,
    step_change _ _ _ _ _ _ id h hne, mpost_eq, findAcct_of _ _ _ ha, findXref_of _ _ _ hx]
  show ofSt (mpostR r p c t _) false = ofSt (mpostR (Model.findRate dv (Model.aGrp a) _ _) p c t _) false
  rw [findRate_of _ _ _ _ _ hr]
  rfl

/-! ## The model's invariants along the every-input run -/

/-- The current account is in the account table (the rewrite finds it). -/
def MInvE (s : Model.St) : Prop :=
  s.lastId.isSome → ∃ a ∈ s.accts, Model.aId a = Model.aId s.acct

theorem interest_props (p c : List UInt8) (S : Model.St) (t : List FVal) (r : Int) :
    (mpostR r p c t S).accts = S.accts ∧ (mpostR r p c t S).acct = S.acct ∧
      (mpostR r p c t S).lastId = S.lastId ∧
      ((mpostR r p c t S).total = S.total ∨ ((mpostR r p c t S).total).natAbs < 10 ^ 11) ∧
      ((mpostR r p c t S).k = S.k ∨ (mpostR r p c t S).k < 1000000) := by
  unfold mpostR
  split_ifs
  · exact ⟨rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨rfl, rfl, rfl, Or.inr (tmod11_bound _), Or.inr (Nat.mod_lt _ (by norm_num))⟩

/-- The rate part, when it does not abend, keeps the table, the account and the last id, and
keeps the bounds of the total and the suffix. -/
theorem rate_props (dv : List (List FVal)) (p c : List UInt8) (S : Model.St) (t : List FVal)
    (hns : ((ofSt S false).rate dv p c t).stop = false) :
    (toSt ((ofSt S false).rate dv p c t)).accts = S.accts ∧
      (toSt ((ofSt S false).rate dv p c t)).acct = S.acct ∧
      (toSt ((ofSt S false).rate dv p c t)).lastId = S.lastId ∧
      ((toSt ((ofSt S false).rate dv p c t)).total = S.total ∨
        ((toSt ((ofSt S false).rate dv p c t)).total).natAbs < 10 ^ 11) ∧
      ((toSt ((ofSt S false).rate dv p c t)).k = S.k ∨
        (toSt ((ofSt S false).rate dv p c t)).k < 1000000) := by
  cases h1 : Model.findRateO dv (Model.aGrp S.acct) (Model.tType t) (Model.tCat t) with
  | some r =>
    rw [rate_direct _ _ _ _ _ r h1, toSt_ofSt]
    exact interest_props p c S t r
  | none =>
    cases h2 : Model.findRateO dv Model.defaultGrp (Model.tType t) (Model.tCat t) with
    | some r =>
      rw [rate_dflt _ _ _ _ _ r h1 h2, toSt_ofSt]
      exact interest_props p c _ t r
    | none =>
      rw [rate_dmiss _ _ _ _ _ h1 h2] at hns
      cases hns

theorem posted_aId' (a : List FVal) (t : Int) : Model.aId (Model.posted a t) = Model.aId a :=
  posted_aId a t

theorem findAcctO_mem (l : List (List FVal)) (id : Int) (a : List FVal)
    (h : Model.findAcctO l id = some a) : a ∈ l ∧ Model.aId a = id := by
  unfold Model.findAcctO at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The invariants after a record (when the run does not abend). -/
theorem inv_step (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (hm : MInvE s) (hb : MBounds s)
    (hns : (Model.stepE xr dv p c (ofSt s false) t).stop = false) :
    MInvE (toSt (Model.stepE xr dv p c (ofSt s false) t)) ∧
      MBounds (toSt (Model.stepE xr dv p c (ofSt s false) t)) := by
  by_cases h : s.lastId = some (Model.tAcct t)
  · rw [stepE_same _ _ _ _ _ _ h] at hns ⊢
    obtain ⟨e1, e2, e3, e4, e5⟩ := rate_props dv p c _ t hns
    refine ⟨?_, ?_⟩
    · intro hs
      rw [e3] at hs
      rw [e1, e2]
      exact hm hs
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rcases e4 with e | e
        · rw [e]; exact hb.total
        · exact e
      · rcases e5 with e | e
        · rw [e]; exact hb.k
        · exact e
      · rw [e1]; exact hb.bal
      · rw [e2]; exact hb.acct
  · rw [stepE_new _ _ _ _ _ _ h] at hns ⊢
    have hbal : ∀ a ∈ (preAcct s t).accts, (Model.aBal a).natAbs < 10 ^ 12 := by
      intro a ha
      unfold preAcct at ha
      split_ifs at ha
      · rcases mem_replaceFirst _ _ _ _ ha with h' | h'
        · exact hb.bal a h'
        · rw [h']; exact posted_aBal_bound _ _ hb.acct
      · exact hb.bal a ha
    have hk : (preAcct s t).k = s.k := by unfold preAcct; split_ifs <;> rfl
    split at hns
    · cases hns
    · rename_i a ha
      split at hns
      · cases hns
      · rename_i x hx
        obtain ⟨e1, e2, e3, e4, e5⟩ := rate_props dv p c _ t hns
        obtain ⟨hmem, -⟩ := findAcctO_mem _ _ _ ha
        refine ⟨?_, ?_⟩
        · intro _
          rw [e1, e2]
          exact ⟨a, hmem, rfl⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · rcases e4 with e | e
            · rw [e]; simp [withAcct]
            · exact e
          · rcases e5 with e | e
            · rw [e]; simp only [withAcct, hk]; exact hb.k
            · exact e
          · rw [e1]; exact hbal
          · rw [e2]; exact hbal a hmem

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: `process_record`, all cases
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-- What `process_record` does to the relation: on `true` the relation with the model's next
state (not abended), on `false` the outputs of the model's abended state. -/
def PRel (st' : cbact04c_t.State) (out' : cbact04c_t.Output) (b : Bool) (s' : Model.StE) : Prop :=
  (b = true → SRel st' out' (toSt s') ∧ s'.stop = false) ∧ (b = false → ORel out' s' ∧ s'.stop = true)

theorem prel_true {st' : cbact04c_t.State} {out' : cbact04c_t.Output} {s' : Model.StE}
    (h1 : SRel st' out' (toSt s')) (h2 : s'.stop = false) : PRel st' out' true s' :=
  ⟨(fun _ => ⟨h1, h2⟩), (fun h => by cases h)⟩

theorem prel_false {st' : cbact04c_t.State} {out' : cbact04c_t.Output} {s' : Model.StE}
    (h1 : ORel out' s') (h2 : s'.stop = true) : PRel st' out' false s' :=
  ⟨(fun h => by cases h), (fun _ => ⟨h1, h2⟩)⟩

set_option maxHeartbeats 2000000 in
/-- **One category record, on every input.** -/
theorem process_record_specE (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hrel : SRel st out s) (hm : MInvE s) (hb : MBounds s)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hl1 : out.displays.val.length + 6 < Usize.max)
    (hl2 : out.transact_file_writes.val.length < Usize.max)
    (hl3 : out.account_file_rewrites.val.length < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ b st' out', o = .ok (b, st', out') ∧
        PRel st' out' b (Model.stepE (xrefs.val.map CardXrefRecord.vals)
          (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk
          (ofSt s false) (TranCatBalRecord.vals r))) := by
  have hl1' : out.displays.val.length < Usize.max := by omega
  rcases hlast : s.lastId with _ | id
  · -- the first record
    by_cases hfa : st.accounts.val.findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
        st.accounts.val.length
    · by_cases hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
          xrefs.val.length
      · by_cases hdd : discs.val.findIdx (discKey (st.accounts.val[st.accounts.val.findIdx
            (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
            r.trancat_cd) < discs.val.length
        · have hok := stepE_first_ok (xrefs.val.map CardXrefRecord.vals)
            (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk s
            (TranCatBalRecord.vals r) hlast _ _
            (by rw [← hrel.accts, tAcct_vals, findAcctO_eq, dite_eq_left hfa])
            (by rw [tAcct_vals, findXrefO_eq, dite_eq_left hfx]) _
            (by rw [aGrp_vals, tType_vals, tCat_vals, findRateO_eq, dite_eq_left hdd])
          refine wp_mono (process_record_first st out s r xrefs discs parms clock clk hrel hb hclk
            hclen hbal hlast hfa hfx hdd hrates hl1' hl2) ?_
          rintro o ⟨st', out', rfl, hr⟩
          exact ⟨true, st', out', rfl, prel_true (by rw [hok, toSt_ofSt]; exact hr) (by rw [hok]; rfl)⟩
        · by_cases hdd2 : discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd) <
              discs.val.length
          · refine wp_mono (process_record_first_dflt st out s r xrefs discs parms clock clk hrel
              hlast hfa hfx hdd hdd2 hb hclk hclen hbal hrates (by omega) hl2) ?_
            rintro o ⟨st', out', rfl, h1, h2⟩
            exact ⟨true, st', out', rfl, prel_true h1 h2⟩
          · refine wp_mono (process_record_first_dmiss st out s r xrefs discs parms clock clk hrel
              hlast hfa hfx hdd hdd2 hl1) ?_
            rintro o ⟨st', out', rfl, h1, h2⟩
            exact ⟨false, st', out', rfl, prel_false h1 h2⟩
      · refine wp_mono (process_record_first_xmiss st out s r xrefs discs parms clock clk hrel
          hlast hfa hfx (by omega)) ?_
        rintro o ⟨st', out', rfl, h1, h2⟩
        exact ⟨false, st', out', rfl, prel_false h1 h2⟩
    · refine wp_mono (process_record_first_amiss st out s r xrefs discs parms clock clk hrel
        hlast hfa (by omega)) ?_
      rintro o ⟨st', out', rfl, h1, h2⟩
      exact ⟨false, st', out', rfl, prel_false h1 h2⟩
  · have hsome : s.lastId.isSome := by rw [hlast]; rfl
    by_cases hsame : id = r.trancat_acct_id.val
    · -- the same account as the previous record
      subst hsame
      have hgrp : Model.aGrp s.acct = st.account_record.acct_group_id.val.map ebc := by
        rw [← hrel.acct hsome, aGrp_vals]
      by_cases hdd : discs.val.findIdx (discKey st.account_record.acct_group_id r.trancat_type_cd
          r.trancat_cd) < discs.val.length
      · have hok := stepE_same_ok (xrefs.val.map CardXrefRecord.vals)
          (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk s
          (TranCatBalRecord.vals r) (by rw [hlast, tAcct_vals]) _
          (by rw [hgrp, tType_vals, tCat_vals, findRateO_eq, dite_eq_left hdd])
        refine wp_mono (process_record_same st out s r xrefs discs parms clock clk hrel hb hclk
          hclen hbal hlast hdd hrates hl1' hl2) ?_
        rintro o ⟨st', out', rfl, hr⟩
        exact ⟨true, st', out', rfl, prel_true (by rw [hok, toSt_ofSt]; exact hr) (by rw [hok]; rfl)⟩
      · by_cases hdd2 : discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd) <
            discs.val.length
        · refine wp_mono (process_record_same_dflt st out s r xrefs discs parms clock clk hrel hb
            hclk hclen hbal hlast hdd hdd2 hrates (by omega) hl2) ?_
          rintro o ⟨st', out', rfl, h1, h2⟩
          exact ⟨true, st', out', rfl, prel_true h1 h2⟩
        · refine wp_mono (process_record_same_dmiss st out s r xrefs discs parms clock clk hrel
            hlast hdd hdd2 hl1) ?_
          rintro o ⟨st', out', rfl, h1, h2⟩
          exact ⟨false, st', out', rfl, prel_false h1 h2⟩
    · -- a new account: the previous one is rewritten
      obtain ⟨a0, ha0, he0⟩ := hm hsome
      have hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
          st.accounts.val.length := by
        rw [List.findIdx_lt_length]
        have : a0 ∈ st.accounts.val.map AccountRecord.vals := by rw [hrel.accts]; exact ha0
        obtain ⟨b, hb', rfl⟩ := List.mem_map.1 this
        refine ⟨b, hb', ?_⟩
        rw [aId_vals, ← hrel.acct hsome, aId_vals] at he0
        simp [he0]
      have hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
          st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807 := by
        have h1 := hb.acct
        rw [← hrel.acct hsome, aBal_vals] at h1
        have h2 := hb.total
        rw [← hrel.total] at h2
        omega
      have haccts := acctsAfter_vals st out s hrel hsome hf0
      by_cases hfa : (acctsAfter st).findIdx (fun a => a.acct_id.val == r.trancat_acct_id.val) <
          (acctsAfter st).length
      · by_cases hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
            xrefs.val.length
        · by_cases hdd : discs.val.findIdx (discKey ((acctsAfter st)[(acctsAfter st).findIdx
              (fun a => a.acct_id.val == r.trancat_acct_id.val)]).acct_group_id r.trancat_type_cd
              r.trancat_cd) < discs.val.length
          · have hok := stepE_change_ok (xrefs.val.map CardXrefRecord.vals)
              (discs.val.map DisGroupRecord.vals) (Model.parmOf (ExternalParms.vals parms)) clk s
              (TranCatBalRecord.vals r) id hlast (by rw [tAcct_vals]; exact hsame) _ _
              (by rw [← haccts, tAcct_vals, findAcctO_eq, dite_eq_left hfa])
              (by rw [tAcct_vals, findXrefO_eq, dite_eq_left hfx]) _
              (by rw [aGrp_vals, tType_vals, tCat_vals, findRateO_eq, dite_eq_left hdd])
            refine wp_mono (process_record_change st out s r xrefs discs parms clock clk hrel hb hclk
              hclen hbal id hlast hsame hf0 hbt hfa hfx hdd hrates hl1' hl2 hl3) ?_
            rintro o ⟨st', out', rfl, hr⟩
            exact ⟨true, st', out', rfl,
              prel_true (by rw [hok, toSt_ofSt]; exact hr) (by rw [hok]; rfl)⟩
          · by_cases hdd2 : discs.val.findIdx (discKey defR r.trancat_type_cd r.trancat_cd) <
                discs.val.length
            · refine wp_mono (process_record_change_dflt st out s r xrefs discs parms clock clk hrel
                id hlast hsame hf0 hbt hl3 hfa hfx hdd hdd2 hb hclk hclen hbal hrates (by omega)
                hl2) ?_
              rintro o ⟨st', out', rfl, h1, h2⟩
              exact ⟨true, st', out', rfl, prel_true h1 h2⟩
            · refine wp_mono (process_record_change_dmiss st out s r xrefs discs parms clock clk hrel
                id hlast hsame hf0 hbt hl3 hfa hfx hdd hdd2 hl1) ?_
              rintro o ⟨st', out', rfl, h1, h2⟩
              exact ⟨false, st', out', rfl, prel_false h1 h2⟩
        · refine wp_mono (process_record_change_xmiss st out s r xrefs discs parms clock clk hrel
            id hlast hsame hf0 hbt hl3 hfa hfx (by omega)) ?_
          rintro o ⟨st', out', rfl, h1, h2⟩
          exact ⟨false, st', out', rfl, prel_false h1 h2⟩
      · refine wp_mono (process_record_change_amiss st out s r xrefs discs parms clock clk hrel
          id hlast hsame hf0 hbt hl3 hfa (by omega)) ?_
        rintro o ⟨st', out', rfl, h1, h2⟩
        exact ⟨false, st', out', rfl, prel_false h1 h2⟩

end EquivLean.Modernize.Cbact04c.Rust
