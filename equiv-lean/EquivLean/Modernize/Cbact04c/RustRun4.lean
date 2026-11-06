import EquivLean.Modernize.Cbact04c.RustRun3

/-!
# CBACT04C → Rust: `process_record` from the model's invariants and the domain

`process_record_spec` dispatches to the three cases of `RustRun3.lean`; the Rust searches succeed
because the domain's records are in the model's tables (`MInv`).  `MBounds` (running total,
suffix, account balances) holds along the run (`mbounds_step`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-- An element of the field values of a Rust list comes from an element of the list. -/
theorem exists_of_map_vals {α : Type _} (f : α → List FVal) (l : List α) (P : List FVal → Prop)
    (h : ∃ x ∈ l.map f, P x) : ∃ y ∈ l, P (f y) := by
  obtain ⟨x, hx, hp⟩ := h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact ⟨y, hy, hp⟩

/-- An id in the model's table is found by the Rust search. -/
theorem findIdx_acct_lt (l : List cbact04c_t.AccountRecord) (id : Int)
    (h : ∃ a ∈ l.map AccountRecord.vals, Model.aId a = id) :
    l.findIdx (fun a => a.acct_id.val == id) < l.length := by
  obtain ⟨y, hy, hp⟩ := exists_of_map_vals _ _ _ h
  rw [List.findIdx_lt_length]
  exact ⟨y, hy, by rw [aId_vals] at hp; simp [hp]⟩

theorem findIdx_xref_lt (l : List cbact04c_t.CardXrefRecord) (id : Int)
    (h : ∃ x ∈ l.map CardXrefRecord.vals, Model.xAcct x = id) :
    l.findIdx (fun x => x.xref_acct_id.val == id) < l.length := by
  obtain ⟨y, hy, hp⟩ := exists_of_map_vals _ _ _ h
  rw [List.findIdx_lt_length]
  exact ⟨y, hy, by rw [xAcct_vals] at hp; simp [hp]⟩

/-- The disclosure group record of the account `ar` is found by the Rust search. -/
theorem findIdx_disc_lt (l : List cbact04c_t.DisGroupRecord) (ar : cbact04c_t.AccountRecord)
    (r : cbact04c_t.TranCatBalRecord)
    (h : ∃ d ∈ l.map DisGroupRecord.vals, Model.dGrp d = Model.aGrp (AccountRecord.vals ar) ∧
      Model.dType d = Model.tType (TranCatBalRecord.vals r) ∧
      Model.dCat d = Model.tCat (TranCatBalRecord.vals r)) :
    l.findIdx (discKey ar.acct_group_id r.trancat_type_cd r.trancat_cd) < l.length := by
  obtain ⟨y, hy, h1, h2, h3⟩ := exists_of_map_vals _ _ _ h
  rw [List.findIdx_lt_length]
  refine ⟨y, hy, ?_⟩
  rw [← discKey_comp]
  simp only [Function.comp_apply, h1, h2, h3, aGrp_vals, tType_vals, tCat_vals, beq_self_eq_true,
    Bool.and_self]

/-- The model's table has the ids of the input table. -/
theorem minv_has_id (accts0 xrefs : List (List FVal)) (s : Model.St) (hm : MInv accts0 xrefs s)
    (id : Int) (h : ∃ a ∈ accts0, Model.aId a = id) : ∃ a ∈ s.accts, Model.aId a = id := by
  obtain ⟨a, ha, he⟩ := h
  have : (Model.aId a, Model.aGrp a) ∈ s.accts.map (fun a => (Model.aId a, Model.aGrp a)) := by
    rw [hm.ids]; exact List.mem_map_of_mem ha
  obtain ⟨b, hb, hbe⟩ := List.mem_map.1 this
  exact ⟨b, hb, by simp only [Prod.mk.injEq] at hbe; rw [hbe.1, he]⟩

/-- **One category record**: from the relation, the model's invariants and the domain at the
record, `process_record` returns `true` and the relation holds with the model's next state. -/
theorem process_record_spec (st : cbact04c_t.State) (out : cbact04c_t.Output) (s : Model.St)
    (r : cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (accts0 : List (List FVal))
    (hrel : SRel st out s) (hm : MInv accts0 (xrefs.val.map CardXrefRecord.vals) s) (hb : MBounds s)
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hda : ∃ a ∈ accts0, Model.aId a = Model.tAcct (TranCatBalRecord.vals r))
    (hdx : ∃ x ∈ xrefs.val.map CardXrefRecord.vals, Model.xAcct x = Model.tAcct (TranCatBalRecord.vals r))
    (hdd : ∃ d ∈ discs.val.map DisGroupRecord.vals,
      Model.dGrp d = Model.aGrp (Model.findAcct accts0 (Model.tAcct (TranCatBalRecord.vals r))) ∧
      Model.dType d = Model.tType (TranCatBalRecord.vals r) ∧
      Model.dCat d = Model.tCat (TranCatBalRecord.vals r))
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hl1 : out.displays.val.length < Usize.max) (hl2 : out.transact_file_writes.val.length < Usize.max)
    (hl3 : out.account_file_rewrites.val.length < Usize.max) :
    wp (cbact04c_t.process_record { st with tran_cat_bal_record := r } xrefs discs parms clock out)
      (fun o => ∃ st' out', o = .ok (true, st', out') ∧
        SRel st' out' (Model.step (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk s (TranCatBalRecord.vals r))) := by
  have hm' := minv_step accts0 (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
    (Model.parmOf (ExternalParms.vals parms)) clk s (TranCatBalRecord.vals r) hm hda
  have hfx : xrefs.val.findIdx (fun x => x.xref_acct_id.val == r.trancat_acct_id.val) <
      xrefs.val.length := findIdx_xref_lt _ _ (by rw [← tAcct_vals]; exact hdx)
  -- the disclosure group of a table with the input's ids and groups
  have hdisc : ∀ (l : List (List FVal)) (ar : cbact04c_t.AccountRecord),
      l.map (fun a => (Model.aId a, Model.aGrp a)) = accts0.map (fun a => (Model.aId a, Model.aGrp a)) →
      AccountRecord.vals ar = Model.findAcct l r.trancat_acct_id.val →
      discs.val.findIdx (discKey ar.acct_group_id r.trancat_type_cd r.trancat_cd) < discs.val.length := by
    intro l ar hl har
    apply findIdx_disc_lt
    rw [har, findAcct_grp _ _ _ hl, ← tAcct_vals]
    exact hdd
  rcases hlast : s.lastId with _ | id
  · -- the first record
    have hex := minv_has_id _ _ s hm _ hda
    rw [← hrel.accts, tAcct_vals] at hex
    have hfa := findIdx_acct_lt _ _ hex
    refine process_record_first st out s r xrefs discs parms clock clk hrel hb hclk hclen hbal hlast hfa
      hfx (hdisc s.accts _ hm.ids ?_) hrates hl1 hl2
    rw [← hrel.accts, findAcct_eq _ _ hfa]
  · by_cases hsame : id = r.trancat_acct_id.val
    · -- the same account as the previous record
      subst hsame
      have hsome : s.lastId.isSome := by rw [hlast]; rfl
      refine process_record_same st out s r xrefs discs parms clock clk hrel hb hclk hclen hbal hlast
        (hdisc s.accts _ hm.ids ?_) hrates hl1 hl2
      rw [hrel.acct hsome]
      exact (hm.cur _ hlast).1
    · -- a new account: the previous one is rewritten
      have hsome : s.lastId.isSome := by rw [hlast]; rfl
      obtain ⟨hacc, -, hex0⟩ := hm.cur _ hlast
      obtain ⟨hmem, haid⟩ := findAcct_spec _ _ hex0
      have hf0 : st.accounts.val.findIdx (fun a => a.acct_id.val == st.account_record.acct_id.val) <
          st.accounts.val.length := by
        apply findIdx_acct_lt
        rw [hrel.accts, ← aId_vals, hrel.acct hsome]
        exact ⟨s.acct, hacc ▸ hmem, rfl⟩
      have hbt : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
          st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807 := by
        have h1 := hb.bal _ (hacc ▸ hmem)
        rw [← hrel.acct hsome, aBal_vals] at h1
        have h2 := hb.total
        rw [← hrel.total] at h2
        omega
      have haccts := acctsAfter_vals st out s hrel hsome hf0
      have hstep : (Model.step (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk s (TranCatBalRecord.vals r)).accts =
          (acctsAfter st).map AccountRecord.vals := by
        rw [step_accts, haccts, hlast]
        simp [tAcct_vals, hsame]
      have hex : ∃ a ∈ (acctsAfter st).map AccountRecord.vals, Model.aId a = r.trancat_acct_id.val := by
        rw [← hstep]
        have := (hm'.cur _ (step_lastId _ _ _ _ _ _)).2.2
        rw [tAcct_vals] at this
        exact this
      have hfa := findIdx_acct_lt _ _ hex
      refine process_record_change st out s r xrefs discs parms clock clk hrel hb hclk hclen hbal id
        hlast hsame hf0 hbt hfa hfx (hdisc ((acctsAfter st).map AccountRecord.vals) _ ?_ ?_) hrates
        hl1 hl2 hl3
      · rw [← hstep]; exact hm'.ids
      · rw [findAcct_eq _ _ hfa]

/-! ## Bounds and lengths along the model's run -/

theorem mem_replaceFirst {α : Type _} (p : α → Bool) (y : α) :
    ∀ (l : List α) (a : α), a ∈ Model.replaceFirst p y l → a ∈ l ∨ a = y
  | [], a, h => by simp [Model.replaceFirst] at h
  | b :: l, a, h => by
    simp only [Model.replaceFirst] at h
    split_ifs at h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self ..)
      · rcases mem_replaceFirst p y l a h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem posted_aBal_bound (a : List FVal) (t : Int) (ha : (Model.aBal a).natAbs < 10 ^ 12) :
    (Model.aBal (Model.posted a t)).natAbs < 10 ^ 12 := by
  by_cases h : 2 < a.length
  · have e : Model.aBal (Model.posted a t) = Int.tmod (Model.aBal a + t) (10 ^ 12) := by
      simp only [Model.aBal, Model.posted, List.getD_eq_getElem?_getD, List.getElem?_set]
      simp [h, Model.numOf]
    rw [e, Int.natAbs_tmod]
    exact Nat.mod_lt _ (by norm_num)
  · have e : Model.aBal (Model.posted a t) = Model.aBal a := by
      simp only [Model.aBal, Model.posted, List.getD_eq_getElem?_getD, List.getElem?_set]
      simp [h]
    rw [e]; exact ha

theorem findAcct_bal_bound (l : List (List FVal)) (id : Int)
    (h : ∀ a ∈ l, (Model.aBal a).natAbs < 10 ^ 12) :
    (Model.aBal (Model.findAcct l id)).natAbs < 10 ^ 12 := by
  unfold Model.findAcct
  cases hf : l.find? (fun a => Model.aId a == id) with
  | none => simp [Model.aBal, Model.numOf]; decide
  | some a => exact h a (List.mem_of_find?_eq_some hf)

theorem mbounds_step (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (hb : MBounds s) : MBounds (Model.step xr dv p c s t) := by
  have hbal : ∀ a ∈ (Model.step xr dv p c s t).accts, (Model.aBal a).natAbs < 10 ^ 12 := by
    intro a ha
    rw [step_accts] at ha
    split_ifs at ha
    · exact hb.bal a ha
    · rcases mem_replaceFirst _ _ _ _ ha with h | h
      · exact hb.bal a h
      · rw [h]; exact posted_aBal_bound _ _ hb.acct
    · exact hb.bal a ha
  refine ⟨?_, ?_, hbal, ?_⟩
  · dsimp only [Model.step]
    split_ifs <;> first | exact hb.total | exact tmod11_bound _ | simp
  · dsimp only [Model.step]
    split_ifs <;> first | exact hb.k | exact Nat.mod_lt _ (by norm_num)
  · rw [step_acct]
    split_ifs
    · exact hb.acct
    · exact findAcct_bal_bound _ _ hbal

theorem step_disp_length (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr dv p c s t).disp.length = s.disp.length + 1 := by
  dsimp only [Model.step]
  split_ifs <;> simp

theorem step_writes_length (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal) :
    (Model.step xr dv p c s t).writes.length ≤ s.writes.length + 1 := by
  dsimp only [Model.step]
  split_ifs <;> simp

theorem step_rewrites_length (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St)
    (t : List FVal) : (Model.step xr dv p c s t).rewrites.length ≤ s.rewrites.length + 1 := by
  dsimp only [Model.step]
  split_ifs <;> simp

end EquivLean.Modernize.Cbact04c.Rust
