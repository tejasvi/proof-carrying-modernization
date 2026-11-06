import EquivLean.Modernize.Cbact04c.Every.RustRun4
/-!
# CBACT04C → Rust on every input: the read loop and the equation of `run` (`RunSpecE`)
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-- The equation of `run` on every input: `cbact04c_t.run` returns (never panics) the outputs of
`Model.runE` (the lines displayed, the transactions written, the accounts rewritten, whether the
run abended). -/
def RunSpecE : Prop :=
  ∀ (s1 : Slice cbact04c_t.TranCatBalRecord) (s2 : Slice cbact04c_t.CardXrefRecord)
    (s3 : Slice cbact04c_t.AccountRecord) (s4 : Slice cbact04c_t.DisGroupRecord)
    (q1 : cbact04c_t.ExternalParms) (rclk : Std.Array Std.U8 21#usize)
    (vals1 vals2 vals3 vals4 : List (List FVal)) (link1 : List FVal) (clk : List UInt8),
    s1.val.map TranCatBalRecord.vals = vals1 → s2.val.map CardXrefRecord.vals = vals2 →
    s3.val.map AccountRecord.vals = vals3 → s4.val.map DisGroupRecord.vals = vals4 →
    ExternalParms.vals q1 = link1 → rclk.val.map (·.val) = rustLine clk → clk.length = 21 →
    (∀ v ∈ vals1, TranCatBalRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
    (∀ v ∈ vals3, AccountRecord.Valid v) → (∀ v ∈ vals4, DisGroupRecord.Valid v) →
    ExternalParms.Valid link1 →
    vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
    let o := Model.runE vals1 vals2 vals3 vals4 (Model.parmOf link1) clk
    ∃ out, cbact04c_t.run s1 s2 s3 s4 q1 rclk = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.transact_file_writes.val.map TranRecord.vals = o.writes ∧
      out.account_file_rewrites.val.map AccountRecord.vals = o.rewrites ∧
      out.abended = o.abended

/-! ## The model's run -/

/-- The every-input model after the first `k` category records. -/
def foldE (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal)) (k : Nat) :
    Model.StE :=
  (tcat.take k).foldl (Model.stepE xr dv p c) (Model.initE accts0)

theorem initE_eq (accts0 : List (List FVal)) : Model.initE accts0 = ofSt (Model.init accts0) false :=
  rfl

theorem foldE_succ (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal))
    (k : Nat) (h : k < tcat.length) :
    foldE xr dv p c accts0 tcat (k + 1) = Model.stepE xr dv p c (foldE xr dv p c accts0 tcat k) tcat[k] := by
  simp only [foldE, take_succ_of_lt' h, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem foldl_stepE_stop (xr dv : List (List FVal)) (p c : List UInt8) :
    ∀ (l : List (List FVal)) (s : Model.StE), s.stop = true → l.foldl (Model.stepE xr dv p c) s = s
  | [], _, _ => rfl
  | t :: l, s, h => by
    rw [List.foldl_cons]
    have : Model.stepE xr dv p c s t = s := by unfold Model.stepE; rw [h]; rfl
    rw [this, foldl_stepE_stop xr dv p c l s h]

theorem foldE_after_stop (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal))
    (k : Nat) (hk : k ≤ tcat.length) (h : (foldE xr dv p c accts0 tcat k).stop = true) :
    foldE xr dv p c accts0 tcat tcat.length = foldE xr dv p c accts0 tcat k := by
  have e : tcat.take tcat.length = tcat.take k ++ (tcat.drop k) := by
    rw [List.take_length, List.take_append_drop]
  unfold foldE at h ⊢
  rw [e, List.foldl_append]
  exact foldl_stepE_stop xr dv p c _ _ h

theorem ofSt_toSt_of (s : Model.StE) (h : s.stop = false) : ofSt (toSt s) false = s := by
  cases s; simp only [ofSt, toSt] at h ⊢; rw [h]

/-! ## Lengths -/

theorem interest_lens (p c : List UInt8) (S : Model.St) (t : List FVal) (r : Int) :
    (mpostR r p c t S).disp = S.disp ∧ (mpostR r p c t S).writes.length ≤ S.writes.length + 1 ∧
      (mpostR r p c t S).rewrites = S.rewrites := by
  unfold mpostR
  split_ifs
  · exact ⟨rfl, by omega, rfl⟩
  · exact ⟨rfl, by simp, rfl⟩

theorem rate_lens (dv : List (List FVal)) (p c : List UInt8) (S : Model.St) (t : List FVal)
    (hns : ((ofSt S false).rate dv p c t).stop = false) :
    (toSt ((ofSt S false).rate dv p c t)).disp.length ≤ S.disp.length + 2 ∧
      (toSt ((ofSt S false).rate dv p c t)).writes.length ≤ S.writes.length + 1 ∧
      (toSt ((ofSt S false).rate dv p c t)).rewrites = S.rewrites := by
  cases h1 : Model.findRateO dv (Model.aGrp S.acct) (Model.tType t) (Model.tCat t) with
  | some r =>
    rw [rate_direct _ _ _ _ _ r h1, toSt_ofSt]
    obtain ⟨e1, e2, e3⟩ := interest_lens p c S t r
    exact ⟨by rw [e1]; omega, e2, e3⟩
  | none =>
    cases h2 : Model.findRateO dv Model.defaultGrp (Model.tType t) (Model.tCat t) with
    | some r =>
      rw [rate_dflt _ _ _ _ _ r h1 h2, toSt_ofSt]
      obtain ⟨e1, e2, e3⟩ := interest_lens p c { S with disp := S.disp ++ dfltLines } t r
      refine ⟨by rw [e1]; simp [dfltLines], e2, e3⟩
    | none =>
      rw [rate_dmiss _ _ _ _ _ h1 h2] at hns
      cases hns

theorem stepE_lens (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (hns : (Model.stepE xr dv p c (ofSt s false) t).stop = false) :
    (toSt (Model.stepE xr dv p c (ofSt s false) t)).disp.length ≤ s.disp.length + 3 ∧
      (toSt (Model.stepE xr dv p c (ofSt s false) t)).writes.length ≤ s.writes.length + 1 ∧
      (toSt (Model.stepE xr dv p c (ofSt s false) t)).rewrites.length ≤ s.rewrites.length + 1 := by
  by_cases h : s.lastId = some (Model.tAcct t)
  · rw [stepE_same _ _ _ _ _ _ h] at hns ⊢
    obtain ⟨e1, e2, e3⟩ := rate_lens dv p c _ t hns
    dsimp only at e1 e2 e3
    simp only [List.length_append, List.length_singleton] at e1
    refine ⟨by omega, e2, by rw [e3]; omega⟩
  · rw [stepE_new _ _ _ _ _ _ h] at hns ⊢
    have hd : (preAcct s t).disp.length = s.disp.length + 1 := by
      unfold preAcct; split_ifs <;> simp
    have hw : (preAcct s t).writes = s.writes := by unfold preAcct; split_ifs <;> rfl
    have hr : (preAcct s t).rewrites.length ≤ s.rewrites.length + 1 := by
      unfold preAcct; split_ifs <;> simp
    split at hns
    · cases hns
    · rename_i a ha
      split at hns
      · cases hns
      · rename_i x hx
        obtain ⟨e1, e2, e3⟩ := rate_lens dv p c (withAcct (preAcct s t) t a x) t hns
        have f1 : (withAcct (preAcct s t) t a x).disp = (preAcct s t).disp := rfl
        have f2 : (withAcct (preAcct s t) t a x).writes = (preAcct s t).writes := rfl
        have f3 : (withAcct (preAcct s t) t a x).rewrites = (preAcct s t).rewrites := rfl
        rw [f1] at e1
        rw [f2, hw] at e2
        rw [f3] at e3
        refine ⟨by omega, e2, by rw [e3]; exact hr⟩

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: the read loop and `run_specE : RunSpecE`
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

theorem orel_of_srel {st : cbact04c_t.State} {out : cbact04c_t.Output} {s : Model.StE}
    (h : SRel st out (toSt s)) (hs : s.stop = false) : ORel out s :=
  ⟨h.disp, h.writes, h.rewrites, by rw [h.abended, hs]⟩

set_option maxHeartbeats 4000000 in
/-- **The read loop on every input**: it ends with the outputs of the model after all records
(or after the abend). -/
theorem run_loop1_specE (tcat : Slice cbact04c_t.TranCatBalRecord)
    (xrefs : Slice cbact04c_t.CardXrefRecord) (discs : Slice cbact04c_t.DisGroupRecord)
    (parms : cbact04c_t.ExternalParms) (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (accts0 : List (List FVal)) (out0 : cbact04c_t.Output) (st0 : cbact04c_t.State)
    (hrel0 : SRel st0 out0 (Model.init accts0)) (hb0 : MBounds (Model.init accts0))
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : ∀ r ∈ tcat.val, r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hlen : tcat.val.length < 2 ^ 28) :
    wp (cbact04c_t.run_loop1 tcat xrefs discs parms clock out0 st0 false false 0#usize)
      (fun o => ∃ out b, o = .ok (out, b) ∧
        ORel out (foldE (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk accts0 (tcat.val.map TranCatBalRecord.vals)
          tcat.val.length) ∧
        (foldE (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk accts0 (tcat.val.map TranCatBalRecord.vals)
          tcat.val.length).stop = b ∧
        (b = false → out.displays.val.length ≤ 1 + 3 * tcat.val.length)) := by
  have hm := usize_max_ge
  set xv := xrefs.val.map CardXrefRecord.vals with hxv
  set dv := discs.val.map DisGroupRecord.vals with hdv
  set pm := Model.parmOf (ExternalParms.vals parms) with hpm
  set tv := tcat.val.map TranCatBalRecord.vals with htv
  have htl : tv.length = tcat.val.length := by rw [htv, List.length_map]
  simp only [cbact04c_t.run_loop1]
  refine wp_loop (loop_shape _)
    (fun x => x.2.2.2.2.val ≤ tcat.val.length ∧ (x.2.2.1 = true → x.2.2.2.2.val = tcat.val.length) ∧
      (x.2.2.2.1 = false → SRel x.2.1 x.1 (toSt (foldE xv dv pm clk accts0 tv x.2.2.2.2.val)) ∧
        (foldE xv dv pm clk accts0 tv x.2.2.2.2.val).stop = false ∧
        MInvE (toSt (foldE xv dv pm clk accts0 tv x.2.2.2.2.val)) ∧
        MBounds (toSt (foldE xv dv pm clk accts0 tv x.2.2.2.2.val)) ∧
        x.1.displays.val.length ≤ 1 + 3 * x.2.2.2.2.val ∧
        x.1.transact_file_writes.val.length ≤ x.2.2.2.2.val ∧
        x.1.account_file_rewrites.val.length ≤ x.2.2.2.2.val) ∧
      (x.2.2.2.1 = true → ORel x.1 (foldE xv dv pm clk accts0 tv x.2.2.2.2.val) ∧
        (foldE xv dv pm clk accts0 tv x.2.2.2.2.val).stop = true))
    (fun x => (tcat.val.length - x.2.2.2.2.val) + (if x.2.2.1 then 0 else 1)) ?_ _ ?_
  · simp only [Prod.forall]
    intro out st eof stop pos hinv
    obtain ⟨hpos, heof, hrun, hstp⟩ := hinv
    simp only [cbact04c_t.run_loop1.body]
    cases eof
    · simp only [Bool.false_eq_true, _root_.ite_false]
      cases stop
      · -- reading
        obtain ⟨hrel, hns, hmi, hmb, hL1, hL2, hL3⟩ := hrun rfl
        simp only [Bool.false_eq_true, _root_.ite_false]
        by_cases hlt : pos.val < tcat.val.length
        · have hov : pos.val + 1 ≤ Usize.max := by omega
          have hr := List.getElem_mem hlt
          have hs := ofSt_toSt_of _ hns
          have hfs : foldE xv dv pm clk accts0 tv (pos.val + 1) =
              Model.stepE xv dv pm clk (ofSt (toSt (foldE xv dv pm clk accts0 tv pos.val)) false)
                (TranCatBalRecord.vals tcat.val[pos.val]) := by
            rw [foldE_succ xv dv pm clk accts0 tv pos.val (by omega), hs]
            simp [htv]
          aeneas_wp [usz_lit_val]
          simp only [hlt, hov, _root_.dite_true]
          refine wp_mono (process_record_specE st out _ tcat.val[pos.val] xrefs discs parms clock clk
            hrel hmi hmb hclk hclen (hbal _ hr) hrates (by omega) (by omega) (by omega)) ?_
          rintro _ ⟨b, st', out', rfl, hp⟩
          cases b
          · obtain ⟨ho, hst⟩ := hp.2 rfl
            simp only [Aeneas.Std.uncurry_apply_pair, Bool.false_eq_true, _root_.ite_false, wp_ok,
              loopCls_cont, UScalar.ofNatCore_val_eq]
            refine ⟨⟨by omega, (fun h => by cases h), (fun h => by cases h), (fun _ => ?_)⟩, by
              first | omega | (simp only [Bool.false_eq_true, _root_.ite_false]; omega)⟩
            rw [hfs]
            exact ⟨ho, hst⟩
          · obtain ⟨hr', hst⟩ := hp.1 rfl
            rw [← hxv, ← hdv, ← hpm] at hr' hst
            have hinv' := inv_step xv dv pm clk _ (TranCatBalRecord.vals tcat.val[pos.val]) hmi hmb hst
            have hlens := stepE_lens xv dv pm clk _ (TranCatBalRecord.vals tcat.val[pos.val]) hst
            have e1 := congrArg List.length hr'.disp
            have e2 := congrArg List.length hr'.writes
            have e3 := congrArg List.length hr'.rewrites
            have f1 := congrArg List.length hrel.disp
            have f2 := congrArg List.length hrel.writes
            have f3 := congrArg List.length hrel.rewrites
            simp only [List.length_map] at e1 e2 e3 f1 f2 f3
            simp only [Aeneas.Std.uncurry_apply_pair, _root_.ite_true, wp_ok, loopCls_cont,
              UScalar.ofNatCore_val_eq]
            refine ⟨⟨by omega, (fun h => by cases h), (fun _ => ?_), (fun h => by cases h)⟩, by
              first | omega | (simp only [Bool.false_eq_true, _root_.ite_false]; omega)⟩
            rw [hfs]
            exact ⟨hr', hst, hinv'.1, hinv'.2, by omega, by omega, by omega⟩
        · aeneas_wp [usz_lit_val]
          simp only [hlt, _root_.ite_false, loopCls_cont, _root_.ite_true]
          exact ⟨⟨hpos, (fun _ => by omega), (fun _ => ⟨hrel, hns, hmi, hmb, hL1, hL2, hL3⟩),
            (fun h => by cases h)⟩, by omega⟩
      · -- stopped
        simp only [_root_.ite_true, wp_ok, loopCls_done]
        obtain ⟨ho, hst⟩ := hstp rfl
        rw [← foldE_after_stop xv dv pm clk accts0 tv pos.val (by omega) hst] at ho hst
        rw [htl] at ho hst
        exact ⟨out, true, rfl, ho, hst, fun h => by cases h⟩
    · -- end of file
      simp only [_root_.ite_true, wp_ok, loopCls_done]
      have hp := heof rfl
      cases stop
      · obtain ⟨hrel, hns, -, -, hL1, -⟩ := hrun rfl
        rw [hp, ← htl] at hrel hns
        rw [htl] at hrel hns
        exact ⟨out, false, rfl, orel_of_srel hrel hns, hns, fun _ => by omega⟩
      · obtain ⟨ho, hst⟩ := hstp rfl
        rw [hp] at ho hst
        exact ⟨out, true, rfl, ho, hst, fun h => by cases h⟩
  · have e0 : foldE xv dv pm clk accts0 tv 0 = ofSt (Model.init accts0) false := by
      simp [foldE, initE_eq]
    have f1 : out0.displays.val.length = 1 := by
      have := congrArg List.length hrel0.disp; simpa [Model.init] using this
    have f2 : out0.transact_file_writes.val.length = 0 := by
      have := congrArg List.length hrel0.writes; simpa [Model.init] using this
    have f3 : out0.account_file_rewrites.val.length = 0 := by
      have := congrArg List.length hrel0.rewrites; simpa [Model.init] using this
    simp only [UScalar.ofNatCore_val_eq, e0, toSt_ofSt, ofSt_stop]
    refine ⟨by omega, (fun h => by cases h), (fun _ => ⟨hrel0, trivial, ?_, hb0, by omega,
      by omega, by omega⟩), (fun h => by cases h)⟩
    intro h; simp [Model.init] at h

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: `run_specE : RunSpecE`
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

theorem foldE_length (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal)) :
    foldE xr dv p c accts0 tcat tcat.length = tcat.foldl (Model.stepE xr dv p c) (Model.initE accts0) := by
  simp [foldE]

set_option maxHeartbeats 2000000 in
/-- **The equation of `run` on every input** (`RunSpecE`). -/
theorem run_specE : RunSpecE := by
  intro s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1 clk h1 h2 h3 h4 hq hclk hclen hv1 hv2 hv3 hv4
    hvq hlen
  have hm := usize_max_ge
  have hl1 : s1.val.length < 2 ^ 28 := by rw [← h1, List.length_map] at hlen; omega
  have hbal : ∀ r ∈ s1.val, r.tran_cat_bal.val.natAbs < 10 ^ 11 := fun r hr =>
    tcat_bal_bound r (hv1 _ (h1 ▸ List.mem_map_of_mem hr))
  have hrates : ∀ d ∈ s4.val, d.dis_int_rate.val.natAbs < 10 ^ 6 := fun d hd =>
    disc_rate_bound d (hv4 _ (h4 ▸ List.mem_map_of_mem hd))
  have hb0 : MBounds (Model.init vals3) := by
    refine ⟨by simp [Model.init], by simp [Model.init], ?_,
      by simp [Model.init, Model.aBal, Model.numOf]; decide⟩
    intro a ha
    rw [← h3] at ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    exact acct_bal_bound r (hv3 _ (h3 ▸ List.mem_map_of_mem hr))
  simp only []
  refine exists_ok_of_wp' ?_
  simp only [cbact04c_t.run, run_loop0_eq, m_start_eq, bind_ok]
  have hnew : ∀ α, (alloc.vec.Vec.new α).val = [] := fun _ => rfl
  have h0 : (alloc.vec.Vec.new (alloc.vec.Vec U8)).val.length < Usize.max := by
    rw [hnew]; simp; omega
  simp only [wp_bind, wp_Vec_push]
  rw [dite_eq_left h0]
  refine wp_mono (run_loop1_specE s1 s2 s4 q1 rclk clk vals3 _ _ ?_ hb0 hclk hclen hbal hrates hl1) ?_
  · refine ⟨?_, by simp [hnew, Model.init], by simp [hnew, Model.init], rfl, ?_, rfl, rfl, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp [startBytes_text, Model.init]
    · simp [h3, Model.init]
    · intro id hid; simp [Model.init] at hid
    · intro h; simp [Model.init] at h
    · intro h; simp [Model.init] at h
    · simp [Model.init]
    · simp [Model.init]
    · simp
    · simp
  · rintro _ ⟨out, b, rfl, ho, hb, hd⟩
    have hf := foldE_length (s2.val.map CardXrefRecord.vals) (s4.val.map DisGroupRecord.vals)
      (Model.parmOf (ExternalParms.vals q1)) clk vals3 (s1.val.map TranCatBalRecord.vals)
    rw [List.length_map] at hf
    rw [hf, h1, h2, h4, hq] at ho hb
    cases b
    · have hd' : out.displays.val.length < Usize.max := by have := hd rfl; omega
      simp only [Aeneas.Std.uncurry_apply_pair, Bool.false_eq_true, _root_.ite_false, wp_bind,
        m_end_eq, wp_ok, wp_Vec_push]
      rw [dite_eq_left hd']
      simp only [Except.ok.injEq, exists_eq_left']
      refine ⟨?_, ho.writes, ho.rewrites, ?_⟩
      · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, ho.disp,
          endBytes_text, Model.runE, hb, Bool.false_eq_true, _root_.ite_false]
      · simp only [Model.runE]; rw [ho.abended, hb]
    · simp only [Aeneas.Std.uncurry_apply_pair, _root_.ite_true, wp_ok, Except.ok.injEq,
        exists_eq_left']
      refine ⟨?_, ho.writes, ho.rewrites, ?_⟩
      · simp only [ho.disp, Model.runE, hb, _root_.ite_true]
      · simp only [Model.runE]; rw [ho.abended, hb]

end EquivLean.Modernize.Cbact04c.Rust
