import EquivLean.Modernize.Cbact04c.RustRun4
import EquivLean.Modernize.Cbact04c.RustProof

/-!
# CBACT04C → Rust: the equation of `run` (`run_spec : RunSpec`)

* field bounds of valid records (`valid_num_bound`): category balance, rate, account balance;
* the read loop `run_loop1` (`run_loop1_spec`): a loop ended by the end-of-file flag; invariant:
  no stop, `pos ≤ len`, end of file only at `pos = len`, and `SRel`, `MInv`, `MBounds` with the
  model's state after the first `pos` records (`foldAt`);
* `run_spec`: the account table copied, the start line, the loop, the end line; the domain gives
  the lookups' success at each record (`DomAt`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

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

theorem tcat_bal_bound (r : cbact04c_t.TranCatBalRecord)
    (hv : TranCatBalRecord.Valid (TranCatBalRecord.vals r)) : r.tran_cat_bal.val.natAbs < 10 ^ 11 := by
  simp only [Schema.Valid, TranCatBalRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩⟩
  exact valid_num_bound h3 rfl rfl

theorem disc_rate_bound (d : cbact04c_t.DisGroupRecord)
    (hv : DisGroupRecord.Valid (DisGroupRecord.vals d)) : d.dis_int_rate.val.natAbs < 10 ^ 6 := by
  simp only [Schema.Valid, DisGroupRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩⟩
  exact valid_num_bound h3 rfl rfl

theorem acct_bal_bound (a : cbact04c_t.AccountRecord)
    (hv : AccountRecord.Valid (AccountRecord.vals a)) :
    (Model.aBal (AccountRecord.vals a)).natAbs < 10 ^ 12 := by
  rw [aBal_vals]
  simp only [Schema.Valid, AccountRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩
  exact valid_num_bound h2 rfl rfl

/-! ## Lengths along the model's run -/

theorem fold_disp_length (xr dv : List (List FVal)) (p c : List UInt8) :
    ∀ (l : List (List FVal)) (s : Model.St),
      (l.foldl (Model.step xr dv p c) s).disp.length = s.disp.length + l.length
  | [], s => rfl
  | t :: l, s => by
    rw [List.foldl_cons, fold_disp_length xr dv p c l, step_disp_length, List.length_cons]; omega

theorem fold_writes_length (xr dv : List (List FVal)) (p c : List UInt8) :
    ∀ (l : List (List FVal)) (s : Model.St),
      (l.foldl (Model.step xr dv p c) s).writes.length ≤ s.writes.length + l.length
  | [], s => le_refl _
  | t :: l, s => by
    have h1 := fold_writes_length xr dv p c l (Model.step xr dv p c s t)
    have h2 := step_writes_length xr dv p c s t
    rw [List.foldl_cons, List.length_cons]; omega

theorem fold_rewrites_length (xr dv : List (List FVal)) (p c : List UInt8) :
    ∀ (l : List (List FVal)) (s : Model.St),
      (l.foldl (Model.step xr dv p c) s).rewrites.length ≤ s.rewrites.length + l.length
  | [], s => le_refl _
  | t :: l, s => by
    have h1 := fold_rewrites_length xr dv p c l (Model.step xr dv p c s t)
    have h2 := step_rewrites_length xr dv p c s t
    rw [List.foldl_cons, List.length_cons]; omega

theorem fold_minv (accts0 xr dv : List (List FVal)) (p c : List UInt8) :
    ∀ (l : List (List FVal)) (s : Model.St), (∀ t ∈ l, ∃ a ∈ accts0, Model.aId a = Model.tAcct t) →
      MInv accts0 xr s → MInv accts0 xr (l.foldl (Model.step xr dv p c) s)
  | [], s, _, h => h
  | t :: l, s, hl, h => by
    rw [List.foldl_cons]
    exact fold_minv accts0 xr dv p c l _ (fun t' ht' => hl t' (List.mem_cons_of_mem _ ht'))
      (minv_step accts0 xr dv p c s t h (hl t (List.mem_cons_self ..)))

/-! ## The read loop -/

/-- The model's state after the first `i` category records. -/
def foldAt (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal)) (i : Nat) :
    Model.St :=
  (tcat.take i).foldl (Model.step xr dv p c) (Model.init accts0)

theorem foldAt_succ (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal))
    (i : Nat) (h : i < tcat.length) :
    foldAt xr dv p c accts0 tcat (i + 1) = Model.step xr dv p c (foldAt xr dv p c accts0 tcat i) tcat[i] := by
  simp only [foldAt, take_succ_of_lt' h, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The domain at one category record (the part of `Domain` about the record). -/
def DomAt (accts0 xr dv : List (List FVal)) (t : List FVal) : Prop :=
  (∃ a ∈ accts0, Model.aId a = Model.tAcct t) ∧ (∃ x ∈ xr, Model.xAcct x = Model.tAcct t) ∧
    ∃ d ∈ dv, Model.dGrp d = Model.aGrp (Model.findAcct accts0 (Model.tAcct t)) ∧
      Model.dType d = Model.tType t ∧ Model.dCat d = Model.tCat t

theorem foldAt_lengths (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal))
    (i : Nat) :
    (foldAt xr dv p c accts0 tcat i).disp.length ≤ 1 + i ∧
      (foldAt xr dv p c accts0 tcat i).writes.length ≤ i ∧
      (foldAt xr dv p c accts0 tcat i).rewrites.length ≤ i := by
  have h1 := fold_disp_length xr dv p c (tcat.take i) (Model.init accts0)
  have h2 := fold_writes_length xr dv p c (tcat.take i) (Model.init accts0)
  have h3 := fold_rewrites_length xr dv p c (tcat.take i) (Model.init accts0)
  have h4 : (tcat.take i).length ≤ i := by simp
  simp only [foldAt, Model.init, List.length_cons, List.length_nil] at h1 h2 h3 ⊢
  omega

set_option maxHeartbeats 1000000 in
theorem run_loop1_spec (tcat : Slice cbact04c_t.TranCatBalRecord) (xrefs : Slice cbact04c_t.CardXrefRecord)
    (discs : Slice cbact04c_t.DisGroupRecord) (parms : cbact04c_t.ExternalParms)
    (clock : Std.Array U8 21#usize) (clk : List UInt8) (accts0 : List (List FVal))
    (out0 : cbact04c_t.Output) (st0 : cbact04c_t.State)
    (hrel0 : SRel st0 out0 (Model.init accts0)) (hb0 : MBounds (Model.init accts0))
    (hclk : clock.val.map (·.val) = rustLine clk) (hclen : clk.length = 21)
    (hbal : ∀ r ∈ tcat.val, r.tran_cat_bal.val.natAbs < 10 ^ 11)
    (hdom : ∀ t ∈ tcat.val.map TranCatBalRecord.vals, DomAt accts0 (xrefs.val.map CardXrefRecord.vals)
      (discs.val.map DisGroupRecord.vals) t)
    (hrates : ∀ d ∈ discs.val, d.dis_int_rate.val.natAbs < 10 ^ 6)
    (hlen : tcat.val.length < 2 ^ 28) :
    wp (cbact04c_t.run_loop1 tcat xrefs discs parms clock out0 st0 false false 0#usize)
      (fun o => ∃ out, o = .ok (out, false) ∧ ∃ st, SRel st out
        (foldAt (xrefs.val.map CardXrefRecord.vals) (discs.val.map DisGroupRecord.vals)
          (Model.parmOf (ExternalParms.vals parms)) clk accts0 (tcat.val.map TranCatBalRecord.vals)
          tcat.val.length)) := by
  have hm := usize_max_ge
  set xv := xrefs.val.map CardXrefRecord.vals with hxv
  set dv := discs.val.map DisGroupRecord.vals with hdv
  set pm := Model.parmOf (ExternalParms.vals parms) with hpm
  set tv := tcat.val.map TranCatBalRecord.vals with htv
  have htl : tv.length = tcat.val.length := by rw [htv, List.length_map]
  simp only [cbact04c_t.run_loop1]
  refine wp_loop (loop_shape _)
    (fun x => x.2.2.2.1 = false ∧ x.2.2.2.2.val ≤ tcat.val.length ∧
      (x.2.2.1 = true → x.2.2.2.2.val = tcat.val.length) ∧
      SRel x.2.1 x.1 (foldAt xv dv pm clk accts0 tv x.2.2.2.2.val) ∧
      MInv accts0 xv (foldAt xv dv pm clk accts0 tv x.2.2.2.2.val) ∧
      MBounds (foldAt xv dv pm clk accts0 tv x.2.2.2.2.val))
    (fun x => (tcat.val.length - x.2.2.2.2.val) + (if x.2.2.1 then 0 else 1)) ?_ _ ?_
  · simp only [Prod.forall]
    intro out st eof stop pos hinv
    obtain ⟨hstop, hpos, heof, hrel, hmi, hmb⟩ := hinv
    subst hstop
    simp only [cbact04c_t.run_loop1.body]
    cases eof
    · -- reading
      simp only [Bool.false_eq_true, _root_.ite_false]
      by_cases hlt : pos.val < tcat.val.length
      · have hov : pos.val + 1 ≤ Usize.max := by omega
        have hr := List.getElem_mem hlt
        obtain ⟨hda, hdx, hdd⟩ := hdom _ (List.mem_map_of_mem hr)
        obtain ⟨hL1, hL2, hL3⟩ := foldAt_lengths xv dv pm clk accts0 tv pos.val
        have hl1 : out.displays.val.length < Usize.max := by
          have := congrArg List.length hrel.disp
          rw [List.length_map] at this
          omega
        have hl2 : out.transact_file_writes.val.length < Usize.max := by
          have := congrArg List.length hrel.writes
          rw [List.length_map] at this
          omega
        have hl3 : out.account_file_rewrites.val.length < Usize.max := by
          have := congrArg List.length hrel.rewrites
          rw [List.length_map] at this
          omega
        aeneas_wp [usz_lit_val]
        simp only [hlt, hov, _root_.dite_true]
        refine wp_mono (process_record_spec st out _ tcat.val[pos.val] xrefs discs parms clock clk accts0
          hrel hmi hmb hclk hclen (hbal _ hr) hda hdx hdd hrates hl1 hl2 hl3) ?_
        rintro _ ⟨st', out', rfl, hrel'⟩
        have hfs : foldAt xv dv pm clk accts0 tv (pos.val + 1) =
            Model.step xv dv pm clk (foldAt xv dv pm clk accts0 tv pos.val)
              (TranCatBalRecord.vals tcat.val[pos.val]) := by
          rw [foldAt_succ xv dv pm clk accts0 tv pos.val (by omega)]
          simp [htv]
        simp only [Aeneas.Std.uncurry_apply_pair, _root_.ite_true, wp_ok, loopCls_cont,
          UScalar.ofNatCore_val_eq, Bool.false_eq_true, false_implies, true_and, hfs,
          _root_.ite_false]
        refine ⟨⟨by omega, hrel', ?_, ?_⟩, by omega⟩
        · exact minv_step _ _ _ _ _ _ _ hmi hda
        · exact mbounds_step _ _ _ _ _ _ hmb
      · aeneas_wp [usz_lit_val]
        simp only [hlt, _root_.ite_false, loopCls_cont, _root_.ite_true]
        exact ⟨⟨trivial, hpos, by omega, hrel, hmi, hmb⟩, by omega⟩
    · -- end of file
      simp only [_root_.ite_true, wp_ok, loopCls_done]
      refine ⟨out, rfl, st, ?_⟩
      rw [← heof rfl]
      exact hrel
  · refine ⟨rfl, by simp, by simp, ?_, ?_, ?_⟩
    · simpa [foldAt] using hrel0
    · simpa [foldAt] using minv_init accts0 xv
    · simpa [foldAt] using hb0

/-- `∃ v, c = ok v ∧ P v` from its weakest precondition. -/
theorem exists_ok_of_wp' {α : Type _} {c : Result α} {P : α → Prop}
    (h : wp c (fun o => ∃ v, o = .ok v ∧ P v)) : ∃ v, c = .ok v ∧ P v := by
  rcases (wp_iff _ _).1 h with ⟨s, hs, v, hv, hp⟩ | ⟨e, he, v, hv, hp⟩
  · cases hv; exact ⟨s, hs, hp⟩
  · cases hv

/-! ## The start and end lines -/

def startBytes : List U8 := [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8,
  88#u8, 69#u8, 67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8,
  79#u8, 71#u8, 82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8, 52#u8, 67#u8]

def endBytes : List U8 := [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8,
  67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8,
  82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8, 52#u8, 67#u8]

theorem startBytes_le : startBytes.length ≤ Usize.max := by
  have := usize_max_ge; simp [startBytes]; omega

theorem endBytes_le : endBytes.length ≤ Usize.max := by
  have := usize_max_ge; simp [endBytes]; omega

theorem m_start_eq : cbact04c_t.m_start = .ok (alloc.vec.Vec.from startBytes startBytes_le) := by
  simp only [cbact04c_t.m_start, lift, Std.Array.to_slice, bind_ok, to_vec_eq]
  rfl

theorem m_end_eq : cbact04c_t.m_end = .ok (alloc.vec.Vec.from endBytes endBytes_le) := by
  simp only [cbact04c_t.m_end, lift, Std.Array.to_slice, bind_ok, to_vec_eq]
  rfl

theorem startBytes_text : startBytes.map UScalar.val = Model.txt "START OF EXECUTION OF PROGRAM CBACT04C" := by
  decide +kernel

theorem endBytes_text : endBytes.map UScalar.val = Model.txt "END OF EXECUTION OF PROGRAM CBACT04C" := by
  decide +kernel

/-! ## `run` -/

theorem foldAt_length (xr dv : List (List FVal)) (p c : List UInt8) (accts0 tcat : List (List FVal)) :
    foldAt xr dv p c accts0 tcat tcat.length = tcat.foldl (Model.step xr dv p c) (Model.init accts0) := by
  simp [foldAt]

set_option maxHeartbeats 2000000 in
/-- **The equation of `run`** (`RunSpec`). -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1 clk h1 h2 h3 h4 hq hclk hclen hv1 hv2 hv3 hv4
    hvq hdom hlen
  obtain ⟨-, hdom⟩ := hdom
  have hm := usize_max_ge
  have hl1 : s1.val.length < 2 ^ 28 := by rw [← h1, List.length_map] at hlen; omega
  have hbal : ∀ r ∈ s1.val, r.tran_cat_bal.val.natAbs < 10 ^ 11 := fun r hr =>
    tcat_bal_bound r (hv1 _ (h1 ▸ List.mem_map_of_mem hr))
  have hrates : ∀ d ∈ s4.val, d.dis_int_rate.val.natAbs < 10 ^ 6 := fun d hd =>
    disc_rate_bound d (hv4 _ (h4 ▸ List.mem_map_of_mem hd))
  have hdom' : ∀ t ∈ s1.val.map TranCatBalRecord.vals, DomAt vals3 (s2.val.map CardXrefRecord.vals)
      (s4.val.map DisGroupRecord.vals) t := by
    rw [h1, h2, h4]; exact hdom
  have hb0 : MBounds (Model.init vals3) := by
    refine ⟨by simp [Model.init], by simp [Model.init], ?_, by simp [Model.init, Model.aBal, Model.numOf]; decide⟩
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
  refine wp_mono (run_loop1_spec s1 s2 s4 q1 rclk clk vals3 _ _ ?_ hb0 hclk hclen hbal hdom' hrates hl1) ?_
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
  · rintro _ ⟨out, rfl, st, hrel⟩
    obtain ⟨hL1, -, -⟩ := foldAt_lengths (s2.val.map CardXrefRecord.vals) (s4.val.map DisGroupRecord.vals)
      (Model.parmOf (ExternalParms.vals q1)) clk vals3 (s1.val.map TranCatBalRecord.vals) s1.val.length
    have hd : out.displays.val.length < Usize.max := by
      have := congrArg List.length hrel.disp
      rw [List.length_map] at this
      omega
    simp only [Aeneas.Std.uncurry_apply_pair, Bool.false_eq_true, _root_.ite_false, wp_bind, m_end_eq,
      wp_ok, wp_Vec_push]
    rw [dite_eq_left hd]
    simp only [Except.ok.injEq, exists_eq_left']
    have hf := foldAt_length (s2.val.map CardXrefRecord.vals) (s4.val.map DisGroupRecord.vals)
      (Model.parmOf (ExternalParms.vals q1)) clk vals3 (s1.val.map TranCatBalRecord.vals)
    rw [List.length_map] at hf
    rw [hf] at hrel
    rw [h1, h2, h4, hq] at hrel
    refine ⟨?_, hrel.writes, hrel.rewrites, hrel.abended⟩
    simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hrel.disp,
      endBytes_text, Model.run]


/-- **CBACT04C → Rust**: the generated statement. -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbact04c.Rust

#print axioms EquivLean.Modernize.Cbact04c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbact04c.Rust.rust
