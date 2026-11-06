import EquivLean.Modernize.Cbtrn02c.RustRun6
import EquivLean.Modernize.Cbtrn02c.RustProof
/-!
# CBTRN02C → Rust: the main loop and `run_spec : RunSpec`
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

theorem exists_ok_of_wp {α : Type _} {c : Result α} {P : α → Prop}
    (h : wp c (fun o => ∃ a, o = .ok a ∧ P a)) : ∃ a, c = .ok a ∧ P a := by
  rcases (wp_iff _ _).1 h with ⟨s, hs, hq⟩ | ⟨e, he, hq⟩
  · obtain ⟨b, hb, hp⟩ := hq
    have e : s = b := by injection hb
    subst e
    exact ⟨s, hs, hp⟩
  · obtain ⟨b, hb, -⟩ := hq
    cases hb

/-- The outputs of `Model.run`. -/
def Final (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8) (out : cbtrn02c.Output) :
    Prop :=
  out.displays.val.map (fun l => l.val.map (·.val)) = (Model.run vals1 vals2 vals3 vals4 clk).disp ∧
    out.transact_file_writes.val.map TranRecord.vals = (Model.run vals1 vals2 vals3 vals4 clk).tranW ∧
    out.dalyrejs_file_writes.val.map RejectRecord.vals = (Model.run vals1 vals2 vals3 vals4 clk).rejW ∧
    out.account_file_rewrites.val.map AccountRecord.vals =
      (Model.run vals1 vals2 vals3 vals4 clk).acctRW ∧
    out.tcatbal_file_writes.val.map TranCatBalRecord.vals = (Model.run vals1 vals2 vals3 vals4 clk).catW ∧
    out.tcatbal_file_rewrites.val.map TranCatBalRecord.vals =
      (Model.run vals1 vals2 vals3 vals4 clk).catRW ∧
    out.return_code.val = (Model.run vals1 vals2 vals3 vals4 clk).rc ∧ out.abended = false

set_option maxHeartbeats 1000000 in
/-- One iteration of the main loop, against the invariant and the variant. -/
theorem loop_step (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
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
    (tr : cbtrn02c.TranRecord) (pos : Usize) (eof : Bool) (tx rej : I64)
    (hst : LInv file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 v v1 v2 v3 v4 v5 accounts
      tcatbals tcr tr pos eof tx rej) :
    wp (cbtrn02c.run_loop2.body file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr
        pos eof tx rej)
      (fun r => match loopCls r with
        | .inl o => (∃ out, o = .ok out ∧ Final (file.val.map DalytranRecord.vals)
            (xrefs.val.map CardXrefRecord.vals) accts0 cats0 clk out)
        | .inr s' => LInvT file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 s' ∧
            VarT file s' < VarT file (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr,
              pos, eof, tx, rej)) := by
  cases eof
  · have hV : VarT file (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos, false,
        tx, rej) = file.val.length - pos.val + 1 := by
      simp only [VarT, Bool.false_eq_true, _root_.ite_false]
    rw [hV]
    by_cases hlt : pos.val < file.val.length
    · refine wp_mono (body_next file xrefs clock clk hclk hclen accts0 cats0 hv1 hnd hsz v v1 v2 v3 v4
        v5 accounts tcatbals dr cxr ar tcr tr pos tx rej hst hlt) ?_
      rintro r ⟨st', rfl, hinv', hvar⟩
      simp only [loopCls_cont]
      exact ⟨hinv', hvar⟩
    · refine wp_mono (body_end file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr pos
        tx rej hlt) ?_
      rintro r rfl
      simp only [loopCls_cont]
      obtain ⟨h1, -, h3, h4, h5, h6⟩ := hst
      refine ⟨⟨h1, fun _ => by omega, h3, h4, h5, h6⟩, ?_⟩
      simp only [VarT, _root_.ite_true]
      omega
  · obtain ⟨h1, h2, h3, hrel, -, -⟩ := hst
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
    have hall : foldAt (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0
        (file.val.map DalytranRecord.vals) pos.val =
        (file.val.map DalytranRecord.vals).foldl (Model.step (xrefs.val.map CardXrefRecord.vals) clk)
          (Model.init accts0 cats0) := by
      rw [foldAt, hpos, List.take_of_length_le (by simp)]
    rw [hall] at hrel
    have hrj := hrel.rej
    simp only [Final, Model.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hab⟩
    · rw [hdisp, hrel.disp, List.length_map]
      have e1 : tx.val.natAbs = file.val.length := by omega
      have e2 : rej.val.natAbs = ((file.val.map DalytranRecord.vals).foldl
          (Model.step (xrefs.val.map CardXrefRecord.vals) clk) (Model.init accts0 cats0)).rejects := by
        omega
      rw [e1, e2]
    · rw [h1', hrel.tranW]
    · rw [h2', hrel.rejW]
    · rw [h3', hrel.acctRW]
    · rw [h4', hrel.catW]
    · rw [h5', hrel.catRW]
    · rw [hrc, hrj]
      simp

/-- **The main loop**: from the invariant, `run_loop2` returns `Model.run`'s outputs. -/
theorem loop_spec (file : Slice cbtrn02c.DalytranRecord) (xrefs : Slice cbtrn02c.CardXrefRecord)
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
    (tr : cbtrn02c.TranRecord) (pos : Usize) (eof : Bool) (tx rej : I64)
    (h0 : LInv file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0 v v1 v2 v3 v4 v5 accounts
      tcatbals tcr tr pos eof tx rej) :
    wp (cbtrn02c.run_loop2 file xrefs clock v v1 v2 v3 v4 v5 accounts tcatbals dr cxr ar tcr tr pos eof
        tx rej)
      (fun o => ∃ out, o = .ok out ∧ Final (file.val.map DalytranRecord.vals)
        (xrefs.val.map CardXrefRecord.vals) accts0 cats0 clk out) := by
  simp only [cbtrn02c.run_loop2]
  refine wp_loop (loop_shape _) (LInvT file (xrefs.val.map CardXrefRecord.vals) clk accts0 cats0)
    (VarT file) ?_ (v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos, eof, tx, rej) h0
  rintro ⟨v, v1, v2, v3, v4, v5, accounts, tcatbals, dr, cxr, ar, tcr, tr, pos, eof, tx, rej⟩ hst
  refine wp_mono (loop_step file xrefs clock clk hclk hclen accts0 cats0 hv1 hnd hsz v v1 v2 v3 v4 v5
    accounts tcatbals dr cxr ar tcr tr pos eof tx rej hst) ?_
  intro r hr
  rcases r with e | c
  · simp only [loopCls_error] at hr ⊢; exact hr
  · rcases c with s' | o
    · simp only [loopCls_cont] at hr ⊢; exact hr
    · simp only [loopCls_done] at hr ⊢; exact hr

/-- `START OF EXECUTION OF PROGRAM CBTRN02C` (Latin-1). -/
def startR : List U8 := [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8,
  88#u8, 69#u8, 67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8,
  79#u8, 71#u8, 82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 84#u8, 82#u8, 78#u8, 48#u8, 50#u8, 67#u8]

theorem startR_text : startR.map UScalar.val = Model.txt "START OF EXECUTION OF PROGRAM CBTRN02C" := by
  decide

theorem sp22_ebc : (List.replicate 22 32#u8).map ebc = Model.sp 22 := by
  have h32 : ebc 32#u8 = 64 := by decide +kernel
  rw [List.map_replicate, h32]; rfl

set_option maxHeartbeats 2000000 in
/-- **CBTRN02C, Rust side**: `cbtrn02c.run` returns `Model.run`'s outputs (the equation of `run`). -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 rclk vals1 vals2 vals3 vals4 clk hs1 hs2 hs3 hs4 hclk hcd hv1 hv2 hv3 hv4 hdom hsz
  subst hs1 hs2 hs3 hs4
  apply exists_ok_of_wp
  have hm := usize_max_ge
  have hclen : clk.length = 21 := hcd.1
  simp only [cbtrn02c.run, cbtrn02c.blank_dalytran, cbtrn02c.blank_xref, cbtrn02c.blank_account,
    cbtrn02c.blank_tcatbal, cbtrn02c.blank_tran]
  awp [run_loop0_eq, run_loop1_eq, lit_eq]
  simp (disch := omega) only [List.length_nil, dite_eq_left]
  refine loop_spec s1 s2 rclk clk hclk hclen (s3.val.map AccountRecord.vals)
    (s4.val.map TranCatBalRecord.vals) (fun d hd => hv1 _ (List.mem_map_of_mem hd))
    (by unfold Domain at hdom; simpa [List.map_map] using hdom.1)
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
  · intro t ht
    simp at ht

/-- **CBTRN02C → Rust, every input in the domain**: the generated statement (`RustStatement.lean`). -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbtrn02c.Rust

#print axioms EquivLean.Modernize.Cbtrn02c.Rust.rust
