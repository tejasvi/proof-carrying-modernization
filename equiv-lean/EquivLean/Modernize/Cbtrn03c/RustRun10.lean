import EquivLean.Modernize.Cbtrn03c.RustRun9

/-!
# CBTRN03C → Rust, part 10: the read loop

`run_loop0_spec`: the read loop returns the outputs of the model (`loopInv`, by `wp_loop`); each
iteration is one of the paths of parts 7, 8 and 9, by the outcome of the date test and of the
lookups.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-- From `stepPost` to the postcondition of `wp_loop`'s step (the same `match`, another
matcher). -/
macro "post_of_step" : tactic =>
  `(tactic| (
    intro o h
    unfold stepPost at h
    revert h
    generalize loopCls o = cl
    cases cl <;> exact id))

set_option maxHeartbeats 20000000 in
/-- **The read loop.** -/
theorem run_loop0_spec (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hv1 : ∀ t ∈ s1.val, Model.TranRecord.Valid (TranRecord.vals t))
    (hv2 : ∀ x ∈ s2.val, Model.CardXrefRecord.Valid (CardXrefRecord.vals x))
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (eof : Bool)
    (idx : Usize)
    (hinv : loopInv s1.val (s2.val.map CardXrefRecord.vals) (s3.val.map TranTypeRecord.vals)
      (s4.val.map TranCatRecord.vals) (WsDateparmRecord.vals ⟨ds, df, de⟩) R
      (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10, xref, ttype, tcat, first, card,
        eof, idx)) :
    wp (cbtrn03c.run_loop0 s1 s2 s3 s4 st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10 xref ttype tcat
      ds df de first card eof idx) (OutQ R) := by
  unfold cbtrn03c.run_loop0
  refine wp_loop (loop_shape _) (loopInv s1.val (s2.val.map CardXrefRecord.vals)
    (s3.val.map TranTypeRecord.vals) (s4.val.map TranCatRecord.vals)
    (WsDateparmRecord.vals ⟨ds, df, de⟩) R) (loopVar s1.val.length) ?_ _ hinv
  rintro ⟨st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10, xref, ttype, tcat, first, card,
    eof, idx⟩ hinv
  simp only [loopInv] at hinv
  obtain ⟨s, hc, hb, hf, hcard, hx, hxa, hidx, hwl, hdl, hamt0, hcat0, hmer0, hrest⟩ := hinv
  rcases hrest with ⟨rfl, hR⟩ | ⟨rfl, hR⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hwl hdl
    by_cases hp : idx.val < s1.val.length
    · obtain ⟨t, ht⟩ : ∃ t, s1.val[idx.val]'hp = t := ⟨_, rfl⟩
      have htm : t ∈ s1.val := ht ▸ List.getElem_mem hp
      obtain ⟨hc0, -, hamt, hm0, -⟩ := tran_ranges t (hv1 t htm)
      rw [drop_map_cons _ _ _ hp, ht] at hR
      cases hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t)
      · rw [rest_cons_out _ _ _ _ _ _ _ _ hin] at hR
        refine wp_mono (step_out s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
          xref ttype tcat first card idx s hc hp t ht (by omega) hin hR) ?_
        post_of_step
      · rw [rest_cons_in _ _ _ _ _ _ _ _ hin] at hR
        -- the lookups on field values, from the searches on the structs
        have hyM : ∀ o, s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = o →
            (s3.val.map TranTypeRecord.vals).find?
              (fun y => Model.yType y == Model.tType (TranRecord.vals t)) =
              o.map TranTypeRecord.vals := by
          intro o ho
          rw [tType_vals, find_ttype, ho]
        have hcM : ∀ o, s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
              decide (c.tran_cat_cd = t.tran_cat_cd)) = o →
            (s4.val.map TranCatRecord.vals).find?
              (fun c => Model.cType c == Model.tType (TranRecord.vals t) &&
                Model.cCat c == Model.tCat (TranRecord.vals t)) = o.map TranCatRecord.vals := by
          intro o ho
          rw [tType_vals, tCat_vals, find_tcat, ho]
        have hxM : ∀ o, s2.val.find? (fun x => decide (x.xref_card_num.val = t.tran_card_num.val)) =
              o →
            (s2.val.map CardXrefRecord.vals).find?
              (fun x => Model.xCard x == Model.tCard (TranRecord.vals t)) =
              o.map CardXrefRecord.vals := by
          intro o ho
          rw [tCard_vals, find_xref, ho]
        by_cases hsame : card.val = t.tran_card_num.val
        · have hcs := cardStep_same (s2.val.map CardXrefRecord.vals) s
            (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t)
            (by rw [hcard, tCard_vals, hsame])
          rcases hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) with
            _ | y
          · rw [tranStep_noty _ _ _ _ _ _ _ hcs (hyM none hy)] at hR
            refine wp_mono (step_same_noty s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
              xref ttype tcat first card idx s hc hp t ht hc0 hamt hm0 (by omega) hin hsame hy
              hR) ?_
            post_of_step
          rcases hcz : s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
              decide (c.tran_cat_cd = t.tran_cat_cd)) with _ | c
          · rw [tranStep_nocat _ _ _ _ _ _ _ _ hcs (hyM _ hy) (hcM none hcz)] at hR
            refine wp_mono (step_same_nocat s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
              xref ttype tcat first card idx s hc hp t ht hc0 hamt hm0 (by omega) hin hsame y hy
              hcz hR) ?_
            post_of_step
          rw [tranStep_found _ _ _ _ _ _ _ _ _ hcs (hyM _ hy) (hcM _ hcz)] at hR
          refine wp_mono (step_same s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
            xref ttype tcat first card idx s hc hb hf hcard hx hxa hp t ht hc0 hamt hm0
            (by omega) (by omega) hin hsame y hy c hcz hR) ?_
          post_of_step
        · have hne : ¬ s.card = Model.tCard (TranRecord.vals t) := by
            rw [hcard, tCard_vals]
            intro h
            exact hsame (List.map_injective_iff.mpr (fun u w huw => ebcU_inj u w huw) h)
          rcases hxr : s2.val.find? (fun x => decide (x.xref_card_num.val = t.tran_card_num.val))
            with _ | x
          · rw [tranStep_err _ _ _ _ _ _ _ (cardStep_nox _ _ _ _ hne (hxM none hxr))] at hR
            refine wp_mono (step_new_nox s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
              xref ttype tcat first card idx s hc hb hf hp t ht hc0 hamt hm0 (by omega) (by omega)
              hin hsame hxr hR) ?_
            post_of_step
          have hxm : x ∈ s2.val := List.mem_of_find?_eq_some hxr
          have hxa' := (xref_acct_range x (hv2 x hxm)).1
          have hcs := cardStep_new (s2.val.map CardXrefRecord.vals) s
            (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t)
            (CardXrefRecord.vals x) hne (hxM _ hxr)
          rcases hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) with
            _ | y
          · rw [tranStep_noty _ _ _ _ _ _ _ hcs (hyM none hy)] at hR
            refine wp_mono (step_new_noty s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
              xref ttype tcat first card idx s hc hb hf hp t ht hc0 hamt hm0 (by omega) (by omega)
              hin hsame x hxr hy hR) ?_
            post_of_step
          rcases hcz : s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
              decide (c.tran_cat_cd = t.tran_cat_cd)) with _ | c
          · rw [tranStep_nocat _ _ _ _ _ _ _ _ hcs (hyM _ hy) (hcM none hcz)] at hR
            refine wp_mono (step_new_nocat s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
              xref ttype tcat first card idx s hc hb hf hp t ht hc0 hamt hm0 (by omega) (by omega)
              hin hsame x hxr y hy hcz hR) ?_
            post_of_step
          rw [tranStep_found _ _ _ _ _ _ _ _ _ hcs (hyM _ hy) (hcM _ hcz)] at hR
          refine wp_mono (step_new s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
            xref ttype tcat first card idx s hc hb hf hp t ht hc0 hamt hm0 (by omega) (by omega)
            hin hsame x hxr (by omega) y hy c hcz hR) ?_
          post_of_step
    · have hdrop : (s1.val.map TranRecord.vals).drop idx.val = [] :=
        List.drop_eq_nil_of_le (by simp only [List.length_map]; omega)
      rw [hdrop, rest_nil] at hR
      cases hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩)
          (TranRecord.vals ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩)
      · rw [hin] at hR
        refine wp_mono (step_end_out s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
          xref ttype tcat first card idx s hc hp (by omega) hidx hin hR) ?_
        post_of_step
      · rw [hin] at hR
        refine wp_mono (step_end_in s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
          xref ttype tcat first card idx s hc hb hf hcard hx hxa hp hidx hwl hdl hamt0 hcat0 hmer0
          hin hR) ?_
        post_of_step
  · simp only [↓reduceIte, eq_self_iff_true] at hwl hdl
    refine wp_mono (step_eof s1 s2 s3 s4 ds df de R hL st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10 xref
      ttype tcat first card idx s hc hidx hdl hR) ?_
    post_of_step

end EquivLean.Modernize.Cbtrn03c.Rust
