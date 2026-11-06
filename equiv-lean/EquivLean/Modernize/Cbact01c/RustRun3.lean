import EquivLean.Modernize.Cbact01c.RustRun2

/-!
# CBACT01C → Rust: `run`'s read loop, hence `run` in bytes

The loop is ended by the end-of-file flag (`while !end_of_file`, with `idx`).  Its state has 18
variables; `Inv` speaks of the ones the outputs depend on: the records read so far (`take idx`)
have been output (`rfold`), the cycle debit is the last copy's, bytes 30-31 of the conversion
area are spaces, and the flag is set only at the end.  `run_loop_step` (one record) is the
symbolic execution of the body in pieces (`chunkA1` … `chunkE`, `codate_bind`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec
open Aeneas.Std.Result ControlFlow Error

namespace EquivLean.Modernize.Cbact01c.Rust
open cbact01c

def LSt.disp (s : LSt) := s.1
def LSt.outs (s : LSt) := s.2.1
def LSt.arrs (s : LSt) := s.2.2.1
def LSt.vbrcs (s : LSt) := s.2.2.2.1
def LSt.cd (s : LSt) := s.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def LSt.codatecn (s : LSt) := s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def LSt.eof (s : LSt) := s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def LSt.idx (s : LSt) := s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The invariant of `run`'s loop: the records read so far (`take idx`) have been output; the
flag is set only at the end; the two bytes after the converted date are spaces. -/
def Inv (accts : List AccountRecord) (s : LSt) : Prop :=
  s.idx.val ≤ accts.length ∧ (s.eof = true → s.idx.val = accts.length) ∧
  s.disp.val.map (·.val) = (rfold (accts.take s.idx.val)).disp ∧
  s.outs.val = (rfold (accts.take s.idx.val)).outs ∧
  s.arrs.val = (rfold (accts.take s.idx.val)).arrs ∧
  s.vbrcs.val.map (·.val) = (rfold (accts.take s.idx.val)).vbrcs ∧
  s.cd = (rfold (accts.take s.idx.val)).cd ∧
  (s.codatecn.val.drop 30).take 2 = [32#u8, 32#u8]

theorem codateNext_drop30 (c d : List U8) (hd : d.length = 10) :
    (codateNext c d).drop 30 = c.drop 30 := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, rfl⟩ := list10 d hd
  simp [codateNext, picks]

/-- The variant of `run`'s loop. -/
def Var (accts : List AccountRecord) (s : LSt) : Nat :=
  accts.length - s.idx.val + (if s.eof then 0 else 1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- One record of `run`'s loop. -/
theorem run_loop_step (accts : Slice AccountRecord) (hU : 4294967295 ≤ Usize.max)
    (hlen : 15 * accts.val.length + 2 < Usize.max)
    (d : alloc.vec.Vec (alloc.vec.Vec U8)) (o : alloc.vec.Vec OutAcctRec)
    (ar : alloc.vec.Vec ArrArrayRec) (vb : alloc.vec.Vec (alloc.vec.Vec U8)) (x4 : I64)
    (x5 : Array U8 1#usize) (x6 x7 x8 : I64) (x9 x10 x11 : Array U8 10#usize) (x12 cd : I64)
    (x14 : Array U8 10#usize) (cod : Array U8 80#usize) (idx : Usize)
    (hs : Inv accts.val (d, o, ar, vb, x4, x5, x6, x7, x8, x9, x10, x11, x12, cd, x14, cod, false, idx))
    (hlt : idx.val < accts.val.length)
    (Q : Except Error (alloc.vec.Vec (alloc.vec.Vec U8) × alloc.vec.Vec OutAcctRec ×
      alloc.vec.Vec ArrArrayRec × alloc.vec.Vec (alloc.vec.Vec U8)) → Prop) :
    wp (run_loop.body accts d o ar vb x4 x5 x6 x7 x8 x9 x10 x11 x12 cd x14 cod false idx)
      (fun r => match loopCls r with
        | .inl o => Q o
        | .inr s' => Inv accts.val s' ∧
            Var accts.val s' < Var accts.val (d, o, ar, vb, x4, x5, x6, x7, x8, x9, x10, x11, x12,
              cd, x14, cod, false, idx)) := by
  simp only [Inv, LSt.disp, LSt.outs, LSt.arrs, LSt.vbrcs, LSt.cd, LSt.codatecn, LSt.eof,
    LSt.idx] at hs
  obtain ⟨hidx, -, hdisp, houts, harrs, hvbrcs, hcd, hcod⟩ := hs
  have hl := rfold_lengths (accts.val.take idx.val)
  have hdl : d.val.length = 1 + 15 * idx.val := by
    rw [← List.length_map (f := fun x : alloc.vec.Vec U8 => x.val), hdisp, hl.1, List.length_take]
    omega
  have hvl : vb.val.length = 2 * idx.val := by
    rw [← List.length_map (f := fun x : alloc.vec.Vec U8 => x.val), hvbrcs, hl.2.2.2,
      List.length_take]
    omega
  have hol : o.val.length = idx.val := by rw [houts, hl.2.1, List.length_take]; omega
  have hal : ar.val.length = idx.val := by rw [harrs, hl.2.2.1, List.length_take]; omega
  unfold run_loop.body
  simp only [Bool.false_eq_true, _root_.ite_false]
  have hc : idx < Slice.len accts := by rw [UScalar.lt_equiv, Slice.len_val]; exact hlt
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc), wp_bind, wp_Slice_index_usize,
    dite_eq_left_of_eq_true (eq_true hlt)]
  dsimp only
  rw [wp_bind, wp_UScalar_add_val, dite_eq_left_of_eq_true (eq_true (by
    simp only [uscalar_ofNat_val, UScalar.max_USize_eq]; omega))]
  dsimp only
  have hlen15 : (recLines (accts.val[idx.val]'hlt)).length = 15 := by simp [recLines]
  apply chunkA1 _ _ _ _ hU (by omega)
  intro d6 hd6
  have hd6l : d6.val.length = d.val.length + 6 := by
    have := congrArg List.length hd6
    simp only [List.length_map, List.length_append, List.length_take, hlen15] at this
    omega
  apply chunkA2 _ _ _ _ hU (by omega)
  intro d12 hd12
  have hd12l : d12.val.length = d.val.length + 12 := by
    have := congrArg List.length hd12
    simp only [List.length_map, List.length_append, List.length_take, List.length_drop,
      hlen15] at this
    omega
  rw [codate_bind]
  apply chunkC _ _ _ _ _ _ _ (by omega) (by omega)
  intro o1 a1 ho1 ha1
  apply chunkD _ _ _ _ _ hU (by omega) (by omega)
  intro v1 d14 vw2 hv1 hd14 hvw2
  have hd14l : d14.val.length = d.val.length + 14 := by
    have := congrArg List.length hd14
    simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at this
    omega
  apply chunkE _ _ _ _ _ hU hv1 (by omega)
  intro d15 hd15
  rw [wp_ok]
  simp only [loopCls_cont]
  have hidx1 : (UScalar.ofNatCore (idx.val + (1#usize).val) (by scalar_tac) : Usize).val =
      idx.val + 1 := by simp [UScalar.ofNatCore_val_eq]
  have hfold : rfold (accts.val.take (idx.val + 1)) =
      rstep (rfold (accts.val.take idx.val)) (accts.val[idx.val]'hlt) := by
    rw [take_succ_of_lt hlt]
    simp only [rfold, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hreis : (accts.val[idx.val]'hlt).acct_reissue_date.val.length = 10 := by
    rw [Array.length_eq]; rfl
  refine ⟨?_, ?_⟩
  · simp only [Inv, LSt.disp, LSt.outs, LSt.arrs, LSt.vbrcs, LSt.cd, LSt.codatecn, LSt.eof,
      LSt.idx, hidx1, hfold]
    refine ⟨by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hd15, hd14, hd12, hd6, hdisp]
      simp only [rstep, recLines, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
        List.drop_zero, List.append_assoc, List.cons_append, List.nil_append]
    · rw [ho1, houts]
      simp only [rstep, outRec, hcd, hcod]
    · rw [ha1, harrs]
      simp only [rstep]
    · rw [hvw2, hvbrcs]
      simp only [rstep]
    · simp only [rstep, hcd]
    · rw [Array.from_val, codateNext_drop30 _ _ hreis, hcod]
  · simp only [Var, LSt.idx, LSt.eof, hidx1, Bool.false_eq_true, _root_.ite_false]
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`run`, in bytes.** -/
theorem run_bytes_eq (accts : Slice AccountRecord) (hU : 4294967295 ≤ Usize.max)
    (hlen : 15 * accts.val.length + 2 < Usize.max) :
    ∃ out, cbact01c.run accts = .ok out ∧
      out.displays.val.map (·.val) = (rfold accts.val).disp ++ [endLine] ∧
      out.out_file_writes.val = (rfold accts.val).outs ∧
      out.arry_file_writes.val = (rfold accts.val).arrs ∧
      out.vbrc_file_writes.val.map (·.val) = (rfold accts.val).vbrcs ∧
      out.abended = false := by
  refine exists_ok_of_wp ?_
  unfold cbact01c.run
  cwp_c01 [lit_eq, Array.make_val, Array.val_to_slice, dite_pos']
  unfold run_loop
  refine wp_loop (loop_shape _) (Inv accts.val) (Var accts.val) ?_ _ ?_
  · rintro ⟨d, o, ar, vb, x4, x5, x6, x7, x8, x9, x10, x11, x12, cd, x14, cod, eof, idx⟩ hs
    dsimp only
    cases eof with
    | true =>
      have hs' := hs
      simp only [Inv, LSt.disp, LSt.outs, LSt.arrs, LSt.vbrcs, LSt.cd, LSt.codatecn, LSt.eof,
        LSt.idx] at hs'
      obtain ⟨hidx, heof, hdisp, houts, harrs, hvbrcs, -, -⟩ := hs'
      have he : idx.val = accts.val.length := heof trivial
      rw [he, List.take_length] at hdisp houts harrs hvbrcs
      have hl := rfold_lengths accts.val
      have hdl : d.val.length = 1 + 15 * accts.val.length := by
        rw [← List.length_map (f := fun x : alloc.vec.Vec U8 => x.val), hdisp, hl.1]
      unfold run_loop.body
      simp only [_root_.ite_true, wp_ok, loopCls_done]
      cwp_c01 [lit_eq, Array.make_val, Array.val_to_slice, dite_pos', hdl]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, rfl⟩
      · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hdisp,
          endLine]
      · exact houts
      · exact harrs
      · exact hvbrcs
    | false =>
      by_cases hlt : idx.val < accts.val.length
      · refine wp_mono (run_loop_step accts hU hlen d o ar vb x4 x5 x6 x7 x8 x9 x10 x11 x12 cd x14
          cod idx hs hlt (fun _ => False)) ?_
        intro r hr
        rcases h : loopCls r with o' | s' <;> simp only [h] at hr ⊢
        exact hr
      · have hs' := hs
        simp only [Inv, LSt.disp, LSt.outs, LSt.arrs, LSt.vbrcs, LSt.cd, LSt.codatecn, LSt.eof,
          LSt.idx] at hs'
        obtain ⟨hidx, -, hdisp, houts, harrs, hvbrcs, hcd, hcod⟩ := hs'
        unfold run_loop.body
        have hc : ¬ idx < Slice.len accts := by rw [UScalar.lt_equiv, Slice.len_val]; exact hlt
        simp only [Bool.false_eq_true, _root_.ite_false, hc, wp_ok, loopCls_cont]
        refine ⟨?_, ?_⟩
        · simp only [Inv, LSt.disp, LSt.outs, LSt.arrs, LSt.vbrcs, LSt.cd, LSt.codatecn, LSt.eof,
            LSt.idx]
          exact ⟨hidx, fun _ => by omega, hdisp, houts, harrs, hvbrcs, hcd, hcod⟩
        · simp only [Var, LSt.idx, LSt.eof, _root_.ite_true, Bool.false_eq_true, _root_.ite_false]
          omega
  · simp only [Inv, LSt.disp, LSt.outs, LSt.arrs, LSt.vbrcs, LSt.cd, LSt.codatecn, LSt.eof,
      LSt.idx, uscalar_ofNat_val, List.take_zero, rfold, List.foldl_nil, rinit,
      alloc.vec.Vec.from_val, List.nil_append, List.map_cons, List.map_nil, alloc.vec.Vec.new,
      Array.repeat_val, List.drop_replicate, List.take_replicate, startLine]
    and_intros <;> (first | trivial | omega | simp)

end EquivLean.Modernize.Cbact01c.Rust
