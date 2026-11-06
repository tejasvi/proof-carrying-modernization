import EquivLean.Modernize.Cbtrn03c.RustRun5

/-!
# CBTRN03C → Rust, part 6: the searches

The five search loops of `run` are `List.find?` (the two category searches by hand), which
`Model`'s lookups are on field values (`find_xref`, `find_ttype`, `find_tcat`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## The searches -/

theorem run_loop0_loop0_eq (ys : Slice cbtrn03c.TranTypeRecord) (ttype : cbtrn03c.TranTypeRecord)
    (key : Array U8 2#usize) :
    cbtrn03c.run_loop0_loop0 ys ttype key 0#usize =
      .ok (match ys.val.find? (fun y => decide (y.tran_type.val = key.val)) with
        | some y => (y, true)
        | none => (ttype, false)) := by
  aeneas_spec [cbtrn03c.run_loop0_loop0] with [bytes_eq_eq, Array.val_to_slice]

theorem run_loop0_loop3_eq (ys : Slice cbtrn03c.TranTypeRecord) (ttype : cbtrn03c.TranTypeRecord)
    (key : Array U8 2#usize) :
    cbtrn03c.run_loop0_loop3 ys ttype key 0#usize =
      .ok (match ys.val.find? (fun y => decide (y.tran_type.val = key.val)) with
        | some y => (y, true)
        | none => (ttype, false)) := by
  aeneas_spec [cbtrn03c.run_loop0_loop3] with [bytes_eq_eq, Array.val_to_slice]

theorem run_loop0_loop2_eq (xs : Slice cbtrn03c.CardXrefRecord) (xref : cbtrn03c.CardXrefRecord)
    (key : Array U8 16#usize) :
    cbtrn03c.run_loop0_loop2 xs xref key 0#usize =
      .ok (match xs.val.find? (fun x => decide (x.xref_card_num.val = key.val)) with
        | some x => (x, true)
        | none => (xref, false)) := by
  aeneas_spec [cbtrn03c.run_loop0_loop2] with [bytes_eq_eq, Array.val_to_slice]

/-- A search with no match in the prefix and none at the next element. -/
theorem find?_take_succ_none {α : Type _} {l : List α} {p : α → Bool} {i : Nat}
    (hi : i < l.length) (hf : (l.take i).find? p = none) (hp : p l[i] = false) :
    (l.take (i + 1)).find? p = none := by
  rw [take_succ_of_lt hi, List.find?_append, hf]
  simp [hp]

set_option maxHeartbeats 4000000 in
theorem run_loop0_loop1_eq (cs : Slice cbtrn03c.TranCatRecord) (tcat : cbtrn03c.TranCatRecord)
    (key : Array U8 2#usize) (cat : I64) :
    cbtrn03c.run_loop0_loop1 cs tcat key cat 0#usize =
      .ok (match cs.val.find? (fun c => decide (c.tran_type_cd.val = key.val) &&
          decide (c.tran_cat_cd = cat)) with
        | some c => (c, true)
        | none => (tcat, false)) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn03c.run_loop0_loop1]
  refine wp_loop (loop_shape _) (fun i => i.val ≤ cs.val.length ∧
      (cs.val.take i.val).find? (fun c => decide (c.tran_type_cd.val = key.val) &&
        decide (c.tran_cat_cd = cat)) = none)
    (fun i => cs.val.length - i.val) ?_ _ ⟨by simp, by simp⟩
  rintro i ⟨hi, hf⟩
  simp only [IScalar.eq_equiv] at hf
  simp only [cbtrn03c.run_loop0_loop1.body]
  by_cases hlt : i.val < cs.val.length
  · by_cases hb : (cs.val[i.val]'hlt).tran_type_cd.val = key.val
    · by_cases hc : (cs.val[i.val]'hlt).tran_cat_cd = cat
      · aeneas_wp [bytes_eq_eq, Array.val_to_slice, hlt, hb, hc, eq_self_iff_true]
        try simp only [loopCls_done, Except.ok.injEq]
        rw [find?_of_take_none hf hlt (by simp [hb, hc])]
      · have hc' : ¬ (cs.val[i.val]'hlt).tran_cat_cd.val = cat.val :=
          fun h => hc (IScalar.eq_of_val_eq h)
        aeneas_wp [bytes_eq_eq, Array.val_to_slice, hlt, hb, hc, hc', eq_self_iff_true]
        simp (disch := first | omega | scalar_tac) only [dite_eq_left]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        exact find?_take_succ_none hlt hf (by simp only [hc', decide_false, Bool.and_false])
    · aeneas_wp [bytes_eq_eq, Array.val_to_slice, hlt, hb]
      simp (disch := first | omega | scalar_tac) only [dite_eq_left]
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      exact find?_take_succ_none hlt hf (by simp only [hb, decide_false, Bool.false_and])
  · aeneas_wp [hlt]
    try simp only [loopCls_done, Except.ok.injEq]
    rw [show i.val = cs.val.length by omega, List.take_length] at hf
    simp [hf]

set_option maxHeartbeats 4000000 in
theorem run_loop0_loop4_eq (cs : Slice cbtrn03c.TranCatRecord) (tcat : cbtrn03c.TranCatRecord)
    (key : Array U8 2#usize) (cat : I64) :
    cbtrn03c.run_loop0_loop4 cs tcat key cat 0#usize =
      .ok (match cs.val.find? (fun c => decide (c.tran_type_cd.val = key.val) &&
          decide (c.tran_cat_cd = cat)) with
        | some c => (c, true)
        | none => (tcat, false)) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn03c.run_loop0_loop4]
  refine wp_loop (loop_shape _) (fun i => i.val ≤ cs.val.length ∧
      (cs.val.take i.val).find? (fun c => decide (c.tran_type_cd.val = key.val) &&
        decide (c.tran_cat_cd = cat)) = none)
    (fun i => cs.val.length - i.val) ?_ _ ⟨by simp, by simp⟩
  rintro i ⟨hi, hf⟩
  simp only [IScalar.eq_equiv] at hf
  simp only [cbtrn03c.run_loop0_loop4.body]
  by_cases hlt : i.val < cs.val.length
  · by_cases hb : (cs.val[i.val]'hlt).tran_type_cd.val = key.val
    · by_cases hc : (cs.val[i.val]'hlt).tran_cat_cd = cat
      · aeneas_wp [bytes_eq_eq, Array.val_to_slice, hlt, hb, hc, eq_self_iff_true]
        try simp only [loopCls_done, Except.ok.injEq]
        rw [find?_of_take_none hf hlt (by simp [hb, hc])]
      · have hc' : ¬ (cs.val[i.val]'hlt).tran_cat_cd.val = cat.val :=
          fun h => hc (IScalar.eq_of_val_eq h)
        aeneas_wp [bytes_eq_eq, Array.val_to_slice, hlt, hb, hc, hc', eq_self_iff_true]
        simp (disch := first | omega | scalar_tac) only [dite_eq_left]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        exact find?_take_succ_none hlt hf (by simp only [hc', decide_false, Bool.and_false])
    · aeneas_wp [bytes_eq_eq, Array.val_to_slice, hlt, hb]
      simp (disch := first | omega | scalar_tac) only [dite_eq_left]
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      exact find?_take_succ_none hlt hf (by simp only [hb, decide_false, Bool.false_and])
  · aeneas_wp [hlt]
    try simp only [loopCls_done, Except.ok.injEq]
    rw [show i.val = cs.val.length by omega, List.take_length] at hf
    simp [hf]

/-! ## The lookups on field values -/

theorem ebcU_inj (u w : U8) (h : ebcU u = ebcU w) : u = w := by
  have hu := cp037_roundtrip ⟨u.val, by have := u.hBounds; simpa using this⟩
  have hw := cp037_roundtrip ⟨w.val, by have := w.hBounds; simpa using this⟩
  simp only at hu hw
  apply UScalar.eq_of_val_eq
  rw [← hu, ← hw]
  exact congrArg cp037Code h

/-- The EBCDIC bytes of alphanumeric fields are equal iff their Latin-1 bytes are. -/
theorem ebcU_map_beq (l1 l2 : List U8) : (l1.map ebcU == l2.map ebcU) = decide (l1 = l2) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun u w huw => ebcU_inj u w huw) h
  · rintro rfl
    rfl

theorem i64_beq (x y : I64) : (x.val == y.val) = decide (x = y) := by
  by_cases h : x = y
  · subst h
    simp
  · have h' : x.val ≠ y.val := fun e => h (IScalar.eq_of_val_eq e)
    simp [h, h']

theorem find_xref (xs : List cbtrn03c.CardXrefRecord) (key : List U8) :
    (xs.map CardXrefRecord.vals).find? (fun x => Model.xCard x == key.map ebcU) =
      (xs.find? (fun x => decide (x.xref_card_num.val = key))).map CardXrefRecord.vals := by
  simp only [List.find?_map, Function.comp_def, xCard_vals, ebcU_map_beq]

theorem find_ttype (ys : List cbtrn03c.TranTypeRecord) (key : List U8) :
    (ys.map TranTypeRecord.vals).find? (fun y => Model.yType y == key.map ebcU) =
      (ys.find? (fun y => decide (y.tran_type.val = key))).map TranTypeRecord.vals := by
  simp only [List.find?_map, Function.comp_def, yType_vals, ebcU_map_beq]

theorem find_tcat (cs : List cbtrn03c.TranCatRecord) (key : List U8) (cat : I64) :
    (cs.map TranCatRecord.vals).find? (fun c => Model.cType c == key.map ebcU &&
        Model.cCat c == cat.val) =
      (cs.find? (fun c => decide (c.tran_type_cd.val = key) && decide (c.tran_cat_cd = cat))).map
        TranCatRecord.vals := by
  simp only [List.find?_map, Function.comp_def, cType_vals, cCat_vals, ebcU_map_beq, i64_beq]

theorem map_ebcU_take (l : List U8) (n : Nat) : (l.map ebcU).take n = (l.take n).map ebcU := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ n => exact congrArg (List.cons (ebcU a)) (ih n)

end EquivLean.Modernize.Cbtrn03c.Rust
