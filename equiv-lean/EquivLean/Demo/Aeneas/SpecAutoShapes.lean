import EquivLean.Bridge.Aeneas.SpecAuto
import EquivLean.Demo.Gen.Aeneas.ModCbtrn02c.Funs
import EquivLean.Demo.Gen.Aeneas.ModCbtrn03c.Funs

/-!
# The Rust spec kit on loops of the CardDemo translations (CBTRN02C, CBTRN03C)

`aeneas_spec` with generated invariants, on loops of veriforch's translations
(`Demo/Gen/Aeneas/ModCbtrn02c`, `ModCbtrn03c`):
* a copy to an offset of a slice written in place (`buf[pos + i] = src[i]`): `put_loop_eq`;
* a search for an index (the position of the first match, and whether there is one):
  `run_loop2_loop7_eq`;
* a search for a match (`any`), given the specification of the comparison it calls:
  `run_loop2_loop8_eq` (with `same_eq`, by hand: a loop that compares two slices);
* a copy into a `Vec` (`push_bytes_loop_eq`) and a padded copy, whose head condition tests a
  bound while the body tests the source's length (`push_padded_loop_eq`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.SpecAutoShapes

section Cbtrn02c
open cbtrn02c

/-- `put`'s copy loop: `buf[pos + i] = src[i]`. -/
theorem put_loop_eq (buf : Slice U8) (pos : Usize) (src : Slice U8)
    (h : pos.val + src.val.length ≤ buf.val.length) :
    put_loop buf pos src 0#usize =
      .ok (Slice.from (buf.val.take pos.val ++ src.val ++ buf.val.drop (pos.val + src.val.length))
        (by have := buf.property; simp; omega)) := by
  aeneas_spec [put_loop]

/-- The account search of `run` that returns the position (2700/1500 lookups). -/
theorem run_loop2_loop7_eq (accounts : alloc.vec.Vec AccountRecord) (i : I64) :
    ∃ r, run_loop2_loop7 accounts i 0#usize = .ok r ∧
      r.1.val = (accounts.val.findIdx? (fun a => decide (a.acct_id = i))).getD 0 ∧
      r.2 = (accounts.val.findIdx? (fun a => decide (a.acct_id = i))).isSome := by
  aeneas_spec [run_loop2_loop7]

/-- `same`: byte-slice equality (lengths first). -/
theorem same_eq (a b : Slice U8) : same a b = .ok (decide (a.val = b.val)) := by
  refine eq_ok_of_wp ?_
  unfold same
  by_cases hl : a.val.length = b.val.length
  · have hne : ¬ (Slice.len a != Slice.len b) = true := by
      simp [hl, UScalar.eq_equiv]
    simp only [hne]
    simp only [same_loop]
    refine wp_loop (loop_shape _)
      (fun i => i.val ≤ a.val.length ∧ a.val.take i.val = b.val.take i.val)
      (fun i => a.val.length - i.val) ?_ _ ?_
    · intro i hinv
      obtain ⟨hi, ht⟩ := hinv
      aeneas_wp [rust_loop_body]
      by_cases h1 : i.val < a.val.length
      · simp only [h1, _root_.ite_true, _root_.dite_true, show i.val < b.val.length by omega]
        by_cases h2 : (a.val[i.val]'h1).val = (b.val[i.val]'(by omega)).val
        · have h3 : i.val + 1 ≤ Usize.max := by scalar_tac
          simp only [h2, not_true_eq_false, _root_.ite_false, h3, _root_.dite_true, loopCls_cont,
            UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          rw [take_succ_of_lt (by omega), take_succ_of_lt (by omega), ht, UScalar.eq_of_val_eq h2]
        · simp only [h2, not_false_eq_true, _root_.ite_true, loopCls_done, Except.ok.injEq]
          have hne' : ¬ a.val = b.val := fun heq => h2 (by simp only [heq])
          simp only [hne', decide_false]
      · simp only [h1, _root_.ite_false, loopCls_done, Except.ok.injEq]
        have hi' : i.val = a.val.length := by omega
        rw [hi', List.take_of_length_le (by omega), hl, List.take_of_length_le (by omega)] at ht
        simp [ht]
    · simp
  · have hne : (Slice.len a != Slice.len b) = true := by
      simp [hl]
    simp only [hne, _root_.ite_true, wp_ok, Except.ok.injEq]
    have : ¬ a.val = b.val := fun heq => hl (by rw [heq])
    simp [this]

/-- The duplicate check of 2900-WRITE-TRANSACTION-FILE: some transaction written has the id. -/
theorem run_loop2_loop8_eq (v : alloc.vec.Vec TranRecord) (a : Array U8 16#usize) :
    run_loop2_loop8 v a 0#usize = .ok (v.val.any (fun t => decide (t.tran_id.val = a.val))) := by
  aeneas_spec [run_loop2_loop8] with [same_eq]

end Cbtrn02c

section Cbtrn03c
open cbtrn03c

/-- `push_bytes`: append the slice. -/
theorem push_bytes_loop_eq (out : alloc.vec.Vec U8) (s : Slice U8)
    (h : out.val.length + s.val.length ≤ Usize.max) :
    ∃ r, push_bytes_loop out s 0#usize = .ok r ∧ r.val = out.val ++ s.val := by
  aeneas_spec [push_bytes_loop]

set_option maxHeartbeats 400000 in
/-- `push_padded`: the first `width` bytes of `s`, padded with spaces (the list walk over `s` is
tried first and fails: hence the heartbeats). -/
theorem push_padded_loop_eq (out : alloc.vec.Vec U8) (s : Slice U8) (width : Usize)
    (h : out.val.length + width.val ≤ Usize.max) :
    ∃ r, push_padded_loop out s width 0#usize = .ok r ∧
      r.val = out.val ++ (s.val.take width.val ++
        List.replicate (width.val - s.val.length) 32#u8) := by
  aeneas_spec [push_padded_loop]

end Cbtrn03c

end EquivLean.Demo.Aeneas.SpecAutoShapes

#print axioms EquivLean.Demo.Aeneas.SpecAutoShapes.put_loop_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoShapes.run_loop2_loop7_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoShapes.same_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoShapes.run_loop2_loop8_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoShapes.push_bytes_loop_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoShapes.push_padded_loop_eq
