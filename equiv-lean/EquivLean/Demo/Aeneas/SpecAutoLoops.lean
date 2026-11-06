import EquivLean.Bridge.Aeneas.SpecAuto
import EquivLean.Demo.Gen.Aeneas.SpecLoops.Funs

/-!
# Rust loops against specifications: the loop shapes of the Headline A translations

`aeneas_spec [defs] (with [lemmas])?` (`Bridge/Aeneas/SpecAuto.lean`) on the loop shapes that
veriforch's guided Rust translations of the CardDemo programs use (`examples/rust/specloops`,
`Demo/Gen/Aeneas/SpecLoops/Funs.lean`, unmodified Charon + Aeneas output).  No invariant is
written:

* `for i in 0..s.len()` (a `Range` loop variable, `IteratorRange.next`): `copy_range`;
* `for _ in 0..n` (a range up to a bound; the specification at `i` instead of `n`): `spaces`;
* `while j < digits && j < 18` (a counter with two bounds): `take_digits`, also with the
  invariant written by hand (`aeneas_spec … using (I) (V)`, `take_digits_using`);
* `b"…".to_vec()` and `extend_from_slice` (value forms of the library functions): `labelled`;
* a COBOL read loop ended by the end-of-file flag (`while !end_of_file`, with the position, an
  `at_eof` flag, an `Option<Rec>`, the status of each read compared as `[u8; 2]`, an early return
  that abends, and the end line pushed in the loop's exit branch): `listing`.  The generated
  invariant: the lines of the records read so far (`take pos`), and `at_eof = end_of_file = false`
  while the loop goes on, `pos = len` once it stops.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.SpecAutoLoops

open specloops

/-- `for i in 0..s.len()`: the copy of a slice. -/
theorem copy_range_eq (s : Slice U8) :
    copy_range s = .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  aeneas_spec [copy_range, copy_range_loop]

/-- `for _ in 0..n`: `n` spaces. -/
theorem spaces_eq (n : Usize) :
    spaces n = .ok (alloc.vec.Vec.from (List.replicate n.val 32#u8) (by simp; scalar_tac)) := by
  aeneas_spec [spaces, spaces_loop]

/-- `while j < digits && j < 18`: the first `digits` bytes of the buffer. -/
theorem take_digits_eq (buf : Array U8 18#usize) (digits : Usize) (hd : digits.val ≤ 18) :
    take_digits buf digits =
      .ok (alloc.vec.Vec.from (buf.val.take digits.val) (by simp; scalar_tac)) := by
  aeneas_spec [take_digits, take_digits_loop]

/-- `b"ID: ".to_vec()`, then `extend_from_slice`. -/
theorem labelled_eq (b : Array U8 4#usize) :
    labelled b = .ok (alloc.vec.Vec.from ([73#u8, 68#u8, 58#u8, 32#u8] ++ b.val)
      (by simp; scalar_tac)) := by
  aeneas_spec [labelled]

/-- The same copy with the invariant written by hand (`using (I) (V)`: the state is `(out, j)`;
the kit proves the step and the entry). -/
theorem take_digits_using (buf : Array U8 18#usize) (digits : Usize) (hd : digits.val ≤ 18) :
    take_digits buf digits =
      .ok (alloc.vec.Vec.from (buf.val.take digits.val) (by simp; scalar_tac)) := by
  aeneas_spec [take_digits, take_digits_loop]
    using (fun (out, j) => j.val ≤ digits.val ∧ out.val = buf.val.take j.val)
      (fun (_, j) => digits.val - j.val)

set_option maxHeartbeats 400000 in
/-- The read loop: the start line, the tag of each record, the end line; no abend. -/
theorem listing_spec (recs : Slice Rec) (hlen : recs.val.length + 2 < Usize.max) :
    ∃ out, listing recs = .ok out ∧
      out.displays.val.map (·.val) =
        [[83#u8, 84#u8, 65#u8, 82#u8, 84#u8]] ++ recs.val.map (·.tag.val) ++
          [[69#u8, 78#u8, 68#u8]] ∧
      out.abended = false := by
  aeneas_spec [listing, listing_loop]

end EquivLean.Demo.Aeneas.SpecAutoLoops

#print axioms EquivLean.Demo.Aeneas.SpecAutoLoops.copy_range_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoLoops.spaces_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoLoops.take_digits_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoLoops.take_digits_using
#print axioms EquivLean.Demo.Aeneas.SpecAutoLoops.labelled_eq
#print axioms EquivLean.Demo.Aeneas.SpecAutoLoops.listing_spec
