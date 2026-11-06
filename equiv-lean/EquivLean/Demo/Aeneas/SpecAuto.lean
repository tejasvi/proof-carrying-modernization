import EquivLean.Bridge.Aeneas.SpecAuto
import EquivLean.Demo.Gen.Aeneas.SpecKit.Funs
import EquivLean.Demo.Cobol.Cbact04cRust.Lookup
import EquivLean.Bridge.Cobol.Records

/-!
# Rust loops against specifications, with generated invariants (no invariant written)

`aeneas_spec [defs] (with [lemmas])?` (`Bridge/Aeneas/SpecAuto.lean`) proves that a function of
the Charon + Aeneas translation meets a specification written as a pure Lean function of its
inputs (`List.map`, `List.filter`, `List.foldl`, `List.find?`, `List.any`, appends); it generates
the loop invariants.  All code is unmodified Charon + Aeneas output.

* `examples/rust/speckit` (`Demo/Gen/Aeneas/SpecKit/Funs.lean`), loops over a slice of records
  that build output `Vec`s: one line per record (`map_lines`), with a header and a trailer
  (`framed`), for the records that pass a filter (`filter_lines`), with their count in a final
  line (`count_lines`; also against a `foldl` with a structure state, `count_lines_fold`), with a
  wrapping running total (`total_line`, a `foldl`), two outputs and a return code
  (`two_outputs`), a linear search (`lookup`) and a loop that calls it (`joined`, given
  `lookup_eq`), two loops in sequence (`two_loops`), a return code set by a flag (`with_rc`).
* The CBACT04C Rust port (`Demo/Cobol/Cbact04cRust`): its keyed lookups `read_account` and
  `find_rate`, as `List.find?`.
* A CBACT02C-shaped program in the Headline A Rust interface: a record struct with `[u8; 16]`,
  `i64`, `i64` and `[u8; 59]` fields; `run` displays a start line, one line per record (the
  alphanumeric fields copied byte by byte, the numeric fields zero-padded) and an end line, into
  `displays: Vec<Vec<u8>>`.  The byte-copy loop `push_bytes`, the straight-line `card_line` and
  the record loop of `run` are proved by the kit.  The digit loops of `zero_pad` are proved by
  hand (`zero_pad_eq`): their invariants are arithmetic (`p = 10 ^ (n - j)`), which the kit does
  not generate.  `run_displays` states the lines in code points, with
  `EquivLean.Cobol.Rec.zpad` for the numeric fields.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.SpecAuto

/-! ## Loops over a slice of records -/

section
open speckit

def toLine (r : Rec) : Line := ⟨r.id, r.amount⟩
def p (r : Rec) : Bool := r.amount.val ≠ 0
def q (r : Rec) : Bool := r.amount.val = 0
def Line.toNat (l : Line) : Nat × Nat := (l.key.val, l.val.val)

theorem map_lines_spec (recs : Slice Rec) :
    wp (map_lines recs) (fun o => ∃ v, o = .ok v ∧ v.val = recs.val.map toLine) := by
  aeneas_spec [map_lines, map_lines_loop] with [toLine]

theorem framed_spec (recs : Slice Rec) (h : recs.val.length + 2 ≤ Usize.max) :
    wp (framed recs) (fun o => ∃ v, o = .ok v ∧
      v.val = [⟨0#u32, 0#u32⟩] ++ recs.val.map toLine ++ [⟨1#u32, 1#u32⟩]) := by
  aeneas_spec [framed, framed_loop] with [toLine]

theorem filter_lines_spec (recs : Slice Rec) :
    wp (filter_lines recs) (fun o => ∃ v, o = .ok v ∧
      v.val = (recs.val.filter p).map toLine) := by
  aeneas_spec [filter_lines, filter_lines_loop] with [toLine, p]

theorem two_outputs_spec (recs : Slice Rec) :
    wp (two_outputs recs) (fun o => ∃ a b c, o = .ok (a, b, c) ∧
      a.val = recs.val.map toLine ∧ b.val = recs.val.filter p ∧ c = 0#u32) := by
  aeneas_spec [two_outputs, two_outputs_loop] with [toLine, p]

/-- The output lines as pairs of numbers (a decoder of the output `Vec`). -/
theorem count_lines_spec (recs : Slice Rec) (h : recs.val.length < U32.max) :
    wp (count_lines recs) (fun o => ∃ v, o = .ok v ∧
      v.val.map Line.toNat = ((recs.val.filter p).map toLine).map Line.toNat ++
        [(9, (recs.val.filter p).length)]) := by
  aeneas_spec [count_lines, count_lines_loop] with [toLine, p, Line.toNat]

/-- The wrapping running total, as a fold: the lines and the total. -/
def totStep (s : List Line × U32) (r : Rec) : List Line × U32 :=
  (s.1 ++ [⟨r.id, core.num.U32.wrapping_add s.2 r.amount⟩], core.num.U32.wrapping_add s.2 r.amount)

theorem total_line_spec (recs : Slice Rec) (h : recs.val.length + 1 < Usize.max) :
    wp (total_line recs) (fun o => ∃ v, o = .ok v ∧
      v.val = (recs.val.foldl totStep ([], 0#u32)).1 ++
        [⟨9#u32, (recs.val.foldl totStep ([], 0#u32)).2⟩]) := by
  aeneas_spec [total_line, total_line_loop] with [totStep]

/-- `count_lines` against a fold with a structure state, in the `∃ v, f x = ok v ∧ P v` form. -/
structure CState where
  lines : List Line
  n : Nat

def cstep (s : CState) (r : Rec) : CState :=
  if r.amount.val ≠ 0 then ⟨s.lines ++ [toLine r], s.n + 1⟩ else s

/-- The counter of the fold, as a length (the kit derives no bound for a counter). -/
theorem cstep_n (l : List Rec) (s : CState) : (l.foldl cstep s).n = s.n + (l.filter p).length := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih =>
    simp only [List.foldl_cons, List.filter_cons, ih]
    by_cases hr : r.amount.val = 0
    · simp [cstep, p, hr]
    · simp [cstep, p, hr]; omega

theorem count_lines_fold (recs : Slice Rec) (h : recs.val.length < U32.max) :
    ∃ v, count_lines recs = .ok v ∧
      v.val.map Line.toNat = (recs.val.foldl cstep ⟨[], 0⟩).lines.map Line.toNat ++
        [(9, (recs.val.foldl cstep ⟨[], 0⟩).n)] := by
  aeneas_spec [count_lines, count_lines_loop] with [cstep, toLine, Line.toNat, cstep_n, p]

def lookupSpec (tbl : Slice Rec) (key : U32) : U32 :=
  match tbl.val.find? (fun r => decide (r.id = key)) with
  | some r => r.amount
  | none => 0#u32

/-- A linear search with an early `return`. -/
theorem lookup_eq (tbl : Slice Rec) (key : U32) : lookup tbl key = .ok (lookupSpec tbl key) := by
  aeneas_spec [lookup, lookup_loop, lookupSpec]

/-- A loop that calls `lookup`, given its specification. -/
theorem joined_spec (recs tbl : Slice Rec) :
    wp (joined recs tbl) (fun o => ∃ v, o = .ok v ∧
      v.val = recs.val.map (fun r => ⟨r.id, lookupSpec tbl r.id⟩)) := by
  aeneas_spec [joined, joined_loop] with [lookup_eq]

theorem two_loops_spec (a b : Slice Rec) (h : a.val.length + b.val.length < Usize.max) :
    wp (two_loops a b) (fun o => ∃ v, o = .ok v ∧
      v.val = a.val.map toLine ++ b.val.map toLine) := by
  aeneas_spec [two_loops, two_loops_loop0, two_loops_loop1] with [toLine]

theorem with_rc_spec (recs : Slice Rec) :
    wp (with_rc recs) (fun o => ∃ v rc, o = .ok (v, rc) ∧
      v.val = (recs.val.filter p).map toLine ∧ rc = if recs.val.any q then 4#u32 else 0#u32) := by
  aeneas_spec [with_rc, with_rc_loop] with [toLine, p, q]

end

/-! ## The keyed lookups of the CBACT04C Rust port -/

section
open cbact04c EquivLean.Demo.Cbact04cRust

/-- `read_account`: the first account with the key. -/
theorem read_account_spec (accounts : Slice Account) (id : Std.I64) :
    read_account accounts id = .ok (accounts.val.find? (acctKey id)) := by
  aeneas_spec [read_account, read_account_loop] with [acctKey]

/-- `find_rate`: the rate of the first disclosure-group record with the key. -/
theorem find_rate_spec (discs : Slice Disc) (g : Std.U128) (t : Std.U16) (k : Std.I32) :
    find_rate discs g t k = .ok ((discs.val.find? (discKey g t k)).map (·.rate)) := by
  aeneas_spec [find_rate, find_rate_loop] with [discKey]

end

/-! ## A CBACT02C-shaped program -/

section
open speckit
open EquivLean.Cobol.Rec (zpad)
open Cobol.Digits (toDigits)

/-- Digit `j` (from the left) of the `n` digits of `v`. -/
theorem toDigits_getElem (n v j : Nat) (h : j < n) :
    (toDigits 10 n v)[j]'(by simpa using h) = v / 10 ^ (n - 1 - j) % 10 := by
  induction n generalizing v j with
  | zero => omega
  | succ n ih =>
    simp only [toDigits]
    by_cases hj : j < n
    · rw [List.getElem_append_left (by simpa using hj), ih (v / 10) j hj]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
    · have : j = n := by omega
      subst this
      rw [List.getElem_append_right (by simp)]
      simp

/-- A code point as a byte. -/
def byteOf (d : Nat) : U8 := ⟨BitVec.ofNat 8 d⟩

/-- The `n` zero-padded digits of `v`, as Latin-1 bytes. -/
def zeroPad (n v : Nat) : List U8 := (zpad n v).map byteOf

theorem zeroPad_length (n v : Nat) : (zeroPad n v).length = n := by
  simp [zeroPad, zpad]

theorem zeroPad_take_succ (n v j : Nat) (h : j < n) :
    (zeroPad n v).take (j + 1) =
      (zeroPad n v).take j ++ [byteOf (48 + v / 10 ^ (n - 1 - j) % 10)] := by
  rw [take_succ_of_lt (by rw [zeroPad_length]; exact h)]
  congr 2
  simp only [zeroPad, zpad, List.getElem_map, toDigits_getElem n v j h]

theorem byteOf_val (a : Nat) (h : a < 256) : (byteOf a).val = a := by
  simp [byteOf, UScalar.val, Nat.mod_eq_of_lt h]

theorem zeroPad_val (n v : Nat) : (zeroPad n v).map UScalar.val = zpad n v := by
  simp only [zeroPad, zpad, List.map_map]
  apply List.map_congr_left
  intro e he
  have := Cobol.Digits.toDigits_lt (by decide) n v e he
  simp only [Function.comp_apply]
  rw [byteOf_val _ (by omega)]

set_option maxHeartbeats 1000000 in
/-- The first loop of `zero_pad`: `p = 10 ^ n`. -/
theorem zero_pad_loop0_spec (n : Usize) (hn : n.val ≤ 19) :
    wp (zero_pad_loop0 n 1#u64 0#usize) (fun o => ∃ p, o = .ok p ∧ p.val = 10 ^ n.val) := by
  simp only [zero_pad_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.val ≤ n.val ∧ s.1.val = 10 ^ s.2.val)
    (fun s => n.val - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro p k hinv
    obtain ⟨hk, hp⟩ := hinv
    aeneas_wp [rust_loop_body]
    split_ifs with h1 h2 h3
    · simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hp, pow_succ]
    · exfalso; scalar_tac
    · exfalso
      have h18 : 10 ^ k.val ≤ 10 ^ 18 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact h2 (by rw [hp]; omega)
    · simp only [loopCls_done]
      exact ⟨p, rfl, by rw [hp]; congr 1; omega⟩
  · simp

set_option maxHeartbeats 2000000 in
/-- The second loop of `zero_pad`: the digits, from the left. -/
theorem zero_pad_loop1_spec (n : Usize) (x p : U64) (hp : p.val = 10 ^ n.val) :
    wp (zero_pad_loop1 n x p (alloc.vec.Vec.new U8) 0#usize)
      (fun o => ∃ w, o = .ok w ∧ w.val = zeroPad n.val x.val) := by
  simp only [zero_pad_loop1]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ n.val ∧ s.1.val = 10 ^ (n.val - s.2.2.val) ∧
      s.2.1.val = (zeroPad n.val x.val).take s.2.2.val)
    (fun s => n.val - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro q out j hinv
    obtain ⟨hj, hq, hout⟩ := hinv
    aeneas_wp [rust_loop_body]
    by_cases h1 : j.val < n.val
    · have hm : n.val - j.val = (n.val - 1 - j.val) + 1 := by omega
      have hq10 : q.val / 10 = 10 ^ (n.val - 1 - j.val) := by
        rw [hq, hm, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      have hpos : 0 < 10 ^ (n.val - 1 - j.val) := by positivity
      have hd : x.val / 10 ^ (n.val - 1 - j.val) % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have hlen : out.val.length = j.val := by
        rw [hout, List.length_take, zeroPad_length]; omega
      simp only [h1, _root_.ite_true, hq10, UScalar.cast_val_eq, UScalar.ofNatCore_val_eq,
        UScalarTy.U8_numBits_eq, hlen]
      split_ifs with h2 h3 h4 h5 h6
      all_goals try (first | (exfalso; omega) | (exfalso; scalar_tac))
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val, hout]
      refine ⟨⟨by omega, by congr 1; omega, ?_⟩, by omega⟩
      rw [zeroPad_take_succ _ _ _ h1]
      congr 2
      rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq, byteOf_val _ (by omega)]
      omega
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨out, rfl, ?_⟩
      rw [hout, List.take_of_length_le (by rw [zeroPad_length]; omega)]
  · simp [hp]

/-- **`zero_pad`** (by hand): the `n` zero-padded digits of `v` (of 0 for a negative `v`). -/
theorem zero_pad_eq (v : I64) (n : Usize) (hn : n.val ≤ 19) :
    zero_pad v n = .ok (alloc.vec.Vec.from (zeroPad n.val v.val.toNat)
      (by rw [zeroPad_length]; scalar_tac)) := by
  refine eq_ok_of_wp ?_
  -- the digits of `x`, for the `u64` value `x` of `v` (0 for a negative `v`)
  have key : ∀ x : U64, x.val = v.val.toNat →
      wp (Std.bind (zero_pad_loop0 n 1#u64 0#usize)
        (fun p => zero_pad_loop1 n x p (alloc.vec.Vec.new U8) 0#usize))
      (fun o => o = .ok (alloc.vec.Vec.from (zeroPad n.val v.val.toNat)
        (by rw [zeroPad_length]; scalar_tac))) := by
    intro x hx
    rw [wp_bind]
    refine wp_mono (zero_pad_loop0_spec n hn) ?_
    rintro _ ⟨p, rfl, hp⟩
    refine wp_mono (zero_pad_loop1_spec n x p hp) ?_
    rintro _ ⟨w, rfl, hw⟩
    rw [hx] at hw
    simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hw]
  unfold zero_pad
  by_cases hv : v.val < 0
  · have : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [this, _root_.ite_true, bind_ok]
    exact key 0#u64 (by simp; omega)
  · have : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [this, _root_.ite_false, bind_ok]
    refine key _ ?_
    rw [IScalar.hcast_val_eq]
    have h1 := v.hBounds
    simp only [UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq] at *
    omega

/-- The byte-copy loop. -/
theorem push_bytes_eq (line : alloc.vec.Vec U8) (b : Slice U8)
    (h : line.val.length + b.val.length < Usize.max) :
    push_bytes line b = .ok (alloc.vec.Vec.from (line.val ++ b.val) (by simp; omega)) := by
  aeneas_spec [push_bytes, push_bytes_loop]

/-- The display line of a card record: its fields in order (Latin-1 bytes). -/
def cardLine (c : CardRecord) : List U8 :=
  c.card_num.val ++ zeroPad 11 c.card_acct_id.val.toNat ++ zeroPad 3 c.card_cvv_cd.val.toNat ++
    c.filler1.val

theorem cardLine_length (c : CardRecord) : (cardLine c).length = 89 := by
  simp [cardLine, zeroPad_length]

/-- The line of a record: straight-line code over `push_bytes` and `zero_pad`. -/
theorem card_line_eq (c : CardRecord) :
    card_line c = .ok (alloc.vec.Vec.from (cardLine c) (by rw [cardLine_length]; scalar_tac)) := by
  aeneas_spec [card_line, cardLine] with [push_bytes_eq, zero_pad_eq, Array.to_slice,
    alloc.vec.Vec.deref, Array.length_eq, zeroPad_length]

/-- **The CBACT02C-shaped `run`**: a start line, the line of each card record, an end line. -/
theorem run_spec (cards : Slice CardRecord) (hlen : cards.val.length + 2 < Usize.max) :
    wp (run cards) (fun o => ∃ out, o = .ok out ∧
      out.displays.val.map (·.val) = [[83#u8, 84#u8]] ++ cards.val.map cardLine ++
        [[69#u8, 78#u8]] ∧ out.abended = false) := by
  aeneas_spec [run, run_loop] with [card_line_eq]

/-- The same in code points, the COBOL observable: each numeric `PIC 9(n)` field shows `zpad n`
of its value. -/
theorem run_displays (cards : Slice CardRecord) (hlen : cards.val.length + 2 < Usize.max) :
    ∃ out, run cards = .ok out ∧
      out.displays.val.map (fun l => l.val.map UScalar.val) =
        [[83, 84]] ++ cards.val.map (fun c => c.card_num.val.map UScalar.val ++
          zpad 11 c.card_acct_id.val.toNat ++ zpad 3 c.card_cvv_cd.val.toNat ++
          c.filler1.val.map UScalar.val) ++ [[69, 78]] ∧
      out.abended = false := by
  obtain ⟨out, h, hd, ha⟩ := exists_ok_of_wp (run_spec cards hlen)
  refine ⟨out, h, ?_, ha⟩
  have := congrArg (List.map (List.map UScalar.val)) hd
  simp only [List.map_map, List.map_append, List.map_cons, List.map_nil] at this
  rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
    (fun l => l.val.map UScalar.val) from rfl] at this
  rw [this]
  simp [cardLine, List.map_append, zeroPad_val, Function.comp_def]

end

end EquivLean.Demo.Aeneas.SpecAuto

#print axioms EquivLean.Demo.Aeneas.SpecAuto.map_lines_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.framed_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.filter_lines_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.two_outputs_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.count_lines_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.total_line_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.count_lines_fold
#print axioms EquivLean.Demo.Aeneas.SpecAuto.lookup_eq
#print axioms EquivLean.Demo.Aeneas.SpecAuto.joined_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.two_loops_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.with_rc_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.read_account_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.find_rate_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.zero_pad_eq
#print axioms EquivLean.Demo.Aeneas.SpecAuto.push_bytes_eq
#print axioms EquivLean.Demo.Aeneas.SpecAuto.card_line_eq
#print axioms EquivLean.Demo.Aeneas.SpecAuto.run_spec
#print axioms EquivLean.Demo.Aeneas.SpecAuto.run_displays
