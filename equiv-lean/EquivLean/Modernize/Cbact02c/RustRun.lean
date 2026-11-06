import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Modernize.Cbact02c.RustProof

/-!
# CBACT02C → Rust: the equation of `run` (`RunSpec`), hence the generated statement

The translation is veriforch's guided v1 (`examples/rust/mod_cbact02c`,
`Demo/Gen/Aeneas/ModCbact02c`).

* The helpers: `push_bytes` (a byte copy loop) and the copy loop of `push_unsigned` by
  `aeneas_spec`; the digit loop of `push_unsigned` (a `[u8; 18]` buffer filled from its end) by
  hand, `push_unsigned_loop0_spec`: the `digits` low digits, right-aligned.  `push_unsigned_eq`:
  `dst` followed by `zeroPad digits |value|`.  `card_record_display` (straight-line code over the
  helpers) by `aeneas_spec`.
* `run_eq`: `run` in bytes, by `aeneas_spec`.  The read loop is ended by the end-of-file flag
  (`while !end_of_file`, with `pos`, `at_eof` and an `Option<CardRecord>`); the generated
  invariant: the lines of the records read so far (`take pos`), and `at_eof = end_of_file = false`
  while the loop goes on, `pos = len` once it stops.
* The glue: a record's line is `CardRecord.text` of its field values (`cardLine_text`: an
  alphanumeric field's Latin-1 bytes are the CP037 text of its EBCDIC bytes, a numeric field shows
  `zpad`); the start and end lines are the CP037 texts of coblean's messages (`decide`); the
  numeric fields of a valid record are nonnegative (`vals_neg_ok`), so `push_unsigned` can negate
  them; `2 ^ 28` records fit in a `Vec` with a 32-bit `usize`.
* `run_spec : RunSpec`, and `rust : Statement`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact02c.Rust
open cbact02c
open Cobol.Digits (toDigits)

/-! ## The helpers -/

theorem push_bytes_eq (dst : alloc.vec.Vec U8) (src : Slice U8)
    (h : dst.val.length + src.val.length < Usize.max) :
    push_bytes dst src = .ok (alloc.vec.Vec.from (dst.val ++ src.val) (by simp; omega)) := by
  aeneas_spec [push_bytes, push_bytes_loop]

/-- The copy loop of `push_unsigned`: the first `digits` bytes of the buffer. -/
theorem push_unsigned_loop1_eq (dst : alloc.vec.Vec U8) (digits : Usize) (buf : Array U8 18#usize)
    (hd : digits.val ≤ 18) (h : dst.val.length + digits.val < Usize.max) :
    push_unsigned_loop1 dst digits buf 0#usize =
      .ok (alloc.vec.Vec.from (dst.val ++ buf.val.take digits.val) (by simp; omega)) := by
  aeneas_spec [push_unsigned_loop1]

set_option maxHeartbeats 2000000 in
/-- The digit loop of `push_unsigned`: after `digits` iterations, the `digits` low digits of `x`,
right-aligned in the first `digits` bytes of the buffer. -/
theorem push_unsigned_loop0_spec (digits : Usize) (x : Nat) (v : U64) (hd : digits.val ≤ 18)
    (hv : v.val = x) :
    wp (push_unsigned_loop0 digits v (Array.repeat 18#usize 48#u8) 0#usize)
      (fun o => ∃ b, o = .ok b ∧
        b.val = zeroPad digits.val x ++ List.replicate (18 - digits.val) 48#u8) := by
  simp only [push_unsigned_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ digits.val ∧ s.1.val = x / 10 ^ s.2.2.val ∧
      s.2.1.val = List.replicate (digits.val - s.2.2.val) 48#u8 ++ zeroPad s.2.2.val x ++
        List.replicate (18 - digits.val) 48#u8)
    (fun s => digits.val - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w buf i hinv
    obtain ⟨hi, hw, hbuf⟩ := hinv
    have hlen : buf.val.length = 18 := buf.property
    aeneas_wp [rust_loop_body, array_update_eq, UScalar.cast_val_eq, Array.from_val, hlen]
    by_cases h1 : i.val < digits.val
    · have hd10 : w.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have hm : digits.val - i.val = (digits.val - 1 - i.val) + 1 := by omega
      have h256 : w.val % 10 % 2 ^ 8 = w.val % 10 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, _root_.ite_true, h256]
      split_ifs
      all_goals try (exfalso; omega)
      all_goals try (exfalso; scalar_tac)
      simp only [loopCls_cont]
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [UScalar.ofNatCore_val_eq, UScalar.ofNatCore_val_eq, hw, Nat.div_div_eq_div_mul,
          ← Nat.pow_succ]
      · simp only [Array.from_val, hbuf, UScalar.ofNatCore_val_eq]
        rw [set_mid _ _ h1, zeroPad_succ_left,
          show digits.val - (i.val + 1) = digits.val - 1 - i.val by omega]
        simp only [List.append_cancel_left_eq, List.append_cancel_right_eq, List.singleton_append,
          List.cons.injEq, and_true]
        rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), hw]
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      have e : i.val = digits.val := by omega
      rw [hbuf, e, Nat.sub_self, List.replicate_zero, List.nil_append]
  · refine ⟨by simp, by simp [hv], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_zero]
    have z : zeroPad 0 x = [] := by simp [zeroPad, zpad, toDigits]
    rw [z, List.append_nil, ← List.replicate_add]
    congr 1
    omega

theorem zeroPad_rep_length (n x : Nat) (hn : n ≤ 18) :
    (zeroPad n x ++ List.replicate (18 - n) 48#u8).length = 18 := by
  simp [zeroPad_length]; omega

/-- `push_unsigned`: the `digits` low decimal digits of `|value|` after `dst` (`digits ≤ 18`; the
negation of `value` must not overflow). -/
theorem push_unsigned_eq (dst : alloc.vec.Vec U8) (value : I64) (digits : Usize)
    (hd : digits.val ≤ 18) (hmin : -9223372036854775808 < value.val)
    (h : dst.val.length + digits.val < Usize.max) :
    push_unsigned dst value digits =
      .ok (alloc.vec.Vec.from (dst.val ++ zeroPad digits.val value.val.natAbs)
        (by simp [zeroPad_length]; omega)) := by
  refine eq_ok_of_wp ?_
  unfold push_unsigned
  -- the digits of the `u64` value `w` of `|value|`
  have key : ∀ w : U64, w.val = value.val.natAbs →
      wp (Std.bind (push_unsigned_loop0 digits w (Array.repeat 18#usize 48#u8) 0#usize)
        (fun buf1 => push_unsigned_loop1 dst digits buf1 0#usize))
      (fun o => o = .ok (alloc.vec.Vec.from (dst.val ++ zeroPad digits.val value.val.natAbs)
        (by simp [zeroPad_length]; omega))) := by
    intro w hw
    rw [wp_bind]
    refine wp_mono (push_unsigned_loop0_spec digits value.val.natAbs w hd hw) ?_
    rintro _ ⟨b, rfl, hb⟩
    dsimp only
    rw [push_unsigned_loop1_eq dst digits b hd h]
    simp only [wp_ok, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hb]
    rw [List.take_append_of_le_length (by simp [zeroPad_length]),
      List.take_of_length_le (by simp [zeroPad_length])]
  by_cases hv : value.val < 0
  · have hlt : (value < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp [IScalar.cast_val_eq]
    have hb : (↑value : Int).bmod (2 ^ min 64 128) = value.val := by
      have := value.hBounds
      simp only [IScalarTy.I64_numBits_eq] at this
      exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
    rw [dite_eq_left_of_eq_true (eq_true (by rw [hb]; omega)), ← wp_bind]
    apply key
    rw [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, hb]
    simp only [UScalarTy.U64_numBits_eq]
    omega
  · have hlt : (value < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    rw [← wp_bind]
    apply key
    rw [IScalar.hcast_val_eq]
    have := value.hBounds
    simp only [UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq] at *
    omega


/-! ## A record's line, and `run` -/

/-- The display line of a card record (Latin-1 bytes): its fields in order, the numeric ones as
zero-padded digits of their absolute value. -/
def cardLine (r : cbact02c.CardRecord) : List U8 :=
  r.card_num.val ++ zeroPad 11 r.card_acct_id.val.natAbs ++ zeroPad 3 r.card_cvv_cd.val.natAbs ++
    r.card_embossed_name.val ++ r.card_expiraion_date.val ++ r.card_active_status.val ++
    r.filler1.val

theorem cardLine_length (r : cbact02c.CardRecord) : (cardLine r).length = 150 := by
  simp [cardLine, zeroPad_length]

theorem card_record_display_eq (r : cbact02c.CardRecord)
    (ha : -9223372036854775808 < r.card_acct_id.val)
    (hc : -9223372036854775808 < r.card_cvv_cd.val) :
    card_record_display r =
      .ok (alloc.vec.Vec.from (cardLine r) (by rw [cardLine_length]; scalar_tac)) := by
  aeneas_spec [card_record_display, cardLine] with [push_bytes_eq, push_unsigned_eq,
    Array.length_eq, zeroPad_length]

/-- The start line as `run` builds it (`b"START OF EXECUTION OF PROGRAM CBACT02C"`). -/
def startLine : List U8 :=
  [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8,
    67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8,
    79#u8, 71#u8, 82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8,
    50#u8, 67#u8]
/-- The end line as `run` builds it. -/
def endLine : List U8 :=
  [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8, 85#u8,
    84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8,
    82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8, 50#u8, 67#u8]

set_option maxHeartbeats 1000000 in
/-- **`run`, in bytes**: the start line, the line of each card record, the end line; no abend. -/
theorem run_eq (cards : Slice cbact02c.CardRecord)
    (hv : ∀ r ∈ cards.val, -9223372036854775808 < r.card_acct_id.val ∧
      -9223372036854775808 < r.card_cvv_cd.val)
    (hlen : cards.val.length + 2 < Usize.max) :
    ∃ out, cbact02c.run cards = .ok out ∧
      out.displays.val.map (·.val) = [startLine] ++ cards.val.map cardLine ++ [endLine] ∧
      out.abended = false := by
  aeneas_spec [cbact02c.run, cbact02c.run_loop] with [card_record_display_eq, startLine, endLine]

/-! ## Glue -/

theorem startLine_text : startLine.map UScalar.val = startText := by decide +kernel
theorem endLine_text : endLine.map UScalar.val = endText := by decide +kernel

/-- The numeric fields of a valid record are nonnegative, so `push_unsigned` can negate them. -/
theorem vals_neg_ok (r : cbact02c.CardRecord) (hv : CardRecord.Valid (CardRecord.vals r)) :
    -9223372036854775808 < r.card_acct_id.val ∧ -9223372036854775808 < r.card_cvv_cd.val := by
  simp only [Schema.Valid, CardRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨h2, _ | ⟨h3, -⟩⟩⟩
  have a := num_nonneg (fun fmt hk => by cases hk; exact ⟨rfl, rfl⟩) h2
  have c := num_nonneg (fun fmt hk => by cases hk; exact ⟨rfl, rfl⟩) h3
  omega

/-- **A record's line is its text**: `CardRecord.text` of its field values. -/
theorem cardLine_text (r : cbact02c.CardRecord) :
    (cardLine r).map UScalar.val = CardRecord.text (CardRecord.vals r) := by
  simp only [cardLine, List.map_append, zeroPad_val, Schema.text, CardRecord.vals,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, fieldText, latin1_text, List.append_nil, List.append_assoc]

/-- **The equation of `run`** (`RunSpec` of `RustProof.lean`). -/
theorem run_spec : RunSpec := by
  intro s vals hs hv hn
  have hneg : ∀ r ∈ s.val, -9223372036854775808 < r.card_acct_id.val ∧
      -9223372036854775808 < r.card_cvv_cd.val := fun r hr =>
    vals_neg_ok r (hv _ (hs ▸ List.mem_map_of_mem hr))
  have hlen : s.val.length + 2 < Usize.max := by
    have : s.val.length = vals.length := by rw [← hs, List.length_map]
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega
  obtain ⟨out, hrun, hd, ha⟩ := run_eq s hneg hlen
  refine ⟨out, hrun, ?_, ha⟩
  have := congrArg (List.map (List.map UScalar.val)) hd
  simp only [List.map_map, List.map_append, List.map_cons, List.map_nil] at this
  rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
    (fun l => l.val.map UScalar.val) from rfl] at this
  rw [this, startLine_text, endLine_text, ← hs, List.map_map]
  simp only [List.cons_append, List.cons.injEq, true_and, List.append_cancel_right_eq]
  exact List.map_congr_left fun r _ => cardLine_text r

/-- **CBACT02C → Rust, every input.** -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbact02c.Rust

#print axioms EquivLean.Modernize.Cbact02c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbact02c.Rust.rust
