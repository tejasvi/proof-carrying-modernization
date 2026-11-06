import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Modernize.Cbact03c.RustProof

/-!
# CBACT03C → Rust: the equation of `run` (`RunSpec`), hence the generated statement

The translation is veriforch's guided v1 (`examples/rust/mod_cbact03c`,
`Demo/Gen/Aeneas/ModCbact03c`).  It displays every card cross-reference record twice.

* The helpers: `push_bytes` and the copy loop of `push_unsigned` by `aeneas_spec`; the digit loop
  of `push_unsigned` (a `[u8; 20]` buffer filled from position `digits` down, `DIGITS[v % 10]`,
  signed `i64` arithmetic on a nonnegative value) by hand, `push_unsigned_loop0_spec`;
  `record_bytes` by `aeneas_spec`.
* `run_eq`: `run` in bytes, by `aeneas_spec`: a read loop ended by the end-of-file flag that pushes
  each record's line twice (the generated invariant bounds the lines by `1 + 2 * pos`).
* The glue, as for CBACT02C (`Modernize/Cbact02c/RustRun.lean`), and `rust : Statement`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact03c.Rust
open cbact03c

/-! ## The helpers -/

theorem push_bytes_eq (dst : alloc.vec.Vec U8) (src : Slice U8)
    (h : dst.val.length + src.val.length < Usize.max) :
    push_bytes dst src = .ok (alloc.vec.Vec.from (dst.val ++ src.val) (by simp; omega)) := by
  aeneas_spec [push_bytes, push_bytes_loop]

/-- The copy loop of `push_unsigned`: the first `digits` bytes of the buffer. -/
theorem push_unsigned_loop1_eq (dst : alloc.vec.Vec U8) (digits : Usize) (buf : Array U8 20#usize)
    (hd : digits.val ≤ 20) (h : dst.val.length + digits.val < Usize.max) :
    push_unsigned_loop1 dst digits buf 0#usize =
      .ok (alloc.vec.Vec.from (dst.val ++ buf.val.take digits.val) (by simp; omega)) := by
  aeneas_spec [push_unsigned_loop1]

/-- `DIGITS[d]` for a digit `d`. -/
theorem digits_get10 : ∀ d : Fin 10,
    DIGITS.val[d.val]'(by simp [DIGITS]) = byteOf (48 + d.val) := by
  decide +kernel

theorem digits_length : DIGITS.val.length = 10 := DIGITS.property

theorem digits_get (i : Nat) (h : i < DIGITS.val.length) : DIGITS.val[i] = byteOf (48 + i) :=
  digits_get10 ⟨i, by rw [digits_length] at h; exact h⟩

/-- `usize` holds at least the 32-bit values. -/
theorem usize_two_pow_ge : (2 : Int) ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

set_option maxHeartbeats 2000000 in
/-- The digit loop of `push_unsigned`: the buffer filled from position `digits` down, with the
`digits` low digits of `x`. -/
theorem push_unsigned_loop0_spec (digits : Usize) (x : Nat) (v : I64) (hd : digits.val ≤ 20)
    (hv : v.val = x) :
    wp (push_unsigned_loop0 v (Array.repeat 20#usize 48#u8) digits)
      (fun o => ∃ b, o = .ok b ∧
        b.val = zeroPad digits.val x ++ List.replicate (20 - digits.val) 48#u8) := by
  simp only [push_unsigned_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ digits.val ∧
      s.1.val = ((x / 10 ^ (digits.val - s.2.2.val) : Nat) : Int) ∧
      s.2.1.val = List.replicate s.2.2.val 48#u8 ++ zeroPad (digits.val - s.2.2.val) x ++
        List.replicate (20 - digits.val) 48#u8)
    (fun s => s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w buf pos hinv
    obtain ⟨hp, hw, hbuf⟩ := hinv
    have hlen : buf.val.length = 20 := buf.property
    aeneas_wp [rust_loop_body, array_update_eq, array_index_usize_eq, iscalar_srem_val,
      IScalar.hcast_val_eq, Array.from_val, hlen, digits_get]
    by_cases h1 : 0 < pos.val
    · obtain ⟨q, hq⟩ : ∃ q, q = x / 10 ^ (digits.val - pos.val) := ⟨_, rfl⟩
      rw [← hq] at hw
      have hw0 : (0 : Int) ≤ w.val := by rw [hw]; omega
      have hmod : (↑w : Int).tmod 10 = ((q % 10 : Nat) : Int) := by
        rw [Int.tmod_eq_emod_of_nonneg hw0, hw]; omega
      have hnb := usize_two_pow_ge
      have hd' : ((↑w : Int).tmod 10 % 2 ^ UScalarTy.Usize.numBits).toNat = q % 10 := by
        rw [hmod, Int.emod_eq_of_lt (by omega) (by omega)]; omega
      have hq' : x / 10 ^ (digits.val - (pos.val - 1)) = q / 10 := by
        have e : digits.val - (pos.val - 1) = (digits.val - pos.val) + 1 := by omega
        rw [e, pow_succ, ← Nat.div_div_eq_div_mul, hq]
      have hdiv : (↑w : Int).tdiv 10 = ((q / 10 : Nat) : Int) := by
        rw [Int.tdiv_eq_ediv_of_nonneg hw0, hw]; omega
      have hdl : q % 10 < DIGITS.val.length := by rw [digits_length]; omega
      have hp1 : pos.val - 1 < 20 := by omega
      simp only [h1, _root_.ite_true, hd', hdiv, hdl, hp1, _root_.dite_true]
      have hp1' : 1 ≤ pos.val := h1
      have hmin : ¬(w.val = -9223372036854775808 ∧ (10 : Int) = -1) := by omega
      simp only [hp1', _root_.ite_true, hmin, not_false_eq_true, _root_.dite_true,
        show ¬(10 : Int) = 0 by decide, loopCls_cont]
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [IScalar.ofInt_val_eq, UScalar.ofNatCore_val_eq, hq', hq]
      · rw [Array.from_val, UScalar.ofNatCore_val_eq, hbuf]
        obtain ⟨k, hk⟩ : ∃ k, pos.val = k + 1 := ⟨pos.val - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel, List.append_assoc, set_replicate_end]
        have e : digits.val - k = (digits.val - (k + 1)) + 1 := by omega
        rw [e, zeroPad_succ_left, ← hk, hq]
        simp only [List.append_assoc, List.cons_append]
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      have h0 : pos.val = 0 := by omega
      rw [hbuf, h0, List.replicate_zero, List.nil_append, Nat.sub_zero]
  · refine ⟨le_refl _, by simp [hv], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_self]
    have z : zeroPad 0 x = [] := by simp [zeroPad, zpad, Cobol.Digits.toDigits]
    rw [z, List.append_nil, ← List.replicate_add]
    congr 1
    omega

/-- `push_unsigned`: the `digits` low decimal digits of `|value|` after `dst` (`digits ≤ 20`; the
negation of `value` must not overflow). -/
theorem push_unsigned_eq (dst : alloc.vec.Vec U8) (value : I64) (digits : Usize)
    (hd : digits.val ≤ 20) (hmin : -9223372036854775808 < value.val)
    (h : dst.val.length + digits.val < Usize.max) :
    push_unsigned dst value digits =
      .ok (alloc.vec.Vec.from (dst.val ++ zeroPad digits.val value.val.natAbs)
        (by simp [zeroPad_length]; omega)) := by
  refine eq_ok_of_wp ?_
  unfold push_unsigned
  -- the digits of the `i64` value `w` of `|value|`
  have key : ∀ w : I64, w.val = value.val.natAbs →
      wp (Std.bind (push_unsigned_loop0 w (Array.repeat 20#usize 48#u8) digits)
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
    aeneas_wp
    rw [dite_eq_left_of_eq_true (eq_true (by
      have := value.hBounds
      simp only [IScalarTy.I64_numBits_eq] at this
      omega)), ← wp_bind]
    apply key
    rw [IScalar.ofInt_val_eq]
    omega
  · have hlt : (value < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    rw [← wp_bind]
    apply key
    omega

/-! ## A record's line, and `run` -/

/-- The display line of a card cross-reference record (Latin-1 bytes): its fields in order, the
numeric ones as zero-padded digits of their absolute value. -/
def xrefLine (r : cbact03c.CardXrefRecord) : List U8 :=
  r.xref_card_num.val ++ zeroPad 9 r.xref_cust_id.val.natAbs ++
    zeroPad 11 r.xref_acct_id.val.natAbs ++ r.filler1.val

theorem xrefLine_length (r : cbact03c.CardXrefRecord) : (xrefLine r).length = 50 := by
  simp [xrefLine, zeroPad_length]

theorem record_bytes_eq (r : cbact03c.CardXrefRecord)
    (hc : -9223372036854775808 < r.xref_cust_id.val)
    (ha : -9223372036854775808 < r.xref_acct_id.val) :
    record_bytes r =
      .ok (alloc.vec.Vec.from (xrefLine r) (by rw [xrefLine_length]; scalar_tac)) := by
  aeneas_spec [record_bytes, xrefLine] with [push_bytes_eq, push_unsigned_eq,
    Array.length_eq, zeroPad_length]

/-- The start line as `run` builds it (`b"START OF EXECUTION OF PROGRAM CBACT03C"`). -/
def startLine : List U8 :=
  [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8,
    67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8,
    79#u8, 71#u8, 82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8,
    51#u8, 67#u8]
/-- The end line as `run` builds it. -/
def endLine : List U8 :=
  [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8, 85#u8,
    84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8,
    82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8, 51#u8, 67#u8]

set_option maxHeartbeats 1000000 in
/-- **`run`, in bytes**: the start line, the line of each record twice, the end line; no abend. -/
theorem run_eq (s : Slice cbact03c.CardXrefRecord)
    (hv : ∀ r ∈ s.val, -9223372036854775808 < r.xref_cust_id.val ∧
      -9223372036854775808 < r.xref_acct_id.val)
    (hlen : 2 * s.val.length + 2 < Usize.max) :
    ∃ out, cbact03c.run s = .ok out ∧
      out.displays.val.map (·.val) =
        [startLine] ++ s.val.flatMap (fun r => [xrefLine r, xrefLine r]) ++ [endLine] ∧
      out.abended = false := by
  aeneas_spec [cbact03c.run, cbact03c.run_loop] with [record_bytes_eq, push_bytes_eq, startLine,
    endLine]

/-! ## Glue -/

theorem startLine_text : startLine.map UScalar.val = startText := by decide +kernel
theorem endLine_text : endLine.map UScalar.val = endText := by decide +kernel

/-- The numeric fields of a valid record are nonnegative, so `push_unsigned` can negate them. -/
theorem vals_neg_ok (r : cbact03c.CardXrefRecord)
    (hv : CardXrefRecord.Valid (CardXrefRecord.vals r)) :
    -9223372036854775808 < r.xref_cust_id.val ∧ -9223372036854775808 < r.xref_acct_id.val := by
  simp only [Schema.Valid, CardXrefRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨h2, _ | ⟨h3, -⟩⟩⟩
  have a := num_nonneg (fun fmt hk => by cases hk; exact ⟨rfl, rfl⟩) h2
  have c := num_nonneg (fun fmt hk => by cases hk; exact ⟨rfl, rfl⟩) h3
  omega

/-- **A record's line is its text**: `CardXrefRecord.text` of its field values. -/
theorem xrefLine_text (r : cbact03c.CardXrefRecord) :
    (xrefLine r).map UScalar.val = CardXrefRecord.text (CardXrefRecord.vals r) := by
  simp only [xrefLine, List.map_append, zeroPad_val, Schema.text, CardXrefRecord.vals,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, fieldText, latin1_text, List.append_nil, List.append_assoc]

/-- **The equation of `run`** (`RunSpec` of `RustProof.lean`). -/
theorem run_spec : RunSpec := by
  intro s vals hs hv hn
  have hneg : ∀ r ∈ s.val, -9223372036854775808 < r.xref_cust_id.val ∧
      -9223372036854775808 < r.xref_acct_id.val := fun r hr =>
    vals_neg_ok r (hv _ (hs ▸ List.mem_map_of_mem hr))
  have hlen : 2 * s.val.length + 2 < Usize.max := by
    have : s.val.length = vals.length := by rw [← hs, List.length_map]
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega
  obtain ⟨out, hrun, hd, ha⟩ := run_eq s hneg hlen
  refine ⟨out, hrun, ?_, ha⟩
  have := congrArg (List.map (List.map UScalar.val)) hd
  simp only [List.map_map, List.map_append, List.map_cons, List.map_nil, List.map_flatMap] at this
  rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
    (fun l => l.val.map UScalar.val) from rfl] at this
  rw [this, startLine_text, endLine_text, ← hs, List.flatMap_map]
  simp only [List.cons_append, List.cons.injEq, true_and, List.append_cancel_right_eq]
  exact List.flatMap_congr fun r _ => by simp [xrefLine_text]

/-- **CBACT03C → Rust, every input.** -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbact03c.Rust

#print axioms EquivLean.Modernize.Cbact03c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbact03c.Rust.rust
