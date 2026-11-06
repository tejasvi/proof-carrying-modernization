import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Modernize.Cbcus01c.RustProof

/-!
# CBCUS01C → Rust: the equation of `run` (`RunSpec`), hence the generated statement

The translation is veriforch's guided v1 (`examples/rust/mod_cbcus01c`,
`Demo/Gen/Aeneas/ModCbcus01c`).  It displays every customer record twice.

* The helpers: `push_bytes`, `lit` and the copy loop of `push_unsigned` by `aeneas_spec`;
  `magnitude` (the absolute value as `u64`, also of `i64::MIN`) by cases; the digit loop of
  `push_unsigned` (a `[u8; 20]` buffer filled from position `digits - 1` down) by hand,
  `push_unsigned_loop0_spec`; `customer_display` (19 calls) by `aeneas_spec`.
* `run_eq`: `run` in bytes, by `aeneas_spec`: a read loop ended by the end-of-file flag (`'N'` /
  `'Y'`) that pushes each record's line twice.
* The glue, as for CBACT02C (`Modernize/Cbact02c/RustRun.lean`), and `rust : Statement`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbcus01c.Rust
open cbcus01c
open Cobol.Digits (toDigits)

/-! ## The helpers -/

theorem push_bytes_eq (out : alloc.vec.Vec U8) (b : Slice U8)
    (h : out.val.length + b.val.length < Usize.max) :
    push_bytes out b = .ok (alloc.vec.Vec.from (out.val ++ b.val) (by simp; omega)) := by
  aeneas_spec [push_bytes, push_bytes_loop]

theorem lit_eq (s : Slice U8) (h : s.val.length < Usize.max) :
    lit s = .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  aeneas_spec [lit] with [push_bytes_eq]

/-- `magnitude`: the absolute value, as a `u64`. -/
theorem magnitude_eq (v : I64) :
    ∃ u : U64, magnitude v = .ok u ∧ u.val = v.val.natAbs := by
  refine exists_ok_of_wp ?_
  unfold magnitude
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp [IScalar.hcast_val_eq]
    split_ifs <;> first
      | (exfalso; omega)
      | (refine ⟨_, rfl, ?_⟩; simp only [UScalar.ofNatCore_val_eq]; omega)
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_ok]
    refine ⟨_, rfl, ?_⟩
    rw [IScalar.hcast_val_eq]
    simp only [UScalarTy.U64_numBits_eq]
    omega

/-- The copy loop of `push_unsigned`: the first `digits` bytes of the buffer. -/
theorem push_unsigned_loop1_eq (out : alloc.vec.Vec U8) (digits : Usize) (buf : Array U8 20#usize)
    (hd : digits.val ≤ 20) (h : out.val.length + digits.val < Usize.max) :
    push_unsigned_loop1 out digits buf 0#usize =
      .ok (alloc.vec.Vec.from (out.val ++ buf.val.take digits.val) (by simp; omega)) := by
  aeneas_spec [push_unsigned_loop1]

set_option maxHeartbeats 2000000 in
/-- The digit loop of `push_unsigned`: after `digits` iterations, the `digits` low digits of `x`,
right-aligned in the first `digits` bytes of the buffer. -/
theorem push_unsigned_loop0_spec (digits : Usize) (x : Nat) (v : U64) (hd : digits.val ≤ 20)
    (hv : v.val = x) :
    wp (push_unsigned_loop0 digits v (Array.repeat 20#usize 48#u8) 0#usize)
      (fun o => ∃ b, o = .ok b ∧
        b.val = zeroPad digits.val x ++ List.replicate (20 - digits.val) 48#u8) := by
  simp only [push_unsigned_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ digits.val ∧ s.1.val = x / 10 ^ s.2.2.val ∧
      s.2.1.val = List.replicate (digits.val - s.2.2.val) 48#u8 ++ zeroPad s.2.2.val x ++
        List.replicate (20 - digits.val) 48#u8)
    (fun s => digits.val - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w buf i hinv
    obtain ⟨hi, hw, hbuf⟩ := hinv
    have hlen : buf.val.length = 20 := buf.property
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

theorem zeroPad_rep_length (n x : Nat) (hn : n ≤ 20) :
    (zeroPad n x ++ List.replicate (20 - n) 48#u8).length = 20 := by
  simp [zeroPad_length]; omega

/-- `push_unsigned`: the `digits` low decimal digits of `|v|` after `out` (`digits ≤ 20`). -/
theorem push_unsigned_eq (out : alloc.vec.Vec U8) (v : I64) (digits : Usize)
    (hd : digits.val ≤ 20) (h : out.val.length + digits.val < Usize.max) :
    push_unsigned out v digits =
      .ok (alloc.vec.Vec.from (out.val ++ zeroPad digits.val v.val.natAbs)
        (by simp [zeroPad_length]; omega)) := by
  refine eq_ok_of_wp ?_
  obtain ⟨u, hu, huv⟩ := magnitude_eq v
  simp only [push_unsigned, hu, wp_bind, wp_ok]
  refine wp_mono (push_unsigned_loop0_spec digits v.val.natAbs u hd huv) ?_
  rintro _ ⟨b, rfl, hb⟩
  dsimp only
  rw [push_unsigned_loop1_eq out digits b hd h]
  simp only [wp_ok, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hb]
  rw [List.take_append_of_le_length (by simp [zeroPad_length]),
    List.take_of_length_le (by simp [zeroPad_length])]

/-! ## A record's line, and `run` -/

/-- The display line of a customer record (Latin-1 bytes): its fields in order, the numeric ones
as zero-padded digits of their absolute value. -/
def custLine (r : cbcus01c.CustomerRecord) : List U8 :=
  zeroPad 9 r.cust_id.val.natAbs ++
    r.cust_first_name.val ++
    r.cust_middle_name.val ++
    r.cust_last_name.val ++
    r.cust_addr_line_1.val ++
    r.cust_addr_line_2.val ++
    r.cust_addr_line_3.val ++
    r.cust_addr_state_cd.val ++
    r.cust_addr_country_cd.val ++
    r.cust_addr_zip.val ++
    r.cust_phone_num_1.val ++
    r.cust_phone_num_2.val ++
    zeroPad 9 r.cust_ssn.val.natAbs ++
    r.cust_govt_issued_id.val ++
    r.cust_dob_yyyy_mm_dd.val ++
    r.cust_eft_account_id.val ++
    r.cust_pri_card_holder_ind.val ++
    zeroPad 3 r.cust_fico_credit_score.val.natAbs ++
    r.filler1.val

theorem custLine_length (r : cbcus01c.CustomerRecord) : (custLine r).length = 500 := by
  simp [custLine, zeroPad_length]

set_option maxHeartbeats 1000000 in
/-- The line of a record: straight-line code over `push_bytes` and `push_unsigned` (19 calls). -/
theorem customer_display_eq (r : cbcus01c.CustomerRecord) :
    customer_display r =
      .ok (alloc.vec.Vec.from (custLine r) (by rw [custLine_length]; scalar_tac)) := by
  aeneas_spec [customer_display, custLine] with [push_bytes_eq, push_unsigned_eq,
    Array.length_eq, zeroPad_length]

/-- The start line as `run` builds it (`b"START OF EXECUTION OF PROGRAM CBCUS01C"`). -/
def startLine : List U8 :=
  [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8,
    67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8,
    79#u8, 71#u8, 82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 67#u8, 85#u8, 83#u8, 48#u8,
    49#u8, 67#u8]
/-- The end line as `run` builds it. -/
def endLine : List U8 :=
  [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8, 85#u8,
    84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8,
    82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 67#u8, 85#u8, 83#u8, 48#u8, 49#u8, 67#u8]

set_option maxHeartbeats 1000000 in
/-- **`run`, in bytes**: the start line, the line of each record twice, the end line; no abend. -/
theorem run_eq (s : Slice cbcus01c.CustomerRecord) (hlen : 2 * s.val.length + 2 < Usize.max) :
    ∃ out, cbcus01c.run s = .ok out ∧
      out.displays.val.map (·.val) =
        [startLine] ++ s.val.flatMap (fun r => [custLine r, custLine r]) ++ [endLine] ∧
      out.abended = false := by
  aeneas_spec [cbcus01c.run, cbcus01c.run_loop] with [customer_display_eq, lit_eq, startLine,
    endLine]

/-! ## Glue -/

theorem startLine_text : startLine.map UScalar.val = startText := by decide +kernel
theorem endLine_text : endLine.map UScalar.val = endText := by decide +kernel

/-- **A record's line is its text**: `CustomerRecord.text` of its field values. -/
theorem custLine_text (r : cbcus01c.CustomerRecord) :
    (custLine r).map UScalar.val = CustomerRecord.text (CustomerRecord.vals r) := by
  simp only [custLine, List.map_append, zeroPad_val, Schema.text, CustomerRecord.vals,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, fieldText, latin1_text, List.append_nil, List.append_assoc]

/-- **The equation of `run`** (`RunSpec` of `RustProof.lean`). -/
theorem run_spec : RunSpec := by
  intro s vals hs hv hn
  have hlen : 2 * s.val.length + 2 < Usize.max := by
    have : s.val.length = vals.length := by rw [← hs, List.length_map]
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega
  obtain ⟨out, hrun, hd, ha⟩ := run_eq s hlen
  refine ⟨out, hrun, ?_, ha⟩
  have := congrArg (List.map (List.map UScalar.val)) hd
  simp only [List.map_map, List.map_append, List.map_cons, List.map_nil, List.map_flatMap] at this
  rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
    (fun l => l.val.map UScalar.val) from rfl] at this
  rw [this, startLine_text, endLine_text, ← hs, List.flatMap_map]
  simp only [List.cons_append, List.cons.injEq, true_and, List.append_cancel_right_eq]
  exact List.flatMap_congr fun r _ => by simp [custLine_text]

/-- **CBCUS01C → Rust, every input.** -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbcus01c.Rust

#print axioms EquivLean.Modernize.Cbcus01c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbcus01c.Rust.rust
