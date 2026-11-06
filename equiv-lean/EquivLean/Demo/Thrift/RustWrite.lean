import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___thrift__protocol__compact__TCompactOutputProtocol_T____write_field_header
import EquivLean.Demo.Thrift.RustContracts
import EquivLean.Demo.Thrift.RustZigzag
import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Bridge.Aeneas.SpecAuto

/-!
# Thrift (T4), Rust side: the compact protocol's writers

The Rust writers (`lib/rs/src/protocol/compact.rs` at f0eb8b84e, through Aeneas) on a generic transport, under the
transport contract `WriteContract` and the library contracts of `RustContracts.lean` (`StdContract`,
`ShiftContract`, and the `io::Cursor` / varint-rs models of `ThriftRs/F_v_anon13.lean`).
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-! ## `write_byte` -/

theorem write_byte_ok (hS : StdContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.compact.TCompactOutputProtocol T)
    (b : U8) :
    ∃ t', protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_byte inst self b =
      ok (.Ok (), { self with transport := t' }) ∧ sent t' = sent self.transport ++ [b] := by
  obtain ⟨n, t', hw, ht'⟩ := hW.write_ok self.transport (Array.to_slice (Array.make 1#usize [b]))
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_byte
    aeneas_wp [hw, core.result.Result.map_err_ok, hS.map_ok,
      protocol.compact.TOutputProtocolTCompactOutputProtocol.write_byte.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeTuple,
      protocol.compact.TOutputProtocolTCompactOutputProtocol.write_byte.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeTuple.call_once]
  · rw [ht']
    simp [Array.to_slice, Array.make]

/-! ## The cursor and varint-rs models -/

theorem blanket_write_cursor (c : rusttrn_model.CursorM)
    (f : rusttrn_model.CursorM → rusttrn_model.CursorM) (b : U8) (h : c.pos < c.buf.length) :
    varint_rs.VarintWriterWError.Blanket.write thrift.core.io.cursor.CursorMut0SliceU8.Insts.CoreIoWriteWrite
        (c, f) b =
      ok (.Ok (), (⟨c.buf.take c.pos ++ [b] ++ c.buf.drop (c.pos + 1), c.pos + 1⟩, f)) := by
  unfold varint_rs.VarintWriterWError.Blanket.write
  have hmin : min c.pos c.buf.length = c.pos := by omega
  have hk : min (c.buf.length - c.pos) 1 = 1 := by omega
  have h1 : 1 ≤ c.buf.length - c.pos := by omega
  simp [lift, Array.to_slice, Array.make, rusttrn_model.cursorWrite, hmin, h1]

theorem writeBytes_cursor : ∀ (bs pre rest : List U8) (f : rusttrn_model.CursorM → rusttrn_model.CursorM),
    bs.length ≤ rest.length →
    rusttrn_model.writeBytes
        (varint_rs.VarintWriterWError.Blanket.write thrift.core.io.cursor.CursorMut0SliceU8.Insts.CoreIoWriteWrite)
        bs (⟨pre ++ rest, pre.length⟩, f) =
      ok (.Ok (), (⟨pre ++ bs ++ rest.drop bs.length, pre.length + bs.length⟩, f))
  | [], pre, rest, f, _ => by simp [rusttrn_model.writeBytes]
  | [b], pre, rest, f, h => by
    simp only [List.length_singleton] at h
    rw [rusttrn_model.writeBytes, blanket_write_cursor _ _ _ (by simp; omega)]
    simp
  | b :: b' :: bs, pre, rest, f, h => by
    simp only [List.length_cons] at h
    obtain ⟨r0, rest', rfl⟩ : ∃ r0 rest', rest = r0 :: rest' := by
      match rest with
      | r0 :: rest' => exact ⟨r0, rest', rfl⟩
      | [] => simp at h
    simp only [rusttrn_model.writeBytes]
    rw [blanket_write_cursor _ _ _ (by simp), bind_ok]
    have hbuf : List.take pre.length (pre ++ r0 :: rest') ++ [b] ++
        List.drop (pre.length + 1) (pre ++ r0 :: rest') = (pre ++ [b]) ++ rest' := by simp
    have hpos : pre.length + 1 = (pre ++ [b]).length := by simp
    change rusttrn_model.writeBytes _ (b' :: bs)
      ((⟨List.take pre.length (pre ++ r0 :: rest') ++ [b] ++ List.drop (pre.length + 1) (pre ++ r0 :: rest'),
        pre.length + 1⟩ : rusttrn_model.CursorM), f) = _
    rw [hbuf, hpos, writeBytes_cursor (b' :: bs) (pre ++ [b]) rest' f (by simp at h ⊢; omega)]
    simp only [List.length_append, List.length_cons, List.append_assoc, List.cons_append,
      List.drop_succ_cons, ok.injEq, Prod.mk.injEq, true_and, rusttrn_model.CursorM.mk.injEq, and_true,
      List.nil_append, List.length_nil]
    omega

theorem writeBytes_cursor0 (bs buf : List U8) (f : rusttrn_model.CursorM → rusttrn_model.CursorM)
    (h : bs.length ≤ buf.length) :
    rusttrn_model.writeBytes
        (varint_rs.VarintWriterWError.Blanket.write thrift.core.io.cursor.CursorMut0SliceU8.Insts.CoreIoWriteWrite)
        bs (⟨buf, 0⟩, f) = ok (.Ok (), (⟨bs ++ buf.drop bs.length, bs.length⟩, f)) := by
  have := writeBytes_cursor bs [] buf f h
  simpa using this

theorem leb128_length_le (n k : Nat) (h : n < 2 ^ (7 * (k + 1))) :
    (rusttrn_model.leb128 n).length ≤ k + 1 := by
  induction k generalizing n with
  | zero =>
    rw [rusttrn_model.leb128]
    have : n < 128 := by simpa using h
    simp [this]
  | succ k ih =>
    rw [rusttrn_model.leb128]
    split_ifs with h128
    · simp
    · simp only [List.length_cons, Nat.add_le_add_iff_right]
      apply ih
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
        rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by ring, Nat.pow_add]
      omega

theorem uval_mk {ty : UScalarTy} (bv : BitVec ty.numBits) : (⟨bv⟩ : UScalar ty).val = bv.toNat := rfl

/-- The transport contract, in `wp` form. -/
theorem wp_write_all {T : Type} {inst : transport.TWriteTransport T} {sent : T → List U8}
    (hW : WriteContract inst sent) (t : T) (s : Slice U8)
    (Q : Except Error ((core.result.Result Unit core.io.error.Error) × T) → Prop)
    (h : ∀ t', sent t' = sent t ++ s.val → Q (.ok (.Ok (), t'))) :
    wp (inst.coreiowriteWriteInst.write_all t s) Q := by
  obtain ⟨t', hw, ht'⟩ := hW.write_all_ok t s
  rw [hw]
  exact (wp_ok _ _).2 (h t' ht')

/-! ## `write_i16` (compact): the zigzag varint of the value -/

set_option maxHeartbeats 4000000 in
theorem write_i16_wp (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (i : I16) :
    wp (protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i16 inst self i)
      (fun o => ∃ t', o = .ok (.Ok (), { self with transport := t' }) ∧
        sent t' = sent self.transport ++ rusttrn_model.leb128 (zz i.val)) := by
  have hu : (⟨(i.bv <<< 1) ^^^ i.bv.sshiftRight 15⟩ : U16).val = zz i.val := zigzag_bv16 i.bv
  have hlen : (rusttrn_model.leb128 (zz i.val)).length ≤ 3 := by
    apply leb128_length_le _ 2
    rw [← hu]
    have := (⟨(i.bv <<< 1) ^^^ i.bv.sshiftRight 15⟩ : U16).hBounds
    simp at this ⊢
    omega
  have hbuf0 : (Array.repeat 3#usize (0#u8)).to_slice.val = [0#u8, 0#u8, 0#u8] := by
    simp [Array.to_slice, Array.repeat_val]
  have hwb := writeBytes_cursor0 (rusttrn_model.leb128 (zz i.val)) [0#u8, 0#u8, 0#u8] id (by simpa using hlen)
  have hk : (rusttrn_model.leb128 (zz i.val)).length < 2 ^ 64 := by omega
  unfold protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i16
  aeneas_wp [core.array.Array.index_mut, core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    thrift.core.io.cursor.Cursor.new, varint_rs.VarintWriter.write_i16_varint.default, zigzag16_eq hSh,
    varint_rs.VarintWriterWError.Blanket, rusttrn_model.blanketBase,
    core.slice.index.SliceIndexRangeFullSlice.index_mut, hu, hbuf0, hwb,
    core.result.Result.Insts.CoreOpsTry.branch, thrift.core.io.cursor.Cursor.position,
    Array.index_SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    UScalar.cast_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, id_eq]
  have hnb : 4 < 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  have hmax : 3 ≤ Usize.max := by scalar_tac
  generalize rusttrn_model.leb128 (zz i.val) = L at hlen ⊢
  have hk4 : ∀ k, k < 4 → k % 2 ^ System.Platform.numBits = k := fun k hk => by
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  match L, hlen with
  | [], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk4, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk4, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk4, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk4, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩

/-! ## `write_field_header` -/

/-- A byte of the given value (modulo 256). -/
def mkByte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

/-- What Rust's `write_field_header` appends, when the delta `d = field_id - last_write_field_id` is an `i16`: the
short form `(d as u8) << 4 | field_type` for `0 < d < 15`, else the type byte and the zigzag varint of the id. -/
def rustFieldHeader (d : Int) (ty : U8) (id : I16) : List U8 :=
  if 0 < d ∧ d < 15 then [mkByte (16 * d.toNat ||| ty.val)] else ty :: rusttrn_model.leb128 (zz id.val)

theorem u8_shl4 (x : U8) : x <<< (4#i32) = ok ⟨x.bv <<< 4⟩ := by
  show UScalar.shiftLeft_IScalar x 4#i32 = _
  simp [UScalar.shiftLeft_IScalar, UScalar.shiftLeft]

theorem short_byte (d : Int) (h1 : 0 < d) (h2 : d < 15) (h : -32768 ≤ d ∧ d ≤ 32767) (ty : U8) :
    (⟨(IScalar.hcast UScalarTy.U8 (IScalar.ofIntCore (ty := .I16) d (by scalar_tac))).bv <<< 4⟩ ||| ty : U8) =
      mkByte (16 * d.toNat ||| ty.val) := by
  apply UScalar.eq_of_val_eq
  have hty : ty.val < 256 := by scalar_tac
  have hl : 16 * d.toNat ||| ty.val < 2 ^ 8 := Nat.or_lt_two_pow (by omega) (by simpa using hty)
  rw [UScalar.val_or, uval_mk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  show ((IScalar.hcast UScalarTy.U8 _).val * 2 ^ 4 % 2 ^ 8 ||| ty.val) = (BitVec.ofNat 8 _).toNat
  rw [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  congr 1
  simp only [UScalarTy.U8_numBits_eq]
  omega

set_option maxHeartbeats 4000000 in
theorem write_field_header_wp (hS : StdContract) (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (ty : U8) (id : I16)
    (hd : -32768 ≤ id.val - self.last_write_field_id.val ∧ id.val - self.last_write_field_id.val ≤ 32767) :
    wp (protocol.compact.TCompactOutputProtocol.write_field_header inst self ty id)
      (fun o => ∃ t', o = .ok (.Ok (), { self with transport := t', last_write_field_id := id }) ∧
        sent t' = sent self.transport ++ rustFieldHeader (id.val - self.last_write_field_id.val) ty id) := by
  unfold protocol.compact.TCompactOutputProtocol.write_field_header
  by_cases hshort : 0 < id.val - self.last_write_field_id.val ∧ id.val - self.last_write_field_id.val < 15
  · obtain ⟨t', hwb, ht'⟩ := write_byte_ok hS hW self
      (mkByte (16 * (id.val - self.last_write_field_id.val).toNat ||| ty.val))
    aeneas_wp [hd, hshort, u8_shl4, short_byte _ hshort.1 hshort.2 hd ty, hwb,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact ⟨t', rfl, by rw [ht', rustFieldHeader, ite_eq_left hshort]⟩
  · obtain ⟨t1, hwb, ht1⟩ := write_byte_ok hS hW self ty
    have hlong : ¬ (0 < id.val - self.last_write_field_id.val) ∨
        ¬ (id.val - self.last_write_field_id.val < 15) := by omega
    rcases hlong with hl | hl
    · aeneas_wp [hd, hl, hwb, core.result.Result.Insts.CoreOpsTry.branch]
      refine wp_mono (write_i16_wp hSh hW _ id) ?_
      rintro o ⟨t2, rfl, ht2⟩
      aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
      exact ⟨t2, rfl, by rw [ht2, ht1, rustFieldHeader, ite_eq_right hshort]; simp⟩
    · have hp : 0 < id.val - self.last_write_field_id.val := by omega
      aeneas_wp [hd, hp, hl, hwb, core.result.Result.Insts.CoreOpsTry.branch]
      refine wp_mono (write_i16_wp hSh hW _ id) ?_
      rintro o ⟨t2, rfl, ht2⟩
      aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
      exact ⟨t2, rfl, by rw [ht2, ht1, rustFieldHeader, ite_eq_right hshort]; simp⟩

/-- (M) When `field_id - last_write_field_id` leaves `i16`, `write_field_header` panics (Aeneas's semantics, as a
debug build; a release build wraps the delta instead). -/
theorem write_field_header_overflow {T : Type} (inst : transport.TWriteTransport T)
    (self : protocol.compact.TCompactOutputProtocol T) (ty : U8) (id : I16)
    (hd : ¬ (-32768 ≤ id.val - self.last_write_field_id.val ∧ id.val - self.last_write_field_id.val ≤ 32767)) :
    protocol.compact.TCompactOutputProtocol.write_field_header inst self ty id = fail .integerOverflow := by
  have h : wp (protocol.compact.TCompactOutputProtocol.write_field_header inst self ty id)
      (fun o => o = .error .integerOverflow) := by
    unfold protocol.compact.TCompactOutputProtocol.write_field_header
    aeneas_wp [hd]
  rcases (wp_iff _ _).1 h with ⟨a, _, ha⟩ | ⟨e, he, he'⟩
  · cases ha
  · cases he'
    exact he

/-- The prereg's compact field header (as byte values), with the zigzag varint written as the Rust model's LEB128
bytes: the short form `16 * (id - last) + ty` when `1 ≤ id - last ≤ 15`. -/
def specFieldHeader (last id : Int) (ty : Nat) : List Nat :=
  if 1 ≤ id - last ∧ id - last ≤ 15 then [16 * (id - last).toNat + ty]
  else ty :: (rusttrn_model.leb128 (zz id)).map (·.val)

/-- (E) Off the delta 15 (and inside `i16`), Rust's field header is the prereg's, for every type nibble. -/
theorem rustFieldHeader_spec (last id : I16) (ty : U8) (hty : ty.val < 16)
    (h15 : id.val - last.val ≠ 15) :
    (rustFieldHeader (id.val - last.val) ty id).map (·.val) = specFieldHeader last.val id.val ty.val := by
  unfold rustFieldHeader specFieldHeader
  by_cases hs : 0 < id.val - last.val ∧ id.val - last.val < 15
  · have hs' : 1 ≤ id.val - last.val ∧ id.val - last.val ≤ 15 := by omega
    rw [ite_eq_left hs, ite_eq_left hs']
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by omega) (by simpa using
      (show ty.val < 2 ^ 8 by omega)))]
    have hor := Nat.two_pow_add_eq_or_of_lt (show ty.val < 2 ^ 4 by omega) (id.val - last.val).toNat
    rw [show 16 * (id.val - last.val).toNat = 2 ^ 4 * (id.val - last.val).toNat by ring, ← hor]
  · have hs' : ¬ (1 ≤ id.val - last.val ∧ id.val - last.val ≤ 15) := by omega
    rw [ite_eq_right hs, ite_eq_right hs']
    simp

/-- DISCREPANCY (delta 15): for `id - last = 15`, Rust writes the long form (the type byte, then the zigzag varint
of the id), while the prereg's spec, C++ and Java write the one byte `0xF0 | ty`. -/
theorem write_field_header_delta15 (hS : StdContract) (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (ty : U8) (id : I16)
    (h15 : id.val - self.last_write_field_id.val = 15) :
    ∃ t', protocol.compact.TCompactOutputProtocol.write_field_header inst self ty id =
        ok (.Ok (), { self with transport := t', last_write_field_id := id }) ∧
      sent t' = sent self.transport ++ ty :: rusttrn_model.leb128 (zz id.val) ∧
      (ty :: rusttrn_model.leb128 (zz id.val)).map (·.val) ≠
        specFieldHeader self.last_write_field_id.val id.val ty.val := by
  have hd : -32768 ≤ id.val - self.last_write_field_id.val ∧ id.val - self.last_write_field_id.val ≤ 32767 := by
    omega
  have h := write_field_header_wp hS hSh hW self ty id hd
  rcases (wp_iff _ _).1 h with ⟨a, ha, t', hat, ht'⟩ | ⟨e, _, t', hfalse, _⟩
  · cases hat
    refine ⟨t', ha, ?_, ?_⟩
    · rw [ht', rustFieldHeader, ite_eq_right (by omega)]
    · intro heq
      have hl := congrArg List.length heq
      have hne : rusttrn_model.leb128 (zz id.val) ≠ [] := by
        rw [rusttrn_model.leb128]
        split_ifs <;> simp
      have hpos : 0 < (rusttrn_model.leb128 (zz id.val)).length := List.length_pos_of_ne_nil hne
      rw [specFieldHeader, ite_eq_left (by omega)] at hl
      simp only [List.length_cons, List.length_map, List.length_nil] at hl
      omega
  · cases hfalse

/-- DISCREPANCY, the byte sequence: previous field id 0, field id 15, type 5 (i32): Rust appends `[0x05, 0x1E]`
(type, then zigzag(15) = 30 as a varint), where the prereg's spec (and C++/Java) give `[0xF5]`. -/
theorem write_field_header_delta15_example (hS : StdContract) (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (hlast : self.last_write_field_id = 0#i16) :
    ∃ t', protocol.compact.TCompactOutputProtocol.write_field_header inst self 5#u8 15#i16 =
        ok (.Ok (), { self with transport := t', last_write_field_id := 15#i16 }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++ [0x05, 0x1E] ∧
      specFieldHeader 0 15 5 = [0xF5] := by
  obtain ⟨t', ho, ht', -⟩ := write_field_header_delta15 hS hSh hW self 5#u8 15#i16 (by rw [hlast]; decide)
  refine ⟨t', ho, ?_, by decide⟩
  rw [ht', List.map_append]
  congr 1
  have hz : zz (15#i16 : I16).val = 30 := by decide
  rw [hz, rusttrn_model.leb128, ite_eq_left (by decide)]
  rfl

end EquivLean.Demo.Thrift.Rust
