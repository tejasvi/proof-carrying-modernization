import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TOutputProtocol_for_thrift__protocol__compact__TCompactOutpu_d1ba3f51406554e7
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TOutputProtocol_for_thrift__protocol__compact__TCompactOutpu_73ac3069db6207c5
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__compact__TCompactInputP_9c2fb6bd250e5409
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__compact__TCompactInputP_cc411c4a3c99025e
import EquivLean.Demo.Thrift.RustBytes

/-!
# Thrift (T4), Rust side: the compact `i32` / `i64` writers (zigzag varints)

`write_i32` / `write_i64` (compact.rs:705, 713): varint-rs's `write_i32_varint` / `write_i64_varint` (extracted trait
defaults: the zigzag, then `write_u32_varint` / `write_u64_varint`) into a 5- / 10-byte `Cursor`, then `write_all`
of the bytes written. Under `ShiftContract` (varint-rs's zigzag) and the models of `ThriftRs/F_v_anon13.lean` (the
cursor; `write_uN_varint` as varint-rs's `write_varint!` macro); transport `WriteContract`. And the readers
`read_i32` / `read_i64` (compact.rs:345, 349): `read_varint32/64`, then `zigzag_to_i32/64`.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

theorem zz_eq_zigzag (v : Int) : zz v = Spec.zigzag v := rfl

theorem unzz_eq_unzigzag (n : Nat) : unzz n = Spec.unzigzag n := rfl

set_option maxHeartbeats 8000000 in
theorem write_i32_wp (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (i : I32) :
    wp (protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i32 inst self i)
      (fun o => ∃ t', o = .ok (.Ok (), { self with transport := t' }) ∧
        sent t' = sent self.transport ++ rusttrn_model.leb128 (zz i.val)) := by
  have hu : (⟨(i.bv <<< 1) ^^^ i.bv.sshiftRight 31⟩ : U32).val = zz i.val := zigzag_bv (w := 31) i.bv
  have hlen : (rusttrn_model.leb128 (zz i.val)).length ≤ 5 := by
    apply leb128_length_le _ 4
    rw [← hu]
    have := (⟨(i.bv <<< 1) ^^^ i.bv.sshiftRight 31⟩ : U32).hBounds
    simp at this ⊢
    omega
  have hbuf0 : (Array.repeat 5#usize (0#u8)).to_slice.val = [0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp [Array.to_slice, Array.repeat_val]
  have hwb := writeBytes_cursor0 (rusttrn_model.leb128 (zz i.val)) [0#u8, 0#u8, 0#u8, 0#u8, 0#u8] id
    (by simpa using hlen)
  have hk : (rusttrn_model.leb128 (zz i.val)).length < 2 ^ 64 := by omega
  unfold protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i32
  aeneas_wp [core.array.Array.index_mut, core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    thrift.core.io.cursor.Cursor.new, varint_rs.VarintWriter.write_i32_varint.default, zigzag32_eq hSh,
    varint_rs.VarintWriterWError.Blanket, rusttrn_model.blanketBase,
    core.slice.index.SliceIndexRangeFullSlice.index_mut, hu, hbuf0, hwb,
    core.result.Result.Insts.CoreOpsTry.branch, thrift.core.io.cursor.Cursor.position,
    Array.index_SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    UScalar.cast_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, id_eq]
  have hmax : 5 ≤ Usize.max := by scalar_tac
  generalize rusttrn_model.leb128 (zz i.val) = L at hlen ⊢
  have hk6 : ∀ k, k < 6 → k % 2 ^ System.Platform.numBits = k := fun k hk => by
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  match L, hlen with
  | [], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩

/-- (E, compact i32: zigzag + varint32) For every `i32` value, `write_i32` appends exactly
`Spec.varint (Spec.zigzag v)`. -/
theorem write_i32_E (hSh : ShiftContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.compact.TCompactOutputProtocol T)
    (i : I32) :
    ∃ t', protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i32 inst self i =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++
        (Spec.varint (Spec.zigzag i.val)).map UInt8.toNat := by
  rcases (wp_iff _ _).1 (write_i32_wp hSh hW self i) with ⟨a, ha, t', hat, ht'⟩ | ⟨e, _, t', hfalse, _⟩
  · cases hat
    refine ⟨t', ha, ?_⟩
    rw [ht', List.map_append, leb128_eq_varint, zz_eq_zigzag]
  · cases hfalse

set_option maxHeartbeats 16000000 in
theorem write_i64_wp (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (i : I64) :
    wp (protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i64 inst self i)
      (fun o => ∃ t', o = .ok (.Ok (), { self with transport := t' }) ∧
        sent t' = sent self.transport ++ rusttrn_model.leb128 (zz i.val)) := by
  have hu : (⟨(i.bv <<< 1) ^^^ i.bv.sshiftRight 63⟩ : U64).val = zz i.val := zigzag_bv (w := 63) i.bv
  have hlen : (rusttrn_model.leb128 (zz i.val)).length ≤ 10 := by
    apply leb128_length_le _ 9
    rw [← hu]
    have := (⟨(i.bv <<< 1) ^^^ i.bv.sshiftRight 63⟩ : U64).hBounds
    simp at this ⊢
    omega
  have hbuf0 : (Array.repeat 10#usize (0#u8)).to_slice.val =
      [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp [Array.to_slice, Array.repeat_val]
  have hwb := writeBytes_cursor0 (rusttrn_model.leb128 (zz i.val))
    [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8] id (by simpa using hlen)
  have hk : (rusttrn_model.leb128 (zz i.val)).length < 2 ^ 64 := by omega
  unfold protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i64
  aeneas_wp [core.array.Array.index_mut, core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    thrift.core.io.cursor.Cursor.new, varint_rs.VarintWriter.write_i64_varint.default, zigzag64_eq hSh,
    varint_rs.VarintWriterWError.Blanket, rusttrn_model.blanketBase,
    core.slice.index.SliceIndexRangeFullSlice.index_mut, hu, hbuf0, hwb,
    core.result.Result.Insts.CoreOpsTry.branch, thrift.core.io.cursor.Cursor.position,
    Array.index_SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    UScalar.cast_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, id_eq]
  have hmax : 10 ≤ Usize.max := by scalar_tac
  generalize rusttrn_model.leb128 (zz i.val) = L at hlen ⊢
  have hk11 : ∀ k, k < 11 → k % 2 ^ System.Platform.numBits = k := fun k hk => by
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  match L, hlen with
  | [], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e, f], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e, f, g], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e, f, g, h], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e, f, g, h, i], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩
  | [a, b, c, d, e, f, g, h, i, j], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk11, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    exact ⟨t', rfl, by rw [ht']; simp⟩

/-- (E, compact i64: zigzag + varint64) For every `i64` value, `write_i64` appends exactly
`Spec.varint (Spec.zigzag v)`. -/
theorem write_i64_E (hSh : ShiftContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.compact.TCompactOutputProtocol T)
    (i : I64) :
    ∃ t', protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i64 inst self i =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++
        (Spec.varint (Spec.zigzag i.val)).map UInt8.toNat := by
  rcases (wp_iff _ _).1 (write_i64_wp hSh hW self i) with ⟨a, ha, t', hat, ht'⟩ | ⟨e, _, t', hfalse, _⟩
  · cases hat
    refine ⟨t', ha, ?_⟩
    rw [ht', List.map_append, leb128_eq_varint, zz_eq_zigzag]
  · cases hfalse

/-! ## The readers -/

/-- (D, compact i32) On `Spec.varint (Spec.zigzag v) ++ rest` (any `i32` value `v`), `read_i32` returns `v` and
leaves `rest`. -/
theorem read_i32_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (v : Int) (hv : Spec.InI32 v) (bs rest : List U8)
    (hbs : bs.map (·.val) = (Spec.varint (Spec.zigzag v)).map UInt8.toNat) (h : rem self.transport = bs ++ rest) :
    ∃ (t' : T) (x : I32), protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32 inst
        self = ok (.Ok x, { self with transport := t' }) ∧ x.val = v ∧ rem t' = rest := by
  have hlt : Spec.zigzag v < 2 ^ UScalarTy.U32.numBits := by
    rw [UScalarTy.U32_numBits_eq]; exact Spec.zigzag_lt32 hv
  obtain ⟨t', hrv, ht'⟩ := read_varint32_D hS hR self (UScalar.ofNatCore (Spec.zigzag v) hlt) bs rest
    (by rw [UScalar.ofNatCore_val_eq, encVar_eq_varint]; exact hbs) h
  obtain ⟨y, hy, hyv⟩ := zigzag_to_i32_val (UScalar.ofNatCore (Spec.zigzag v) hlt)
  refine ⟨t', y, ?_, ?_, ht'⟩
  · apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32
    aeneas_wp [hrv, core.result.Result.Insts.CoreOpsTry.branch, hy]
  · rw [hyv, UScalar.ofNatCore_val_eq, ← zz_eq_zigzag, unzz_zz]

/-- (D, compact i64) On `Spec.varint (Spec.zigzag v) ++ rest` (any `i64` value `v`), `read_i64` returns `v` and
leaves `rest`. -/
theorem read_i64_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (v : Int) (hv : Spec.InI64 v) (bs rest : List U8)
    (hbs : bs.map (·.val) = (Spec.varint (Spec.zigzag v)).map UInt8.toNat) (h : rem self.transport = bs ++ rest) :
    ∃ (t' : T) (x : I64), protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64 inst
        self = ok (.Ok x, { self with transport := t' }) ∧ x.val = v ∧ rem t' = rest := by
  have hlt : Spec.zigzag v < 2 ^ UScalarTy.U64.numBits := by
    rw [UScalarTy.U64_numBits_eq]; exact Spec.zigzag_lt64 hv
  obtain ⟨t', hrv, ht'⟩ := read_varint64_D hS hR self (UScalar.ofNatCore (Spec.zigzag v) hlt) bs rest
    (by rw [UScalar.ofNatCore_val_eq, encVar_eq_varint]; exact hbs) h
  obtain ⟨y, hy, hyv⟩ := zigzag_to_i64_val (UScalar.ofNatCore (Spec.zigzag v) hlt)
  refine ⟨t', y, ?_, ?_, ht'⟩
  · apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64
    aeneas_wp [hrv, core.result.Result.Insts.CoreOpsTry.branch, hy]
  · rw [hyv, UScalar.ofNatCore_val_eq, ← zz_eq_zigzag, unzz_zz]

end EquivLean.Demo.Thrift.Rust
