import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__compact__TCompactInputP_2c577b86dbb36b1d
import EquivLean.Demo.Thrift.RustRead
import EquivLean.Demo.Thrift.RustWrite
import EquivLean.Demo.Thrift.RustZigzag
import EquivLean.Demo.Thrift.Spec

/-!
# Thrift (T4), Rust side: the field header on the named inputs

The spec's named inputs (`Spec.exDelta15`, `Spec.exI16Overflow`), run on the Rust writer and reader (Aeneas's
semantics):

* (a) `write_field_header` on `exDelta15` appends `[0x05, 0x1E]`; the spec gives `[0xF5]`;
* (b) `write_field_header` on `exI16Overflow` panics (the `i16` delta overflows; a release build would wrap to delta
  1 and write `[0x15]`, which is not on this semantics);
* (c) `read_field_begin` on `[0x15]` after id 32767 returns the protocol error "field id overflow";
* (d) `read_field_begin` on `[0x05, 0x1E]` after id 0 returns the field (I32, 15).
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-- (c) The one-byte header `0x15` (delta 1, type I32) after field id 32767: `checked_add` overflows and
`read_field_begin` returns `InvalidData` "field id overflow". -/
theorem read_field_begin_exI16Overflow_short (hS : StdContract) (hO : OptionContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (rest : List U8)
    (hlast : self.last_read_field_id = 32767#i16) (h : rem self.transport = 0x15#u8 :: rest) :
    ∃ t' m, protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin inst
        self = ok (.Err (.Protocol { kind := .InvalidData, message := m }), { self with transport := t' }) ∧
      rem t' = rest := by
  obtain ⟨t', hrb, ht'⟩ := read_byte_ok hS hR self _ _ h
  obtain ⟨m, hm⟩ := hS.str_from (toStr "field id overflow")
  refine ⟨t', m, ?_, ht'⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
  have h1 : (21#u8 &&& 240#u8 : U8) = 16#u8 := by decide
  have h2 : (16#u8 : U8) >>> (4#i32) = ok 1#u8 := by
    show UScalar.shiftRight_IScalar 16#u8 4#i32 = ok 1#u8
    simp [UScalar.shiftRight_IScalar, UScalar.shiftRight]
    rfl
  have h3 : (21#u8 &&& 15#u8 : U8) = 5#u8 := by decide
  have hty : protocol.compact.u8_to_type 5#u8 = ok (.Ok .I32) := by
    unfold protocol.compact.u8_to_type
    rfl
  aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, h1, h2, h3]
  split
  · rename_i heq
    exact absurd heq (by decide)
  · rename_i heq
    exact absurd heq (by decide)
  · have h4 : self.last_read_field_id.checked_add (UScalar.hcast IScalarTy.I16 1#u8) = none := by
      rw [hlast]
      decide
    aeneas_wp [hty, core.result.Result.Insts.CoreOpsTry.branch, h4, hO.ok_or_else_none,
      protocol.compact.TInputProtocolTCompactInputProtocol.read_field_begin.closure.Insts.CoreOpsFunctionFnOnceTupleError,
      protocol.compact.TInputProtocolTCompactInputProtocol.read_field_begin.closure.Insts.CoreOpsFunctionFnOnceTupleError.call_once,
      errors.ProtocolError.new, core.convert.IntoFrom, core.convert.IntoFrom.into, hm,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    simp

/-- (d) The long form `[0x05, 0x1E]` (type I32, zigzag varint 30) after field id 0: `read_field_begin` returns
the field (I32, 15) and leaves the rest; so Rust's long form for delta 15 interoperates. -/
theorem read_field_begin_exDelta15_long (hS : StdContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (rest : List U8)
    (h : rem self.transport = 0x05#u8 :: 0x1E#u8 :: rest) :
    ∃ t', protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin inst
        self = ok (.Ok { «name» := none, field_type := .I32, id := some 15#i16 },
          { self with transport := t', last_read_field_id := 15#i16 }) ∧ rem t' = rest := by
  obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self _ _ h
  obtain ⟨t2, hrv, ht2⟩ := read_varint32_D hS hR { self with transport := t1 } 30#u32 [0x1E#u8] rest
    (by rw [encVar, ite_eq_left (by decide)]; rfl) (by rw [ht1]; rfl)
  refine ⟨t2, ?_, ht2⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
  have h1 : (5#u8 &&& 240#u8 : U8) = 0#u8 := by decide
  have h2 : (0#u8 : U8) >>> (4#i32) = ok 0#u8 := by
    show UScalar.shiftRight_IScalar 0#u8 4#i32 = ok 0#u8
    simp [UScalar.shiftRight_IScalar, UScalar.shiftRight]
    rfl
  have h3 : (5#u8 &&& 15#u8 : U8) = 5#u8 := by decide
  have hty : protocol.compact.u8_to_type 5#u8 = ok (.Ok .I32) := by
    unfold protocol.compact.u8_to_type
    rfl
  have hzz : protocol.compact.zigzag_to_i32 30#u32 = ok 15#i32 := by
    obtain ⟨x, hx, hxv⟩ := zigzag_to_i32_val 30#u32
    rw [hx, show x = 15#i32 from IScalar.eq_of_val_eq (by rw [hxv]; decide)]
  aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, h1, h2, h3]
  split
  · rename_i heq
    exact absurd heq (by decide)
  · rename_i heq
    exact absurd heq (by decide)
  · have hcast : IScalar.cast IScalarTy.I16 (15#i32 : I32) = 15#i16 := by decide
    aeneas_wp [hty, core.result.Result.Insts.CoreOpsTry.branch, not_true_eq_false, _root_.ite_false,
      protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16, hrv, hzz, hcast]

/-- (a) `Spec.exDelta15` (previous id 0, id 15, type 5) on Rust's `write_field_header`: it appends the bytes
`[0x05, 0x1E]`, where the spec gives `[0xF5]`. DISCREPANCY. -/
theorem write_field_header_exDelta15 (hS : StdContract) (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T)
    (hlast : self.last_write_field_id.val = Spec.exDelta15.last) :
    (∃ t', protocol.compact.TCompactOutputProtocol.write_field_header inst self
        (UScalar.ofNatCore Spec.exDelta15.ty (by decide)) (IScalar.ofIntCore Spec.exDelta15.id (by decide)) =
        ok (.Ok (), { self with transport := t', last_write_field_id := 15#i16 }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++ [0x05, 0x1E]) ∧
    (Spec.fieldHeader Spec.exDelta15.last Spec.exDelta15.id Spec.exDelta15.ty).map (·.toNat) = [0xF5] := by
  refine ⟨?_, by rw [Spec.fieldHeader_exDelta15]; rfl⟩
  have hl : self.last_write_field_id = 0#i16 := IScalar.eq_of_val_eq (by rw [hlast]; rfl)
  obtain ⟨t', ho, ht', -⟩ := write_field_header_delta15_example hS hSh hW self hl
  exact ⟨t', ho, ht'⟩

/-- (b) `Spec.exI16Overflow` (previous id 32767, id -32768, type 5) on Rust's `write_field_header`: the `i16`
delta `-32768 - 32767` overflows and Aeneas panics (the spec gives `[0x05, 0xFF, 0xFF, 0x03]`; a release build
would wrap the delta to 1 and write `[0x15]`, which `Spec.readFieldHeader_exI16Overflow_short` reads as malformed;
the release behaviour is not on this semantics). -/
theorem write_field_header_exI16Overflow {T : Type} (inst : transport.TWriteTransport T)
    (self : protocol.compact.TCompactOutputProtocol T)
    (hlast : self.last_write_field_id.val = Spec.exI16Overflow.last) :
    protocol.compact.TCompactOutputProtocol.write_field_header inst self
        (UScalar.ofNatCore Spec.exI16Overflow.ty (by decide))
        (IScalar.ofIntCore Spec.exI16Overflow.id (by decide)) = fail .integerOverflow ∧
    (Spec.fieldHeader Spec.exI16Overflow.last Spec.exI16Overflow.id Spec.exI16Overflow.ty).map (·.toNat) =
      [0x05, 0xFF, 0xFF, 0x03] := by
  refine ⟨write_field_header_overflow inst self _ _ ?_, by rw [Spec.fieldHeader_exI16Overflow]; rfl⟩
  rw [hlast, IScalar.ofInt_val_eq]
  decide

end EquivLean.Demo.Thrift.Rust
