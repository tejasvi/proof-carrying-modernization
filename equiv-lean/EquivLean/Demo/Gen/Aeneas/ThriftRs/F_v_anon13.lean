-- MARKED LIBRARY MODEL (rusttrn, T4), NOT GENERATED. This file replaces veriforch's generated F_v_anon13
-- (manifest ~/veriforch/notes/thrift/T1_rsts_gen_manifest.tsv, original
-- ~/veriforch/runs/thrift_rs/lean_rust_rev/v0/Gen/default/Thrift_rs/F_v_anon13.lean, sha256
-- 7189b33611dc43d3503813ddb7ce5b13623c36036c8e4878b3b4be85199ecb43, kept unchanged and uncompiled next to this file as
-- F_v_anon13.lean.veriforch). The original (`impl io::Write for Cursor<&mut [u8]>`) does not check: its methods are
-- the opaque declarations' triples (with a backward function) where `core.io.write.Write` expects pairs. The compact
-- writers also call `Cursor::new` and the `VarintWriter` methods with the backward functions of the `&mut [u8]`
-- borrow, unlike their opaque declarations, and the blanket `impl<W: io::Write> VarintWriter for W` (F_v_anon123)
-- does not check either.
--
-- This module gives, in namespace `thrift` (the writers' call sites resolve to these names before the root
-- declarations), models of two libraries; every pair proved under them lists this module (ThriftRs.F_v_anon13):
--   * std `io::Cursor<&mut [u8]>` (rustc library/core/src/io/cursor.rs: `Cursor::new` l.101, `position` l.185,
--     `impl Write for Cursor<&mut [u8]>` l.363-394 with `slice_write`; io's default `write_all`): the buffer and the
--     position;
--   * varint-rs 2.2.1 (vendor/varint-rs/src/lib.rs) `impl<W: io::Write> VarintWriter for W` (l.404-419): its `write` is
--     veriforch's generated body; the `write_uN_varint` methods are the `write_varint!` macro (l.270-290, not
--     extractable: an early return inside a loop): the LEB128 bytes of the value, one `write` each, the first error
--     returned; the signed methods are the generated trait defaults (zigzag, then the unsigned method).
-- The cursor travels with the identity backward function of its borrow (`CursorW`), as the generated code
-- destructures it.
module
public import Aeneas
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.Types
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.Support
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.FunsExternal
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_v_impl_varint_rs__VarintWriter_core__io__error__Error__for_W___write
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_VarintWriter__write_i8_varint
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_VarintWriter__write_i16_varint
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_VarintWriter__write_i32_varint
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_VarintWriter__write_i64_varint
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_VarintWriter__write_i128_varint
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_VarintWriter__write_isize_varint
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace thrift

/-! ## `io::Cursor<&mut [u8]>` (std), modelled -/

/-- A `Cursor<&mut [u8]>`: the slice's bytes and the position. -/
structure rusttrn_model.CursorM where
  buf : List Std.U8
  pos : Nat

/-- The cursor as the writers pass it, with the (identity) backward function of its borrow. -/
abbrev rusttrn_model.CursorW := rusttrn_model.CursorM × (rusttrn_model.CursorM → rusttrn_model.CursorM)

/-- `slice_write` (std `io::cursor`): `pos = min(pos, len)`; `(&mut slice[pos..]).write(buf)` copies
`amt = min(len - pos, buf.len())` bytes; the position advances by `amt`. -/
def rusttrn_model.cursorWrite (c : rusttrn_model.CursorM) (s : List Std.U8) : rusttrn_model.CursorM × Nat :=
  let p := min c.pos c.buf.length
  let k := min (c.buf.length - p) s.length
  (⟨c.buf.take p ++ s.take k ++ c.buf.drop (p + k), c.pos + k⟩, k)

/-- The error `write_all` returns when the slice is full (`ErrorKind::WriteZero`); its value is not modelled. -/
opaque rusttrn_model.writeZeroErr : Result core.io.error.Error

/-- `Cursor::new(&mut buf[..])`: position 0; the backward function gives the slice its bytes back. -/
def core.io.cursor.Cursor.new (s : Slice Std.U8) :
    Result (rusttrn_model.CursorW × (rusttrn_model.CursorM → Slice Std.U8)) :=
  ok ((⟨s.val, 0⟩, id), fun c => if h : c.buf.length ≤ Usize.max then Slice.from c.buf h else s)

/-- `Cursor::position`. -/
def core.io.cursor.Cursor.position (c : rusttrn_model.CursorM) : Result Std.U64 :=
  ok ⟨BitVec.ofNat 64 c.pos⟩

/-- `impl io::Write for Cursor<&mut [u8]>`: `write` is `slice_write`; `write_all` is io's default (write until
done; a write of 0 bytes is the error `WriteZero`); `flush` does nothing. -/
@[reducible]
def core.io.cursor.CursorMut0SliceU8.Insts.CoreIoWriteWrite :
    core.io.write.Write rusttrn_model.CursorW := {
  write := fun w s =>
    let (c', k) := rusttrn_model.cursorWrite w.1 s.val
    ok (.Ok ⟨BitVec.ofNat UScalarTy.Usize.numBits k⟩, (c', w.2))
  flush := fun w => ok (.Ok (), w)
  write_all := fun w s =>
    let (c', k) := rusttrn_model.cursorWrite w.1 s.val
    if k = s.val.length then ok (.Ok (), (c', w.2))
    else do
      let e ← rusttrn_model.writeZeroErr
      ok (.Err e, (c', w.2))
}

/-! ## varint-rs `impl<W: io::Write> VarintWriter for W`, modelled -/

/-- The LEB128 bytes of `n`: 7-bit groups, least significant first, the high bit set on all but the last. -/
def rusttrn_model.leb128 (n : Nat) : List Std.U8 :=
  if n < 128 then [⟨BitVec.ofNat 8 n⟩] else ⟨BitVec.ofNat 8 (n % 128 + 128)⟩ :: rusttrn_model.leb128 (n / 128)
termination_by n
decreasing_by omega

/-- `write_varint!` over a `VarintWriter::write`: one write per byte; an error on a byte before the last is
returned at once; the last write's result is the result. -/
def rusttrn_model.writeBytes {W E : Type} (wr : W → Std.U8 → Result ((core.result.Result Unit E) × W)) :
    List Std.U8 → W → Result ((core.result.Result Unit E) × W)
  | [], w => ok (.Ok (), w)
  | [b], w => wr w b
  | b :: bs, w => do
    let (r, w') ← wr w b
    match r with
    | .Ok _ => rusttrn_model.writeBytes wr bs w'
    | .Err e => ok (.Err e, w')

/-- The unsigned methods (`write_varint!`) on the generated `write`; the signed ones are placeholders here and are
replaced by the generated trait defaults in `varint_rs.VarintWriterWError.Blanket`. -/
def rusttrn_model.blanketBase {W : Type} (coreiowriteWriteInst : core.io.write.Write W) :
    varint_rs.VarintWriter W core.io.error.Error :=
  let wr := varint_rs.VarintWriterWError.Blanket.write coreiowriteWriteInst
  { write := wr
    write_i8_varint := fun s _ => ok (.Ok (), s)
    write_u8_varint := fun s v => rusttrn_model.writeBytes wr (rusttrn_model.leb128 v.val) s
    write_i16_varint := fun s _ => ok (.Ok (), s)
    write_u16_varint := fun s v => rusttrn_model.writeBytes wr (rusttrn_model.leb128 v.val) s
    write_i32_varint := fun s _ => ok (.Ok (), s)
    write_u32_varint := fun s v => rusttrn_model.writeBytes wr (rusttrn_model.leb128 v.val) s
    write_i64_varint := fun s _ => ok (.Ok (), s)
    write_u64_varint := fun s v => rusttrn_model.writeBytes wr (rusttrn_model.leb128 v.val) s
    write_i128_varint := fun s _ => ok (.Ok (), s)
    write_u128_varint := fun s v => rusttrn_model.writeBytes wr (rusttrn_model.leb128 v.val) s
    write_isize_varint := fun s _ => ok (.Ok (), s)
    write_usize_varint := fun s v => rusttrn_model.writeBytes wr (rusttrn_model.leb128 v.val) s }

/-- `impl<W: io::Write> VarintWriter for W` (varint-rs): the unsigned methods modelled, the signed methods the
generated defaults over them. -/
@[reducible]
def varint_rs.VarintWriterWError.Blanket {W : Type} (coreiowriteWriteInst : core.io.write.Write W) :
    varint_rs.VarintWriter W core.io.error.Error :=
  let base := rusttrn_model.blanketBase coreiowriteWriteInst
  { base with
    write_i8_varint := varint_rs.VarintWriter.write_i8_varint.default base
    write_i16_varint := varint_rs.VarintWriter.write_i16_varint.default base
    write_i32_varint := varint_rs.VarintWriter.write_i32_varint.default base
    write_i64_varint := varint_rs.VarintWriter.write_i64_varint.default base
    write_i128_varint := varint_rs.VarintWriter.write_i128_varint.default base
    write_isize_varint := varint_rs.VarintWriter.write_isize_varint.default base }

end thrift
