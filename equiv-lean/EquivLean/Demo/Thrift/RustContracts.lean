import EquivLean.Demo.Gen.Aeneas.ThriftRs.FunsExternal
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_v_anon15
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_v_anon13
import EquivLean.Demo.Gen.Aeneas.ThriftRs.LibModel_byteorder

/-!
# Thrift (T4), Rust side: the contracts

The Rust theorems are conditional on these stated contracts (PREREG_T_v1 T4; the evidence-owner session's ruling of 10-25 ~17:0xZ):

* transport contracts, the generic `TReadTransport` / `TWriteTransport`: `ReadContract`, `WriteContract`;
* library contracts, MARKED, to be listed with every pair proved under them:
  * `StdContract`: std functions the extraction keeps opaque (`Result::map`, `String::from(&str)`,
    `io::Error::to_string`), as Rust defines them;
  * `OptionContract`: std `Option::ok_or_else` (opaque);
  * `ShiftContract`: std `Shl<i32>` / `Shr<i32>` for `&i16`, `&i32`, `&i64` (varint-rs's zigzag);
  * `VarintContract`: varint-rs `VarintWriter::write_u32_varint` / `write_u64_varint` (trait defaults, not
    extractable) as the `write_varint!` macro;
  * the definitions in `ThriftRs/F_v_anon13.lean` (replacing veriforch's failing module): std
    `io::Cursor<&mut [u8]>` and varint-rs `impl<W: io::Write> VarintWriter for W`;
  * `ByteorderContract`: byteorder `WriteBytesExt::write_i16/i32/i64` and `ReadBytesExt::read_i16/i32/i64` for
    `BigEndian` (trait defaults, opaque), with the instances of `ThriftRs/LibModel_byteorder.lean`;
  * `FmtContract`: std `format!` (`alloc::fmt::format`, opaque) returns a string, `core::hint::must_use` (opaque) is
    the identity: for the error messages of the M rows.
-/

open Aeneas Aeneas.Std Result thrift

namespace EquivLean.Demo.Thrift.Rust

/-- The standard-library functions the Rust readers call and the extraction keeps opaque. -/
structure StdContract : Prop where
  /-- `Result::map` on `Ok` applies the closure. -/
  map_ok : ∀ {T E U F : Type} (inst : core.ops.function.FnOnce F T U) (v : T) (f : F),
    core.result.Result.map (E := E) inst (.Ok v) f = (do
      let u ← inst.call_once f v
      ok (.Ok u))
  /-- `Result::map` on `Err` returns the error. -/
  map_err : ∀ {T E U F : Type} (inst : core.ops.function.FnOnce F T U) (e : E) (f : F),
    core.result.Result.map inst (.Err e : core.result.Result T E) f = ok (.Err e)
  /-- `String::from(&str)` returns. -/
  str_from : ∀ s, ∃ v, alloc.string.String.Insts.CoreConvertFromShared0Str.from s = ok v
  /-- `io::Error::to_string` returns. -/
  io_to_string : ∀ e, ∃ m,
    alloc.string.ToString.Blanket.to_string core.io.error.Error.Insts.CoreFmtDisplay e = ok m

/-- A Rust read transport (`TReadTransport`, i.e. `io::Read`) over the bytes it still holds (`rem`):
`read_exact` into a buffer of `n` bytes returns the next `n` bytes and leaves the rest; with fewer than `n` bytes left
it reports an `UnexpectedEof` error. -/
structure ReadContract {T : Type} (inst : transport.TReadTransport T) (rem : T → List U8) : Prop where
  read_exact_ok : ∀ (t : T) (s : Slice U8), s.length ≤ (rem t).length →
    ∃ t' s', inst.allocioreadReadInst.read_exact t s = ok (.Ok (), t', s') ∧
      s'.val = (rem t).take s.length ∧ rem t' = (rem t).drop s.length
  read_exact_eof : ∀ (t : T) (s : Slice U8), (rem t).length < s.length →
    ∃ e t' s', inst.allocioreadReadInst.read_exact t s = ok (.Err e, t', s') ∧
      core.io.error.Error.kind e = ok .UnexpectedEof

/-- std `Option::ok_or_else`: `Some v` gives `Ok v`; `None` gives `Err` of the closure's value. -/
structure OptionContract : Prop where
  ok_or_else_some : ∀ {T E F : Type} (inst : core.ops.function.FnOnce F Unit E) (v : T) (f : F),
    core.option.Option.ok_or_else inst (some v) f = ok (.Ok v)
  ok_or_else_none : ∀ {T E F : Type} (inst : core.ops.function.FnOnce F Unit E) (f : F),
    core.option.Option.ok_or_else (T := T) inst none f = (do
      let e ← inst.call_once f ()
      ok (.Err e))

/-- A Rust write transport (`TWriteTransport`, i.e. `io::Write`) over the bytes written to it (`sent`): `write` and
`write_all` append all their bytes. -/
structure WriteContract {T : Type} (inst : transport.TWriteTransport T) (sent : T → List U8) : Prop where
  write_ok : ∀ (t : T) (s : Slice U8), ∃ n t', inst.coreiowriteWriteInst.write t s = ok (.Ok n, t') ∧
    sent t' = sent t ++ s.val
  write_all_ok : ∀ (t : T) (s : Slice U8), ∃ t', inst.coreiowriteWriteInst.write_all t s = ok (.Ok (), t') ∧
    sent t' = sent t ++ s.val

/-- std `Shl<i32>` / `Shr<i32>` for `&i16`, `&i32`, `&i64` (shift amount below the width): the bits shifted, the
left shift wrapping, the right shift arithmetic. -/
structure ShiftContract : Prop where
  shl16 : ∀ (x : I16) (s : I32), 0 ≤ s.val → s.val < 16 →
    Shared0I16.Insts.CoreOpsBitShlI32I16.shl x s = ok ⟨x.bv <<< s.val.toNat⟩
  shr16 : ∀ (x : I16) (s : I32), 0 ≤ s.val → s.val < 16 →
    Shared0I16.Insts.CoreOpsBitShrI32I16.shr x s = ok ⟨x.bv.sshiftRight s.val.toNat⟩
  shl32 : ∀ (x : I32) (s : I32), 0 ≤ s.val → s.val < 32 →
    Shared0I32.Insts.CoreOpsBitShlI32I32.shl x s = ok ⟨x.bv <<< s.val.toNat⟩
  shr32 : ∀ (x : I32) (s : I32), 0 ≤ s.val → s.val < 32 →
    Shared0I32.Insts.CoreOpsBitShrI32I32.shr x s = ok ⟨x.bv.sshiftRight s.val.toNat⟩
  shl64 : ∀ (x : I64) (s : I32), 0 ≤ s.val → s.val < 64 →
    Shared0I64.Insts.CoreOpsBitShlI32I64.shl x s = ok ⟨x.bv <<< s.val.toNat⟩
  shr64 : ∀ (x : I64) (s : I32), 0 ≤ s.val → s.val < 64 →
    Shared0I64.Insts.CoreOpsBitShrI32I64.shr x s = ok ⟨x.bv.sshiftRight s.val.toNat⟩

/-- varint-rs `VarintWriter::write_u32_varint` / `write_u64_varint` (trait defaults): the `write_varint!` macro
over the writer's `write`. -/
structure VarintContract : Prop where
  u32 : ∀ {Self E : Type} (inst : varint_rs.VarintWriter Self E) (s : Self) (v : U32),
    varint_rs.VarintWriter.write_u32_varint.default inst s v =
      rusttrn_model.writeBytes inst.write (rusttrn_model.leb128 v.val) s
  u64 : ∀ {Self E : Type} (inst : varint_rs.VarintWriter Self E) (s : Self) (v : U64),
    varint_rs.VarintWriter.write_u64_varint.default inst s v =
      rusttrn_model.writeBytes inst.write (rusttrn_model.leb128 v.val) s

/-- The `w` low bytes of `n`, most significant first (big-endian `n mod 256^w`). -/
def beU8 : Nat → Nat → List U8
  | 0, _ => []
  | w + 1, n => ⟨BitVec.ofNat 8 (n / 256 ^ w)⟩ :: beU8 w n

/-- The big-endian value of bytes. -/
def beValU8 (bs : List U8) : Nat := bs.foldl (fun acc b => 256 * acc + b.val) 0

/-- byteorder 1.5.0, `BigEndian`, on any writer / reader (the trait defaults; opaque in the extraction):
* `WriteBytesExt::write_i16/i32/i64` (io.rs l.1178/1286/1394): `T::write_iN(&mut buf, n); self.write_all(&buf)`: the
  `write_all` of the big-endian bytes of `n as uN` (lib.rs l.770/814/858, `BigEndian::write_uN` l.1978-1990);
* `ReadBytesExt::read_i16/i32/i64` (io.rs l.139/243/347): `self.read_exact(&mut buf)?; Ok(T::read_iN(&buf))` with
  `buf = [0; w]`: an error of `read_exact` is returned, else the big-endian value of the bytes read, `as iN`
  (lib.rs l.546/590/634, `BigEndian::read_uN` l.1940-1952). -/
structure ByteorderContract : Prop where
  write_i16 : ∀ {W : Type} (inst : byteorder.io.WriteBytesExt W) (w : W) (n : I16), ∃ buf : Slice U8,
    buf.val = beU8 2 n.bv.toNat ∧
    byteorder.io.WriteBytesExt.write_i16.default inst byteorder.BigEndian.Insts.ByteorderByteOrder w n =
      inst.coreiowriteWriteInst.write_all w buf
  write_i32 : ∀ {W : Type} (inst : byteorder.io.WriteBytesExt W) (w : W) (n : I32), ∃ buf : Slice U8,
    buf.val = beU8 4 n.bv.toNat ∧
    byteorder.io.WriteBytesExt.write_i32.default inst byteorder.BigEndian.Insts.ByteorderByteOrder w n =
      inst.coreiowriteWriteInst.write_all w buf
  write_i64 : ∀ {W : Type} (inst : byteorder.io.WriteBytesExt W) (w : W) (n : I64), ∃ buf : Slice U8,
    buf.val = beU8 8 n.bv.toNat ∧
    byteorder.io.WriteBytesExt.write_i64.default inst byteorder.BigEndian.Insts.ByteorderByteOrder w n =
      inst.coreiowriteWriteInst.write_all w buf
  read_i16 : ∀ {R : Type} (inst : byteorder.io.ReadBytesExt R) (r : R), ∃ z : Slice U8,
    z.val = List.replicate 2 0#u8 ∧
    byteorder.io.ReadBytesExt.read_i16.default inst byteorder.BigEndian.Insts.ByteorderByteOrder r = (do
      let (res, r', buf) ← inst.allocioreadReadInst.read_exact r z
      match res with
      | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
      | .Err e => ok (.Err e, r'))
  read_i32 : ∀ {R : Type} (inst : byteorder.io.ReadBytesExt R) (r : R), ∃ z : Slice U8,
    z.val = List.replicate 4 0#u8 ∧
    byteorder.io.ReadBytesExt.read_i32.default inst byteorder.BigEndian.Insts.ByteorderByteOrder r = (do
      let (res, r', buf) ← inst.allocioreadReadInst.read_exact r z
      match res with
      | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
      | .Err e => ok (.Err e, r'))
  read_i64 : ∀ {R : Type} (inst : byteorder.io.ReadBytesExt R) (r : R), ∃ z : Slice U8,
    z.val = List.replicate 8 0#u8 ∧
    byteorder.io.ReadBytesExt.read_i64.default inst byteorder.BigEndian.Insts.ByteorderByteOrder r = (do
      let (res, r', buf) ← inst.allocioreadReadInst.read_exact r z
      match res with
      | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
      | .Err e => ok (.Err e, r'))

/-- std `alloc::fmt::format` (`format!`) returns a string; `core::hint::must_use` returns its argument. -/
structure FmtContract : Prop where
  format_ok : ∀ a, ∃ s, alloc.fmt.format a = ok s
  must_use : ∀ {T : Type} (x : T), core.hint.must_use x = ok x

end EquivLean.Demo.Thrift.Rust
