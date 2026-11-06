-- MARKED LIBRARY MODEL (rusttrn, T4), NOT GENERATED. veriforch's binary-protocol modules
-- (manifest ~/veriforch/notes/thrift/T1_rsts_gen_manifest.tsv: binary read_i16/i32/i64, write_i16/i32/i64,
-- read_binary_len) name three byteorder 1.5.0 constants that no generated module defines:
--   * `byteorder::BigEndian`'s `impl ByteOrder` (vendor/byteorder/src/lib.rs l.1812-1819, l.1938-);
--   * `impl<R: io::Read + ?Sized> ReadBytesExt for R {}` (vendor/byteorder/src/io.rs l.1049);
--   * `impl<W: io::Write + ?Sized> WriteBytesExt for W {}` (io.rs l.1579).
-- The copies of those modules in this directory import this one (one added import line each, marked in each file).
--
-- The binary protocol calls the trait defaults `WriteBytesExt::write_i16/i32/i64` and `ReadBytesExt::read_i16/i32/i64`,
-- which the extraction keeps opaque (FunsExternal), at these instances. The behaviour the theorems assume of them is the
-- library contract `ByteorderContract` (EquivLean/Demo/Thrift/RustContracts.lean); every pair proved under it lists
-- that contract and this module (ThriftRs.LibModel_byteorder). The instances here only name the Rust impls:
--   * `BigEndian` is an uninhabited enum: its derived traits are vacuous, `Default` panics (lib.rs l.1815-1819);
--   * the blanket impls carry their `io::Read` / `io::Write` instance (the parent the generated code passes);
--   * the trait methods are not modelled: each is an unknown function (`rusttrn_model.unmodelled`, one per name), so
--     no theorem can depend on them.
module
public import Aeneas
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.Types
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.Support
public import EquivLean.Demo.Gen.Aeneas.ThriftRs.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

universe u

namespace thrift

/-- A library function this model does not describe: an unknown value, one per name. -/
opaque rusttrn_model.unmodelled (fn : String) (α : Sort u) [Inhabited α] : α

/-- `PartialEq` for the uninhabited `BigEndian` (derived). -/
def rusttrn_model.bePartialEq : core.cmp.PartialEq byteorder.BigEndian byteorder.BigEndian :=
  { eq := fun x _ => nomatch x }

/-- `PartialOrd` for the uninhabited `BigEndian` (derived). -/
def rusttrn_model.bePartialOrd : core.cmp.PartialOrd byteorder.BigEndian byteorder.BigEndian :=
  { partialEqInst := rusttrn_model.bePartialEq, partial_cmp := fun x _ => nomatch x }

/-- `impl ByteOrder for BigEndian`: the derived traits of an uninhabited enum, `Default` panicking, the methods
unknown. -/
def byteorder.BigEndian.Insts.ByteorderByteOrder : byteorder.ByteOrder byteorder.BigEndian := {
  corecloneCloneInst := { clone := fun x => nomatch x }
  coremarkerCopyInst := { cloneInst := { clone := fun x => nomatch x } }
  corefmtDebugInst := { fmt := fun x _ => nomatch x }
  coredefaultDefaultInst := { default := fail .panic }
  corecmpEqInst := { partialEqInst := rusttrn_model.bePartialEq }
  corehashHashInst := { hash := fun _ x _ => nomatch x }
  corecmpOrdInst := { eqInst := { partialEqInst := rusttrn_model.bePartialEq },
                      partialOrdInst := rusttrn_model.bePartialOrd, cmp := fun x _ => nomatch x }
  corecmpPartialEqInst := rusttrn_model.bePartialEq
  corecmpPartialOrdInst := rusttrn_model.bePartialOrd
  privateSealedInst := {}
  read_u16 := rusttrn_model.unmodelled "BigEndian::read_u16" _
  read_u32 := rusttrn_model.unmodelled "BigEndian::read_u32" _
  read_u64 := rusttrn_model.unmodelled "BigEndian::read_u64" _
  read_u128 := rusttrn_model.unmodelled "BigEndian::read_u128" _
  read_uint := rusttrn_model.unmodelled "BigEndian::read_uint" _
  read_uint128 := rusttrn_model.unmodelled "BigEndian::read_uint128" _
  write_u16 := rusttrn_model.unmodelled "BigEndian::write_u16" _
  write_u32 := rusttrn_model.unmodelled "BigEndian::write_u32" _
  write_u64 := rusttrn_model.unmodelled "BigEndian::write_u64" _
  write_u128 := rusttrn_model.unmodelled "BigEndian::write_u128" _
  write_uint := rusttrn_model.unmodelled "BigEndian::write_uint" _
  write_uint128 := rusttrn_model.unmodelled "BigEndian::write_uint128" _
  read_i32 := rusttrn_model.unmodelled "BigEndian::read_i32" _
  read_u16_into := rusttrn_model.unmodelled "BigEndian::read_u16_into" _
  read_u32_into := rusttrn_model.unmodelled "BigEndian::read_u32_into" _
  read_u64_into := rusttrn_model.unmodelled "BigEndian::read_u64_into" _
  read_u128_into := rusttrn_model.unmodelled "BigEndian::read_u128_into" _
  write_u16_into := rusttrn_model.unmodelled "BigEndian::write_u16_into" _
  write_u32_into := rusttrn_model.unmodelled "BigEndian::write_u32_into" _
  write_u64_into := rusttrn_model.unmodelled "BigEndian::write_u64_into" _
  write_u128_into := rusttrn_model.unmodelled "BigEndian::write_u128_into" _
  from_slice_u16 := rusttrn_model.unmodelled "BigEndian::from_slice_u16" _
  from_slice_u32 := rusttrn_model.unmodelled "BigEndian::from_slice_u32" _
  from_slice_u64 := rusttrn_model.unmodelled "BigEndian::from_slice_u64" _
  from_slice_u128 := rusttrn_model.unmodelled "BigEndian::from_slice_u128" _
  from_slice_f32 := rusttrn_model.unmodelled "BigEndian::from_slice_f32" _
  from_slice_f64 := rusttrn_model.unmodelled "BigEndian::from_slice_f64" _
}

/-- `impl<R: io::Read + ?Sized> ReadBytesExt for R {}`: the reader's `io::Read`, the methods unknown. -/
def byteorder.io.ReadBytesExt.Blanket {R : Type} (allocioreadReadInst : alloc.io.read.Read R) :
    byteorder.io.ReadBytesExt R := {
  allocioreadReadInst := allocioreadReadInst
  read_u8 := rusttrn_model.unmodelled "ReadBytesExt::read_u8" _
  read_i8 := rusttrn_model.unmodelled "ReadBytesExt::read_i8" _
  read_i16 := rusttrn_model.unmodelled "ReadBytesExt::read_i16" _
  read_i32 := rusttrn_model.unmodelled "ReadBytesExt::read_i32" _
  read_i64 := rusttrn_model.unmodelled "ReadBytesExt::read_i64" _
  read_f64 := rusttrn_model.unmodelled "ReadBytesExt::read_f64" _
}

/-- `impl<W: io::Write + ?Sized> WriteBytesExt for W {}`: the writer's `io::Write`, the methods unknown. -/
def byteorder.io.WriteBytesExt.Blanket {W : Type} (coreiowriteWriteInst : core.io.write.Write W) :
    byteorder.io.WriteBytesExt W := {
  coreiowriteWriteInst := coreiowriteWriteInst
  write_u8 := rusttrn_model.unmodelled "WriteBytesExt::write_u8" _
  write_i8 := rusttrn_model.unmodelled "WriteBytesExt::write_i8" _
  write_i16 := rusttrn_model.unmodelled "WriteBytesExt::write_i16" _
  write_u32 := rusttrn_model.unmodelled "WriteBytesExt::write_u32" _
  write_i32 := rusttrn_model.unmodelled "WriteBytesExt::write_i32" _
  write_i64 := rusttrn_model.unmodelled "WriteBytesExt::write_i64" _
  write_f64 := rusttrn_model.unmodelled "WriteBytesExt::write_f64" _
}

end thrift
