# T4 rows for checking (Apache Thrift's wire protocol in C++, Java and Rust)

The per-pair results, every theorem name per pair and language, and each language's contracts are in the README
section "Apache Thrift's wire protocol in C++, Java and Rust". This file adds what a replay needs: the commits, the
named inputs as byte literals, the discrepancy theorems with the hypotheses their statements take, and the build.

## Commits

Integration branch `t4-final` from 751764f (the headline commit): the merges of the column branches below, one
README section, and one rename: in `Java/BinW.lean` (binary `writeI16`, from `t4-java-rt`) the helpers `wi16Ref`,
`wi16N`, `wi16SpecI`, `wi16_body` became `bwi16Ref`, `bwi16N`, `bwi16SpecI`, `bwi16_body`, because the compact
protocol's `writeI16` helpers on `t4-java` (`WfD.lean`, `Wi16.lean`) have the same names and a module importing
both failed. Theorem names are unchanged. Column branches: specification `t4-spec` f93f948
(`EquivLean/Demo/Thrift/Spec.lean`, identical on every branch); C++ `t4-cpp` 64c9183; Java `t4-java` 14956e7,
`t4-java-rt` ce981c6 (binary integers, 64-bit varint writer), `t4-java-coll` bdc58ab (list/set header); Rust
`t4-rust` fed0c3b. Thrift f0eb8b84e. Java classes: `thrift-java-f0eb8b84.jar`, sha256
`d7b84d858ad0d6c6bcc18a305c08a5e85e351199b76e31ff4e1a4e8ea77bb143` (262 classes; the drop-in has those and the 15
lambda classes Soot adds, 277). Front ends: cirlean 28e2380 (C++), JimpleLean 20261025T0149Z with Soot 4.7.1 (Java),
Charon 0.1.293 and Aeneas fdebf20 (Rust).

## Named inputs (`Spec.lean` l.910-956)

| name | bytes / values |
|---|---|
| `exDelta15` | field header input: previous id 0, id 15, type 5 (I32); the specification's bytes `[0xF5]` |
| `exI16Overflow` | previous id 32767, id -32768, type 5; the specification's bytes `[0x05, 0xFF, 0xFF, 0x03]` |
| `exVarint32Exceeds` | `[0x85, 0x80, 0x80, 0x80, 0x10]` (value 2^32 + 5) |
| `exVarint64Exceeds` | `[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]` (value 2^64) |
| `exVarint32Overlong` | `[0x80, 0x80, 0x80, 0x80, 0x80]` |
| `exStopNibble` | `[0x10]`, read after id 0 |
| `exIdOutOfRange` | `[0x05, 0x80, 0x80, 0x04]`, read after id 0 (id 32768) |
| `exNegSize` | `[0xF5, 0x80, 0x80, 0x80, 0x80, 0x08]` (list size 2^31) |

Unnamed inputs of the discrepancy table: `[0x15]` read after id 32767; `[0x80, 0x80, 0x80, 0x80, 0x80, 0x00]`;
the list header `[0x0D]` (size 0, element nibble 13 = UUID).

## Discrepancy theorems and the hypotheses their statements name

Extracted from each statement's text (the binders before `:=`); a replay prints the statements themselves.

| row | C++ (`EquivLean.Demo.Thrift.Cpp`) | Java (`EquivLean.Demo.Thrift.Java`) | Rust (`EquivLean.Demo.Thrift.Rust`) |
|---|---|---|---|
| W1 `exDelta15` | `writeFieldBeginInternal_exDelta15` (FieldHeader): WriteContract, cTypeTable | `wfb_exDelta15` (WfbP): tContracts, Contains, NoRedeclW, CPAt | `write_field_header_exDelta15` (RustField): WriteContract, StdContract, ShiftContract |
| W2 `exI16Overflow` | `writeFieldBeginInternal_exI16Overflow` (FieldHeader): WriteContract, cTypeTable | `wfb_exI16Overflow` (WfbP): tContracts, Contains, NoRedeclW, CPAt | `write_field_header_exI16Overflow` (RustField): none (the subtraction fails first) |
| R1 `[0x15]` after 32767 | `readFieldBegin_exI16Overflow_short` (FieldRead): ReadContract | `rfb_I16Overflow_short` (FhRD): tContracts, Contains, NoRedeclR, CPAt | `read_field_begin_exI16Overflow_short` (RustField): ReadContract, StdContract, OptionContract |
| R2 `exStopNibble` | `readFieldBegin_exStopNibble` (FieldRead): ReadContract | `rfb_exStopNibble` (FhRD): tContracts, Contains, NoRedeclR, CPAt | `rust_exStopNibble` (RustMalformed): ReadContract, StdContract |
| R3 `exIdOutOfRange` | `readFieldBegin_exIdOutOfRange` (FieldRead): ReadContract | `rfb_exIdOutOfRange` (FhRD): tContracts, Contains, NoRedeclR, CPAt | `rust_exIdOutOfRange` (RustMalformed): ReadContract, StdContract |
| V1 `exVarint32Overlong` | `readVarint32_exVarint32Overlong` (Eof): ReadContract, EofContract | `rv32_exVarint32Overlong` (Rv32P): tContracts, Contains, CPAt | `rust_exVarint32Overlong` (RustMalformed): ReadContract, StdContract |
| V2 `[0x80 x5, 0x00]` | `readVarint32_overlong6` (VarintRead32): ReadContract | `rv32_exVarint32Overlong` (any continuation) | `rust_exVarint32Overlong` (any continuation) |
| L1 `[0x0D]` | `readListBegin_D` (ListRead) at nibble 13: ReadContract, CheckContract, vtProto | `rlb_uuid` (RlbP): tContracts, Contains, NoRedeclL, CPAt | `read_list_set_begin_D` (RustList): ReadContract, StdContract |
| agreement `exNegSize` | `readListBegin_exNegSize` (NegSize): ReadContract, ExnProgram (message on cirlean's `std::string` model) | `rlb_exNegSize` (RlbP): tContracts, Contains, NoRedeclL, CPAt | `rust_exNegSize` (RustMalformed): ReadContract, StdContract, FmtContract |

Java's program hypotheses for Thrift's own program: `thrift_fh_hyps` (Contains, NoRedeclR, NoRedeclW; field header)
and `thrift_classes_length` (`EquivLean.Gen.ThriftJ.prog.classes.length = 277`) in `Java/ThriftProg.lean`,
`thrift_coll_hyps` (Contains, NoRedeclL, NoRedeclS, NoRedeclW; list/set: `rlb_*` take NoRedeclL, `rsb_*` NoRedeclS,
`wcb_E` NoRedeclW) in `Java/ThriftProgC.lean`, by `decide +kernel` / `rfl` (no `native_decide`). (This list
corrects ac65118's ROWS.md, which named only NoRedeclW for the list/set theorems.)

Since `t4-java-total` (613c77c, JimpleLean 20261025T2312Z) the Java rows also have total versions (`Java/Term/`):
W1 `wfb_exDelta15_total`, W2 `wfb_exI16Overflow_total`, R1 `rfb_I16Overflow_short_total`, R2
`rfb_exStopNibble_total`, R3 `rfb_exIdOutOfRange_total` (the partial theorem's premises plus `TransportTerm`,
`TRepConc`); V1 and V2 `rv32_exVarint32Overlong_total` (plus `TransportTerm`, `TConc`); L1 `rlb_uuid_total` and
the agreement row `rlb_exNegSize_total` (plus `TransportTerm`, `TRepConc`). The contract names are defined in `Cpp/Transport.lean` (+ `Cpp/Eof.lean`, `Cpp/ListRead.lean`),
`Java/Tr.lean`, `RustContracts.lean`; MARKED library contracts and models are listed per language in the README.

## Build

From a checkout of this commit next to `../equivlean_work/vendor` (cirlean-28e2380, coblean-20261024T2306Z,
JimpleLean-20261025T0149Z for ac65118, JimpleLean-20261025T2312Z for t4-java-total, JimpleLean-20261026T2035Z
for master, strictts-a15926a) and
`../equivlean_work/dl/aeneas` (as for 751764f):
`scripts/lrun.sh lake build` builds everything (one Lean thread per module). The T4 modules are
`EquivLean.Demo.Thrift.*` and the drop-ins `EquivLean.Demo.Gen.Cir.Thrift.*`, `EquivLean.Demo.Gen.Jimple.Thrift`,
`EquivLean.Demo.Gen.Aeneas.ThriftRs.*`; `lake build +EquivLean.Demo.Thrift.Cpp.ListRead` (any module) builds one
with its imports. The Java drop-in reads `EquivLean/Demo/Gen/Jimple/thrift/*.jimple` while elaborating (not tracked
by Lake: build from a clean checkout).
