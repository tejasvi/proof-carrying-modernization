import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TOutputProtocol_for_thrift__protocol__binary__TBinaryOutputPr_6240a778646fd27a
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TOutputProtocol_for_thrift__protocol__binary__TBinaryOutputPr_5f1952badb7b1648
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TOutputProtocol_for_thrift__protocol__binary__TBinaryOutputPr_bd63e52f61329ad1
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__binary__TBinaryInputProt_787b54cf694b02b1
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__binary__TBinaryInputProt_bb468cb4e409046c
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__binary__TBinaryInputProt_810db4a9b4d786b7
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__binary___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__binary__TBinaryInputProt_6d81c7598bdbd2e2
import EquivLean.Demo.Thrift.RustBytes

/-!
# Thrift (T4), Rust side: the binary protocol

`write_i16/i32/i64` (binary.rs:509/513/517), `read_i16/i32/i64` (:246/250/254), `write_bytes` (:492),
`read_binary_len` (:97), `read_bytes` (:220) (lib/rs/src/protocol/binary.rs at f0eb8b84e, through Aeneas)
against `Spec.beI16/32/64`, `Spec.readI16/32/64`, `Spec.binLenPrefix`, `Spec.readBinLenPrefix`, under the transport
contracts and the library contract `ByteorderContract` (with the instances of `ThriftRs/LibModel_byteorder.lean`).
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-! ## Bytes and values -/

theorem beU8_map : ∀ (w n : Nat), (beU8 w n).map (·.val) = (Spec.be w n).map UInt8.toNat
  | 0, _ => rfl
  | w + 1, n => by
    simp only [beU8, Spec.be, List.map_cons, beU8_map w n, UInt8.toNat_ofNat']
    rfl

theorem beU8_length : ∀ (w n : Nat), (beU8 w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [beU8, beU8_length w n]

theorem beValU8_of_map (pre : List U8) (l : Spec.Bytes) (h : pre.map (·.val) = l.map UInt8.toNat) :
    beValU8 pre = Spec.beVal l := by
  have e1 : beValU8 pre = (pre.map (·.val)).foldl (fun acc x => 256 * acc + x) 0 := by
    rw [beValU8, List.foldl_map]
  rw [e1, h, List.foldl_map, Spec.beVal]

theorem beVal_be (w n : Nat) : Spec.beVal (Spec.be w n) = n % 256 ^ w := by
  rw [Spec.beVal, Spec.foldl_be]
  simp

theorem toU_toInt {w : Nat} (x : BitVec w) : Spec.toU w x.toInt = x.toNat := by
  unfold Spec.toU
  rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod, Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)]
  simp

/-! ## Writers -/

/-- (E, binary i16) `write_i16` appends `Spec.beI16`: the two bytes of the value, big-endian. -/
theorem bin_write_i16_E (hB : ByteorderContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.binary.TBinaryOutputProtocol T) (i : I16) :
    ∃ t', protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i16 inst self i =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++ (Spec.beI16 i.val).map UInt8.toNat := by
  obtain ⟨buf, hbuf, hd⟩ := hB.write_i16 (byteorder.io.WriteBytesExt.Blanket inst.coreiowriteWriteInst)
    self.transport i
  have hd' : byteorder.io.WriteBytesExt.write_i16.default
      (byteorder.io.WriteBytesExt.Blanket inst.coreiowriteWriteInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport i = inst.coreiowriteWriteInst.write_all self.transport buf := hd
  obtain ⟨t', hwa, ht'⟩ := hW.write_all_ok self.transport buf
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i16
    aeneas_wp [hd', hwa, core.result.Result.map_err_ok]
  · rw [ht', List.map_append, hbuf, beU8_map, Spec.beI16, show Spec.toU 16 i.val = i.bv.toNat from toU_toInt (w := 16) i.bv]

/-- (E, binary i32) `write_i32` appends `Spec.beI32`. -/
theorem bin_write_i32_E (hB : ByteorderContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.binary.TBinaryOutputProtocol T) (i : I32) :
    ∃ t', protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i32 inst self i =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++ (Spec.beI32 i.val).map UInt8.toNat := by
  obtain ⟨buf, hbuf, hd⟩ := hB.write_i32 (byteorder.io.WriteBytesExt.Blanket inst.coreiowriteWriteInst)
    self.transport i
  have hd' : byteorder.io.WriteBytesExt.write_i32.default
      (byteorder.io.WriteBytesExt.Blanket inst.coreiowriteWriteInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport i = inst.coreiowriteWriteInst.write_all self.transport buf := hd
  obtain ⟨t', hwa, ht'⟩ := hW.write_all_ok self.transport buf
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i32
    aeneas_wp [hd', hwa, core.result.Result.map_err_ok]
  · rw [ht', List.map_append, hbuf, beU8_map, Spec.beI32, show Spec.toU 32 i.val = i.bv.toNat from toU_toInt (w := 32) i.bv]

/-- (E, binary i64) `write_i64` appends `Spec.beI64`. -/
theorem bin_write_i64_E (hB : ByteorderContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.binary.TBinaryOutputProtocol T) (i : I64) :
    ∃ t', protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i64 inst self i =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++ (Spec.beI64 i.val).map UInt8.toNat := by
  obtain ⟨buf, hbuf, hd⟩ := hB.write_i64 (byteorder.io.WriteBytesExt.Blanket inst.coreiowriteWriteInst)
    self.transport i
  have hd' : byteorder.io.WriteBytesExt.write_i64.default
      (byteorder.io.WriteBytesExt.Blanket inst.coreiowriteWriteInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport i = inst.coreiowriteWriteInst.write_all self.transport buf := hd
  obtain ⟨t', hwa, ht'⟩ := hW.write_all_ok self.transport buf
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_i64
    aeneas_wp [hd', hwa, core.result.Result.map_err_ok]
  · rw [ht', List.map_append, hbuf, beU8_map, Spec.beI64, show Spec.toU 64 i.val = i.bv.toNat from toU_toInt (w := 64) i.bv]

/-- (E, binary string/binary) For every byte slice, `write_bytes` appends `Spec.binLenPrefix`: the length as a
big-endian `i32` (`len as i32`, so modulo 2^32, as `Spec.beI32` takes it), then the bytes. -/
theorem bin_write_bytes_E (hB : ByteorderContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.binary.TBinaryOutputProtocol T)
    (b : Slice U8) :
    ∃ t', protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_bytes inst self b =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++
        ((Spec.beI32 b.length).map UInt8.toNat ++ b.val.map (·.val)) := by
  obtain ⟨t1, h1, ht1⟩ := bin_write_i32_E hB hW self (UScalar.hcast .I32 (Slice.len b))
  obtain ⟨t2, hwa, ht2⟩ := hW.write_all_ok t1 b
  have hlen : Spec.toU 32 (UScalar.hcast IScalarTy.I32 (Slice.len b)).val = Spec.toU 32 b.length := by
    rw [UScalar.hcast_val_eq, Slice.len_val, IScalarTy.I32_numBits_eq]
    exact Spec.toU_toS 32 _
  refine ⟨t2, ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_bytes
    aeneas_wp [h1, core.result.Result.Insts.CoreOpsTry.branch, hwa, core.result.Result.map_err_ok]
  · rw [ht2, List.map_append, ht1, Spec.beI32, hlen, ← Spec.beI32, List.append_assoc]

/-! ## Readers -/

/-- `read_i16` on a transport holding at least 2 bytes: the big-endian value of the first 2, as `i16`; the rest is
left. -/
theorem bin_read_i16_ok (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (pre rest : List U8) (hpre : pre.length = 2) (h : rem self.transport = pre ++ rest) :
    ∃ t', protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16 inst self =
        ok (.Ok ⟨BitVec.ofNat _ (beValU8 pre)⟩, { self with transport := t' }) ∧ rem t' = rest := by
  obtain ⟨z, hz, hd⟩ := hB.read_i16 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 2 := by simp [Slice.length, hz]
  have hs : z.length ≤ (rem self.transport).length := by rw [hzl, h]; simp [hpre]
  obtain ⟨t', s', hre, hs', ht'⟩ := hR.read_exact_ok self.transport z hs
  have hsv : s'.val = pre := by rw [hs', h, hzl, List.take_left' hpre]
  have hd' : byteorder.io.ReadBytesExt.read_i16.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16
    aeneas_wp [hd', hre, core.result.Result.map_err_ok, hsv]
  · rw [ht', h, hzl, List.drop_left' hpre]

/-- (D, binary i16) On `Spec.beI16 v ++ rest` (any `i16` value `v`), `read_i16` returns `v` and leaves `rest`. -/
theorem bin_read_i16_D (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (v : Int) (hv : Spec.InI16 v) (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.beI16 v).map UInt8.toNat)
    (h : rem self.transport = pre ++ rest) :
    ∃ (t' : T) (x : I16), protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = v ∧ rem t' = rest := by
  have hl : pre.length = 2 := by
    have := congrArg List.length hpre
    simpa [Spec.beI16, Spec.be_length] using this
  obtain ⟨t', hr, ht'⟩ := bin_read_i16_ok hB hR self pre rest hl h
  refine ⟨t', _, hr, ?_, ht'⟩
  show (BitVec.ofNat 16 (beValU8 pre)).toInt = v
  rw [beValU8_of_map _ _ hpre, Spec.beI16, beVal_be,
    Nat.mod_eq_of_lt (by have := Spec.toU_lt 16 v; rwa [show (256 : Nat) ^ 2 = 2 ^ 16 by rfl]),
    BitVec.toInt_ofNat']
  exact Spec.toS_toU16 hv

/-- (M, binary i16) On fewer than 2 bytes, `read_i16` returns the transport error `EndOfFile` (`From<io::Error>` of
the transport's `UnexpectedEof`); `Spec.readI16` is `none` exactly there (`Spec.readI16_eq_none_iff`). -/
theorem bin_read_i16_eof (hS : StdContract) (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (h : (rem self.transport).length < 2) :
    ∃ t' m, protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16 inst self =
        ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  obtain ⟨z, hz, hd⟩ := hB.read_i16 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 2 := by simp [Slice.length, hz]
  obtain ⟨e, t', s', hre, hk⟩ := hR.read_exact_eof self.transport z (by rw [hzl]; exact h)
  obtain ⟨m, hm⟩ := hS.io_to_string e
  have hd' : byteorder.io.ReadBytesExt.read_i16.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', m, ?_⟩
  apply eq_ok_of_wp
  unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16
  aeneas_wp [hd', hre, core.result.Result.map_err_err,
    P.Insts.CoreOpsFunctionFnOnceTupleErrorError, P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    errors.Error.Insts.CoreConvertFromError.from, hk, hm]

/-- `read_i32` on a transport holding at least 4 bytes: the big-endian value of the first 4, as `i32`; the rest is
left. -/
theorem bin_read_i32_ok (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (pre rest : List U8) (hpre : pre.length = 4) (h : rem self.transport = pre ++ rest) :
    ∃ t', protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32 inst self =
        ok (.Ok ⟨BitVec.ofNat _ (beValU8 pre)⟩, { self with transport := t' }) ∧ rem t' = rest := by
  obtain ⟨z, hz, hd⟩ := hB.read_i32 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 4 := by simp [Slice.length, hz]
  have hs : z.length ≤ (rem self.transport).length := by rw [hzl, h]; simp [hpre]
  obtain ⟨t', s', hre, hs', ht'⟩ := hR.read_exact_ok self.transport z hs
  have hsv : s'.val = pre := by rw [hs', h, hzl, List.take_left' hpre]
  have hd' : byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32
    aeneas_wp [hd', hre, core.result.Result.map_err_ok, hsv]
  · rw [ht', h, hzl, List.drop_left' hpre]

/-- (D, binary i32) On `Spec.beI32 v ++ rest` (any `i32` value `v`), `read_i32` returns `v` and leaves `rest`. -/
theorem bin_read_i32_D (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (v : Int) (hv : Spec.InI32 v) (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.beI32 v).map UInt8.toNat)
    (h : rem self.transport = pre ++ rest) :
    ∃ (t' : T) (x : I32), protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = v ∧ rem t' = rest := by
  have hl : pre.length = 4 := by
    have := congrArg List.length hpre
    simpa [Spec.beI32, Spec.be_length] using this
  obtain ⟨t', hr, ht'⟩ := bin_read_i32_ok hB hR self pre rest hl h
  refine ⟨t', _, hr, ?_, ht'⟩
  show (BitVec.ofNat 32 (beValU8 pre)).toInt = v
  rw [beValU8_of_map _ _ hpre, Spec.beI32, beVal_be,
    Nat.mod_eq_of_lt (by have := Spec.toU_lt 32 v; rwa [show (256 : Nat) ^ 4 = 2 ^ 32 by rfl]),
    BitVec.toInt_ofNat']
  exact Spec.toS_toU32 hv

/-- (M, binary i32) On fewer than 4 bytes, `read_i32` returns the transport error `EndOfFile` (`From<io::Error>` of
the transport's `UnexpectedEof`); `Spec.readI32` is `none` exactly there (`Spec.readI32_eq_none_iff`). -/
theorem bin_read_i32_eof (hS : StdContract) (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (h : (rem self.transport).length < 4) :
    ∃ t' m, protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32 inst self =
        ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  obtain ⟨z, hz, hd⟩ := hB.read_i32 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 4 := by simp [Slice.length, hz]
  obtain ⟨e, t', s', hre, hk⟩ := hR.read_exact_eof self.transport z (by rw [hzl]; exact h)
  obtain ⟨m, hm⟩ := hS.io_to_string e
  have hd' : byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', m, ?_⟩
  apply eq_ok_of_wp
  unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i32
  aeneas_wp [hd', hre, core.result.Result.map_err_err,
    P.Insts.CoreOpsFunctionFnOnceTupleErrorError, P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    errors.Error.Insts.CoreConvertFromError.from, hk, hm]

/-- `read_i64` on a transport holding at least 8 bytes: the big-endian value of the first 8, as `i64`; the rest is
left. -/
theorem bin_read_i64_ok (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (pre rest : List U8) (hpre : pre.length = 8) (h : rem self.transport = pre ++ rest) :
    ∃ t', protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64 inst self =
        ok (.Ok ⟨BitVec.ofNat _ (beValU8 pre)⟩, { self with transport := t' }) ∧ rem t' = rest := by
  obtain ⟨z, hz, hd⟩ := hB.read_i64 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 8 := by simp [Slice.length, hz]
  have hs : z.length ≤ (rem self.transport).length := by rw [hzl, h]; simp [hpre]
  obtain ⟨t', s', hre, hs', ht'⟩ := hR.read_exact_ok self.transport z hs
  have hsv : s'.val = pre := by rw [hs', h, hzl, List.take_left' hpre]
  have hd' : byteorder.io.ReadBytesExt.read_i64.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64
    aeneas_wp [hd', hre, core.result.Result.map_err_ok, hsv]
  · rw [ht', h, hzl, List.drop_left' hpre]

/-- (D, binary i64) On `Spec.beI64 v ++ rest` (any `i64` value `v`), `read_i64` returns `v` and leaves `rest`. -/
theorem bin_read_i64_D (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (v : Int) (hv : Spec.InI64 v) (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.beI64 v).map UInt8.toNat)
    (h : rem self.transport = pre ++ rest) :
    ∃ (t' : T) (x : I64), protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = v ∧ rem t' = rest := by
  have hl : pre.length = 8 := by
    have := congrArg List.length hpre
    simpa [Spec.beI64, Spec.be_length] using this
  obtain ⟨t', hr, ht'⟩ := bin_read_i64_ok hB hR self pre rest hl h
  refine ⟨t', _, hr, ?_, ht'⟩
  show (BitVec.ofNat 64 (beValU8 pre)).toInt = v
  rw [beValU8_of_map _ _ hpre, Spec.beI64, beVal_be,
    Nat.mod_eq_of_lt (by have := Spec.toU_lt 64 v; rwa [show (256 : Nat) ^ 8 = 2 ^ 64 by rfl]),
    BitVec.toInt_ofNat']
  exact Spec.toS_toU64 hv

/-- (M, binary i64) On fewer than 8 bytes, `read_i64` returns the transport error `EndOfFile` (`From<io::Error>` of
the transport's `UnexpectedEof`); `Spec.readI64` is `none` exactly there (`Spec.readI64_eq_none_iff`). -/
theorem bin_read_i64_eof (hS : StdContract) (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (h : (rem self.transport).length < 8) :
    ∃ t' m, protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64 inst self =
        ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  obtain ⟨z, hz, hd⟩ := hB.read_i64 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 8 := by simp [Slice.length, hz]
  obtain ⟨e, t', s', hre, hk⟩ := hR.read_exact_eof self.transport z (by rw [hzl]; exact h)
  obtain ⟨m, hm⟩ := hS.io_to_string e
  have hd' : byteorder.io.ReadBytesExt.read_i64.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', m, ?_⟩
  apply eq_ok_of_wp
  unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i64
  aeneas_wp [hd', hre, core.result.Result.map_err_err,
    P.Insts.CoreOpsFunctionFnOnceTupleErrorError, P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    errors.Error.Insts.CoreConvertFromError.from, hk, hm]

/-! ## The binary string/binary length prefix -/

/-- (D) `read_binary_len` (binary) reads the big-endian `i32` length (non-negative, inside the configured string
limit). -/
theorem bin_read_binary_len_D (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (n : Nat) (hn : n < 2 ^ 31)
    (hcfg : ∀ m : Usize, self.config.max_string_size = some m → n ≤ m.val)
    (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.beI32 n).map UInt8.toNat)
    (h : rem self.transport = pre ++ rest) :
    ∃ (t' : T) (len : Usize), protocol.binary.TBinaryInputProtocol.read_binary_len inst self =
        ok (.Ok len, { self with transport := t' }) ∧ len.val = n ∧ rem t' = rest := by
  have hl : pre.length = 4 := by
    have := congrArg List.length hpre
    simpa [Spec.beI32, Spec.be_length] using this
  obtain ⟨z, hz, hd⟩ := hB.read_i32 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 4 := by simp [Slice.length, hz]
  have hs : z.length ≤ (rem self.transport).length := by rw [hzl, h]; simp [hl]
  obtain ⟨t', s', hre, hs', ht'⟩ := hR.read_exact_ok self.transport z hs
  have hsv : s'.val = pre := by rw [hs', h, hzl, List.take_left' hl]
  have hd' : byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  have hx : (⟨BitVec.ofNat _ (beValU8 pre)⟩ : I32).val = n := by
    show (BitVec.ofNat 32 (beValU8 pre)).toInt = n
    rw [beValU8_of_map _ _ hpre, Spec.beI32, beVal_be,
      Nat.mod_eq_of_lt (by have := Spec.toU_lt 32 n; rwa [show (256 : Nat) ^ 4 = 2 ^ 32 by rfl]),
      BitVec.toInt_ofNat']
    exact Spec.toS_toU32 (by unfold Spec.InI32; omega)
  obtain ⟨x, hxv, hrd⟩ : ∃ x : I32, x.val = n ∧ byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = ok (.Ok x, t') := by
    refine ⟨_, hx, ?_⟩
    apply eq_ok_of_wp
    rw [hd']
    aeneas_wp [hre, hsv]
  have hmod : (n : Int) % 2 ^ System.Platform.numBits = n := by
    apply Int.emod_eq_of_lt (by omega)
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hc : (IScalar.hcast UScalarTy.Usize x).val = n := by
    rw [IScalar.hcast_val_eq, hxv]
    have : (n : Int) < 2 ^ UScalarTy.Usize.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega
    rw [Int.emod_eq_of_lt (by omega) this]
    simp
  refine ⟨t', IScalar.hcast UScalarTy.Usize x, ?_, hc, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryInputProtocol.read_binary_len
    have hn0 : ¬ ((n : Int) < 0) := by omega
    aeneas_wp [hrd, core.result.Result.Insts.CoreOpsTry.branch, hxv, hn0,
      configuration.TConfiguration.impl.max_string_size]
    rcases hm : self.config.max_string_size with _ | m
    · simp
    · have := hcfg m hm
      have hn' : ¬ (m.val < n) := by omega
      aeneas_wp [hc, hn']
  · rw [ht', h, hzl, List.drop_left' hl]

/-- (D, binary string/binary) On a transport holding the big-endian `i32` length, the bytes `bs`, and then any bytes
`rest`, `read_bytes` returns `bs` and leaves exactly `rest` (for a length below 2^31 inside the configured limit). -/
theorem bin_read_bytes_D (hS : StdContract) (hB : ByteorderContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.binary.TBinaryInputProtocol T)
    (bs pre rest : List U8) (hlen : bs.length < 2 ^ 31)
    (hcfg : ∀ m : Usize, self.config.max_string_size = some m → bs.length ≤ m.val)
    (hpre : pre.map (·.val) = (Spec.beI32 bs.length).map UInt8.toNat)
    (h : rem self.transport = pre ++ (bs ++ rest)) :
    ∃ (t' : T) (v : alloc.vec.Vec U8),
      protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes inst self =
        ok (.Ok v, { self with transport := t' }) ∧ v.val = bs ∧ rem t' = rest := by
  obtain ⟨t1, len, hrl, hlv, ht1⟩ := bin_read_binary_len_D hB hR self bs.length hlen hcfg pre (bs ++ rest) hpre h
  have hmx : len.val ≤ Usize.max := by scalar_tac
  have hfe : alloc.vec.from_elem core.clone.CloneU8 0#u8 len =
      ok (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)) := by
    unfold alloc.vec.from_elem
    rw [list_clone_ok _ (fun x => rfl)]
    simp only [bind_tc_ok]
  have hsl : (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)).slice.length ≤
      (rem t1).length := by
    rw [ht1]
    simp [alloc.vec.Vec.from, Slice.length, hlv]
  obtain ⟨t2, s', hre, hs', ht2⟩ := hR.read_exact_ok t1 _ hsl
  have hslen : (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)).slice.length = bs.length := by
    simp [alloc.vec.Vec.from, Slice.length, hlv]
  refine ⟨t2, { slice := s' }, ?_, ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes
    aeneas_wp [hrl, core.result.Result.Insts.CoreOpsTry.branch, hfe, alloc.vec.Vec.deref_mut, hre,
      core.result.Result.map_err_ok, hS.map_ok,
      protocol.binary.TInputProtocolTBinaryInputProtocol.read_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTupleVecU8,
      protocol.binary.TInputProtocolTBinaryInputProtocol.read_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTupleVecU8.call_once]
  · show s'.val = bs
    rw [hs', ht1, hslen]
    simp
  · rw [ht2, ht1, hslen]
    simp

/-! ## The binary length prefix: the rejected inputs (M) -/

/-- (M) A negative length (`Spec.beI32 v`, `v < 0`): `read_binary_len` returns the protocol error `NegativeSize`
(`Spec.readBinLenPrefix` is `none`). -/
theorem bin_read_binary_len_neg (hB : ByteorderContract) (hF : FmtContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.binary.TBinaryInputProtocol T) (v : Int) (hv : Spec.InI32 v) (hneg : v < 0)
    (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.beI32 v).map UInt8.toNat)
    (h : rem self.transport = pre ++ rest) :
    ∃ (t' : T) (m : String), protocol.binary.TBinaryInputProtocol.read_binary_len inst self =
        ok (.Err (.Protocol { kind := .NegativeSize, message := m }), { self with transport := t' }) ∧
      rem t' = rest := by
  obtain ⟨z, hz, hd⟩ := hB.read_i32 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hl : pre.length = 4 := by
    have := congrArg List.length hpre
    simpa [Spec.beI32, Spec.be_length] using this
  have hzl : z.length = 4 := by simp [Slice.length, hz]
  have hs : z.length ≤ (rem self.transport).length := by rw [hzl, h]; simp [hl]
  obtain ⟨t2, s', hre, hs', ht2⟩ := hR.read_exact_ok self.transport z hs
  have hsv : s'.val = pre := by rw [hs', h, hzl, List.take_left' hl]
  have hd' : byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  obtain ⟨y, hyv, hrd⟩ : ∃ y : I32, y.val = v ∧ byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = ok (.Ok y, t2) := by
    refine ⟨⟨BitVec.ofNat _ (beValU8 pre)⟩, ?_, ?_⟩
    · show (BitVec.ofNat 32 (beValU8 pre)).toInt = v
      rw [beValU8_of_map _ _ hpre, Spec.beI32, beVal_be,
        Nat.mod_eq_of_lt (by have := Spec.toU_lt 32 v; rwa [show (256 : Nat) ^ 4 = 2 ^ 32 by rfl]),
        BitVec.toInt_ofNat']
      exact Spec.toS_toU32 hv
    · apply eq_ok_of_wp
      rw [hd']
      aeneas_wp [hre, hsv]
  obtain ⟨s1, hs1⟩ := hF.format_ok ()
  have hw1 : ∀ (Q : Except Error core.fmt.rt.Argument → Prop), wp (ok () : Result core.fmt.rt.Argument) Q ↔
      Q (.ok ()) := fun Q => wp_ok _ Q
  have hw2 : ∀ (Q : Except Error core.fmt.Arguments → Prop), wp (ok () : Result core.fmt.Arguments) Q ↔
      Q (.ok ()) := fun Q => wp_ok _ Q
  refine ⟨t2, s1, ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.binary.TBinaryInputProtocol.read_binary_len
    aeneas_wp [hrd, core.result.Result.Insts.CoreOpsTry.branch, hyv, hneg, hs1, hF.must_use,
      core.fmt.rt.Argument.new_display, core.fmt.Arguments.new, hw1, hw2,
      errors.ProtocolError.new, core.convert.IntoFrom, core.convert.IntoFrom.into, core.convert.FromSame,
      core.convert.FromSame.from]
  · rw [ht2, h, hzl, List.drop_left' hl]

/-- (M) Fewer than four bytes: `read_binary_len` returns the transport error `EndOfFile` (`Spec.readBinLenPrefix`
is `none`, `Truncated 4`). -/
theorem bin_read_binary_len_eof (hS : StdContract) (hB : ByteorderContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.binary.TBinaryInputProtocol T) (h : (rem self.transport).length < 4) :
    ∃ t' m, protocol.binary.TBinaryInputProtocol.read_binary_len inst self =
        ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  obtain ⟨z, hz, hd⟩ := hB.read_i32 (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) self.transport
  have hzl : z.length = 4 := by simp [Slice.length, hz]
  obtain ⟨e, t', s', hre, hk⟩ := hR.read_exact_eof self.transport z (by rw [hzl]; exact h)
  obtain ⟨m, hm⟩ := hS.io_to_string e
  have hd' : byteorder.io.ReadBytesExt.read_i32.default
      (byteorder.io.ReadBytesExt.Blanket inst.allocioreadReadInst) byteorder.BigEndian.Insts.ByteorderByteOrder
      self.transport = (do
        let (res, r', buf) ← inst.allocioreadReadInst.read_exact self.transport z
        match res with
        | .Ok _ => ok (.Ok ⟨BitVec.ofNat _ (beValU8 buf.val)⟩, r')
        | .Err e => ok (.Err e, r')) := hd
  refine ⟨t', m, ?_⟩
  apply eq_ok_of_wp
  unfold protocol.binary.TBinaryInputProtocol.read_binary_len
  aeneas_wp [hd', hre, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    errors.Error.Insts.CoreConvertFromError.from, hk, hm]

/-- (M) A length `n` (non-negative, inside the limit) with fewer than `n` bytes after it: `read_bytes` returns the
transport error `EndOfFile` (`Spec.readBinLenPrefix` is `none`, `Truncated`). -/
theorem bin_read_bytes_trunc (hS : StdContract) (hB : ByteorderContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.binary.TBinaryInputProtocol T) (n : Nat) (hn : n < 2 ^ 31)
    (hcfg : ∀ m : Usize, self.config.max_string_size = some m → n ≤ m.val)
    (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.beI32 n).map UInt8.toNat) (hshort : rest.length < n)
    (h : rem self.transport = pre ++ rest) :
    ∃ t' m, protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes inst self =
        ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  obtain ⟨t1, len, hrl, hlv, ht1⟩ := bin_read_binary_len_D hB hR self n hn hcfg pre rest hpre h
  have hmx : len.val ≤ Usize.max := by scalar_tac
  have hfe : alloc.vec.from_elem core.clone.CloneU8 0#u8 len =
      ok (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)) := by
    unfold alloc.vec.from_elem
    rw [list_clone_ok _ (fun x => rfl)]
    simp only [bind_tc_ok]
  have hsl : (rem t1).length <
      (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)).slice.length := by
    rw [ht1]
    simp [alloc.vec.Vec.from, Slice.length, hlv, hshort]
  obtain ⟨e, t2, s', hre, hk⟩ := hR.read_exact_eof t1 _ hsl
  obtain ⟨m, hm⟩ := hS.io_to_string e
  refine ⟨t2, m, ?_⟩
  apply eq_ok_of_wp
  unfold protocol.binary.TBinaryInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes
  aeneas_wp [hrl, core.result.Result.Insts.CoreOpsTry.branch, hfe, alloc.vec.Vec.deref_mut, hre, hS.map_err,
    core.result.Result.map_err_err, P.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, errors.Error.Insts.CoreConvertFromError.from, hk, hm]

end EquivLean.Demo.Thrift.Rust
