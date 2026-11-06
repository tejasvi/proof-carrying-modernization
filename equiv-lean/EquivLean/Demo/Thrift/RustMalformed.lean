import EquivLean.Demo.Thrift.RustCompactInt

/-!
# Thrift (T4), Rust side: malformed input (M), on concrete byte sequences

Rust's behaviour (Aeneas's semantics) on inputs the spec's readers reject, each beside the spec's verdict:

* a 5-byte varint32 whose value exceeds `u32` (`[0x85, 0x80, 0x80, 0x80, 0x10]`, value 2^32 + 5): Rust returns 5
  (the bits above bit 31 dropped); `Spec.readVarint32` is `none`;
* a 10-byte varint64 whose value exceeds `u64` (`[0x80 × 9, 0x02]`, value 2^64): Rust returns 0; `Spec.readVarint64` is
  `none`;
* an overlong varint32 (`[0x80 × 5]`): Rust returns `InvalidData` "Variable-length int over 5 bytes."; the spec `none`;
* a compact field header byte with type nibble 0 and delta 1 (`[0x10]`): Rust reads STOP; `Spec.readFieldHeader` is
  `none` (`StopNibble`);
* a long-form field id outside `i16` (`[0x05, 0x80, 0x80, 0x04]`, zigzag value 65536, id 32768): Rust reads the field
  (I32, -32768) (`as i16` wraps); `Spec.readFieldHeader` is `none` (`IdOutOfRange`);
* a list header with size 2^31 (`[0xF5, 0x80, 0x80, 0x80, 0x80, 0x08]`): Rust returns `NegativeSize`; the spec `none`
  (`NegSize`).

The six inputs are the spec's named malformed inputs (`Spec.exVarint32Exceeds`, `Spec.exVarint64Exceeds`,
`Spec.exVarint32Overlong`, `Spec.exStopNibble`, `Spec.exIdOutOfRange`, `Spec.exNegSize`); the theorems
`rust_ex…` at the end state Rust's behaviour on each, beside the spec's verdict `Spec.ex…_malformed`.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-! ## Varints -/

/-- (M, varint32 exceeding `u32`) `[0x85, 0x80, 0x80, 0x80, 0x10]` (value 2^32 + 5): `read_varint32` returns 5 and
leaves the rest; `Spec.readVarint32` is `none`. -/
theorem read_varint32_exceeds_example (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (rest : List U8) (h : rem self.transport = [0x85#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x10#u8] ++ rest) :
    (∃ (t' : T) (x : U32), protocol.compact.TCompactInputProtocol.read_varint32 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = 5 ∧ rem t' = rest) ∧
      Spec.readVarint32 [0x85, 0x80, 0x80, 0x80, 0x10] = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨r, t', hrv, hout⟩ := read_varint32_spec hS hR self
  have hd : decVar 5 (rem self.transport) = .ok (2 ^ 32 + 5) rest := by
    rw [h]
    simp [decVar]
  rw [hd] at hout
  obtain ⟨⟨x, hr, hx⟩, hrest⟩ := hout
  refine ⟨t', x, by rw [hrv, hr], by rw [hx]; rfl, hrest⟩

/-- (M, varint64 exceeding `u64`) `[0x80 × 9, 0x02]` (value 2^64): `read_varint64` returns 0 and leaves the rest;
`Spec.readVarint64` is `none`. -/
theorem read_varint64_exceeds_example (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (rest : List U8)
    (h : rem self.transport = [0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8,
      0x02#u8] ++ rest) :
    (∃ (t' : T) (x : U64), protocol.compact.TCompactInputProtocol.read_varint64 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = 0 ∧ rem t' = rest) ∧
      Spec.readVarint64 [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02] = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨r, t', hrv, hout⟩ := read_varint64_spec hS hR self
  have hd : decVar 10 (rem self.transport) = .ok (2 ^ 64) rest := by
    rw [h]
    simp [decVar]
  rw [hd] at hout
  obtain ⟨⟨x, hr, hx⟩, hrest⟩ := hout
  refine ⟨t', x, by rw [hrv, hr], by rw [hx]; rfl, hrest⟩

/-- (M, overlong varint32) `[0x80 × 5]`: `read_varint32` returns `InvalidData` "Variable-length int over 5 bytes.";
`Spec.readVarint32` is `none`. -/
theorem read_varint32_overlong_example (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (rest : List U8) (h : rem self.transport = [0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8] ++ rest) :
    (∃ t' m, protocol.compact.TCompactInputProtocol.read_varint32 inst self =
        ok (.Err (.Protocol { kind := .InvalidData, message := m }), { self with transport := t' }) ∧
      alloc.string.String.Insts.CoreConvertFromShared0Str.from (toStr "Variable-length int over 5 bytes.") = ok m) ∧
      Spec.readVarint32 [0x80, 0x80, 0x80, 0x80, 0x80] = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨r, t', hrv, hout⟩ := read_varint32_spec hS hR self
  have hd : decVar 5 (rem self.transport) = .overlong := by
    rw [h]
    simp [decVar]
  rw [hd] at hout
  obtain ⟨m, hm, hr⟩ := hout
  exact ⟨t', m, by rw [hrv, hr], hm⟩

/-! ## The field header -/

/-- (M, `StopNibble`) The header byte `0x10` (delta 1, type nibble 0), after any field id: `read_field_begin`
reads STOP (Rust looks at the type nibble only); `Spec.readFieldHeader` is `none`. -/
theorem read_field_begin_stopNibble_example (hS : StdContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (rest : List U8) (h : rem self.transport = 0x10#u8 :: rest) :
    (∃ t', protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin inst self =
        ok (.Ok { «name» := none, field_type := .Stop, id := none }, { self with transport := t' }) ∧
      rem t' = rest) ∧ ∀ last, Spec.readFieldHeader last [0x10] = none := by
  refine ⟨?_, fun last => by simp [Spec.readFieldHeader, Spec.StopNibble]⟩
  obtain ⟨t', hrb, ht'⟩ := read_byte_ok hS hR self _ _ h
  refine ⟨t', ?_, ht'⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
  have h1 : (16#u8 &&& 240#u8 : U8) = 16#u8 := by decide
  have h2 : (16#u8 : U8) >>> (4#i32) = ok 1#u8 := by
    show UScalar.shiftRight_IScalar 16#u8 4#i32 = ok 1#u8
    simp [UScalar.shiftRight_IScalar, UScalar.shiftRight]
    rfl
  have h3 : (16#u8 &&& 15#u8 : U8) = 0#u8 := by decide
  have hty : protocol.compact.u8_to_type 0#u8 = ok (.Ok .Stop) := by
    unfold protocol.compact.u8_to_type
    rfl
  aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, h1, h2, h3]
  split
  · rename_i heq
    exact absurd heq (by decide)
  · rename_i heq
    exact absurd heq (by decide)
  · aeneas_wp [hty, core.result.Result.Insts.CoreOpsTry.branch, protocol.TFieldIdentifier.new,
      core.convert.IntoFrom, core.convert.IntoFrom.into, core.convert.FromSame, core.convert.FromSame.from,
      core.option.Option.map_none]

/-- (M, `IdOutOfRange`) The long form `[0x05, 0x80, 0x80, 0x04]` (type I32, zigzag varint 65536, id 32768) after
field id 0: `read_field_begin` reads the field (I32, -32768) (the id `as i16` wraps); `Spec.readFieldHeader` is
`none`. -/
theorem read_field_begin_idOutOfRange_example (hS : StdContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (rest : List U8)
    (h : rem self.transport = 0x05#u8 :: 0x80#u8 :: 0x80#u8 :: 0x04#u8 :: rest) :
    (∃ t', protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin inst self =
        ok (.Ok { «name» := none, field_type := .I32, id := some (-32768)#i16 },
          { self with transport := t', last_read_field_id := (-32768)#i16 }) ∧ rem t' = rest) ∧
      Spec.readFieldHeader 0 [0x05, 0x80, 0x80, 0x04] = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self _ _ h
  obtain ⟨t2, hrv, ht2⟩ := read_varint32_D hS hR { self with transport := t1 } 65536#u32
    [0x80#u8, 0x80#u8, 0x04#u8] rest (by rw [encVar]; simp [encVar]) (by rw [ht1]; rfl)
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
  have hzz : protocol.compact.zigzag_to_i32 65536#u32 = ok 32768#i32 := by
    obtain ⟨x, hx, hxv⟩ := zigzag_to_i32_val 65536#u32
    rw [hx, show x = 32768#i32 from IScalar.eq_of_val_eq (by rw [hxv]; decide)]
  aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, h1, h2, h3]
  split
  · rename_i heq
    exact absurd heq (by decide)
  · rename_i heq
    exact absurd heq (by decide)
  · have hcast : IScalar.cast IScalarTy.I16 (32768#i32 : I32) = (-32768)#i16 := by decide
    aeneas_wp [hty, core.result.Result.Insts.CoreOpsTry.branch, not_true_eq_false, _root_.ite_false,
      protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16, hrv, hzz, hcast]

/-! ## The list header -/

/-- (M, `NegSize`) The list header `[0xF5, 0x80, 0x80, 0x80, 0x80, 0x08]` (element type I32, size varint 2^31):
`read_list_set_begin` returns the protocol error `NegativeSize` (the size `as i32` is negative);
`Spec.readListHeader` is `none`. -/
theorem read_list_set_begin_negSize_example (hS : StdContract) (hF : FmtContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (rest : List U8)
    (h : rem self.transport = [0xF5#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x08#u8] ++ rest) :
    (∃ t' m, protocol.compact.TCompactInputProtocol.read_list_set_begin inst self =
        ok (.Err (.Protocol { kind := .NegativeSize, message := m }), { self with transport := t' }) ∧
      rem t' = rest) ∧
      Spec.readListHeader [0xF5, 0x80, 0x80, 0x80, 0x80, 0x08] = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self 0xF5#u8 _ h
  obtain ⟨t2, hrv, ht2⟩ := read_varint32_D hS hR { self with transport := t1 } 2147483648#u32
    [0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x08#u8] rest (by rw [encVar]; simp [encVar]) (by rw [ht1]; rfl)
  obtain ⟨x, hx, hxv⟩ := hi_nibble 0xF5#u8
  have hlo : (0xF5#u8 &&& 15#u8 : U8) = 5#u8 := by decide
  have hcoll := collection_u8_to_type_ok 5#u8 .I32 (by rfl)
  have hx15 : x.val = 15 := by rw [hxv]; decide
  have hx15' : x = 15#u8 := UScalar.eq_of_val_eq (by rw [hx15]; rfl)
  obtain ⟨ms, hms, -⟩ := min_serialized_size_eq .I32
  obtain ⟨s1, hs1⟩ := hF.format_ok ()
  have hw1 : ∀ (Q : Except Error core.fmt.rt.Argument → Prop), wp (ok () : Result core.fmt.rt.Argument) Q ↔
      Q (.ok ()) := fun Q => wp_ok _ Q
  have hw2 : ∀ (Q : Except Error core.fmt.Arguments → Prop), wp (ok () : Result core.fmt.Arguments) Q ↔
      Q (.ok ()) := fun Q => wp_ok _ Q
  have hneg : (UScalar.hcast IScalarTy.I32 (2147483648#u32 : U32)).val < 0 := by
    rw [UScalar.hcast_val_eq]; decide
  refine ⟨t2, s1, ?_, ht2⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.read_list_set_begin
  aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hlo, hcoll, hx, hx15', hrv,
    not_true_eq_false, _root_.ite_false, not_false_eq_true, _root_.ite_true,
    protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.min_serialized_size, hms,
    protocol.check_container_size, hneg, core.fmt.rt.Argument.new_display, core.fmt.Arguments.new, hw1, hw2, hs1,
    hF.must_use, errors.ProtocolError.new, core.convert.IntoFrom, core.convert.IntoFrom.into, core.convert.FromSame,
    core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-! ## The compact length prefix -/

/-- (M, compact length prefix, overlong varint) `[0x80 × 5]`: `read_binary_len` returns `InvalidData` "Variable-length
int over 5 bytes." (`read_varint32`'s error); `Spec.readLenPrefix` is `none`. -/
theorem read_binary_len_overlong_example (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (rest : List U8) (h : rem self.transport = [0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8] ++ rest) :
    (∃ t' m, protocol.compact.TCompactInputProtocol.read_binary_len inst self =
        ok (.Err (.Protocol { kind := .InvalidData, message := m }), { self with transport := t' }) ∧
      alloc.string.String.Insts.CoreConvertFromShared0Str.from (toStr "Variable-length int over 5 bytes.") = ok m) ∧
      Spec.readLenPrefix [0x80, 0x80, 0x80, 0x80, 0x80] = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨⟨t', m, hrv, hm⟩, -⟩ := read_varint32_overlong_example hS hR self rest h
  refine ⟨t', m, ?_, hm⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.read_binary_len
  aeneas_wp [hrv, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    core.convert.FromSame.from]

/-- (M, compact length prefix, truncated payload) A length `n` inside the string limit with fewer than `n` bytes after
it: `read_bytes` returns the transport error `EndOfFile`; `Spec.readLenPrefix` is `none` (`Truncated`). -/
theorem read_bytes_trunc (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (n : Nat) (hn : n < 2 ^ 32) (hcfg : ∀ m : Usize, self.config.max_string_size = some m → n ≤ m.val)
    (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.varint n).map UInt8.toNat) (hshort : rest.length < n)
    (h : rem self.transport = pre ++ rest) :
    ∃ t' m, protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes inst self =
        ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  obtain ⟨t1, len, hrl, hlv, ht1⟩ := read_binary_len_D hS hR self n hn hcfg pre rest hpre h
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
  unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes
  aeneas_wp [hrl, core.result.Result.Insts.CoreOpsTry.branch, hfe, alloc.vec.Vec.deref_mut, hre, hS.map_err,
    core.result.Result.map_err_err, P.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, errors.Error.Insts.CoreConvertFromError.from, hk, hm]

/-! ## The spec's named malformed inputs -/

theorem u8s_eq_of_vals : ∀ (bs cs : List U8), bs.map (·.val) = cs.map (·.val) → bs = cs
  | [], [], _ => rfl
  | b :: bs, c :: cs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [UScalar.eq_of_val_eq h.1, u8s_eq_of_vals bs cs h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- (M) `Spec.exVarint32Exceeds` (value 2^32 + 5): Rust's `read_varint32` returns 5; the spec's verdict:
`VarintExceeds`, `readVarint32` is `none`. -/
theorem rust_exVarint32Exceeds (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs rest : List U8) (hbs : bs.map (·.val) = Spec.exVarint32Exceeds.map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    (∃ (t' : T) (x : U32), protocol.compact.TCompactInputProtocol.read_varint32 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = 5 ∧ rem t' = rest) ∧
      (Spec.VarintExceeds 5 (2 ^ 32) Spec.exVarint32Exceeds ∧ Spec.readVarint32 Spec.exVarint32Exceeds = none) := by
  have hb : bs = [0x85#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x10#u8] := u8s_eq_of_vals _ _ (by rw [hbs]; decide)
  subst hb
  exact ⟨(read_varint32_exceeds_example hS hR self rest h).1, Spec.exVarint32Exceeds_malformed⟩

/-- (M) `Spec.exVarint64Exceeds` (value 2^64): Rust's `read_varint64` returns 0; the spec's verdict: `VarintExceeds`,
`readVarint64` is `none`. -/
theorem rust_exVarint64Exceeds (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs rest : List U8) (hbs : bs.map (·.val) = Spec.exVarint64Exceeds.map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    (∃ (t' : T) (x : U64), protocol.compact.TCompactInputProtocol.read_varint64 inst self =
        ok (.Ok x, { self with transport := t' }) ∧ x.val = 0 ∧ rem t' = rest) ∧
      (Spec.VarintExceeds 10 (2 ^ 64) Spec.exVarint64Exceeds ∧ Spec.readVarint64 Spec.exVarint64Exceeds = none) := by
  have hb : bs = [0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x02#u8] :=
    u8s_eq_of_vals _ _ (by rw [hbs]; decide)
  subst hb
  exact ⟨(read_varint64_exceeds_example hS hR self rest h).1, Spec.exVarint64Exceeds_malformed⟩

/-- (M) `Spec.exVarint32Overlong` (five bytes with the high bit set), followed by any bytes: Rust's `read_varint32`
returns `InvalidData` "Variable-length int over 5 bytes." after reading the five bytes; the spec's verdict:
`VarintOverlong 5`, `readVarint32` is `none`. -/
theorem rust_exVarint32Overlong (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs rest : List U8) (hbs : bs.map (·.val) = Spec.exVarint32Overlong.map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    (∃ t' m, protocol.compact.TCompactInputProtocol.read_varint32 inst self =
        ok (.Err (.Protocol { kind := .InvalidData, message := m }), { self with transport := t' }) ∧
      alloc.string.String.Insts.CoreConvertFromShared0Str.from (toStr "Variable-length int over 5 bytes.") = ok m) ∧
      (Spec.VarintOverlong 5 Spec.exVarint32Overlong ∧ Spec.readVarint32 Spec.exVarint32Overlong = none) := by
  have hb : bs = [0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8] := u8s_eq_of_vals _ _ (by rw [hbs]; decide)
  subst hb
  exact ⟨(read_varint32_overlong_example hS hR self rest h).1, Spec.exVarint32Overlong_malformed⟩

/-- (M) `Spec.exStopNibble` (`[0x10]`), after any field id (0 in the spec's verdict): Rust's `read_field_begin` reads
STOP; the spec's verdict: `StopNibble`, `readFieldHeader 0` is `none`. -/
theorem rust_exStopNibble (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs rest : List U8) (hbs : bs.map (·.val) = Spec.exStopNibble.map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    (∃ t', protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin inst self =
        ok (.Ok { «name» := none, field_type := .Stop, id := none }, { self with transport := t' }) ∧
      rem t' = rest) ∧
      (Spec.StopNibble 0x10 ∧ Spec.readFieldHeader 0 Spec.exStopNibble = none) := by
  have hb : bs = [0x10#u8] := u8s_eq_of_vals _ _ (by rw [hbs]; decide)
  subst hb
  exact ⟨(read_field_begin_stopNibble_example hS hR self rest h).1, Spec.exStopNibble_malformed⟩

/-- (M) `Spec.exIdOutOfRange` (`[0x05, 0x80, 0x80, 0x04]`, id 32768), after any field id (0 in the spec's verdict):
Rust's `read_field_begin` reads the field (I32, -32768); the spec's verdict: `IdOutOfRange`, `readFieldHeader 0` is
`none`. -/
theorem rust_exIdOutOfRange (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs rest : List U8) (hbs : bs.map (·.val) = Spec.exIdOutOfRange.map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    (∃ t', protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin inst self =
        ok (.Ok { «name» := none, field_type := .I32, id := some (-32768)#i16 },
          { self with transport := t', last_read_field_id := (-32768)#i16 }) ∧ rem t' = rest) ∧
      (Spec.readVarint32 [0x80, 0x80, 0x04] = some (65536, []) ∧ Spec.unzigzag 65536 = 32768 ∧
        Spec.IdOutOfRange 65536 ∧ Spec.readFieldHeader 0 Spec.exIdOutOfRange = none) := by
  have hb : bs = [0x05#u8, 0x80#u8, 0x80#u8, 0x04#u8] := u8s_eq_of_vals _ _ (by rw [hbs]; decide)
  subst hb
  exact ⟨(read_field_begin_idOutOfRange_example hS hR self rest h).1, Spec.exIdOutOfRange_malformed⟩

/-- (M) `Spec.exNegSize` (list header, size 2^31): Rust's `read_list_set_begin` returns `NegativeSize`; the spec's
verdict: `NegSize`, `readListHeader` is `none`. -/
theorem rust_exNegSize (hS : StdContract) (hF : FmtContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs rest : List U8) (hbs : bs.map (·.val) = Spec.exNegSize.map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    (∃ t' m, protocol.compact.TCompactInputProtocol.read_list_set_begin inst self =
        ok (.Err (.Protocol { kind := .NegativeSize, message := m }), { self with transport := t' }) ∧
      rem t' = rest) ∧
      (Spec.readVarint32 [0x80, 0x80, 0x80, 0x80, 0x08] = some (2 ^ 31, []) ∧ Spec.NegSize (2 ^ 31) ∧
        Spec.readListHeader Spec.exNegSize = none) := by
  have hb : bs = [0xF5#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x08#u8] := u8s_eq_of_vals _ _ (by rw [hbs]; decide)
  subst hb
  exact ⟨(read_list_set_begin_negSize_example hS hF hR self rest h).1, Spec.exNegSize_malformed⟩

end EquivLean.Demo.Thrift.Rust
