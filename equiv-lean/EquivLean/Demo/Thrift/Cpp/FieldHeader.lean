import EquivLean.Demo.Thrift.Cpp.VarintRead32
import EquivLean.Demo.Thrift.Cpp.Zigzag

/-!
# Thrift, C++ side: compact field header, writer (E)

`writeFieldBeginInternal_E`: `TCompactProtocolT<TTransport>::writeFieldBeginInternal(name, t, id, -1)` (what
`writeFieldBegin` calls) appends exactly `Spec.fieldHeader last id c` for every TType `t` with a compact type
nibble `c` (`Spec.compactType`), every `int16_t` `id` and every previous id `last` (`lastFieldId_`), and sets
`lastFieldId_ = id`.  Its callees by their proved specifications: `getCompactType_E` (the program's constant table
`TTypeToCType`, a hypothesis on the memory: its initializer `cTypeTable`), `writeByte_E` (the transport's one-byte
write), `writeI16_E` (`i32ToZigzag` then `writeVarint32`).  The named inputs of the spec:
`writeFieldBeginInternal_exDelta15` (`0xF5`) and `writeFieldBeginInternal_exI16Overflow` (`05 FF FF 03`).
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

def symWriteByte : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE9writeByteEa"
def symWriteI16 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE8writeI16Es"

/-- The local `varint` (bytes as numbers) is the spec's, as numbers. -/
theorem varint_eq_spec (n : Nat) : varint n = (Spec.varint n).map UInt8.toNat := by
  rw [Spec.varint_map_toNat]
  by_cases h : n < 128
  · rw [varint_lt h, ite_eq_left h]
  · rw [varint_ge h, ite_eq_right h, varint_eq_spec (n / 128)]
termination_by n
decreasing_by omega

theorem zigzag_eq_spec (n : Int) : zigzag n = Spec.zigzag n := rfl

theorem zigzag16_lt {n : Int} (hn : -32768 ≤ n ∧ n ≤ 32767) : zigzag n < 65536 := by
  unfold zigzag; split <;> omega

theorem varint_zigzag16_len {n : Int} (hn : -32768 ≤ n ∧ n ≤ 32767) : (varint (zigzag n)).length ≤ 5 := by
  rw [varint_eq_spec, List.length_map]
  exact Spec.varint_length_le5 (Nat.lt_trans (zigzag16_lt hn) (by decide))

/-- `writeByte(c)`: appends the byte `c mod 256`. -/
theorem writeByte_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteByte = some fn_apache_thrift_protocol_TCompactProtocolT_writeByte)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hFp : ∀ b, Fp b → b < m.next)
    (c : Int) (hc : -128 ≤ c ∧ c ≤ 127) :
    Returns ctx symWriteByte [.ptr (.loc pb []), .int c] m
      (fun r m' => r = some (.int 1) ∧ sinkOf m' = sinkOf m ++ [(c % 256).toNat] ∧ m.next ≤ m'.next ∧
        ∀ b, ¬ Fp b → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have hW := TW.write1
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  case h.right.left =>
    rw [hstable cir_mem0 _ (fun b hb => by
      have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post0ba]
    congr 1
    exact hstable m _ (fun b hb => by
      have := hFp b hb; dsimp only; simp (disch := omega) only [upd_apply_ne])
  case h.right.right.left => omega

/-- `writeI16(n)`: appends the varint of `zigzag n`. -/
theorem writeI16_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteI16 = some fn_apache_thrift_protocol_TCompactProtocolT_writeI16)
    (cirH_fz : ctx.mod.findFunc? symI32ToZigzag = some fn_apache_thrift_protocol_TCompactProtocolT_i32ToZigzag)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hFp : ∀ b, Fp b → b < m.next)
    (n : Int) (hn : -32768 ≤ n ∧ n ≤ 32767) :
    Returns ctx symWriteI16 [.ptr (.loc pb []), .int n] m
      (fun r m' => r = some (.int (varint (zigzag n)).length) ∧ sinkOf m' = sinkOf m ++ varint (zigzag n) ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_specz := fun m' this n' hn' => i32ToZigzag_E ctx cirH_fz m' this n' hn'
  have cirH_specw := fun m' pb' kp' v' h1 h2 h3 h4 n0 hn0 =>
    writeVarint32_E ctx cirH_fw tp Fp sinkOf TW m' pb' kp' v' h1 h2 h3 h4 n0 hn0
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  case h.hspec.left => omega
  case h.hspec.right => omega
  case h.hspec.refine'_5 => omega
  case h.hspec.refine'_6 => rename_i b hb; have := hFp b hb; omega
  case h.hspec.refine'_7 => have := zigzag16_lt hn; omega
  case h₁ => have := varint_zigzag16_len hn; omega
  case h.right.left =>
    rw [hstable cir_mem2 _ (fun b hb => by
      have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post2ba]
    congr 1
    rw [hstable m cir_mem0 (fun b hb => by
      have := hFp b hb; rw [cirH_post0bb b (by omega)]; simp (disch := omega) only [upd_apply_ne])]
  case h.right.right.left => omega

def symGetCompactType : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE14getCompactTypeENS1_5TTypeE"
/-- The constant table `detail::compact::TTypeToCType`. -/
def gTTypeToCType : String := "_ZN6apache6thrift8protocol6detail7compactL12TTypeToCTypeE"
/-- `TTypeToCType`'s initializer (its 17 values). -/
def cTypeTable : List Val :=
  [.int 0, .int 0, .int 1, .int 3, .int 7, .int 0, .int 4, .int 0, .int 5, .int 0, .int 6, .int 8, .int 12, .int 11,
    .int 10, .int 9, .int 13]

theorem cTypeTable_get {t c : Nat} (ht : Spec.compactType t = some c) :
    t < 17 ∧ cTypeTable[t]? = some (.int c) := by
  unfold Spec.compactType at ht
  split at ht <;> cases ht <;> exact ⟨by decide, rfl⟩

/-- `getCompactType(t)`: the compact type nibble of every TType `t` with one (`Spec.compactType`), read from the
program's constant table. -/
theorem getCompactType_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symGetCompactType = some fn_apache_thrift_protocol_TCompactProtocolT_getCompactType)
    (gb : Nat) (cirH_g : ctx.gaddr gTTypeToCType = some gb)
    (m : Mem) (kg : BlockKind) (cirH_gb : m.blocks gb = some ⟨kg, true, .array (.int true 8) 17, .arr cTypeTable⟩)
    (cirH_gbl : gb < m.next) (this : Ptr) (t c : Nat) (ht : Spec.compactType t = some c) :
    Returns ctx symGetCompactType [.ptr this, .int t] m
      (fun r m' => r = some (.int c) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  obtain ⟨cirH_t, cirH_tab⟩ := cTypeTable_get ht
  have cirH_tab' : cTypeTable[((t : Int)).toNat]? = some (.int c) := by rw [Int.toNat_natCast]; exact cirH_tab
  have hc := Spec.compactType_lt ht
  unfold gTTypeToCType at cirH_g
  have cirH_len : cTypeTable.length = 17 := rfl
  have cirH_tb : 0 ≤ (t : Int) ∧ (t : Int) ≤ (cTypeTable.length : Int) := by rw [cirH_len]; omega
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals omega

theorem wrap8_range (x : Int) : -128 ≤ wrap true 8 x ∧ wrap true 8 x ≤ 127 := by
  unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

/-- The short field header byte `(int8_t)(d << 4 | c)` as the transport receives it. -/
theorem fh_byte {d : Int} {c : Nat} (hd : 1 ≤ d ∧ d ≤ 15) (hc : c < 16) :
    (wrap true 8 (bitwise true 32 (fun x1 x2 => x1 ||| x2) (d * 16) (c : Int)) % 256).toNat = 16 * d.toNat + c := by
  have hor : bitwise true 32 (fun x1 x2 => x1 ||| x2) (d * 16) (c : Int) = ((16 * d.toNat + c : Nat) : Int) := by
    unfold bitwise
    simp only [ite_true]
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_or, ofInt_toNat_32 (by omega) (by omega),
      ofInt_toNat_32 (by omega) (by omega)]
    have e : (d * 16).toNat ||| (c : Int).toNat = 16 * d.toNat + c := by
      rw [show (d * 16).toNat = 2 ^ 4 * d.toNat by omega, Int.toNat_natCast,
        ← Nat.two_pow_add_eq_or_of_lt (show c < 2 ^ 4 by omega)]
    rw [e]; split <;> omega
  rw [hor]; unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

def symWriteFieldBeginInternal : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE23writeFieldBeginInternalEPKcNS1_5TTypeEsa"

/-- (E) `writeFieldBeginInternal(name, t, id, -1)` after a field with id `last` (`lastFieldId_`), for every TType `t`
with a compact type nibble `c` and every `int16_t` `id`: appends exactly `Spec.fieldHeader last id c`, returns its
length, and sets `lastFieldId_ = id`. -/
theorem writeFieldBeginInternal_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteFieldBeginInternal =
      some fn_apache_thrift_protocol_TCompactProtocolT_writeFieldBeginInternal)
    (cirH_fg : ctx.mod.findFunc? symGetCompactType = some fn_apache_thrift_protocol_TCompactProtocolT_getCompactType)
    (cirH_fb : ctx.mod.findFunc? symWriteByte = some fn_apache_thrift_protocol_TCompactProtocolT_writeByte)
    (cirH_fi : ctx.mod.findFunc? symWriteI16 = some fn_apache_thrift_protocol_TCompactProtocolT_writeI16)
    (cirH_fz : ctx.mod.findFunc? symI32ToZigzag = some fn_apache_thrift_protocol_TCompactProtocolT_i32ToZigzag)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (gb : Nat) (cirH_g : ctx.gaddr gTTypeToCType = some gb)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (kg : BlockKind) (cirH_gb : m.blocks gb = some ⟨kg, true, .array (.int true 8) 17, .arr cTypeTable⟩)
    (cirH_gbl : gb < m.next)
    (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hkp : kp ≠ .readonly) (hFp : ∀ b, Fp b → b < m.next)
    (last : Int) (cirH_last : fs[5]? = some (.int last)) (hlast : Spec.InI16 last)
    (nm : Ptr) (t c : Nat) (ht : Spec.compactType t = some c) (id : Int) (hid : Spec.InI16 id) :
    Returns ctx symWriteFieldBeginInternal [.ptr (.loc pb []), .ptr nm, .int t, .int id, .int (-1)] m
      (fun r m' => r = some (.int (Spec.fieldHeader last id c).length) ∧
        sinkOf m' = sinkOf m ++ (Spec.fieldHeader last id c).map UInt8.toNat ∧
        m'.blocks pb = some ⟨kp, true, .record recProto, .agg (fs.set 5 (.int id))⟩ ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ pb → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_specg := fun m' this' kg' h1 h2 => getCompactType_E ctx cirH_fg gb cirH_g m' kg' h1 h2 this' t c ht
  have cirH_specb := fun m' pb' kp' v' h1 h2 h3 h4 c' hc' =>
    writeByte_E ctx cirH_fb tp Fp sinkOf TW m' pb' kp' v' h1 h2 h3 h4 c' hc'
  have cirH_speci := fun m' pb' kp' v' h1 h2 h3 h4 n' hn' =>
    writeI16_E ctx cirH_fi cirH_fz cirH_fw tp Fp sinkOf TW m' pb' kp' v' h1 h2 h3 h4 n' hn'
  have hc := Spec.compactType_lt ht
  have cirH_kp := hkp
  have cirH_t17 := (cTypeTable_get ht).1
  have neFpPb : ∀ b, Fp b → b ≠ pb := fun b hb h => hpbF (h ▸ hb)
  have hsrc0 : ∀ mm, (∀ b, b < m.next → mm.blocks b = m.blocks b) → sinkOf mm = sinkOf m :=
    fun mm h => hstable m mm (fun b hb => h b (hFp b hb))
  have cirH_vlen := varint_zigzag16_len (n := id) ⟨hid.1, by have := hid.2; omega⟩
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_writeFieldBeginInternal.nothrow = false := rfl
  unfold Spec.InI16 at hlast hid
  unfold gTTypeToCType at cirH_g
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try (first | omega | (rename_i b hb; have := hFp b hb; omega))
  -- the short form `(int8_t)(delta << 4 | c)`
  case h.hspec.refine'_7.left => exact (wrap8_range _).1
  case h.hspec.refine'_7.right => exact (wrap8_range _).2
  case h.left =>
    rw [Spec.fieldHeader_short ⟨by omega, by omega⟩ hc]; rfl
  case h.right.left =>
    rw [hstable cir_mem2 _ (fun b hb => by
      have := hFp b hb; dsimp only
      simp (disch := first | omega | exact neFpPb _ hb) only [killRange_of_lt, upd_apply_ne]), cirH_post2ba,
      hsrc0 _ (fun b hb => by
        dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]; rw [cirH_post0bb b (by omega)]; simp (disch := omega) only [upd_apply_ne]),
      Spec.fieldHeader_short ⟨by omega, by omega⟩ hc, fh_byte ⟨by omega, by omega⟩ hc]
    simp only [List.map_cons, List.map_nil, UInt8.toNat_ofNat']
    congr 2; omega
  -- the long form: the byte `c`, then `writeI16(id)`
  all_goals first
    | (rw [Spec.fieldHeader_long (by omega), List.length_cons, varint_eq_spec, List.length_map, zigzag_eq_spec]
       omega)
    | (rw [hstable cir_mem5 _ (fun b hb => by
          have := hFp b hb; dsimp only
          simp (disch := first | omega | exact neFpPb _ hb) only [killRange_of_lt, upd_apply_ne]), cirH_post5ba,
        hstable cir_mem2 _ (fun b hb => by
          have := hFp b hb; dsimp only; simp (disch := omega) only [upd_apply_ne]), cirH_post2ba,
        hsrc0 _ (fun b hb => by
          dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]; rw [cirH_post0bb b (by omega)]; simp (disch := omega) only [upd_apply_ne]),
        Spec.fieldHeader_long (by omega), List.map_cons, varint_eq_spec, zigzag_eq_spec, UInt8.toNat_ofNat',
        List.append_assoc, List.singleton_append]
       congr 3 <;> omega)

/-! ## The named inputs where the languages can differ (`Spec.exDelta15`, `Spec.exI16Overflow`)

The TType of the field is `T_I32` (8), compact type 5. -/

/-- `writeFieldBeginInternal(name, T_I32, 15, -1)` after field id 0 (`Spec.exDelta15`): the one byte `0xF5`. -/
theorem writeFieldBeginInternal_exDelta15 (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteFieldBeginInternal =
      some fn_apache_thrift_protocol_TCompactProtocolT_writeFieldBeginInternal)
    (cirH_fg : ctx.mod.findFunc? symGetCompactType = some fn_apache_thrift_protocol_TCompactProtocolT_getCompactType)
    (cirH_fb : ctx.mod.findFunc? symWriteByte = some fn_apache_thrift_protocol_TCompactProtocolT_writeByte)
    (cirH_fi : ctx.mod.findFunc? symWriteI16 = some fn_apache_thrift_protocol_TCompactProtocolT_writeI16)
    (cirH_fz : ctx.mod.findFunc? symI32ToZigzag = some fn_apache_thrift_protocol_TCompactProtocolT_i32ToZigzag)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (gb : Nat) (cirH_g : ctx.gaddr gTTypeToCType = some gb)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (kg : BlockKind) (cirH_gb : m.blocks gb = some ⟨kg, true, .array (.int true 8) 17, .arr cTypeTable⟩)
    (cirH_gbl : gb < m.next)
    (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hkp : kp ≠ .readonly) (hFp : ∀ b, Fp b → b < m.next) (nm : Ptr)
    (cirH_last : fs[5]? = some (.int Spec.exDelta15.last)) :
    Returns ctx symWriteFieldBeginInternal [.ptr (.loc pb []), .ptr nm, .int 8, .int Spec.exDelta15.id, .int (-1)] m
      (fun r m' => r = some (.int 1) ∧ sinkOf m' = sinkOf m ++ [0xF5]) := by
  refine returns_mono (writeFieldBeginInternal_E ctx cirH_f cirH_fg cirH_fb cirH_fi cirH_fz cirH_fw gb cirH_g tp Fp sinkOf TW m kg cirH_gb cirH_gbl pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp Spec.exDelta15.last cirH_last (by decide) nm 8
    Spec.exDelta15.ty rfl Spec.exDelta15.id (by decide)) ?_
  rintro r m' ⟨h1, h2, -⟩
  rw [Spec.fieldHeader_exDelta15] at h1 h2
  exact ⟨h1, by rw [h2]; rfl⟩

/-- `writeFieldBeginInternal(name, T_I32, -32768, -1)` after field id 32767 (`Spec.exI16Overflow`): the long form
`05 FF FF 03` (C++ compares the ids as `int`: no wrap, `fieldId > lastFieldId_` is false). -/
theorem writeFieldBeginInternal_exI16Overflow (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteFieldBeginInternal =
      some fn_apache_thrift_protocol_TCompactProtocolT_writeFieldBeginInternal)
    (cirH_fg : ctx.mod.findFunc? symGetCompactType = some fn_apache_thrift_protocol_TCompactProtocolT_getCompactType)
    (cirH_fb : ctx.mod.findFunc? symWriteByte = some fn_apache_thrift_protocol_TCompactProtocolT_writeByte)
    (cirH_fi : ctx.mod.findFunc? symWriteI16 = some fn_apache_thrift_protocol_TCompactProtocolT_writeI16)
    (cirH_fz : ctx.mod.findFunc? symI32ToZigzag = some fn_apache_thrift_protocol_TCompactProtocolT_i32ToZigzag)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (gb : Nat) (cirH_g : ctx.gaddr gTTypeToCType = some gb)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (kg : BlockKind) (cirH_gb : m.blocks gb = some ⟨kg, true, .array (.int true 8) 17, .arr cTypeTable⟩)
    (cirH_gbl : gb < m.next)
    (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hkp : kp ≠ .readonly) (hFp : ∀ b, Fp b → b < m.next) (nm : Ptr)
    (cirH_last : fs[5]? = some (.int Spec.exI16Overflow.last)) :
    Returns ctx symWriteFieldBeginInternal
      [.ptr (.loc pb []), .ptr nm, .int 8, .int Spec.exI16Overflow.id, .int (-1)] m
      (fun r m' => r = some (.int 4) ∧ sinkOf m' = sinkOf m ++ [0x05, 0xFF, 0xFF, 0x03]) := by
  refine returns_mono (writeFieldBeginInternal_E ctx cirH_f cirH_fg cirH_fb cirH_fi cirH_fz cirH_fw gb cirH_g tp Fp sinkOf TW m kg cirH_gb cirH_gbl pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp Spec.exI16Overflow.last cirH_last (by decide) nm 8
    Spec.exI16Overflow.ty rfl Spec.exI16Overflow.id (by decide)) ?_
  rintro r m' ⟨h1, h2, -⟩
  rw [Spec.fieldHeader_exI16Overflow] at h1 h2
  exact ⟨h1, by rw [h2]; rfl⟩

end EquivLean.Demo.Thrift.Cpp
