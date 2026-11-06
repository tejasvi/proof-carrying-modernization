import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___thrift__protocol__compact__TCompactInputProtocol_T____read_list_set_begin
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___thrift__protocol__compact__TCompactOutputProtocol_T____write_list_set_begin
import EquivLean.Demo.Thrift.RustField

/-!
# Thrift (T4), Rust side: the compact list/set header

`read_list_set_begin` (compact.rs:98) against `Spec.listHeader` / `Spec.readListHeader`.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-! ## Bridges to the spec -/

theorem encVar_eq_varint (n : Nat) : encVar n = (Spec.varint n).map UInt8.toNat := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [encVar, Spec.varint_map_toNat]
    split_ifs with h
    · rfl
    · rw [ih (n / 128) (by omega)]

theorem leb128_eq_varint (n : Nat) :
    (rusttrn_model.leb128 n).map (·.val) = (Spec.varint n).map UInt8.toNat := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [rusttrn_model.leb128, Spec.varint_map_toNat]
    split_ifs with h
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      show (BitVec.ofNat 8 n).toNat = n
      rw [BitVec.toNat_ofNat]
      omega
    · simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih (n / 128) (by omega)⟩
      show (BitVec.ofNat 8 _).toNat = _
      rw [BitVec.toNat_ofNat]
      omega

/-! ## Element types -/

/-- `collection_u8_to_type`: the `TType` Rust reads a collection's element-type nibble as (`none`: an error). -/
def collType : Nat → Option protocol.TType
  | 0 => some .Stop
  | 1 => some .Bool
  | 2 => some .Bool
  | 3 => some .I08
  | 4 => some .I16
  | 5 => some .I32
  | 6 => some .I64
  | 7 => some .Double
  | 8 => some .String
  | 9 => some .List
  | 10 => some .Set
  | 11 => some .Map
  | 12 => some .Struct
  | 13 => some .Uuid
  | _ => none

theorem collType_lt {n : Nat} {tt : protocol.TType} (h : collType n = some tt) : n < 14 := by
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ =>
    decide

theorem collection_u8_to_type_ok (b : U8) (tt : protocol.TType) (h : collType b.val = some tt) :
    protocol.compact.collection_u8_to_type b = ok (.Ok tt) := by
  have hb := collType_lt h
  obtain ⟨n, hn⟩ : ∃ n, b.val = n := ⟨_, rfl⟩
  rw [hn] at h hb
  have hbn : b = UScalar.ofNatCore n (Nat.lt_of_lt_of_le hb (by rw [UScalarTy.U8_numBits_eq]; decide)) :=
    UScalar.eq_of_val_eq (by rw [hn]; simp)
  rw [hbn]
  clear hbn hn b
  match n, hb, h with
  | 0, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 1, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 2, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 3, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 4, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 5, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 6, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 7, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 8, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 9, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 10, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 11, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 12, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 13, _, h => simp only [collType, Option.some.injEq] at h; subst h; rfl

/-- `compact_protocol_min_serialized_size`. -/
def minSize : protocol.TType → Nat
  | .Double => 8
  | .Uuid => 16
  | _ => 1

theorem min_serialized_size_eq (tt : protocol.TType) :
    ∃ m : Usize, protocol.compact.compact_protocol_min_serialized_size tt = ok m ∧ m.val = minSize tt := by
  cases tt <;> exact ⟨_, rfl, by simp [minSize]⟩

/-! ## `check_container_size` -/

theorem usize_checked_mul_some (x y : Usize) (h : x.val * y.val ≤ Usize.max) :
    ∃ z : Usize, Usize.checked_mul x y = some z ∧ z.val = x.val * y.val := by
  have hs := core.num.checked_mul_UScalar_bv_spec x y
  unfold Usize.checked_mul
  rcases hz : core.num.checked_mul_UScalar x y with _ | z
  · rw [hz] at hs
    simp only [UScalar.max_USize_eq] at hs
    omega
  · rw [hz] at hs
    exact ⟨z, rfl, hs.2.1⟩

/-- `check_container_size` passes a size inside the configured limits. -/
theorem check_container_size_ok (config : configuration.TConfiguration) (count : I32) (es : Usize)
    (h0 : 0 ≤ count.val)
    (hc1 : ∀ m : Usize, config.max_container_size = some m → count.val.toNat ≤ m.val)
    (hmul : count.val.toNat * es.val ≤ Usize.max)
    (hc2 : ∀ m : Usize, config.max_message_size = some m → count.val.toNat * es.val ≤ m.val) :
    protocol.check_container_size config count es = ok (.Ok ()) := by
  have hcount : count.val < 2 ^ 31 := by scalar_tac
  have hcast : (IScalar.hcast UScalarTy.Usize count).val = count.val.toNat := by
    rw [IScalar.hcast_val_eq]
    have : (2 : Int) ^ 31 ≤ 2 ^ UScalarTy.Usize.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
    rw [Int.emod_eq_of_lt h0 (by omega)]
  obtain ⟨z, hz, hzv⟩ := usize_checked_mul_some (IScalar.hcast UScalarTy.Usize count) es (by rw [hcast]; exact hmul)
  rw [hcast] at hzv
  apply eq_ok_of_wp
  unfold protocol.check_container_size
  have hneg : ¬ count.val < 0 := by omega
  aeneas_wp [hneg, configuration.TConfiguration.impl.max_container_size,
    configuration.TConfiguration.impl.max_message_size, hz]
  rcases hmc : config.max_container_size with _ | m
  · rcases hmm : config.max_message_size with _ | mm
    · simp
    · have := hc2 mm hmm
      simp [hzv, this]
  · have h1 := hc1 m hmc
    have hnc : ¬ ((m.val : Int) < count.val) := by omega
    rcases hmm : config.max_message_size with _ | mm
    · simp [hcast, hnc]
    · have := hc2 mm hmm
      have hnc : ¬ ((m.val : Int) < count.val) := by omega
      have hnm : ¬ (mm.val < z.val) := by omega
      simp [hcast, hzv, hnc, hnm]
      intro hlt
      omega

/-! ## Nibbles -/

theorem lo_nibble (b : U8) : (b &&& 15#u8).val = b.val % 16 := by
  rw [UScalar.val_and, show (15#u8 : U8).val = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem hi_nibble (b : U8) : ∃ x : U8, (b &&& 240#u8) >>> (4#i32) = ok x ∧ x.val = b.val / 16 := by
  refine ⟨⟨(b &&& 240#u8).bv >>> 4⟩, ?_, ?_⟩
  · show UScalar.shiftRight_IScalar _ 4#i32 = _
    simp [UScalar.shiftRight_IScalar, UScalar.shiftRight]
  · show ((b &&& 240#u8).bv >>> 4).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show (b &&& 240#u8).val / 2 ^ 4 = _
    rw [UScalar.val_and, show (240#u8 : U8).val = 240 from rfl]
    have hb : b.val < 256 := by scalar_tac
    have key : ∀ n < 256, (n &&& 240) / 2 ^ 4 = n / 16 := by decide +kernel
    exact key _ hb

/-! ## `read_list_set_begin` -/

set_option maxHeartbeats 4000000 in
/-- (D, list/set header) On a transport holding `Spec.listHeader size ety` and then any bytes `rest`,
`read_list_set_begin` returns the element type and the size and leaves exactly `rest` (for every element-type
nibble Rust accepts, every size below 2^31, inside the configured container and message limits). -/
theorem read_list_set_begin_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (size ety : Nat) (tt : protocol.TType) (hety : collType ety = some tt) (hsize : size < 2 ^ 31)
    (hc1 : ∀ m : Usize, self.config.max_container_size = some m → size ≤ m.val)
    (hmul : size * minSize tt ≤ Usize.max)
    (hc2 : ∀ m : Usize, self.config.max_message_size = some m → size * minSize tt ≤ m.val)
    (bs rest : List U8) (hbs : bs.map (·.val) = (Spec.listHeader size ety).map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    ∃ (t' : T) (c : I32), protocol.compact.TCompactInputProtocol.read_list_set_begin inst self =
        ok (.Ok (tt, c), { self with transport := t' }) ∧ c.val = size ∧ rem t' = rest := by
  have he := collType_lt hety
  obtain ⟨ms, hms, hmsv⟩ := min_serialized_size_eq tt
  by_cases h15 : size < 15
  · rw [Spec.listHeader_short h15 (by omega)] at hbs
    have hl : bs.length = 1 := by
      have := congrArg List.length hbs
      simpa using this
    obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.mp hl
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, UInt8.toNat_ofNat'] at hbs
    have hb0 : b0.val = 16 * size + ety := by rw [hbs]; omega
    obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self b0 rest h
    obtain ⟨x, hx, hxv⟩ := hi_nibble b0
    have hlo : (b0 &&& 15#u8).val = ety := by rw [lo_nibble, hb0]; omega
    have hcoll := collection_u8_to_type_ok (b0 &&& 15#u8) tt (by rw [hlo]; exact hety)
    have hxs : x.val = size := by rw [hxv, hb0]; omega
    have hx15 : ¬ x.val = 15 := by omega
    have hcv : (UScalar.hcast IScalarTy.I32 x).val = size := by
      rw [UScalar.hcast_val_eq, hxs, IScalarTy.I32_numBits_eq]
      exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
    have hcc := check_container_size_ok self.config (UScalar.hcast IScalarTy.I32 x) ms (by omega)
      (fun m hm => by rw [hcv]; simpa using hc1 m hm) (by rw [hcv, hmsv]; simpa using hmul)
      (fun m hm => by rw [hcv, hmsv]; simpa using hc2 m hm)
    refine ⟨t1, UScalar.hcast IScalarTy.I32 x, ?_, hcv, ht1⟩
    apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.read_list_set_begin
    aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hcoll, hx, hx15,
      protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.min_serialized_size, hms, hcc,
      not_false_eq_true, _root_.ite_true]
  · rw [Spec.listHeader_long (by omega) (by omega)] at hbs
    obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
      match bs, hbs with
      | b0 :: bs', _ => exact ⟨b0, bs', rfl⟩
    simp only [List.map_cons, List.cons.injEq, UInt8.toNat_ofNat'] at hbs
    obtain ⟨hbs0, hbs'⟩ := hbs
    have hb0 : b0.val = 240 + ety := by rw [hbs0]; omega
    obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self b0 (bs' ++ rest) h
    obtain ⟨x, hx, hxv⟩ := hi_nibble b0
    have hlo : (b0 &&& 15#u8).val = ety := by rw [lo_nibble, hb0]; omega
    have hcoll := collection_u8_to_type_ok (b0 &&& 15#u8) tt (by rw [hlo]; exact hety)
    have hx15 : x.val = 15 := by rw [hxv, hb0]; omega
    have hsz : size < 2 ^ UScalarTy.U32.numBits := by rw [UScalarTy.U32_numBits_eq]; omega
    obtain ⟨t2, hrv, ht2⟩ := read_varint32_D hS hR { self with transport := t1 } (UScalar.ofNatCore size hsz)
      bs' rest (by rw [UScalar.ofNatCore_val_eq, encVar_eq_varint]; exact hbs') (by rw [ht1])
    have hcv : (UScalar.hcast IScalarTy.I32 (UScalar.ofNatCore size hsz : U32)).val = size := by
      rw [UScalar.hcast_val_eq, UScalar.ofNatCore_val_eq, IScalarTy.I32_numBits_eq]
      exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
    have hcc := check_container_size_ok self.config (UScalar.hcast IScalarTy.I32 (UScalar.ofNatCore size hsz : U32))
      ms (by omega) (fun m hm => by rw [hcv]; simpa using hc1 m hm) (by rw [hcv, hmsv]; simpa using hmul)
      (fun m hm => by rw [hcv, hmsv]; simpa using hc2 m hm)
    refine ⟨t2, UScalar.hcast IScalarTy.I32 (UScalar.ofNatCore size hsz : U32), ?_, hcv, ht2⟩
    apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.read_list_set_begin
    aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hcoll, hx, hx15, hrv,
      protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.min_serialized_size, hms, hcc,
      not_true_eq_false, _root_.ite_false]

/-! ## `write_list_set_begin` -/

set_option maxHeartbeats 8000000 in
/-- (E, list/set header) For every size `count ≥ 0` and every element type with a compact nibble,
`write_list_set_begin` appends exactly `Spec.listHeader count ety`. -/
theorem write_list_set_begin_E (hS : StdContract) (hV : VarintContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (tt : protocol.TType) (count : I32) (ety : U8)
    (hety : protocol.compact.collection_type_to_u8 tt = ok ety) (hety16 : ety.val < 16)
    (h0 : 0 ≤ count.val) :
    ∃ t', protocol.compact.TCompactOutputProtocol.write_list_set_begin inst self tt count =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++
        (Spec.listHeader count.val.toNat ety.val).map UInt8.toNat := by
  have hc32 : count.val < 2 ^ 31 := by scalar_tac
  by_cases h14 : count.val ≤ 14
  · -- the one-byte header `count << 4 | ety`
    have hb : (⟨(IScalar.hcast UScalarTy.U8 count).bv <<< 4⟩ ||| ety : U8) =
        mkByte (16 * count.val.toNat ||| ety.val) := by
      apply UScalar.eq_of_val_eq
      have hl : 16 * count.val.toNat ||| ety.val < 2 ^ 8 := Nat.or_lt_two_pow (by omega) (by omega)
      rw [UScalar.val_or, uval_mk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      show ((IScalar.hcast UScalarTy.U8 count).val * 2 ^ 4 % 2 ^ 8 ||| ety.val) = (BitVec.ofNat 8 _).toNat
      rw [IScalar.hcast_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, UScalarTy.U8_numBits_eq]
      congr 1
      omega
    obtain ⟨t', hwb, ht'⟩ := write_byte_ok hS hW self (mkByte (16 * count.val.toNat ||| ety.val))
    refine ⟨t', ?_, ?_⟩
    · apply eq_ok_of_wp
      unfold protocol.compact.TCompactOutputProtocol.write_list_set_begin
      aeneas_wp [hety, h14, u8_shl4, hb, hwb]
    · rw [ht', List.map_append, Spec.listHeader_short (by omega) hety16]
      simp only [List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
      show (BitVec.ofNat 8 _).toNat = _
      rw [BitVec.toNat_ofNat, UInt8.toNat_ofNat']
      have hor := Nat.two_pow_add_eq_or_of_lt (show ety.val < 2 ^ 4 by omega) count.val.toNat
      rw [show 16 * count.val.toNat = 2 ^ 4 * count.val.toNat by ring, ← hor]
  · -- the byte `0xF0 | ety`, then the varint of `count` through the cursor
    have hb240 : (240 ||| ety.val) = 240 + ety.val := by
      have h := Nat.two_pow_add_eq_or_of_lt (show ety.val < 2 ^ 4 by omega) 15
      rw [show (2 : Nat) ^ 4 * 15 = 240 by norm_num] at h
      omega
    have hb : (240#u8 ||| ety : U8) = mkByte (240 + ety.val) := by
      apply UScalar.eq_of_val_eq
      rw [UScalar.val_or, show (240#u8 : U8).val = 240 from rfl, hb240]
      show _ = (BitVec.ofNat 8 _).toNat
      rw [BitVec.toNat_ofNat]
      omega
    obtain ⟨t1, hwb, ht1⟩ := write_byte_ok hS hW self (mkByte (240 + ety.val))
    have hv : (IScalar.hcast UScalarTy.U32 count).val = count.val.toNat := by
      rw [IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq]
      rw [Int.emod_eq_of_lt h0 (by omega)]
    have hlen : (rusttrn_model.leb128 count.val.toNat).length ≤ 5 :=
      leb128_length_le _ 4 (by omega)
    have hbuf0 : (Array.repeat 5#usize (0#u8)).to_slice.val = [0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
      simp [Array.to_slice, Array.repeat_val]
    have hwb5 := writeBytes_cursor0 (rusttrn_model.leb128 count.val.toNat) [0#u8, 0#u8, 0#u8, 0#u8, 0#u8] id
      (by simpa using hlen)
    have hk : (rusttrn_model.leb128 count.val.toNat).length < 2 ^ 64 := by omega
    have hL := leb128_eq_varint count.val.toNat
    suffices hwp : wp (protocol.compact.TCompactOutputProtocol.write_list_set_begin inst self tt count)
        (fun o => ∃ t', o = .ok (.Ok (), { self with transport := t' }) ∧
          (sent t').map (·.val) = (sent self.transport).map (·.val) ++
            (Spec.listHeader count.val.toNat ety.val).map UInt8.toNat) by
      rcases (wp_iff _ _).1 hwp with ⟨a, ha, t', hat, ht'⟩ | ⟨e, _, t', hfalse, _⟩
      · cases hat
        exact ⟨t', ha, ht'⟩
      · cases hfalse
    unfold protocol.compact.TCompactOutputProtocol.write_list_set_begin
    aeneas_wp [hety, h14, hb, hwb, core.result.Result.Insts.CoreOpsTry.branch,
      core.array.Array.index_mut, core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
      thrift.core.io.cursor.Cursor.new, hV.u32, varint_rs.VarintWriterWError.Blanket, rusttrn_model.blanketBase,
      core.slice.index.SliceIndexRangeFullSlice.index_mut, hv, hbuf0, hwb5, thrift.core.io.cursor.Cursor.position,
      Array.index_SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
      UScalar.cast_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, id_eq]
    have hmax : 5 ≤ Usize.max := by scalar_tac
    have hk6 : ∀ k, k < 6 → k % 2 ^ System.Platform.numBits = k := fun k hk => by
      apply Nat.mod_eq_of_lt
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
    revert hL
    generalize rusttrn_model.leb128 count.val.toNat = L at hlen ⊢
    intro hL
    match L, hlen with
  | [], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t', rfl, ?_⟩
    rw [ht', ht1, Spec.listHeader_long (by omega) hety16]
    simp only [Slice.from_val, List.map_append, List.map_cons, List.map_nil, ← hL, List.append_assoc,
      List.singleton_append, List.append_cancel_left_eq, List.cons.injEq, and_true, UInt8.toNat_ofNat']
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat]
  | [a], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t', rfl, ?_⟩
    rw [ht', ht1, Spec.listHeader_long (by omega) hety16]
    simp only [Slice.from_val, List.map_append, List.map_cons, List.map_nil, ← hL, List.append_assoc,
      List.singleton_append, List.append_cancel_left_eq, List.cons.injEq, and_true, UInt8.toNat_ofNat']
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat]
  | [a, b], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t', rfl, ?_⟩
    rw [ht', ht1, Spec.listHeader_long (by omega) hety16]
    simp only [Slice.from_val, List.map_append, List.map_cons, List.map_nil, ← hL, List.append_assoc,
      List.singleton_append, List.append_cancel_left_eq, List.cons.injEq, and_true, UInt8.toNat_ofNat']
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat]
  | [a, b, c], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t', rfl, ?_⟩
    rw [ht', ht1, Spec.listHeader_long (by omega) hety16]
    simp only [Slice.from_val, List.map_append, List.map_cons, List.map_nil, ← hL, List.append_assoc,
      List.singleton_append, List.append_cancel_left_eq, List.cons.injEq, and_true, UInt8.toNat_ofNat']
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat]
  | [a, b, c, d], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t', rfl, ?_⟩
    rw [ht', ht1, Spec.listHeader_long (by omega) hety16]
    simp only [Slice.from_val, List.map_append, List.map_cons, List.map_nil, ← hL, List.append_assoc,
      List.singleton_append, List.append_cancel_left_eq, List.cons.injEq, and_true, UInt8.toNat_ofNat']
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat]
  | [a, b, c, d, e], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t' ht'
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t', rfl, ?_⟩
    rw [ht', ht1, Spec.listHeader_long (by omega) hety16]
    simp only [Slice.from_val, List.map_append, List.map_cons, List.map_nil, ← hL, List.append_assoc,
      List.singleton_append, List.append_cancel_left_eq, List.cons.injEq, and_true, UInt8.toNat_ofNat']
    show (BitVec.ofNat 8 _).toNat = _
    rw [BitVec.toNat_ofNat]

end EquivLean.Demo.Thrift.Rust
