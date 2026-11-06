import EquivLean.Demo.Thrift.RustMalformed

/-!
# Thrift (T4), Rust side: the compact field header reader on every spec header (D)

`read_field_begin` (compact.rs:248) on `Spec.fieldHeader last id ty ++ rest`, for every previous id `last`, every
`i16` id and every type nibble Rust accepts (1..13): it returns the field (its `TType`, `id`) and leaves `rest`. With
the short form for every delta 1..15 (so Rust reads the spec's `[0xF5]` for `Spec.exDelta15`), and the long form
otherwise. Nibbles 1 and 2 (boolean true / false) also set the pending boolean.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-- The pending boolean after a field header with type nibble `ty`. -/
def pendBool (ty : Nat) (p : Option Bool) : Option Bool :=
  if ty = 1 then some true else if ty = 2 then some false else p

theorem u8_to_type_ok (b : U8) (tt : protocol.TType) (h : collType b.val = some tt) (h0 : b.val ≠ 0)
    (h1 : b.val ≠ 1) (h2 : b.val ≠ 2) : protocol.compact.u8_to_type b = ok (.Ok tt) := by
  have hb := collType_lt h
  obtain ⟨n, hn⟩ : ∃ n, b.val = n := ⟨_, rfl⟩
  rw [hn] at h hb h0 h1 h2
  have hbn : b = UScalar.ofNatCore n (Nat.lt_of_lt_of_le hb (by rw [UScalarTy.U8_numBits_eq]; decide)) :=
    UScalar.eq_of_val_eq (by rw [hn]; simp)
  rw [hbn]
  clear hbn hn b
  match n, hb, h, h0, h1, h2 with
  | 3, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 4, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 5, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 6, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 7, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 8, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 9, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 10, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 11, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 12, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl
  | 13, _, h, _, _, _ => simp only [collType, Option.some.injEq] at h; subst h; rfl

theorem collType_ne_stop {n : Nat} {tt : protocol.TType} (h : collType n = some tt) (h0 : n ≠ 0) :
    tt ≠ .Stop := by
  have hb := collType_lt h
  intro htt
  subst htt
  match n, hb, h, h0 with
  | 1, _, h, _ | 2, _, h, _ | 3, _, h, _ | 4, _, h, _ | 5, _, h, _ | 6, _, h, _ | 7, _, h, _ | 8, _, h, _
  | 9, _, h, _ | 10, _, h, _ | 11, _, h, _ | 12, _, h, _ | 13, _, h, _ => simp [collType] at h

theorem collType_bool {n : Nat} (h : collType n = some .Bool) : n = 1 ∨ n = 2 := by
  have hb := collType_lt h
  match n, hb, h with
  | 1, _, _ => exact Or.inl rfl
  | 2, _, _ => exact Or.inr rfl
  | 0, _, h | 3, _, h | 4, _, h | 5, _, h | 6, _, h | 7, _, h | 8, _, h | 9, _, h | 10, _, h | 11, _, h
  | 12, _, h | 13, _, h => simp [collType] at h

theorem i16_checked_add_some (x y : I16) (h1 : -32768 ≤ x.val + y.val) (h2 : x.val + y.val ≤ 32767) :
    ∃ z : I16, I16.checked_add x y = some z ∧ z.val = x.val + y.val := by
  have hs := core.num.checked_add_IScalar_bv_spec x y
  unfold I16.checked_add
  rcases hc : core.num.checked_add_IScalar x y with _ | z
  · rw [hc] at hs
    exfalso
    apply hs
    simp only [IScalar.min, IScalar.max, IScalarTy.I16_numBits_eq]
    omega
  · rw [hc] at hs
    exact ⟨z, rfl, hs.2.2.1⟩

/-! ## The short form -/

set_option maxHeartbeats 16000000 in
/-- The short form: the header byte `16 * delta + ty`, `delta = id - last` in 1..15. -/
theorem read_field_begin_short (hS : StdContract) (hO : OptionContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (id : Int) (hid : Spec.InI16 id)
    (hd : 1 ≤ id - self.last_read_field_id.val ∧ id - self.last_read_field_id.val ≤ 15)
    (ty : Nat) (tt : protocol.TType) (hty : collType ty = some tt) (hty1 : 1 ≤ ty)
    (b0 : U8) (hb0 : b0.val = 16 * (id - self.last_read_field_id.val).toNat + ty)
    (rest : List U8) (h : rem self.transport = b0 :: rest) :
    ∃ (t' : T) (fid : I16), protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
        inst self = ok (.Ok { «name» := none, field_type := tt, id := some fid },
          { self with
            transport := t'
            last_read_field_id := fid
            pending_read_bool_value := pendBool ty self.pending_read_bool_value }) ∧
      fid.val = id ∧ rem t' = rest := by
  have hty14 := collType_lt hty
  obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self b0 rest h
  obtain ⟨x, hx, hxv⟩ := hi_nibble b0
  have hxd : x.val = (id - self.last_read_field_id.val).toNat := by rw [hxv, hb0]; omega
  have hlo : (b0 &&& 15#u8).val = ty := by rw [lo_nibble, hb0]; omega
  have hx0 : ¬ x.val = 0 := by omega
  have hcx : (UScalar.hcast IScalarTy.I16 x).val = id - self.last_read_field_id.val := by
    rw [UScalar.hcast_val_eq, hxd, IScalarTy.I16_numBits_eq, Int.toNat_of_nonneg (by omega)]
    exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
  obtain ⟨z, hz, hzv⟩ := i16_checked_add_some self.last_read_field_id (UScalar.hcast IScalarTy.I16 x)
    (by rw [hcx]; unfold Spec.InI16 at hid; omega) (by rw [hcx]; unfold Spec.InI16 at hid; omega)
  have hzid : z.val = id := by rw [hzv, hcx]; omega
  refine ⟨t1, z, ?_, hzid, ht1⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
  aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hx]
  split
  · rename_i heq
    have h1 : ty = 1 := by rw [← hlo, heq]; rfl
    subst h1
    simp only [collType, Option.some.injEq] at hty
    subst hty
    rw [show pendBool 1 self.pending_read_bool_value = some true from rfl]
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch, hx0, not_false_eq_true, _root_.ite_true, hz,
      hO.ok_or_else_some]
  · rename_i heq
    have h2 : ty = 2 := by rw [← hlo, heq]; rfl
    subst h2
    simp only [collType, Option.some.injEq] at hty
    subst hty
    rw [show pendBool 2 self.pending_read_bool_value = some false from rfl]
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch, hx0, not_false_eq_true, _root_.ite_true, hz,
      hO.ok_or_else_some]
  · rename_i hn1 hn2
    have hv1 : ty ≠ 1 := fun h1 => hn1 (UScalar.eq_of_val_eq (by rw [hlo, h1]; rfl))
    have hv2 : ty ≠ 2 := fun h2 => hn2 (UScalar.eq_of_val_eq (by rw [hlo, h2]; rfl))
    have hu := u8_to_type_ok (b0 &&& 15#u8) tt (by rw [hlo]; exact hty) (by rw [hlo]; omega) (by rw [hlo]; exact hv1)
      (by rw [hlo]; exact hv2)
    have hne := collType_ne_stop hty (by omega)
    have hpb : pendBool ty self.pending_read_bool_value = self.pending_read_bool_value := by
      simp [pendBool, hv1, hv2]
    rw [hpb]
    aeneas_wp [hu, core.result.Result.Insts.CoreOpsTry.branch]
    cases tt <;> first
      | exact absurd rfl hne
      | aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch, hx0, not_false_eq_true, _root_.ite_true, hz,
          hO.ok_or_else_some]

/-! ## The long form -/

set_option maxHeartbeats 16000000 in
/-- The long form: the header byte `ty`, then the zigzag varint of the `i16` id. -/
theorem read_field_begin_long (hS : StdContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (id : Int) (hid : Spec.InI16 id)
    (ty : Nat) (tt : protocol.TType) (hty : collType ty = some tt) (hty1 : 1 ≤ ty)
    (b0 : U8) (hb0 : b0.val = ty) (bs rest : List U8)
    (hbs : bs.map (·.val) = (Spec.varint (Spec.zigzag id)).map UInt8.toNat)
    (h : rem self.transport = b0 :: (bs ++ rest)) :
    ∃ (t' : T) (fid : I16), protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
        inst self = ok (.Ok { «name» := none, field_type := tt, id := some fid },
          { self with
            transport := t'
            last_read_field_id := fid
            pending_read_bool_value := pendBool ty self.pending_read_bool_value }) ∧
      fid.val = id ∧ rem t' = rest := by
  have hty14 := collType_lt hty
  obtain ⟨t1, hrb, ht1⟩ := read_byte_ok hS hR self b0 (bs ++ rest) h
  obtain ⟨x, hx, hxv⟩ := hi_nibble b0
  have hx0 : x.val = 0 := by rw [hxv, hb0]; omega
  have hlo : (b0 &&& 15#u8).val = ty := by rw [lo_nibble, hb0]; omega
  have hz32 : Spec.zigzag id < 2 ^ UScalarTy.U32.numBits := by
    rw [UScalarTy.U32_numBits_eq]; exact Nat.lt_trans (Spec.zigzag_lt16 hid) (by decide)
  have hbsu : bs.map (·.val) = encVar (UScalar.ofNatCore (Spec.zigzag id) hz32 : U32).val := by
    rw [UScalar.ofNatCore_val_eq, encVar_eq_varint]; exact hbs
  obtain ⟨y, hy, hyv⟩ := zigzag_to_i32_val (UScalar.ofNatCore (Spec.zigzag id) hz32)
  have hyid : y.val = id := by rw [hyv, UScalar.ofNatCore_val_eq, ← zz_eq_zigzag, unzz_zz]
  have hcy : (IScalar.cast IScalarTy.I16 y).val = id := by
    rw [IScalar.cast_val_eq, hyid, IScalarTy.I16_numBits_eq, IScalarTy.I32_numBits_eq]
    unfold Spec.InI16 at hid
    exact Int.bmod_eq_of_le_mul_two (by simp; omega) (by simp; omega)
  -- `read_i16` on the transport after the header byte, whatever the other fields
  have hri : ∀ s : protocol.compact.TCompactInputProtocol T, s.transport = t1 → ∃ t2,
      protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16 inst s =
        ok (.Ok (IScalar.cast IScalarTy.I16 y), { s with transport := t2 }) ∧ rem t2 = rest := by
    intro s hs
    obtain ⟨t2, hrv, ht2⟩ := read_varint32_D hS hR s _ bs rest hbsu (by rw [hs, ht1])
    refine ⟨t2, ?_, ht2⟩
    apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_i16
    aeneas_wp [hrv, core.result.Result.Insts.CoreOpsTry.branch, hy]
  by_cases h1 : ty = 1
  · subst h1
    simp only [collType, Option.some.injEq] at hty
    subst hty
    obtain ⟨t2, hr2, ht2⟩ := hri { { self with transport := t1 } with pending_read_bool_value := some true } rfl
    refine ⟨t2, _, ?_, hcy, ht2⟩
    rw [show pendBool 1 self.pending_read_bool_value = some true from rfl]
    apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
    aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hx]
    split
    · aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch, hx0, hr2, not_true_eq_false, _root_.ite_false]
    · rename_i heq
      exfalso
      have := congrArg UScalar.val heq
      rw [hlo] at this
      exact absurd this (by decide)
    · rename_i hn1 _
      exact absurd (UScalar.eq_of_val_eq (by rw [hlo]; rfl)) hn1
  · by_cases h2 : ty = 2
    · subst h2
      simp only [collType, Option.some.injEq] at hty
      subst hty
      obtain ⟨t2, hr2, ht2⟩ := hri { { self with transport := t1 } with pending_read_bool_value := some false } rfl
      refine ⟨t2, _, ?_, hcy, ht2⟩
      rw [show pendBool 2 self.pending_read_bool_value = some false from rfl]
      apply eq_ok_of_wp
      unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
      aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hx]
      split
      · rename_i heq
        exfalso
        have := congrArg UScalar.val heq
        rw [hlo] at this
        exact absurd this (by decide)
      · aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch, hx0, hr2, not_true_eq_false, _root_.ite_false]
      · rename_i _ hn2
        exact absurd (UScalar.eq_of_val_eq (by rw [hlo]; rfl)) hn2
    · obtain ⟨t2, hr2, ht2⟩ := hri { self with transport := t1 } rfl
      refine ⟨t2, _, ?_, hcy, ht2⟩
      have hpb : pendBool ty self.pending_read_bool_value = self.pending_read_bool_value := by
        simp [pendBool, h1, h2]
      rw [hpb]
      have hu := u8_to_type_ok (b0 &&& 15#u8) tt (by rw [hlo]; exact hty) (by rw [hlo]; omega)
        (by rw [hlo]; exact h1) (by rw [hlo]; exact h2)
      have hne := collType_ne_stop hty (by omega)
      apply eq_ok_of_wp
      unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
      aeneas_wp [hrb, core.result.Result.Insts.CoreOpsTry.branch, hx]
      split
      · rename_i heq
        exfalso
        exact h1 (by rw [← hlo, heq]; rfl)
      · rename_i heq
        exfalso
        exact h2 (by rw [← hlo, heq]; rfl)
      · aeneas_wp [hu, core.result.Result.Insts.CoreOpsTry.branch]
        cases tt <;> first
          | exact absurd rfl hne
          | aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch, hx0, hr2, not_true_eq_false, _root_.ite_false]

/-! ## Every spec header -/

/-- (D, compact field header) For every previous id `last`, every `i16` id and every type nibble Rust accepts
(1..13), `read_field_begin` on `Spec.fieldHeader last id ty ++ rest` returns the field (`collType ty`, `id`), records
`id` as the last id, sets the pending boolean for nibbles 1 / 2, and leaves exactly `rest`. -/
theorem read_field_begin_D (hS : StdContract) (hO : OptionContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (id : Int) (hid : Spec.InI16 id)
    (ty : Nat) (tt : protocol.TType) (hty : collType ty = some tt) (hty1 : 1 ≤ ty)
    (bs rest : List U8)
    (hbs : bs.map (·.val) = (Spec.fieldHeader self.last_read_field_id.val id ty).map UInt8.toNat)
    (h : rem self.transport = bs ++ rest) :
    ∃ (t' : T) (fid : I16), protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
        inst self = ok (.Ok { «name» := none, field_type := tt, id := some fid },
          { self with
            transport := t'
            last_read_field_id := fid
            pending_read_bool_value := pendBool ty self.pending_read_bool_value }) ∧
      fid.val = id ∧ rem t' = rest := by
  have hty14 := collType_lt hty
  by_cases hd : 1 ≤ id - self.last_read_field_id.val ∧ id - self.last_read_field_id.val ≤ 15
  · rw [Spec.fieldHeader_short hd (by omega)] at hbs
    have hl : bs.length = 1 := by
      have := congrArg List.length hbs
      simpa using this
    obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.mp hl
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, UInt8.toNat_ofNat'] at hbs
    exact read_field_begin_short hS hO hR self id hid hd ty tt hty hty1 b0 (by rw [hbs]; omega) rest h
  · rw [Spec.fieldHeader_long hd] at hbs
    obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
      match bs, hbs with
      | b0 :: bs', _ => exact ⟨b0, bs', rfl⟩
    simp only [List.map_cons, List.cons.injEq, UInt8.toNat_ofNat'] at hbs
    obtain ⟨hbs0, hbs'⟩ := hbs
    exact read_field_begin_long hS hR self id hid ty tt hty hty1 b0 (by rw [hbs0]; omega) bs' rest hbs' h

/-- The spec's bytes for `Spec.exDelta15`, `[0xF5]`, after field id 0: Rust's `read_field_begin` reads the field
(I32, 15). So Rust reads the short form the spec (and C++/Java, per their theorems) write for delta 15, although its
writer emits the long form `[0x05, 0x1E]` (`write_field_header_exDelta15`). -/
theorem read_field_begin_exDelta15_short (hS : StdContract) (hO : OptionContract) {T : Type}
    {inst : transport.TReadTransport T} {rem : T → List U8} (hR : ReadContract inst rem)
    (self : protocol.compact.TCompactInputProtocol T) (rest : List U8)
    (hlast : self.last_read_field_id.val = Spec.exDelta15.last) (h : rem self.transport = 0xF5#u8 :: rest) :
    ∃ (t' : T) (fid : I16), protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_field_begin
        inst self = ok (.Ok { «name» := none, field_type := .I32, id := some fid },
          { self with transport := t', last_read_field_id := fid }) ∧ fid.val = 15 ∧ rem t' = rest := by
  obtain ⟨t', fid, hr, hf, ht'⟩ := read_field_begin_D hS hO hR self 15 (by decide) 5 .I32 rfl (by decide)
    [0xF5#u8] rest (by rw [hlast]; decide) h
  exact ⟨t', fid, hr, hf, ht'⟩

/-! ## The writer against `Spec.fieldHeader` -/

/-- `specFieldHeader` (RustWrite) is `Spec.fieldHeader` as byte values, for every type nibble. -/
theorem specFieldHeader_eq (last id : Int) (ty : Nat) (hty : ty < 16) :
    specFieldHeader last id ty = (Spec.fieldHeader last id ty).map UInt8.toNat := by
  unfold specFieldHeader
  by_cases hd : 1 ≤ id - last ∧ id - last ≤ 15
  · rw [ite_eq_left hd, Spec.fieldHeader_short hd hty]
    simp only [List.map_cons, List.map_nil, UInt8.toNat_ofNat']
    congr 1
    omega
  · rw [ite_eq_right hd, Spec.fieldHeader_long hd]
    simp only [List.map_cons, UInt8.toNat_ofNat', leb128_eq_varint, zz_eq_zigzag]
    congr 1
    omega

/-- (E, compact field header) For every type nibble and every field id whose delta from the last id is an `i16`
other than 15, `write_field_header` appends exactly `Spec.fieldHeader last id ty`. (Delta 15:
`write_field_header_delta15`, the discrepancy; delta outside `i16`: `write_field_header_overflow`.) -/
theorem write_field_header_E (hS : StdContract) (hSh : ShiftContract) {T : Type}
    {inst : transport.TWriteTransport T} {sent : T → List U8} (hW : WriteContract inst sent)
    (self : protocol.compact.TCompactOutputProtocol T) (ty : U8) (id : I16) (hty : ty.val < 16)
    (hd : -32768 ≤ id.val - self.last_write_field_id.val ∧ id.val - self.last_write_field_id.val ≤ 32767)
    (h15 : id.val - self.last_write_field_id.val ≠ 15) :
    ∃ t', protocol.compact.TCompactOutputProtocol.write_field_header inst self ty id =
        ok (.Ok (), { self with transport := t', last_write_field_id := id }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++
        (Spec.fieldHeader self.last_write_field_id.val id.val ty.val).map UInt8.toNat := by
  rcases (wp_iff _ _).1 (write_field_header_wp hS hSh hW self ty id hd) with ⟨a, ha, t', hat, ht'⟩ |
    ⟨e, _, t', hfalse, _⟩
  · cases hat
    refine ⟨t', ha, ?_⟩
    rw [ht', List.map_append, rustFieldHeader_spec self.last_write_field_id id ty hty h15,
      specFieldHeader_eq _ _ _ hty]
  · cases hfalse

end EquivLean.Demo.Thrift.Rust
