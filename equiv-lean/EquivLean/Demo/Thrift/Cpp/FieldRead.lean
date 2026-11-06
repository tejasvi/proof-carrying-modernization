import EquivLean.Demo.Thrift.Cpp.FieldHeader

/-!
# Thrift, C++ side: compact field header, reader (D, and M on C++'s semantics)

`TCompactProtocolT<TTransport>::readFieldBegin(name, fieldType, fieldId)` reads the header byte `b` (`readByte`),
its type nibble `b & 0x0F` and delta nibble `b >> 4`, then:
* `readFieldBegin_stop`: type nibble 0: the end of the struct (`T_STOP`, id 0), whatever the delta nibble;
* `readFieldBegin_short`: a nonzero delta `d`: the id `(int16_t)(lastFieldId_ + d)`;
* `readFieldBegin_long`: delta 0: the id from `readI16` (a varint, `(int16_t)` of its inverse zigzag modulo `2^32`);
and the TType from `getTType`.  The callees by their proved specifications: `readByte_D` (the transport's
`readAll` of one byte), `getTType_D`, `readI16_ok` (`readVarint32_ok`, `zigzagToI32_D`).
`readFieldBegin_D`: every header of the spec (`Spec.fieldHeader`) reads back as its type and id, leaving the rest.
On the inputs where the languages can differ: `readFieldBegin_exI16Overflow_short` (`15` after 32767: id -32768,
the spec rejects), `readFieldBegin_exDelta15_long` (`05 1E` after 0: id 15, as the spec),
`readFieldBegin_stopNibble` (`10`: STOP, the spec rejects).
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

def symReadByte : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE8readByteERa"
def symGetTType : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE8getTTypeEa"
def symReadI16 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE7readI16ERs"

/-- `readByte(b)` with a byte left: stores it (as an `int8_t`) and consumes it. -/
theorem readByte_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hFp : ∀ b, Fp b → b < m.next)
    (bo : Nat) (ko : BlockKind) (vo : Val) (cirH_bo : m.blocks bo = some ⟨ko, true, .int true 8, vo⟩)
    (hko : ko ≠ .readonly) (hbo : bo < m.next) (hboF : ¬ Fp bo) (hne : srcOf m ≠ []) :
    Returns ctx symReadByte [.ptr (.loc pb []), .ptr (.loc bo [])] m
      (fun r m' => r = some (.int 1) ∧
        m'.blocks bo = some ⟨ko, true, .int true 8, .int (wrap true 8 ((srcOf m).headD 0))⟩ ∧
        srcOf m' = (srcOf m).tail ∧ m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ bo → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TR.stable
  have hR := TR.readAll1a
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_ko := hko
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  have neFp : ∀ b, Fp b → b ≠ bo := fun b hb h => hboF (h ▸ hb)
  have hb256 : (srcOf m).headD 0 < 256 := by
    cases h : srcOf m with
    | nil => exact absurd h hne
    | cons c rest => exact TR.bytes m c (by rw [h]; simp)
  cir_run
  all_goals try simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]
  case h.hspec.refine'_8 => exact hne
  -- the byte is a `uint8_t` value: the other branches of the load are dead
  all_goals try (simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM] at *; omega)
  all_goals try
    rw [hstable cir_mem0 _ (fun b hb => by
      have := hFp b hb; dsimp only
      simp (disch := first | omega | exact neFp _ hb) only [killRange_of_lt, upd_apply_ne]), cirH_post0bba]
    simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]

/-- `getTType(c)`: the TType of every compact type nibble `c` that has one (`Spec.ttypeOfCompact`). -/
theorem getTType_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (m : Mem) (this : Ptr) (c t : Nat) (ht : Spec.ttypeOfCompact c = some t) :
    Returns ctx symGetTType [.ptr this, .int c] m
      (fun r m' => r = some (.int t) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_getTType.nothrow = false := rfl
  unfold Spec.ttypeOfCompact at ht
  split at ht <;> cases ht
  all_goals
    unfold Returns Calls
    rw [evalCall_body cirH_f rfl rfl]
  all_goals cir_run

theorem wrap_u32_s32 (z : Nat) : wrap false 32 (wrap true 32 (z : Int)) = ((z % 2 ^ 32 : Nat) : Int) := by
  unfold wrap
  simp only [Bool.true_and, Bool.false_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow, Bool.false_eq_true,
    ite_false]
  split <;> omega

/-- `readI16(i16)` on a source whose first at most 10 bytes are a varint of value `z`: stores the inverse zigzag of
`z mod 2^32`, as an `int16_t` (`readVarint32`, then `(int16_t)zigzagToI32(value)`). -/
theorem readI16_ok (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadI16 = some fn_apache_thrift_protocol_TCompactProtocolT_readI16)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_fz : ctx.mod.findFunc? symZigzagToI32 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI32)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bo : Nat) (ko : BlockKind) (vo : Val) (cirH_bo : m.blocks bo = some ⟨ko, true, .int true 16, vo⟩)
    (hko : ko ≠ .readonly) (hbo : bo < m.next) (hboF : ¬ Fp bo)
    (bs rest : Spec.Bytes) (z : Nat) (hrd : Spec.readVarint 10 bs = some (z, rest))
    (hsrc : srcOf m = bs.map UInt8.toNat) :
    Returns ctx symReadI16 [.ptr (.loc pb []), .ptr (.loc bo [])] m
      (fun r m' => r = some (.int (bs.length - rest.length : Nat)) ∧
        m'.blocks bo = some ⟨ko, true, .int true 16, .int (wrap true 16 (unzigzag ((z % 2 ^ 32 : Nat) : Int)))⟩ ∧
        srcOf m' = rest.map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ bo → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_spec32 := fun m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 h10 =>
    readVarint32_ok ctx cirH_f32 cirH_f64 tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 bs rest
      z hrd h10
  have cirH_specz := fun m' this z' hz' => zigzagToI32_D ctx cirH_fz m' this z' hz'
  have cirH_w := wrap_u32_s32 z
  have hlen := readVarint_len 10 bs z rest hrd
  have neFp : ∀ b, Fp b → b ≠ bo := fun b hb h => hboF (h ▸ hb)
  have cirH_ko := hko
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readI16.nothrow = false := rfl
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  case h.hspec.refine'_5 => omega
  case h.hspec.refine'_6 => exact hpbF
  case h.hspec.refine'_7 => rename_i b hb; have := hFp b hb; omega
  case h.hspec.refine'_12 => omega
  case h.hspec.refine'_14 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  case h.hspec.left => omega
  case h.hspec.right => omega
  case h.right.right.left =>
    rw [hstable cir_mem4 _ (fun b hb => by
      have := hFp b hb; dsimp only
      simp (disch := first | omega | exact neFp _ hb) only [killRange_of_lt, upd_apply_ne]),
      hstable cir_mem0 cir_mem4 (fun b hb => by
        have := hFp b hb; rw [cirH_post4bb b (by omega)]; simp (disch := omega) only [upd_apply_ne]), cirH_post0bba]
  case h.right.right.right.left => omega

/-- The type nibble `(int)(int8_t)b & 0x0F` of a byte `b`. -/
theorem lo_nibble_s8 (c : Nat) :
    bitwise true 32 (fun x1 x2 => x1 &&& x2) (wrap true 8 (c : Int)) 15 = ((c % 16 : Nat) : Int) := by
  unfold bitwise
  simp only [ite_true]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_and, BitVec.toNat_ofInt, show (BitVec.ofInt 32 15).toNat = 15 by decide,
    show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  unfold wrap
  simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]
  split <;> split <;> omega

theorem wrap_s32_s8 (x : Int) : wrap true 32 (wrap true 8 x) = wrap true 8 x := by
  unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> split <;> omega

theorem wrap_s8_nat {n : Nat} (h : n < 128) : wrap true 8 (n : Int) = n := by
  unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

theorem wrap_s32_nat {n : Nat} (h : n < 2 ^ 31) : wrap true 32 (n : Int) = n := by
  unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

theorem nat_and_240_tbl : ∀ y, y < 256 → y &&& 240 = 16 * (y / 16) := by
  set_option maxRecDepth 100000 in decide

theorem nat_and_240 (x : Nat) : x &&& 240 = 16 * ((x % 256) / 16) := by
  rw [show x &&& 240 = (x &&& 255) &&& 240 by rw [Nat.and_assoc]; rfl, show (255 : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact nat_and_240_tbl _ (Nat.mod_lt _ (by decide))

/-- The delta nibble `(uint8_t)((int)(int8_t)b & 0xF0)` of a byte `b`, before the shift. -/
theorem hi_nibble_s8 {c : Nat} (hc : c < 256) :
    wrap false 8 (bitwise true 32 (fun x1 x2 => x1 &&& x2) (wrap true 8 (c : Int)) 240) = ((16 * (c / 16) : Nat) : Int) := by
  unfold bitwise
  simp only [ite_true]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_and, BitVec.toNat_ofInt, show (BitVec.ofInt 32 240).toNat = 240 by decide,
    nat_and_240]
  have key : ((wrap true 8 (c : Int)) % ((2 ^ 32 : Nat) : Int)).toNat % 256 = c := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  rw [key]
  unfold wrap; simp only [Bool.false_and, Bool.false_eq_true, ite_false, Nat.reduceSub, Int.reducePow]
  split <;> omega

/-- The type nibble `(int)b & 0x0F` of a byte value below 128 (the cast to `int8_t` changes nothing). -/
theorem lo_nibble_nat (c : Nat) :
    bitwise true 32 (fun x1 x2 => x1 &&& x2) (c : Int) 15 = ((c % 16 : Nat) : Int) := by
  unfold bitwise
  simp only [ite_true]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_and, BitVec.toNat_ofInt, show (BitVec.ofInt 32 15).toNat = 15 by decide,
    show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  split <;> omega

/-- The delta nibble of a byte value below 128, before the shift. -/
theorem hi_nibble_nat {c : Nat} (hc : c < 256) :
    wrap false 8 (bitwise true 32 (fun x1 x2 => x1 &&& x2) (c : Int) 240) = ((16 * (c / 16) : Nat) : Int) := by
  unfold bitwise
  simp only [ite_true]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_and, BitVec.toNat_ofInt, show (BitVec.ofInt 32 240).toNat = 240 by decide,
    nat_and_240]
  have key : ((c : Int) % ((2 ^ 32 : Nat) : Int)).toNat % 256 = c := by omega
  rw [key]
  unfold wrap; simp only [Bool.false_and, Bool.false_eq_true, ite_false, Nat.reduceSub, Int.reducePow]
  split <;> omega

def symReadFieldBegin : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE14readFieldBeginERNSt3__112basic_stringIcNS6_11char_traitsIcEENS6_9allocatorIcEEEERNS1_5TTypeERs"

set_option hygiene false in
/-- The setup shared by the `readFieldBegin` theorems: the callees `readByte` (on the header byte `b`), the
blocks, the source, the type nibble. -/
macro "fieldread_setup" : tactic => `(tactic| (
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  have cirH_kp := hkp
  have cirH_kt := hkt
  have cirH_ki := hki
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin.nothrow = false := rfl
  have cirH_pbt : pb ≠ bt := fun h => by subst h; rw [cirH_pb] at cirH_bt; simp at cirH_bt
  have cirH_btp : bt ≠ pb := fun h => cirH_pbt h.symm
  have cirH_pbi : pb ≠ bi := fun h => by subst h; rw [cirH_pb] at cirH_bi; simp at cirH_bi
  have cirH_bip : bi ≠ pb := fun h => cirH_pbi h.symm
  have cirH_bti := hbti
  have neFpPb : ∀ b, Fp b → b ≠ pb := fun b hb h => hpbF (h ▸ hb)
  have neFpBt : ∀ b, Fp b → b ≠ bt := fun b hb h => hbtF (h ▸ hb)
  have neFpBi : ∀ b, Fp b → b ≠ bi := fun b hb h => hbiF (h ▸ hb)
  have cirH_bit : bi ≠ bt := fun h => hbti h.symm
  have cirH_specb : ∀ (m' : Mem) (pb' : Nat) (kp' : BlockKind) (v' : Val),
      m'.blocks pb' = some ⟨kp', true, .record recProto, v'⟩ → v'.get? [PathElem.idx 1] = some (.ptr tp) →
      pb' < m'.next → (∀ b, Fp b → b < m'.next) →
      ∀ (bo' : Nat) (ko' : BlockKind) (vo' : Val), m'.blocks bo' = some ⟨ko', true, .int true 8, vo'⟩ →
      ko' ≠ .readonly → bo' < m'.next → ¬ Fp bo' → srcOf m' = (b :: tl).map UInt8.toNat →
      Returns ctx symReadByte [.ptr (.loc pb' []), .ptr (.loc bo' [])] m'
        (fun r m'' => r = some (.int 1) ∧
          m''.blocks bo' = some ⟨ko', true, .int true 8, .int (wrap true 8 b.toNat)⟩ ∧
          srcOf m'' = tl.map UInt8.toNat ∧ m'.next ≤ m''.next ∧
          ∀ b'', ¬ Fp b'' → b'' ≠ bo' → b'' < m'.next → m''.blocks b'' = m'.blocks b'') :=
    fun m' pb' kp' v' h1 h2 h3 h4 bo' ko' vo' h5 h6 h7 h8 h9 =>
      returns_mono (readByte_D ctx cirH_fb tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 bo' ko' vo' h5 h6 h7 h8
        (by rw [h9]; simp)) (fun r m'' ⟨e1, e2, e3, e4, e5⟩ => ⟨e1, by rw [e2, h9]; rfl, by rw [e3, h9]; rfl, e4, e5⟩)
  have hb256 := b.toNat_lt
  have cirH_lo := lo_nibble_s8 b.toNat
  have cirH_lo' := lo_nibble_nat b.toNat
  have cirH_hi' := hi_nibble_nat hb256
  have cirH_w328 := wrap_s32_s8
  have cirH_w8 : wrap true 8 ((b.toNat % 16 : Nat) : Int) = ((b.toNat % 16 : Nat) : Int) := wrap_s8_nat (by omega)
  have cirH_w32 : wrap true 32 ((b.toNat % 16 : Nat) : Int) = ((b.toNat % 16 : Nat) : Int) := wrap_s32_nat (by omega)))

/-- `readFieldBegin` on a header byte `b` with a nonzero delta nibble `d` and a type nibble `c` that has a TType
`t`: the field id `(int16_t)(last + d)`, the type `t`; one byte read. -/
theorem readFieldBegin_short (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (last : Int) (cirH_last : fs[5]? = some (.int last)) (hlast : Spec.InI16 last)
    (x0 x1 : Val) (cirH_bv : fs[3]? = some (.agg [x0, x1]))
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (b : UInt8) (tl : Spec.Bytes) (hsrc : srcOf m = (b :: tl).map UInt8.toNat)
    (t : Nat) (ht : Spec.ttypeOfCompact (b.toNat % 16) = some t) (hc0 : b.toNat % 16 ≠ 0) (hd0 : b.toNat / 16 ≠ 0) :
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 1) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int (wrap true 16 (last + (b.toNat / 16 : Nat)))⟩ ∧
        srcOf m' = tl.map UInt8.toNat ∧ m.next ≤ m'.next) := by
  fieldread_setup
  have cirH_lastr : -32768 ≤ last ∧ last ≤ 32767 := ⟨hlast.1, by have := hlast.2; omega⟩
  have cirH_w16l : wrap true 16 last = last := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_w32l : wrap true 32 last = last := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_c0 : ¬ ((b.toNat % 16 : Nat) : Int) = 0 := by omega
  have cirH_hi := hi_nibble_s8 hb256
  have cirH_w32hi : wrap true 32 ((16 * (b.toNat / 16) : Nat) : Int) = ((16 * (b.toNat / 16) : Nat) : Int) :=
    wrap_s32_nat (by omega)
  have cirH_div : ((16 * (b.toNat / 16) : Nat) : Int) / 16 = ((b.toNat / 16 : Nat) : Int) := by omega
  have cirH_w16 : wrap true 16 ((b.toNat / 16 : Nat) : Int) = ((b.toNat / 16 : Nat) : Int) := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_w32d : wrap true 32 ((b.toNat / 16 : Nat) : Int) = ((b.toNat / 16 : Nat) : Int) := wrap_s32_nat (by omega)
  have cirH_d0 : ¬ ((b.toNat / 16 : Nat) : Int) = 0 := by omega
  have cirH_t16 : t ≤ 16 := by unfold Spec.ttypeOfCompact at ht; split at ht <;> cases ht <;> decide
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  have cirH_spect := fun m' this => getTType_D ctx cirH_ft m' this (b.toNat % 16) t ht
  cir_run
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  case h.hspec.refine'_13 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  -- the stores of `boolValue_` store booleans
  all_goals try (rename_i hbad; by_cases hh : (b.toNat : Int) % 16 = 1 <;> simp [hh] at hbad <;> omega)
  all_goals
    rw [hstable cir_mem4 _ (fun b' hb' => by
      have := hFp b' hb'; dsimp only
      simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBi _ hb')
        only [killRange_of_lt, upd_apply_ne]),
      hstable cir_mem0 cir_mem4 (fun b' hb' => by
        have := hFp b' hb'; rw [cirH_post4bb b' (by omega)]
        simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBi _ hb')
          only [upd_apply_ne]), cirH_post0bba]

/-- `readFieldBegin` on a header byte `b` whose type nibble is 0: C++ tests the type nibble only, so this is the end
of the struct (`T_STOP`, field id 0) whatever the delta nibble; one byte read. -/
theorem readFieldBegin_stop (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (b : UInt8) (tl : Spec.Bytes) (hsrc : srcOf m = (b :: tl).map UInt8.toNat)
    (hc0 : b.toNat % 16 = 0) :
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 1) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int 0⟩ ∧ m'.blocks bi = some ⟨ki, true, .int true 16, .int 0⟩ ∧
        srcOf m' = tl.map UInt8.toNat ∧ m.next ≤ m'.next) := by
  fieldread_setup
  have cirH_c0 : ((b.toNat % 16 : Nat) : Int) = 0 := by omega
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  case h.hspec.refine'_13 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  case h.right.right.right.left =>
    rw [hstable cir_mem0 _ (fun b' hb' => by
      have := hFp b' hb'; dsimp only
      simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBi _ hb')
        only [killRange_of_lt, upd_apply_ne]), cirH_post0bba]

/-- `readFieldBegin` on a header byte `b` with delta nibble 0 and a type nibble that has a TType `t`, followed by a
varint of value `z` (at most 10 bytes): the field id is `readI16`'s, `(int16_t)` of the inverse zigzag of
`z mod 2^32`. -/
theorem readFieldBegin_long (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_fi : ctx.mod.findFunc? symReadI16 = some fn_apache_thrift_protocol_TCompactProtocolT_readI16)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_fz : ctx.mod.findFunc? symZigzagToI32 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI32)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (last : Int) (cirH_last : fs[5]? = some (.int last)) (hlast : Spec.InI16 last)
    (x0 x1 : Val) (cirH_bv : fs[3]? = some (.agg [x0, x1]))
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (b : UInt8) (tl : Spec.Bytes) (hsrc : srcOf m = (b :: tl).map UInt8.toNat)
    (t : Nat) (ht : Spec.ttypeOfCompact (b.toNat % 16) = some t) (hc0 : b.toNat % 16 ≠ 0) (hd0 : b.toNat / 16 = 0)
    (z : Nat) (rest : Spec.Bytes) (hrd : Spec.readVarint 10 tl = some (z, rest)) :
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (1 + (tl.length - rest.length : Nat))) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int (wrap true 16 (unzigzag ((z % 2 ^ 32 : Nat) : Int)))⟩ ∧
        srcOf m' = rest.map UInt8.toNat ∧ m.next ≤ m'.next) := by
  fieldread_setup
  have cirH_lastr : -32768 ≤ last ∧ last ≤ 32767 := ⟨hlast.1, by have := hlast.2; omega⟩
  have cirH_w16l : wrap true 16 last = last := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_w32l : wrap true 32 last = last := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_c0 : ¬ ((b.toNat % 16 : Nat) : Int) = 0 := by omega
  have cirH_hi := hi_nibble_s8 hb256
  have cirH_w32hi : wrap true 32 ((16 * (b.toNat / 16) : Nat) : Int) = ((16 * (b.toNat / 16) : Nat) : Int) :=
    wrap_s32_nat (by omega)
  have cirH_div : ((16 * (b.toNat / 16) : Nat) : Int) / 16 = ((b.toNat / 16 : Nat) : Int) := by omega
  have cirH_w16 : wrap true 16 ((b.toNat / 16 : Nat) : Int) = ((b.toNat / 16 : Nat) : Int) := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_w32d : wrap true 32 ((b.toNat / 16 : Nat) : Int) = ((b.toNat / 16 : Nat) : Int) := wrap_s32_nat (by omega)
  have cirH_d0 : ((b.toNat / 16 : Nat) : Int) = 0 := by omega
  have cirH_t16 : t ≤ 16 := by unfold Spec.ttypeOfCompact at ht; split at ht <;> cases ht <;> decide
  have hlen := readVarint_len 10 tl z rest hrd
  have cirH_speci := fun m' pb' kp' v' h1 h2 h3 h4 h5 bo' ko' vo' h6 h7 h8 h9 h10 =>
    readI16_ok ctx cirH_fi cirH_f32 cirH_f64 cirH_fz tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 h5 bo' ko' vo' h6 h7 h8 h9
      tl rest z hrd h10
  have cirH_spect := fun m' this => getTType_D ctx cirH_ft m' this (b.toNat % 16) t ht
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  case h.hspec.refine'_13 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  all_goals try (rename_i hbad; by_cases hh : (b.toNat : Int) % 16 = 1 <;> simp [hh] at hbad <;> omega)
  case h.hspec.refine'_14 =>
    simp (disch := (apply cirH_nfp; omega)) only [srcU]
    rw [hstable cir_mem0 ⟨cir_mem0.blocks, cir_mem0.next⟩ (fun b _ => rfl), cirH_post0bba]
  all_goals
    rw [hstable cir_mem8 _ (fun b' hb' => by
      have := hFp b' hb'; dsimp only
      simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBi _ hb')
        only [killRange_of_lt, upd_apply_ne]),
      hstable cir_mem4 cir_mem8 (fun b' hb' => by
        have := hFp b' hb'; rw [cirH_post8bb b' (by omega)]
        simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBi _ hb')
          only [killRange_of_lt, upd_apply_ne]), cirH_post4bba]

theorem wrap16_id {x : Int} (h : -32768 ≤ x ∧ x < 32768) : wrap true 16 x = x := by
  unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

/-- (D) A field header of the spec (`Spec.fieldHeader last id ty`, every type nibble `ty` with a TType `t`, every
`int16_t` `id`), then any bytes `rest`: `readFieldBegin` returns the type `t` and the id `id`, reads the header's
bytes and leaves exactly `rest`. -/
theorem readFieldBegin_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_fi : ctx.mod.findFunc? symReadI16 = some fn_apache_thrift_protocol_TCompactProtocolT_readI16)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_fz : ctx.mod.findFunc? symZigzagToI32 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI32)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (last : Int) (cirH_last : fs[5]? = some (.int last)) (hlast : Spec.InI16 last)
    (x0 x1 : Val) (cirH_bv : fs[3]? = some (.agg [x0, x1]))
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (ty t : Nat) (ht : Spec.ttypeOfCompact ty = some t) (hty : 1 ≤ ty ∧ ty < 16)
    (id : Int) (hid : Spec.InI16 id) (rest : Spec.Bytes)
    (hsrc : srcOf m = (Spec.fieldHeader last id ty ++ rest).map UInt8.toNat) :
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (Spec.fieldHeader last id ty).length) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧ m'.blocks bi = some ⟨ki, true, .int true 16, .int id⟩ ∧
        srcOf m' = rest.map UInt8.toNat ∧ m.next ≤ m'.next) := by
  unfold Spec.InI16 at hid hlast
  by_cases hd : 1 ≤ id - last ∧ id - last ≤ 15
  · -- the short form: one byte `delta << 4 | ty`
    rw [Spec.fieldHeader_short hd hty.2] at hsrc ⊢
    have hb : (UInt8.ofNat (16 * (id - last).toNat + ty)).toNat = 16 * (id - last).toNat + ty := by
      rw [UInt8.toNat_ofNat']; omega
    refine returns_mono (readFieldBegin_short ctx cirH_f cirH_fb cirH_ft tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp last cirH_last hlast x0 x1 cirH_bv nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti (UInt8.ofNat (16 * (id - last).toNat + ty)) rest
      (by rw [hsrc]; rfl) t (by rw [hb, show (16 * (id - last).toNat + ty) % 16 = ty by omega]; exact ht)
      (by rw [hb]; omega) (by rw [hb]; omega)) ?_
    rintro r m' ⟨e1, e2, e3, e4, e5⟩
    refine ⟨e1, e2, ?_, e4, e5⟩
    rw [e3, hb, show (16 * (id - last).toNat + ty) / 16 = (id - last).toNat by omega,
      Int.toNat_of_nonneg (show 0 ≤ id - last by omega), show last + (id - last) = id by omega, wrap16_id hid]
  · -- the long form: the byte `ty`, then the zigzag varint of the id
    rw [Spec.fieldHeader_long hd] at hsrc ⊢
    have hb : (UInt8.ofNat ty).toNat = ty := by rw [UInt8.toNat_ofNat']; omega
    have hz : Spec.zigzag id < 2 ^ 16 := Spec.zigzag_lt16 ⟨hid.1, hid.2⟩
    have hrd := Spec.readVarint_varint 10 (Spec.zigzag id) rest
      (Nat.le_trans (Spec.varint_length_le5 (Nat.lt_trans hz (by decide))) (by decide))
    refine returns_mono (readFieldBegin_long ctx cirH_f cirH_fb cirH_fi cirH_f32 cirH_f64 cirH_fz cirH_ft tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp last cirH_last hlast x0 x1 cirH_bv nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti (UInt8.ofNat ty) (Spec.varint (Spec.zigzag id) ++ rest)
      (by rw [hsrc]; rfl) t (by rw [hb, Nat.mod_eq_of_lt hty.2]; exact ht) (by rw [hb]; omega) (by rw [hb]; omega)
      (Spec.zigzag id) rest hrd) ?_
    rintro r m' ⟨e1, e2, e3, e4, e5⟩
    refine ⟨?_, e2, ?_, e4, e5⟩
    · rw [e1]; simp only [List.length_cons, List.length_append]; congr 2; omega
    · rw [e3, Nat.mod_eq_of_lt (Nat.lt_trans hz (by decide)), ← zigzag_eq_spec, unzigzag_zigzag, wrap16_id hid]

/-! ## The inputs where the languages can differ, on C++'s semantics

The TType of the field is `T_I32` (8, compact type 5). -/

/-- `15` after id 32767 (`Spec.exI16Overflow.last`): C++ reads field id `(int16_t)(32767 + 1) = -32768`, type
`T_I32`, where the spec has `DeltaIdOverflow` (`Spec.readFieldHeader_exI16Overflow_short`). -/
theorem readFieldBegin_exI16Overflow_short (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (cirH_last : fs[5]? = some (.int Spec.exI16Overflow.last))
    (x0 x1 : Val) (cirH_bv : fs[3]? = some (.agg [x0, x1]))
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (hsrc : srcOf m = [0x15].map UInt8.toNat) :
    Spec.readFieldHeader Spec.exI16Overflow.last [0x15] = none ∧
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 1) ∧ m'.blocks bt = some ⟨kt, true, .int false 32, .int 8⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int (-32768)⟩ ∧ srcOf m' = []) := by
  refine ⟨Spec.readFieldHeader_exI16Overflow_short, ?_⟩
  refine returns_mono (readFieldBegin_short ctx cirH_f cirH_fb cirH_ft tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp Spec.exI16Overflow.last cirH_last (by decide) x0 x1 cirH_bv nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti
    0x15 [] hsrc 8 rfl (by decide) (by decide)) ?_
  rintro r m' ⟨e1, e2, e3, e4, -⟩
  exact ⟨e1, e2, by rw [e3]; rfl, e4⟩

/-- `05 1E` after id 0 (the long form of `Spec.exDelta15`, what Rust writes): C++ reads field id 15, type `T_I32`,
as the spec (`Spec.readFieldHeader_exDelta15_long`). -/
theorem readFieldBegin_exDelta15_long (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_fi : ctx.mod.findFunc? symReadI16 = some fn_apache_thrift_protocol_TCompactProtocolT_readI16)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_fz : ctx.mod.findFunc? symZigzagToI32 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI32)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (cirH_last : fs[5]? = some (.int Spec.exDelta15.last))
    (x0 x1 : Val) (cirH_bv : fs[3]? = some (.agg [x0, x1]))
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (hsrc : srcOf m = [0x05, 0x1E].map UInt8.toNat) :
    Spec.readFieldHeader Spec.exDelta15.last [0x05, 0x1E] = some (.field 5 15, []) ∧
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 2) ∧ m'.blocks bt = some ⟨kt, true, .int false 32, .int 8⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int 15⟩ ∧ srcOf m' = []) := by
  refine ⟨Spec.readFieldHeader_exDelta15_long, ?_⟩
  refine returns_mono (readFieldBegin_long ctx cirH_f cirH_fb cirH_fi cirH_f32 cirH_f64 cirH_fz cirH_ft tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp Spec.exDelta15.last cirH_last (by decide) x0 x1 cirH_bv nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti
    0x05 [0x1E] hsrc 8 rfl (by decide) (by decide) 30 [] rfl) ?_
  rintro r m' ⟨e1, e2, e3, e4, -⟩
  exact ⟨e1, e2, by rw [e3]; rfl, e4⟩

/-- `10` (delta 1, type nibble 0): C++ ends the struct (`T_STOP`, id 0), where the spec has `StopNibble`. -/
theorem readFieldBegin_stopNibble (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (last : Int) (hsrc : srcOf m = [0x10].map UInt8.toNat) :
    Spec.readFieldHeader last [0x10] = none ∧
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 1) ∧ m'.blocks bt = some ⟨kt, true, .int false 32, .int 0⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int 0⟩ ∧ srcOf m' = []) := by
  refine ⟨by simp [Spec.readFieldHeader, Spec.StopNibble], ?_⟩
  refine returns_mono (readFieldBegin_stop ctx cirH_f cirH_fb tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti 0x10 [] hsrc (by decide)) ?_
  rintro r m' ⟨e1, e2, e3, e4, -⟩
  exact ⟨e1, e2, e3, e4⟩

/-! ## The spec's named malformed inputs (`Spec.exVarint32Exceeds` …), on C++'s semantics

The spec rejects each of them (`Spec.exVarint32Exceeds_malformed` …); C++ returns normally on these four, for every
transport. -/

/-- `85 80 80 80 10` (value `2^32 + 5`): `readVarint32` reads the 5 bytes and stores 5. -/
theorem readVarint32_exVarint32Exceeds (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 32, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (hsrc : srcOf m = Spec.exVarint32Exceeds.map UInt8.toNat) :
    Spec.readVarint32 Spec.exVarint32Exceeds = none ∧
    Returns ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 5) ∧ m'.blocks bi = some ⟨ki, true, .int true 32, .int 5⟩ ∧ srcOf m' = []) := by
  refine ⟨Spec.exVarint32Exceeds_malformed.2, returns_mono (readVarint32_ok ctx cirH_f cirH_f64 tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki hbi hbiF Spec.exVarint32Exceeds []
    (2 ^ 32 + 5) (by decide) hsrc) ?_⟩
  rintro r m' ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, by rw [h2, show wrap true 32 (((2 ^ 32 + 5 : Nat)) : Int) = 5 by decide], h3⟩

/-- `80 80 80 80 80 80 80 80 80 02` (value `2^64`): `readVarint64` reads the 10 bytes and stores 0 (`uint64_t`
shifts drop the bit). -/
theorem readVarint64_exVarint64Exceeds (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 64, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (hsrc : srcOf m = Spec.exVarint64Exceeds.map UInt8.toNat) :
    Spec.readVarint64 Spec.exVarint64Exceeds = none ∧
    Returns ctx symReadVarint64 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 10) ∧ m'.blocks bi = some ⟨ki, true, .int true 64, .int 0⟩ ∧ srcOf m' = []) := by
  refine ⟨Spec.exVarint64Exceeds_malformed.2, returns_mono (readVarint64_ok ctx cirH_f tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki hbi hbiF Spec.exVarint64Exceeds []
    (2 ^ 64) (by decide) hsrc) ?_⟩
  rintro r m' ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, by rw [h2, show wrap true 64 (((2 ^ 64 : Nat)) : Int) = 0 by decide], h3⟩

/-- `10` after id 0 (`Spec.exStopNibble`): `readFieldBegin` ends the struct (`T_STOP`, id 0). -/
theorem readFieldBegin_exStopNibble (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (hsrc : srcOf m = Spec.exStopNibble.map UInt8.toNat) :
    Spec.readFieldHeader 0 Spec.exStopNibble = none ∧
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 1) ∧ m'.blocks bt = some ⟨kt, true, .int false 32, .int 0⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int 0⟩ ∧ srcOf m' = []) :=
  readFieldBegin_stopNibble ctx cirH_f cirH_fb tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti 0 hsrc

/-- `05 80 80 04` after id 0 (`Spec.exIdOutOfRange`, id 32768): `readFieldBegin` reads type `T_I32` and id
`(int16_t)32768 = -32768`. -/
theorem readFieldBegin_exIdOutOfRange (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadFieldBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readFieldBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_fi : ctx.mod.findFunc? symReadI16 = some fn_apache_thrift_protocol_TCompactProtocolT_readI16)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_fz : ctx.mod.findFunc? symZigzagToI32 = some fn_apache_thrift_protocol_TCompactProtocolT_zigzagToI32)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb) (hkp : kp ≠ .readonly)
    (hFp : ∀ b, Fp b → b < m.next)
    (cirH_last : fs[5]? = some (.int 0))
    (x0 x1 : Val) (cirH_bv : fs[3]? = some (.agg [x0, x1]))
    (nm : Ptr)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 16, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi) (hbti : bt ≠ bi)
    (hsrc : srcOf m = Spec.exIdOutOfRange.map UInt8.toNat) :
    Spec.readFieldHeader 0 Spec.exIdOutOfRange = none ∧
    Returns ctx symReadFieldBegin [.ptr (.loc pb []), .ptr nm, .ptr (.loc bt []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 4) ∧ m'.blocks bt = some ⟨kt, true, .int false 32, .int 8⟩ ∧
        m'.blocks bi = some ⟨ki, true, .int true 16, .int (-32768)⟩ ∧ srcOf m' = []) := by
  refine ⟨Spec.exIdOutOfRange_malformed.2.2.2, ?_⟩
  refine returns_mono (readFieldBegin_long ctx cirH_f cirH_fb cirH_fi cirH_f32 cirH_f64 cirH_fz cirH_ft tp Fp srcOf TR m pb kp fs cirH_pb cirH_tr hpb hpbF hkp hFp 0 cirH_last (by decide) x0 x1 cirH_bv nm bt kt vt cirH_bt hkt hbt hbtF bi ki vi cirH_bi hki hbi hbiF hbti 0x05 [0x80, 0x80, 0x04] hsrc 8 rfl (by decide) (by decide)
    65536 [] (by decide)) ?_
  rintro r m' ⟨e1, e2, e3, e4, -⟩
  exact ⟨e1, e2, by rw [e3]; rfl, e4⟩

end EquivLean.Demo.Thrift.Cpp
