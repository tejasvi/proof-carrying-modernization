import EquivLean.Demo.Thrift.Cpp.FieldRead
import EquivLean.Demo.Thrift.Cpp.ListHeader

/-!
# Thrift, C++ side: compact list/set header, reader (D)

`TCompactProtocolT<TTransport>::readListBegin(elemType, size)` reads the header byte (`readByte`), the size nibble
`b >> 4` or, when it is 15, a varint32 (`readVarint32`); rejects a negative size and a size past the protocol's
`container_limit_` (by throwing); takes the element TType (`getTType`); builds a `TList` and calls the protocol's
virtual `checkReadBytesAvailable(list)`, which asks the transport (`TTransport::checkReadBytesAvailable`) for
`size * getMinSerializedSize(elemType)` bytes of message budget.
* `readListBegin_short`, `readListBegin_long`: the two header forms;
* `readListBegin_D`: every header of the spec (`Spec.listHeader size ety`, `size < 2^31`) reads back as its element
  type and size, leaving the rest — when the container limit does not reject the size and the rest holds the
  `size * minSize t` bytes the budget check asks for;
* `readSetBegin_D`: `readSetBegin` calls `readListBegin`.
Contracts: `ReadContract` (`readAll` of one byte), `CheckContract` (`checkReadBytesAvailable` returns when the
transport holds the bytes).  Hypotheses on the program and the object (no library models): the protocol object's
vptr (its nested base subobjects) and the class's vtable (`vtProto`, the program's constant), the `TList` record.
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

attribute [cir_exec] rec_apache_thrift_protocol_TList rec_apache_thrift_protocol_TSet

/-- `TTransport::checkReadBytesAvailable(long)`: the transport's message size budget. -/
def symCheckAvail : String := "_ZN6apache6thrift9transport10TTransport23checkReadBytesAvailableEl"

/-- The C++ transport contract, the message size budget: `checkReadBytesAvailable(n)` returns and changes nothing when
`0 ≤ n` and the transport still holds `n` bytes (`srcOf`, as in `ReadContract`): a transport whose message size limit
is no less than what it holds. -/
structure CheckContract (ctx : Ctx) (tp : Ptr) (srcOf : Mem → List Nat) : Prop where
  checkAvail : ∀ (m : Mem) (n : Int), 0 ≤ n → n ≤ (srcOf m).length →
    Returns ctx symCheckAvail [.ptr tp, .int n] m (fun r m' => r = none ∧ m' = m)

def symGetMinSerializedSize : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE20getMinSerializedSizeENS1_5TTypeE"

/-- The fewest bytes an element of TType `t` takes in the compact protocol (`getMinSerializedSize`). -/
def minSize (t : Nat) : Nat := if t = 4 then 8 else if t = 16 then 16 else 1

/-- `getMinSerializedSize(t)` for every TType `t` of a compact type nibble. -/
theorem getMinSerializedSize_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (m : Mem) (this : Ptr) (c t : Nat) (ht : Spec.ttypeOfCompact c = some t) :
    Returns ctx symGetMinSerializedSize [.ptr this, .int t] m
      (fun r m' => r = some (.int (minSize t)) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize.nothrow = false := rfl
  unfold Spec.ttypeOfCompact at ht
  split at ht <;> cases ht
  all_goals
    unfold Returns Calls
    rw [evalCall_body cirH_f rfl rfl]
    cir_run

def symTListCtor : String := "_ZN6apache6thrift8protocol5TListC2ENS1_5TTypeEi"

/-- The constructor `TList(t, s)` on a `TList` object. -/
theorem TList_ctor (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symTListCtor = some fn_apache_thrift_protocol_TList_TList)
    (cirH_rl : ctx.mod.findRecord? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList)
    (m : Mem) (bl : Nat) (kl : BlockKind) (x0 x1 : Val)
    (cirH_bl : m.blocks bl = some ⟨kl, true, .record "apache::thrift::protocol::TList", .agg [x0, x1]⟩)
    (hkl : kl ≠ .readonly) (hbl : bl < m.next) (t : Nat) (ht : t < 2 ^ 32) (s : Int) (hs : -2147483648 ≤ s ∧ s ≤ 2147483647) :
    Returns ctx symTListCtor [.ptr (.loc bl []), .int t, .int s] m
      (fun r m' => r = none ∧
        m'.blocks bl = some ⟨kl, true, .record "apache::thrift::protocol::TList", .agg [.int t, .int s]⟩ ∧
        m.next ≤ m'.next ∧ ∀ b, b ≠ bl → b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_kl := hkl
  have cirH_rl' : ctx.record? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList := cirH_rl
  have cirH_rm : rec_apache_thrift_protocol_TList.members = [(.data, .int false 32), (.data, .int true 32)] := rfl
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run

/-- The protocol class's vtable (the program's constant), its address point. -/
def vtProto : String := "_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEEE"

/-- The entries of the protocol's vtable (the program's initializer of `vtProto`). -/
def vtProtoEntries : List Const :=
  match g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor.init with
  | some (.record [.array es]) => es
  | _ => []

theorem vtProto_init :
    g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor.init =
      some (.record [.array vtProtoEntries]) := rfl

theorem vtProtoEntries_49 : vtProtoEntries[49]? = some (.globalAddr symGetMinSerializedSize []) := rfl

theorem constVal_getMinSerializedSize (ctx : Ctx)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none)
    (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none) :
    ctx.constVal 32 (.ptr (.int false 8)) (.globalAddr symGetMinSerializedSize []) =
      some (.ptr (.fn symGetMinSerializedSize)) := by
  simp [Ctx.constVal, Ctx.symAddr?, cirH_gm, cirH_fm, cirH_gmg]

theorem vtSlot_getMinSerializedSize (ctx : Ctx)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_vtg : ctx.mod.findGlobal? vtProto =
      some g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor)
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none)
    (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none) :
    ctx.vtableSlot? vtProto 0 49 = some (.ptr (.fn symGetMinSerializedSize)) := by
  unfold Ctx.vtableSlot?
  rw [cirH_vtg]
  simp only [g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor]
  simp [Ctx.constVal, Ctx.symAddr?, symGetMinSerializedSize] at cirH_gm cirH_fm cirH_gmg ⊢
  simp [cirH_gm, cirH_fm, cirH_gmg]

def symCRBAList : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE23checkReadBytesAvailableERNS1_5TListE"

/-- `checkReadBytesAvailable(list)` (the protocol's virtual method) on a list of `s` elements of TType `t`: asks the
transport for `s * minSize t` bytes of budget (`getMinSerializedSize` through the vtable). -/
theorem checkReadBytesAvailableList_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symCRBAList =
      some fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_vtg : ctx.mod.findGlobal? vtProto =
      some g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor)
    (cirH_vpath : ctx.vptrPath 16 recProto = some [0, 0, 0, 0])
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none)
    (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (TC : CheckContract ctx tp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hFp : ∀ b, Fp b → b < m.next)
    (f1 f2 f3 : List Val) (cirH_v1 : fs[0]? = some (.agg f1)) (cirH_v2 : f1[0]? = some (.agg f2))
    (cirH_v3 : f2[0]? = some (.agg f3)) (cirH_vp : f3[0]? = some (.ptr (.vtable vtProto 0 2)))
    (bl : Nat) (kl : BlockKind) (c t : Nat) (ht : Spec.ttypeOfCompact c = some t) (sz : Nat) (hsz : sz < 2 ^ 31)
    (cirH_bl : m.blocks bl = some ⟨kl, true, .record "apache::thrift::protocol::TList", .agg [.int t, .int sz]⟩)
    (hbl : bl < m.next) (hrem : sz * minSize t ≤ (srcOf m).length) :
    Returns ctx symCRBAList [.ptr (.loc pb []), .ptr (.loc bl [])] m
      (fun r m' => r = none ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_specm := fun m' this => getMinSerializedSize_D ctx cirH_fm m' this c t ht
  have cirH_specc := TC.checkAvail
  have hmin : minSize t ≤ 16 := by unfold minSize; split <;> (try split) <;> omega
  have cirH_slot := vtSlot_getMinSerializedSize ctx cirH_fm cirH_vtg cirH_gm cirH_gmg
  have cirH_ginit := vtProto_init
  have cirH_e49 := vtProtoEntries_49
  have cirH_cv := constVal_getMinSerializedSize ctx cirH_fm cirH_gm cirH_gmg
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2.nothrow = false := rfl
  have cirH_t16 : t ≤ 16 := by unfold Spec.ttypeOfCompact at ht; split at ht <;> cases ht <;> decide
  unfold vtProto at cirH_vtg cirH_vp cirH_slot
  unfold recProto at cirH_vpath
  have cirH_fm' := cirH_fm
  unfold symGetMinSerializedSize at cirH_gm cirH_slot cirH_e49 cirH_cv cirH_gmg cirH_fm'
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try exact absurd (by assumption :
    fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2.nothrow = true) (by decide)
  all_goals have hprod : sz * minSize t ≤ 2 ^ 31 * 16 := Nat.mul_le_mul (Nat.le_of_lt hsz) hmin
  all_goals have hcast : ((sz : Int) * (minSize t : Int)) = ((sz * minSize t : Nat) : Int) := by push_cast; rfl
  all_goals try (rw [hcast]; omega)
  all_goals try omega
  case h.hspec.refine'_2 =>
    rw [hcast, TR.stable m cir_mem0 (fun b hb => by
      have := hFp b hb; rw [cirH_post0bb b (by omega)]; simp (disch := omega) only [upd_apply_ne])]
    omega

theorem vtProtoEntries_51 : vtProtoEntries[51]? = some (.globalAddr symCRBAList []) := rfl

theorem constVal_CRBAList (ctx : Ctx)
    (cirH_fc : ctx.mod.findFunc? symCRBAList = some fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2)
    (cirH_gc : ctx.gaddr symCRBAList = none) (cirH_gcg : ctx.mod.findGlobal? symCRBAList = none) :
    ctx.constVal 32 (.ptr (.int false 8)) (.globalAddr symCRBAList []) = some (.ptr (.fn symCRBAList)) := by
  simp [Ctx.constVal, Ctx.symAddr?, cirH_gc, cirH_fc, cirH_gcg]

def symReadListBegin : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE13readListBeginERNS1_5TTypeERj"

theorem wrap_u8_s8_nat {c : Nat} (hc : c < 256) : wrap false 8 (wrap true 8 (c : Int)) = c := by
  unfold wrap; simp only [Bool.true_and, Bool.false_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow,
    Bool.false_eq_true, ite_false]; split <;> omega

/-- `readListBegin` on a header byte `b` with a size nibble below 15 and an element type nibble that has a TType
`t`: the element type `t`, the size `b >> 4`; one byte read. -/
theorem readListBegin_short (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadListBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readListBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (cirH_ftl : ctx.mod.findFunc? symTListCtor = some fn_apache_thrift_protocol_TList_TList)
    (cirH_fc : ctx.mod.findFunc? symCRBAList = some fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_rl : ctx.mod.findRecord? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList)
    (cirH_vtg : ctx.mod.findGlobal? vtProto =
      some g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor)
    (cirH_vpath : ctx.vptrPath 16 recProto = some [0, 0, 0, 0])
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none) (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none)
    (cirH_gc : ctx.gaddr symCRBAList = none) (cirH_gcg : ctx.mod.findGlobal? symCRBAList = none)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (TC : CheckContract ctx tp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (f1 f2 f3 : List Val) (cirH_v1 : fs[0]? = some (.agg f1)) (cirH_v2 : f1[0]? = some (.agg f2))
    (cirH_v3 : f2[0]? = some (.agg f3)) (cirH_vp : f3[0]? = some (.ptr (.vtable vtProto 0 2)))
    (lim : Int) (cirH_lim : fs[9]? = some (.int lim)) (hlimr : Spec.InI32 lim)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bz : Nat) (kz : BlockKind) (vz : Val) (cirH_bz : m.blocks bz = some ⟨kz, true, .int false 32, vz⟩)
    (hkz : kz ≠ .readonly) (hbz : bz < m.next) (hbzF : ¬ Fp bz) (hbtz : bt ≠ bz)
    (b : UInt8) (tl : Spec.Bytes) (hsrc : srcOf m = (b :: tl).map UInt8.toNat)
    (t : Nat) (ht : Spec.ttypeOfCompact (b.toNat % 16) = some t) (hsz : b.toNat / 16 < 15)
    (hlim : lim = 0 ∨ ((b.toNat / 16 : Nat) : Int) ≤ lim)
    (hrem : b.toNat / 16 * minSize t ≤ tl.length) :
    Returns ctx symReadListBegin [.ptr (.loc pb []), .ptr (.loc bt []), .ptr (.loc bz [])] m
      (fun r m' => r = some (.int 1) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧
        m'.blocks bz = some ⟨kz, true, .int false 32, .int (b.toNat / 16 : Nat)⟩ ∧
        srcOf m' = tl.map UInt8.toNat ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' ≠ bt → b' ≠ bz → b' < m.next → m'.blocks b' = m.blocks b') := by
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  have cirH_kt := hkt
  have cirH_kz := hkz
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readListBegin.nothrow = false := rfl
  have cirH_pbt : pb ≠ bt := fun h => by subst h; rw [cirH_pb] at cirH_bt; simp at cirH_bt
  have cirH_btp : bt ≠ pb := fun h => cirH_pbt h.symm
  have cirH_pbz : pb ≠ bz := fun h => by subst h; rw [cirH_pb] at cirH_bz; simp at cirH_bz
  have cirH_bzp : bz ≠ pb := fun h => cirH_pbz h.symm
  have cirH_btz := hbtz
  have cirH_bzt : bz ≠ bt := fun h => hbtz h.symm
  have neFpPb : ∀ b, Fp b → b ≠ pb := fun b hb h => hpbF (h ▸ hb)
  have neFpBt : ∀ b, Fp b → b ≠ bt := fun b hb h => hbtF (h ▸ hb)
  have neFpBz : ∀ b, Fp b → b ≠ bz := fun b hb h => hbzF (h ▸ hb)
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
  have cirH_w328 := wrap_s32_s8
  have cirH_w8 : wrap true 8 ((b.toNat % 16 : Nat) : Int) = ((b.toNat % 16 : Nat) : Int) := wrap_s8_nat (by omega)
  have cirH_w32 : wrap true 32 ((b.toNat % 16 : Nat) : Int) = ((b.toNat % 16 : Nat) : Int) := wrap_s32_nat (by omega)
  have cirH_u8 := wrap_u8_s8_nat hb256
  have cirH_w32b : wrap true 32 (b.toNat : Int) = b.toNat := wrap_s32_nat (by omega)
  have cirH_div : (b.toNat : Int) / 16 = ((b.toNat / 16 : Nat) : Int) := by omega
  have cirH_hn := lo_nibble_nat (b.toNat / 16)
  have cirH_hn16 : ((b.toNat / 16 % 16 : Nat) : Int) = ((b.toNat / 16 : Nat) : Int) := by omega
  have cirH_n15 : ¬ ((b.toNat / 16 : Nat) : Int) = 15 := by omega
  have cirH_nn : ¬ ((b.toNat / 16 : Nat) : Int) < 0 := by omega
  have cirH_t16 : t ≤ 16 := by unfold Spec.ttypeOfCompact at ht; split at ht <;> cases ht <;> decide
  have cirH_spect := fun m' this => getTType_D ctx cirH_ft m' this (b.toNat % 16) t ht
  have cirH_spectl := fun m' bl kl x0 x1 h1 h2 h3 t' ht' s' hs' => TList_ctor ctx cirH_ftl cirH_rl m' bl kl x0 x1 h1 h2 h3 t' ht' s' hs'
  have cirH_specc := fun m' pb' kp' fs' h1 h2 h3 h4 f1' f2' f3' h5 h6 h7 h8 bl kl h9 h10 h11 =>
    checkReadBytesAvailableList_D ctx cirH_fc cirH_fm cirH_vtg cirH_vpath cirH_gm cirH_gmg tp Fp srcOf TR TC m' pb' kp' fs'
      h1 h2 h3 h4 f1' f2' f3' h5 h6 h7 h8 bl kl (b.toNat % 16) t ht (b.toNat / 16) (by omega) h9 h10 h11
  have cirH_ginit := vtProto_init
  have cirH_e51 := vtProtoEntries_51
  have cirH_cv := constVal_CRBAList ctx cirH_fc cirH_gc cirH_gcg
  unfold vtProto at cirH_vtg cirH_vp
  unfold recProto at cirH_vpath
  have cirH_fc' := cirH_fc
  unfold symCRBAList at cirH_gc cirH_gcg cirH_e51 cirH_cv cirH_fc'
  have cirH_lim' : ¬ (lim ≠ 0 ∧ lim < ((b.toNat / 16 : Nat) : Int)) := by omega
  have cirH_limr : -2147483648 ≤ lim ∧ lim ≤ 2147483647 := ⟨hlimr.1, by have := hlimr.2; omega⟩
  have cirH_w32lim : wrap true 32 lim = lim := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_fcp : fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2.params.head? =
      some (.ptr (.record "apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>")) := rfl
  have cirH_rl' : ctx.record? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList := cirH_rl
  have cirH_tlinit : ctx.initVal 32 (.record "apache::thrift::protocol::TList") = .agg [.undef, .undef] := by
    simp [Ctx.initVal, Ctx.record?, cirH_rl, rec_apache_thrift_protocol_TList]
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try (exfalso; rename_i h1 h2; simp only [bne_iff_ne, ne_eq] at h1; omega)
  all_goals try (exact Val.undef)
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  all_goals try (simp [rec_apache_thrift_protocol_TList, Ctx.initVal]; done)
  case h.hspec.refine'_13 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  all_goals
    have h60 : srcOf cir_mem6 = srcOf cir_mem0 := hstable cir_mem0 cir_mem6 (fun b' hb' => by
      have := hFp b' hb'
      rw [cirH_post6bbb b' (by omega) (by omega)]
      simp (disch := first | omega | exact neFpBt _ hb' | exact neFpBz _ hb') only [upd_apply_ne]
      rw [cirH_post4bb b' (by omega)]
      simp (disch := omega) only [upd_apply_ne])
  all_goals try (rw [h60, cirH_post0bba, List.length_map]; exact hrem)
  all_goals
    rw [hstable cir_mem9 _ (fun b' hb' => by
      have := hFp b' hb'; dsimp only
      simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBz _ hb')
        only [killRange_of_lt, upd_apply_ne]),
      hstable cir_mem6 cir_mem9 (fun b' hb' => by have := hFp b' hb'; rw [cirH_post9bb b' (by omega)]), h60,
      cirH_post0bba]

/-- `readListBegin` on a header byte `b` with size nibble 15 and an element type nibble that has a TType `t`, then a
varint of value `z < 2^31`: the element type `t`, the size `z`. -/
theorem readListBegin_long (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadListBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readListBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (cirH_ftl : ctx.mod.findFunc? symTListCtor = some fn_apache_thrift_protocol_TList_TList)
    (cirH_fc : ctx.mod.findFunc? symCRBAList = some fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_rl : ctx.mod.findRecord? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList)
    (cirH_vtg : ctx.mod.findGlobal? vtProto =
      some g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor)
    (cirH_vpath : ctx.vptrPath 16 recProto = some [0, 0, 0, 0])
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none) (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none)
    (cirH_gc : ctx.gaddr symCRBAList = none) (cirH_gcg : ctx.mod.findGlobal? symCRBAList = none)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (TC : CheckContract ctx tp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (f1 f2 f3 : List Val) (cirH_v1 : fs[0]? = some (.agg f1)) (cirH_v2 : f1[0]? = some (.agg f2))
    (cirH_v3 : f2[0]? = some (.agg f3)) (cirH_vp : f3[0]? = some (.ptr (.vtable vtProto 0 2)))
    (lim : Int) (cirH_lim : fs[9]? = some (.int lim)) (hlimr : Spec.InI32 lim)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bz : Nat) (kz : BlockKind) (vz : Val) (cirH_bz : m.blocks bz = some ⟨kz, true, .int false 32, vz⟩)
    (hkz : kz ≠ .readonly) (hbz : bz < m.next) (hbzF : ¬ Fp bz) (hbtz : bt ≠ bz)
    (b : UInt8) (tl : Spec.Bytes) (hsrc : srcOf m = (b :: tl).map UInt8.toNat)
    (t : Nat) (ht : Spec.ttypeOfCompact (b.toNat % 16) = some t) (hsz : b.toNat / 16 = 15)
    (z : Nat) (rest : Spec.Bytes) (hrd : Spec.readVarint 10 tl = some (z, rest)) (hz : z < 2 ^ 31)
    (hlim : lim = 0 ∨ (z : Int) ≤ lim) (hrem : z * minSize t ≤ rest.length) :
    Returns ctx symReadListBegin [.ptr (.loc pb []), .ptr (.loc bt []), .ptr (.loc bz [])] m
      (fun r m' => r = some (.int (1 + (tl.length - rest.length : Nat))) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧
        m'.blocks bz = some ⟨kz, true, .int false 32, .int z⟩ ∧
        srcOf m' = rest.map UInt8.toNat ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' ≠ bt → b' ≠ bz → b' < m.next → m'.blocks b' = m.blocks b') := by
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  have cirH_kt := hkt
  have cirH_kz := hkz
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readListBegin.nothrow = false := rfl
  have cirH_pbt : pb ≠ bt := fun h => by subst h; rw [cirH_pb] at cirH_bt; simp at cirH_bt
  have cirH_btp : bt ≠ pb := fun h => cirH_pbt h.symm
  have cirH_pbz : pb ≠ bz := fun h => by subst h; rw [cirH_pb] at cirH_bz; simp at cirH_bz
  have cirH_bzp : bz ≠ pb := fun h => cirH_pbz h.symm
  have cirH_btz := hbtz
  have cirH_bzt : bz ≠ bt := fun h => hbtz h.symm
  have neFpPb : ∀ b, Fp b → b ≠ pb := fun b hb h => hpbF (h ▸ hb)
  have neFpBt : ∀ b, Fp b → b ≠ bt := fun b hb h => hbtF (h ▸ hb)
  have neFpBz : ∀ b, Fp b → b ≠ bz := fun b hb h => hbzF (h ▸ hb)
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
  have cirH_w328 := wrap_s32_s8
  have cirH_w8 : wrap true 8 ((b.toNat % 16 : Nat) : Int) = ((b.toNat % 16 : Nat) : Int) := wrap_s8_nat (by omega)
  have cirH_w32 : wrap true 32 ((b.toNat % 16 : Nat) : Int) = ((b.toNat % 16 : Nat) : Int) := wrap_s32_nat (by omega)
  have cirH_u8 := wrap_u8_s8_nat hb256
  have cirH_w32b : wrap true 32 (b.toNat : Int) = b.toNat := wrap_s32_nat (by omega)
  have cirH_div : (b.toNat : Int) / 16 = ((b.toNat / 16 : Nat) : Int) := by omega
  have cirH_hn := lo_nibble_nat (b.toNat / 16)
  have cirH_hn16 : ((b.toNat / 16 % 16 : Nat) : Int) = ((b.toNat / 16 : Nat) : Int) := by omega
  have cirH_15 : ((b.toNat / 16 : Nat) : Int) = 15 := by omega
  have cirH_b1515 : bitwise true 32 (fun x1 x2 => x1 &&& x2) 15 15 = 15 := by decide
  have cirH_wz : wrap true 32 (z : Int) = z := wrap_s32_nat hz
  have cirH_nn : ¬ (z : Int) < 0 := by omega
  have hlen := readVarint_len 10 tl z rest hrd
  have cirH_spec32 := fun m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 h10 =>
    readVarint32_ok ctx cirH_f32 cirH_f64 tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 tl rest
      z hrd h10
  have cirH_t16 : t ≤ 16 := by unfold Spec.ttypeOfCompact at ht; split at ht <;> cases ht <;> decide
  have cirH_spect := fun m' this => getTType_D ctx cirH_ft m' this (b.toNat % 16) t ht
  have cirH_spectl := fun m' bl kl x0 x1 h1 h2 h3 t' ht' s' hs' => TList_ctor ctx cirH_ftl cirH_rl m' bl kl x0 x1 h1 h2 h3 t' ht' s' hs'
  have cirH_specc := fun m' pb' kp' fs' h1 h2 h3 h4 f1' f2' f3' h5 h6 h7 h8 bl kl h9 h10 h11 =>
    checkReadBytesAvailableList_D ctx cirH_fc cirH_fm cirH_vtg cirH_vpath cirH_gm cirH_gmg tp Fp srcOf TR TC m' pb' kp' fs'
      h1 h2 h3 h4 f1' f2' f3' h5 h6 h7 h8 bl kl (b.toNat % 16) t ht z hz h9 h10 h11
  have cirH_ginit := vtProto_init
  have cirH_e51 := vtProtoEntries_51
  have cirH_cv := constVal_CRBAList ctx cirH_fc cirH_gc cirH_gcg
  unfold vtProto at cirH_vtg cirH_vp
  unfold recProto at cirH_vpath
  have cirH_fc' := cirH_fc
  unfold symCRBAList at cirH_gc cirH_gcg cirH_e51 cirH_cv cirH_fc'
  have cirH_lim' : ¬ (lim ≠ 0 ∧ lim < (z : Int)) := by omega
  have cirH_limr : -2147483648 ≤ lim ∧ lim ≤ 2147483647 := ⟨hlimr.1, by have := hlimr.2; omega⟩
  have cirH_w32lim : wrap true 32 lim = lim := by
    unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega
  have cirH_fcp : fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2.params.head? =
      some (.ptr (.record "apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>")) := rfl
  have cirH_rl' : ctx.record? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList := cirH_rl
  have cirH_tlinit : ctx.initVal 32 (.record "apache::thrift::protocol::TList") = .agg [.undef, .undef] := by
    simp [Ctx.initVal, Ctx.record?, cirH_rl, rec_apache_thrift_protocol_TList]
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try (exfalso; rename_i h1 h2; simp only [bne_iff_ne, ne_eq] at h1; omega)
  all_goals try (exact Val.undef)
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  all_goals try (simp [rec_apache_thrift_protocol_TList, Ctx.initVal]; done)
  case h.hspec.refine'_13 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  case h.hspec.refine'_14 =>
    simp (disch := (apply cirH_nfp; omega)) only [srcU]
    rw [hstable cir_mem0 ⟨cir_mem0.blocks, cir_mem0.next⟩ (fun b _ => rfl), cirH_post0bba]
  all_goals
    have h104 : srcOf cir_mem10 = srcOf cir_mem4 := hstable cir_mem4 cir_mem10 (fun b' hb' => by
      have := hFp b' hb'
      rw [cirH_post10bbb b' (by omega) (by omega)]
      simp (disch := first | omega | exact neFpBt _ hb' | exact neFpBz _ hb') only [upd_apply_ne]
      rw [cirH_post8bb b' (by omega)]
      simp (disch := omega) only [killRange_of_lt, upd_apply_ne])
  all_goals try (rw [h104, cirH_post4bba, List.length_map]; exact hrem)
  all_goals
    rw [hstable cir_mem13 _ (fun b' hb' => by
      have := hFp b' hb'; dsimp only
      simp (disch := first | omega | exact neFpPb _ hb' | exact neFpBt _ hb' | exact neFpBz _ hb')
        only [killRange_of_lt, upd_apply_ne]),
      hstable cir_mem10 cir_mem13 (fun b' hb' => by have := hFp b' hb'; rw [cirH_post13bb b' (by omega)]), h104,
      cirH_post4bba]

/-- (D) A list/set header of the spec (`Spec.listHeader size ety`, every element type nibble `ety` with a TType `t`,
every size below `2^31`), then any bytes `rest`: `readListBegin` returns the element type `t` and the size, reads the
header's bytes and leaves exactly `rest` — for a protocol object without a container size limit (or one the size
does not pass), when `rest` holds the `size * minSize t` bytes the transport's message size check asks for. -/
theorem readListBegin_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadListBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readListBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (cirH_ftl : ctx.mod.findFunc? symTListCtor = some fn_apache_thrift_protocol_TList_TList)
    (cirH_fc : ctx.mod.findFunc? symCRBAList = some fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_rl : ctx.mod.findRecord? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList)
    (cirH_vtg : ctx.mod.findGlobal? vtProto =
      some g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor)
    (cirH_vpath : ctx.vptrPath 16 recProto = some [0, 0, 0, 0])
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none) (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none)
    (cirH_gc : ctx.gaddr symCRBAList = none) (cirH_gcg : ctx.mod.findGlobal? symCRBAList = none)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (TC : CheckContract ctx tp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (f1 f2 f3 : List Val) (cirH_v1 : fs[0]? = some (.agg f1)) (cirH_v2 : f1[0]? = some (.agg f2))
    (cirH_v3 : f2[0]? = some (.agg f3)) (cirH_vp : f3[0]? = some (.ptr (.vtable vtProto 0 2)))
    (lim : Int) (cirH_lim : fs[9]? = some (.int lim)) (hlimr : Spec.InI32 lim)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bz : Nat) (kz : BlockKind) (vz : Val) (cirH_bz : m.blocks bz = some ⟨kz, true, .int false 32, vz⟩)
    (hkz : kz ≠ .readonly) (hbz : bz < m.next) (hbzF : ¬ Fp bz) (hbtz : bt ≠ bz)
    (ety t : Nat) (ht : Spec.ttypeOfCompact ety = some t) (hety : ety < 16)
    (size : Nat) (hs : size < 2 ^ 31) (rest : Spec.Bytes)
    (hsrc : srcOf m = (Spec.listHeader size ety ++ rest).map UInt8.toNat)
    (hlim : lim = 0 ∨ (size : Int) ≤ lim) (hrem : size * minSize t ≤ rest.length) :
    Returns ctx symReadListBegin [.ptr (.loc pb []), .ptr (.loc bt []), .ptr (.loc bz [])] m
      (fun r m' => r = some (.int (Spec.listHeader size ety).length) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧
        m'.blocks bz = some ⟨kz, true, .int false 32, .int size⟩ ∧
        srcOf m' = rest.map UInt8.toNat ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' ≠ bt → b' ≠ bz → b' < m.next → m'.blocks b' = m.blocks b') := by
  by_cases hsz : size < 15
  · -- the short form: one byte `size << 4 | ety`
    rw [Spec.listHeader_short hsz hety] at hsrc ⊢
    have hb : (UInt8.ofNat (16 * size + ety)).toNat = 16 * size + ety := by rw [UInt8.toNat_ofNat']; omega
    have e1 : (16 * size + ety) / 16 = size := by omega
    have e2 : (16 * size + ety) % 16 = ety := by omega
    refine returns_mono (readListBegin_short ctx cirH_f cirH_fb cirH_ft cirH_ftl cirH_fc cirH_fm cirH_rl cirH_vtg cirH_vpath cirH_gm cirH_gmg cirH_gc cirH_gcg tp Fp srcOf TR TC m pb kp fs cirH_pb cirH_tr hpb hpbF hFp f1 f2 f3 cirH_v1 cirH_v2 cirH_v3 cirH_vp lim cirH_lim hlimr bt kt vt cirH_bt hkt hbt hbtF bz kz vz cirH_bz hkz hbz hbzF hbtz (UInt8.ofNat (16 * size + ety)) rest (by rw [hsrc]; rfl) t
      (by rw [hb, e2]; exact ht) (by rw [hb, e1]; exact hsz) (by rw [hb, e1]; exact hlim)
      (by rw [hb, e1]; exact hrem)) ?_
    rintro r m' ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, by rw [h3, hb, e1], h4, h5, h6⟩
  · -- the long form: the byte `0xF0 | ety`, then the varint of the size
    rw [Spec.listHeader_long (by omega) hety] at hsrc ⊢
    have hb : (UInt8.ofNat (0xF0 + ety)).toNat = 240 + ety := by rw [UInt8.toNat_ofNat']; omega
    have hrd := Spec.readVarint_varint 10 size rest
      (Nat.le_trans (Spec.varint_length_le5 (Nat.lt_trans hs (by decide))) (by decide))
    refine returns_mono (readListBegin_long ctx cirH_f cirH_fb cirH_f32 cirH_f64 cirH_ft cirH_ftl cirH_fc cirH_fm cirH_rl cirH_vtg cirH_vpath cirH_gm cirH_gmg cirH_gc cirH_gcg tp Fp srcOf TR TC m pb kp fs cirH_pb cirH_tr hpb hpbF hFp f1 f2 f3 cirH_v1 cirH_v2 cirH_v3 cirH_vp lim cirH_lim hlimr bt kt vt cirH_bt hkt hbt hbtF bz kz vz cirH_bz hkz hbz hbzF hbtz (UInt8.ofNat (0xF0 + ety)) (Spec.varint size ++ rest)
      (by rw [hsrc]; rfl) t (by rw [hb, show (240 + ety) % 16 = ety by omega]; exact ht)
      (by rw [hb]; omega) size rest hrd hs hlim hrem) ?_
    rintro r m' ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, h2, h3, h4, h5, h6⟩
    rw [h1]; simp only [List.length_cons, List.length_append]; congr 2; omega


def symReadSetBegin : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE12readSetBeginERNS1_5TTypeERj"

/-- (D) `readSetBegin` is `readListBegin` (C++ calls it): the same, for a set header. -/
theorem readSetBegin_D (ctx : Ctx)
    (cirH_fs : ctx.mod.findFunc? symReadSetBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readSetBegin)
    (cirH_f : ctx.mod.findFunc? symReadListBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readListBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_ft : ctx.mod.findFunc? symGetTType = some fn_apache_thrift_protocol_TCompactProtocolT_getTType)
    (cirH_ftl : ctx.mod.findFunc? symTListCtor = some fn_apache_thrift_protocol_TList_TList)
    (cirH_fc : ctx.mod.findFunc? symCRBAList = some fn_apache_thrift_protocol_TCompactProtocolT_checkReadBytesAvailable_2)
    (cirH_fm : ctx.mod.findFunc? symGetMinSerializedSize =
      some fn_apache_thrift_protocol_TCompactProtocolT_getMinSerializedSize)
    (cirH_rl : ctx.mod.findRecord? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList)
    (cirH_vtg : ctx.mod.findGlobal? vtProto =
      some g_ZTVN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTranspor)
    (cirH_vpath : ctx.vptrPath 16 recProto = some [0, 0, 0, 0])
    (cirH_gm : ctx.gaddr symGetMinSerializedSize = none) (cirH_gmg : ctx.mod.findGlobal? symGetMinSerializedSize = none)
    (cirH_gc : ctx.gaddr symCRBAList = none) (cirH_gcg : ctx.mod.findGlobal? symCRBAList = none)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (TC : CheckContract ctx tp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (f1 f2 f3 : List Val) (cirH_v1 : fs[0]? = some (.agg f1)) (cirH_v2 : f1[0]? = some (.agg f2))
    (cirH_v3 : f2[0]? = some (.agg f3)) (cirH_vp : f3[0]? = some (.ptr (.vtable vtProto 0 2)))
    (lim : Int) (cirH_lim : fs[9]? = some (.int lim)) (hlimr : Spec.InI32 lim)
    (bt : Nat) (kt : BlockKind) (vt : Val) (cirH_bt : m.blocks bt = some ⟨kt, true, .int false 32, vt⟩)
    (hkt : kt ≠ .readonly) (hbt : bt < m.next) (hbtF : ¬ Fp bt)
    (bz : Nat) (kz : BlockKind) (vz : Val) (cirH_bz : m.blocks bz = some ⟨kz, true, .int false 32, vz⟩)
    (hkz : kz ≠ .readonly) (hbz : bz < m.next) (hbzF : ¬ Fp bz) (hbtz : bt ≠ bz)
    (ety t : Nat) (ht : Spec.ttypeOfCompact ety = some t) (hety : ety < 16)
    (size : Nat) (hs : size < 2 ^ 31) (rest : Spec.Bytes)
    (hsrc : srcOf m = (Spec.listHeader size ety ++ rest).map UInt8.toNat)
    (hlim : lim = 0 ∨ (size : Int) ≤ lim) (hrem : size * minSize t ≤ rest.length) :
    Returns ctx symReadSetBegin [.ptr (.loc pb []), .ptr (.loc bt []), .ptr (.loc bz [])] m
      (fun r m' => r = some (.int (Spec.listHeader size ety).length) ∧
        m'.blocks bt = some ⟨kt, true, .int false 32, .int t⟩ ∧
        m'.blocks bz = some ⟨kz, true, .int false 32, .int size⟩ ∧
        srcOf m' = rest.map UInt8.toNat ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' ≠ bt → b' ≠ bz → b' < m.next → m'.blocks b' = m.blocks b') := by
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readSetBegin.nothrow = false := rfl
  have cirH_specl := fun m' kp' h1 h2 h3 vt' h4 h5 vz' h6 h7 h8 =>
    readListBegin_D ctx cirH_f cirH_fb cirH_f32 cirH_f64 cirH_ft cirH_ftl cirH_fc cirH_fm cirH_rl cirH_vtg cirH_vpath
      cirH_gm cirH_gmg cirH_gc cirH_gcg tp Fp srcOf TR TC m' pb kp' fs h1 cirH_tr h2 hpbF h3 f1 f2 f3 cirH_v1 cirH_v2
      cirH_v3 cirH_vp lim cirH_lim hlimr bt kt vt' h4 hkt h5 hbtF bz kz vz' h6 hkz h7 hbzF hbtz ety t ht hety size hs
      rest h8 hlim hrem
  have hlen : (Spec.listHeader size ety).length ≤ 6 := by
    unfold Spec.listHeader; split
    · simp
    · simp only [List.length_cons]; have := Spec.varint_length_le5 (n := size) (by omega); omega
  have neFpBt : ∀ b, Fp b → b ≠ bt := fun b hb h => hbtF (h ▸ hb)
  have neFpBz : ∀ b, Fp b → b ≠ bz := fun b hb h => hbzF (h ▸ hb)
  unfold Returns Calls
  rw [evalCall_body cirH_fs rfl rfl]
  cir_run
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  all_goals try omega
  case h.hspec.refine'_11 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; rw [hsrc, List.map_append]
  case h.right.right.right.left =>
    rw [hstable cir_mem0 _ (fun b' hb' => by
      have := hFp b' hb'; dsimp only
      simp (disch := first | omega | exact neFpBt _ hb' | exact neFpBz _ hb') only [killRange_of_lt, upd_apply_ne]),
      cirH_post0bbba]

end EquivLean.Demo.Thrift.Cpp
