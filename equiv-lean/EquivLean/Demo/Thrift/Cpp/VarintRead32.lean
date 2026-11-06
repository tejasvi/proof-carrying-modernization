import EquivLean.Demo.Thrift.Cpp.VarintRead

/-!
# Thrift, C++ side: compact varint32 read (D, and the accepted malformed inputs of M)

`TCompactProtocolT<TTransport>::readVarint32(i32)` is `readVarint64` into a local `int64_t`, then
`i32 = (int32_t)val`.  So it reads up to 10 bytes and keeps the value modulo `2^32`:
`readVarint32_ok` (the call of `readVarint64` by its proved specification `readVarint64_ok`),
`readVarint32_D` (the spec's varint of every `x < 2^32`); and inputs the spec's decoders reject but C++ accepts
(M), with their bytes: `readVarint32_overlong6` (6 bytes), `readVarint32_exceeds5` (value `2^33 - 1`),
`readVarint64_exceeds10` (value `2^70 - 1`).
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

def symReadVarint32 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE12readVarint32ERi"

/-- (D, and M where C++ accepts) `readVarint32` on a source whose first at most 10 bytes are a varint of value
`x` followed by `rest`: returns the byte count, stores `x` modulo `2^32` into `i32`, leaves exactly `rest`. -/
theorem readVarint32_ok (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 32, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (bs rest : Spec.Bytes) (x : Nat) (hrd : Spec.readVarint 10 bs = some (x, rest))
    (hsrc : srcOf m = bs.map UInt8.toNat) :
    Returns ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (bs.length - rest.length : Nat)) ∧
        m'.blocks bi = some ⟨ki, true, .int true 32, .int (wrap true 32 x)⟩ ∧ srcOf m' = rest.map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ bi → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_spec64 := fun m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 h10 =>
    readVarint64_ok ctx cirH_f64 tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 bs rest x hrd h10
  have hlen := readVarint_len 10 bs x rest hrd
  have neFp : ∀ b, Fp b → b ≠ bi := fun b hb h => hbiF (h ▸ hb)
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readVarint32.nothrow = false := rfl
  have cirH_ki := hki
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  case h.hspec.refine'_5 => omega
  case h.hspec.refine'_6 => exact hpbF
  case h.hspec.refine'_7 => rename_i b hb; have := hFp b hb; omega
  case h.hspec.refine'_12 => omega
  case h.hspec.refine'_14 =>
    rw [hstable m _ (fun b hb => by
      have := hFp b hb; dsimp only; simp (disch := omega) only [upd_apply_ne]), hsrc]
  case h.right.left => exact wrap32_wrap64 _
  case h.right.right.left =>
    rw [hstable cir_mem0 _ (fun b hb => by
      have := hFp b hb; dsimp only
      simp (disch := first | omega | exact neFp _ hb) only [killRange_of_lt, upd_apply_ne]),
      cirH_post0bba]
  case h.right.right.right.left => omega

/-- (D) The spec's varint of every `x < 2^32`, then any bytes `rest`: `readVarint32` returns its length, stores `x`
(as an `int32_t`) and leaves exactly `rest`. -/
theorem readVarint32_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 32, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (x : Nat) (hx : x < 2 ^ 32) (rest : Spec.Bytes) (hsrc : srcOf m = (Spec.varint x ++ rest).map UInt8.toNat) :
    Returns ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (Spec.varint x).length) ∧
        m'.blocks bi = some ⟨ki, true, .int true 32, .int (wrap true 32 x)⟩ ∧ srcOf m' = rest.map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ bi → b < m.next → m'.blocks b = m.blocks b) := by
  have h := readVarint32_ok ctx cirH_f cirH_f64 tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki hbi hbiF (Spec.varint x ++ rest) rest x
    (Spec.readVarint_varint 10 x rest (by have := Spec.varint_length_le5 hx; omega)) hsrc
  rwa [List.length_append, Nat.add_sub_cancel] at h

/-! ## Malformed inputs C++ accepts (M): instances with their bytes

The spec's decoders reject these byte sequences; C++ returns normally on them, for every transport. -/

/-- (M) `80 80 80 80 80 00`, a varint32 of 6 bytes (`VarintOverlong 5`; value 0): `readVarint32` reads the 6 bytes
and stores 0. -/
theorem readVarint32_overlong6 (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 32, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (hsrc : srcOf m = [0x80, 0x80, 0x80, 0x80, 0x80, 0x00].map UInt8.toNat) :
    Spec.readVarint32 [0x80, 0x80, 0x80, 0x80, 0x80, 0x00] = none ∧
    Returns ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 6) ∧ m'.blocks bi = some ⟨ki, true, .int true 32, .int 0⟩ ∧ srcOf m' = []) := by
  refine ⟨rfl, returns_mono (readVarint32_ok ctx cirH_f cirH_f64 tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki hbi hbiF [0x80, 0x80, 0x80, 0x80, 0x80, 0x00] [] 0 rfl hsrc) ?_⟩
  rintro r m' ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, by rw [h2, show wrap true 32 ((0 : Nat) : Int) = 0 by decide], h3⟩

/-- (M) `FF FF FF FF 1F`, a varint32 of 5 bytes of value `2^33 - 1` (`VarintExceeds 5 (2^32)`): `readVarint32`
reads the 5 bytes and stores -1. -/
theorem readVarint32_exceeds5 (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 32, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (hsrc : srcOf m = [0xFF, 0xFF, 0xFF, 0xFF, 0x1F].map UInt8.toNat) :
    Spec.readVarint32 [0xFF, 0xFF, 0xFF, 0xFF, 0x1F] = none ∧
    Returns ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 5) ∧ m'.blocks bi = some ⟨ki, true, .int true 32, .int (-1)⟩ ∧ srcOf m' = []) := by
  refine ⟨rfl, returns_mono (readVarint32_ok ctx cirH_f cirH_f64 tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki hbi hbiF [0xFF, 0xFF, 0xFF, 0xFF, 0x1F] [] 8589934591 rfl hsrc) ?_⟩
  rintro r m' ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, by rw [h2, show wrap true 32 ((8589934591 : Nat) : Int) = -1 by decide], h3⟩

/-- (M) `FF FF FF FF FF FF FF FF FF 7F`, a varint64 of 10 bytes of value `2^70 - 1` (`VarintExceeds 10 (2^64)`):
`readVarint64` reads the 10 bytes and stores -1. -/
theorem readVarint64_exceeds10 (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 64, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (hsrc : srcOf m = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F].map UInt8.toNat) :
    Spec.readVarint64 [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] = none ∧
    Returns ctx symReadVarint64 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int 10) ∧ m'.blocks bi = some ⟨ki, true, .int true 64, .int (-1)⟩ ∧ srcOf m' = []) := by
  refine ⟨rfl, returns_mono (readVarint64_ok ctx cirH_f tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki hbi hbiF [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] []
    1180591620717411303423 rfl hsrc) ?_⟩
  rintro r m' ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, by rw [h2, show wrap true 64 ((1180591620717411303423 : Nat) : Int) = -1 by decide], h3⟩

end EquivLean.Demo.Thrift.Cpp
