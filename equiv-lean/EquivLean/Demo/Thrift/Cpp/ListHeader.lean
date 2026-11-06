import EquivLean.Demo.Thrift.Cpp.FieldHeader

/-!
# Thrift, C++ side: compact list/set header, writer (E)

`writeCollectionBegin_E`: `TCompactProtocolT<TTransport>::writeCollectionBegin(t, size)` (what `writeListBegin` and
`writeSetBegin` call) appends exactly `Spec.listHeader size c` for every element TType `t` with a compact type nibble
`c` and every `int32_t` `size ≥ 0`.  Callees by their specifications: `getCompactType_E`, `writeByte_E`,
`writeVarint32_E`.
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

def symWriteCollectionBegin : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE20writeCollectionBeginENS1_5TTypeEi"

/-- The short list header byte `(int8_t)(size << 4 | c)` as the transport receives it. -/
theorem lh_byte {d c : Nat} (hd : d ≤ 15) (hc : c < 16) :
    (wrap true 8 (bitwise true 32 (fun x1 x2 => x1 ||| x2) ((d : Int) * 16) (c : Int)) % 256).toNat = 16 * d + c := by
  have hor : bitwise true 32 (fun x1 x2 => x1 ||| x2) ((d : Int) * 16) (c : Int) = ((16 * d + c : Nat) : Int) := by
    unfold bitwise
    simp only [ite_true]
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_or, ofInt_toNat_32 (by omega) (by omega),
      ofInt_toNat_32 (by omega) (by omega)]
    have e : ((d : Int) * 16).toNat ||| (c : Int).toNat = 16 * d + c := by
      rw [show ((d : Int) * 16).toNat = 2 ^ 4 * d by omega, Int.toNat_natCast,
        ← Nat.two_pow_add_eq_or_of_lt (show c < 2 ^ 4 by omega)]
    rw [e]; split <;> omega
  rw [hor]; unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

/-- The long list header byte `(int8_t)(0xF0 | c)`. -/
theorem lh_byte_long {c : Nat} (hc : c < 16) :
    (wrap true 8 (bitwise true 32 (fun x1 x2 => x1 ||| x2) (c : Int) 240) % 256).toNat = 240 + c := by
  have hor : bitwise true 32 (fun x1 x2 => x1 ||| x2) (c : Int) 240 = ((240 + c : Nat) : Int) := by
    unfold bitwise
    simp only [ite_true]
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_or, ofInt_toNat_32 (by omega) (by omega),
      show (BitVec.ofInt 32 240).toNat = 240 by decide]
    have e : (c : Int).toNat ||| 240 = 240 + c := by
      rw [Int.toNat_natCast, Nat.or_comm, show (240 : Nat) = 2 ^ 4 * 15 by decide,
        ← Nat.two_pow_add_eq_or_of_lt (show c < 2 ^ 4 by omega)]
    rw [e]; split <;> omega
  rw [hor]; unfold wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

/-- (E) `writeCollectionBegin(t, size)` (`writeListBegin`, `writeSetBegin`) for every element TType `t` with a compact
type nibble `c` and every `int32_t` `size ≥ 0`: appends exactly `Spec.listHeader size c` and returns its length. -/
theorem writeCollectionBegin_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteCollectionBegin =
      some fn_apache_thrift_protocol_TCompactProtocolT_writeCollectionBegin)
    (cirH_fg : ctx.mod.findFunc? symGetCompactType = some fn_apache_thrift_protocol_TCompactProtocolT_getCompactType)
    (cirH_fb : ctx.mod.findFunc? symWriteByte = some fn_apache_thrift_protocol_TCompactProtocolT_writeByte)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (gb : Nat) (cirH_g : ctx.gaddr gTTypeToCType = some gb)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (kg : BlockKind) (cirH_gb : m.blocks gb = some ⟨kg, true, .array (.int true 8) 17, .arr cTypeTable⟩)
    (cirH_gbl : gb < m.next)
    (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (t c : Nat) (ht : Spec.compactType t = some c) (size : Nat) (hsize : size < 2 ^ 31) :
    Returns ctx symWriteCollectionBegin [.ptr (.loc pb []), .int t, .int size] m
      (fun r m' => r = some (.int (Spec.listHeader size c).length) ∧
        sinkOf m' = sinkOf m ++ (Spec.listHeader size c).map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_specg := fun m' this' kg' h1 h2 => getCompactType_E ctx cirH_fg gb cirH_g m' kg' h1 h2 this' t c ht
  have cirH_specb := fun m' pb' kp' v' h1 h2 h3 h4 c' hc' =>
    writeByte_E ctx cirH_fb tp Fp sinkOf TW m' pb' kp' v' h1 h2 h3 h4 c' hc'
  have cirH_specw := fun m' pb' kp' v' h1 h2 h3 h4 n0 hn0 =>
    writeVarint32_E ctx cirH_fw tp Fp sinkOf TW m' pb' kp' v' h1 h2 h3 h4 n0 hn0
  have hc := Spec.compactType_lt ht
  have cirH_t17 := (cTypeTable_get ht).1
  have hsrc0 : ∀ mm, (∀ b, b < m.next → mm.blocks b = m.blocks b) → sinkOf mm = sinkOf m :=
    fun mm h => hstable m mm (fun b hb => h b (hFp b hb))
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_writeCollectionBegin.nothrow = false := rfl
  have cirH_vlen : (varint size).length ≤ 5 := by
    rw [varint_eq_spec, List.length_map]; exact Spec.varint_length_le5 (by omega)
  unfold gTTypeToCType at cirH_g
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try (first | omega | (rename_i b hb; have := hFp b hb; omega))
  all_goals try exact (wrap8_range _).1
  all_goals try exact (wrap8_range _).2
  -- the short form `(int8_t)(size << 4 | c)`
  case h.left => rw [Spec.listHeader_short (by omega) hc]; rfl
  case h.right.left =>
    rw [hstable cir_mem2 _ (fun b hb => by
      have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post2ba,
      hsrc0 _ (fun b hb => by
        (try dsimp only); (try simp (disch := omega) only [killRange_of_lt, upd_apply_ne]); rw [cirH_post0bb b (by omega)]; (try simp (disch := omega) only [upd_apply_ne])),
      Spec.listHeader_short (by omega) hc, lh_byte (by omega) hc]
    simp only [List.map_cons, List.map_nil, UInt8.toNat_ofNat']
    congr 2; omega
  -- the long form: the byte `0xF0 | c`, then the varint of `size`
  all_goals first
    | (rw [Spec.listHeader_long (by omega) hc, List.length_cons, varint_eq_spec, List.length_map]
       omega)
    | (rw [hstable cir_mem5 _ (fun b hb => by
          have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post5ba,
        hstable cir_mem2 _ (fun b hb => by
          have := hFp b hb; dsimp only; simp (disch := omega) only [upd_apply_ne]), cirH_post2ba,
        hsrc0 _ (fun b hb => by
          (try dsimp only); (try simp (disch := omega) only [killRange_of_lt, upd_apply_ne]); rw [cirH_post0bb b (by omega)]; (try simp (disch := omega) only [upd_apply_ne])),
        Spec.listHeader_long (by omega) hc, List.map_cons, varint_eq_spec, UInt8.toNat_ofNat', lh_byte_long hc,
        List.append_assoc, List.singleton_append]
       congr 3 <;> omega)

end EquivLean.Demo.Thrift.Cpp
