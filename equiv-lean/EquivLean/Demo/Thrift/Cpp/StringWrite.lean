import EquivLean.Demo.Thrift.Cpp.FieldHeader

/-!
# Thrift, C++ side: compact string/binary length prefix, writer (E)

`writeBinary_E`: `TCompactProtocolT<TTransport>::writeBinary(str)` (what `writeString` calls) appends exactly
`Spec.lenPrefix bs` for every `std::string` holding the bytes `bs` (as `char`s), `bs.length < 2^31`.  The string's
`size()` and `data()` run on cirlean's built-in model of libc++'s `std::string` (`CIR.Model.strSize`,
`CIR.Model.strCStr`: the object is a container value `vec g (chars ++ [0])`), a library model, listed as such;
the transport's write of the characters is the transport contract `WriteVecContract`.
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

/-- The byte of a `char` value. -/
def charByte (v : Val) : Nat := match v with | .int c => (c % 256).toNat | _ => 0

/-- The C++ transport contract, writes from a `std::string`'s characters (cirlean's model of `std::string`: a
container value `vec g xs`; `data()` points at element 0): `TTransport::write(p, len)` with `p` at element `k` of
a string object `b` and `len` characters from there appends their bytes. -/
structure WriteVecContract (ctx : Ctx) (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) : Prop where
  writeVec : ∀ (m : Mem) (b : Nat) (kd : BlockKind) (ty : Ty) (g : Nat) (xs : List Val) (k : Nat) (len : Int), ¬ Fp b →
    m.blocks b = some ⟨kd, true, ty, .vec g xs⟩ → 0 ≤ len → k + len.toNat ≤ xs.length →
    Returns ctx symWrite [.ptr tp, .ptr (.loc b [.vel g k]), .int len] m
      (fun r m' => r = none ∧ sinkOf m' = sinkOf m ++ ((xs.drop k).take len.toNat).map charByte ∧
        m.next ≤ m'.next ∧ ∀ b', ¬ Fp b' → b' < m.next → m'.blocks b' = m.blocks b')

theorem charByte_wrap (b : UInt8) : charByte (.int (wrap true 8 b.toNat)) = b.toNat := by
  have hb := b.toNat_lt
  unfold charByte wrap; simp only [Bool.true_and, decide_eq_true_eq, Nat.reduceSub, Int.reducePow]; split <;> omega

theorem bytes_of_chars (bs : Spec.Bytes) :
    (((bs.map (fun b => Val.int (wrap true 8 b.toNat)) ++ [Val.int 0]).drop 0).take bs.length).map charByte =
      bs.map UInt8.toNat := by
  rw [List.drop_zero, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), List.map_map]
  congr 1; funext b; exact charByte_wrap b

def symWriteBinary : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE11writeBinaryERKNSt3__112basic_stringIcNS6_11char_traitsIcEENS6_9allocatorIcEEEE"

/-- (E) `writeBinary(str)` for every `std::string` holding the bytes `bs` (as `char`s): appends exactly
`Spec.lenPrefix bs`. -/
theorem writeBinary_E (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symWriteBinary = some fn_apache_thrift_protocol_TCompactProtocolT_writeBinary)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (cirH_fsz : ctx.mod.findFunc? "_ZNKSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE4sizeB9nqe240000Ev" =
      some fn_std_basic_string_size_abi_nqe240000)
    (cirH_fdt : ctx.mod.findFunc? "_ZNKSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE4dataB9nqe240000Ev" =
      some fn_std_basic_string_data_abi_nqe240000)
    (cirH_fmx : ctx.mod.findFunc? "_ZNSt3__114numeric_limitsIjE3maxB9nqe240000Ev" =
      some fn_std_numeric_limits_max_abi_nqe240000)
    (cirH_fmx2 : ctx.mod.findFunc? "_ZNSt3__123__libcpp_numeric_limitsIjLb1EE3maxB9nqe240000Ev" =
      some fn_std_libcpp_numeric_limits_max_abi_nqe240000)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (TV : WriteVecContract ctx tp Fp sinkOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bs_ : Nat) (ks : BlockKind) (g : Nat) (bs : Spec.Bytes) (hlen : bs.length < 2 ^ 31)
    (cirH_bs : m.blocks bs_ = some ⟨ks, true, .record "std::__1::string",
      .vec g (bs.map (fun b => .int (wrap true 8 b.toNat)) ++ [.int 0])⟩)
    (hbs : bs_ < m.next) (hbsF : ¬ Fp bs_) :
    Returns ctx symWriteBinary [.ptr (.loc pb []), .ptr (.loc bs_ [])] m
      (fun r m' => r = some (.int (Spec.lenPrefix bs).length) ∧
        sinkOf m' = sinkOf m ++ (Spec.lenPrefix bs).map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have cirH_specw := fun m' pb' kp' v' h1 h2 h3 h4 n0 hn0 =>
    writeVarint32_E ctx cirH_fw tp Fp sinkOf TW m' pb' kp' v' h1 h2 h3 h4 n0 hn0
  have cirH_specv := TV.writeVec
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_writeBinary.nothrow = false := rfl
  have cirH_len := hlen
  have cirH_vlen : (varint bs.length).length ≤ 5 := by
    rw [varint_eq_spec, List.length_map]; exact Spec.varint_length_le5 (by omega)
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try omega
  case h.hspec.refine'_6 => rename_i b hb; have := hFp b hb; omega
  case h.hspec.refine'_7 => simp
  case h.left => rw [varint_eq_spec, List.length_map]; simp [Spec.lenPrefix]
  case h.right.left =>
    rw [hstable cir_mem3 _ (fun b hb => by
      have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post3ba,
      hstable cir_mem0 _ (fun b hb => by
        have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post0ba,
      hstable m _ (fun b hb => by
        have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]),
      show (((bs.length : Nat) : Int)).toNat = bs.length from Int.toNat_natCast _, bytes_of_chars, varint_eq_spec,
      Spec.lenPrefix, List.map_append, List.append_assoc]

end EquivLean.Demo.Thrift.Cpp
