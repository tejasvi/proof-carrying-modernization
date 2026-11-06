import EquivLean.Demo.Thrift.Cpp.ListRead

/-!
# Thrift, C++ side: the list header with a negative size (M)

`readListBegin_exNegSize`: on `F5 80 80 80 80 08` (`Spec.exNegSize`, size `2^31`) `readListBegin` reads the
header byte, the varint32 `2^31` into its `int32_t` size (-2^31 < 0), and throws `TProtocolException` with type
`NEGATIVE_SIZE` (2), for every transport.  The throw runs the `TProtocolException`, `TException` and
`std::exception` constructors (`std::string()` by cirlean's model of it); `ExnProgram` collects the program
facts they look up (constructors, vtables, record declarations, base-class and vptr paths).
-/


open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

attribute [cir_exec]
  rec_apache_thrift_protocol_TProtocolException
  rec_apache_thrift_TException
  rec_std_exception
  rec_std_string
  rec_anon_4
  rec_std_basic_string_char_std_char_traits_char_std_allocator_char_rep
  rec_std_basic_string_char_std_char_traits_char_std_allocator_char_short
  rec_anon_5
  rec_std_basic_string_char_std_char_traits_char_std_allocator_char_long
  rec_anon_6
  rec_apache_thrift_protocol_TList

/-- The program facts the `throw TProtocolException(type)` path looks up: the constructors (`std::string()` by
cirlean's model of it), the classes' vtables and record declarations, and the base-class and vptr paths of their
layout. -/
structure ExnProgram (ctx : Ctx) : Prop where
  fPE : ctx.mod.findFunc? "_ZN6apache6thrift8protocol18TProtocolExceptionC2ENS2_22TProtocolExceptionTypeE" =
    some fn_apache_thrift_protocol_TProtocolException_TProtocolException
  fTE : ctx.mod.findFunc? "_ZN6apache6thrift10TExceptionC2Ev" = some fn_apache_thrift_TException_TException_3
  fSE : ctx.mod.findFunc? "_ZNSt9exceptionC2B9nqe240000Ev" = some fn_std_exception_exception_abi_nqe240000
  fStr : ctx.mod.findFunc? "_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEEC2B9nqe240000Ev" =
    some fn_std_basic_string_basic_string_abi_nqe240000
  vPE : ctx.mod.findGlobal? "_ZTVN6apache6thrift8protocol18TProtocolExceptionE" =
    some g_ZTVN6apache6thrift8protocol18TProtocolExceptionE
  vTE : ctx.mod.findGlobal? "_ZTVN6apache6thrift10TExceptionE" = some g_ZTVN6apache6thrift10TExceptionE
  vSE : ctx.mod.findGlobal? "_ZTVSt9exception" = some g_ZTVSt9exception
  rPE : ctx.mod.findRecord? "apache::thrift::protocol::TProtocolException" =
    some rec_apache_thrift_protocol_TProtocolException
  rTE : ctx.mod.findRecord? "apache::thrift::TException" = some rec_apache_thrift_TException
  rSE : ctx.mod.findRecord? "std::exception" = some rec_std_exception
  rStr : ctx.mod.findRecord? "std::__1::string" = some rec_std_string
  rA4 : ctx.mod.findRecord? "anon.4" = some rec_anon_4
  rRep : ctx.mod.findRecord? "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep" =
    some rec_std_basic_string_char_std_char_traits_char_std_allocator_char_rep
  rShort : ctx.mod.findRecord?
      "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short" =
    some rec_std_basic_string_char_std_char_traits_char_std_allocator_char_short
  rA5 : ctx.mod.findRecord? "anon.5" = some rec_anon_5
  rLong : ctx.mod.findRecord?
      "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long" =
    some rec_std_basic_string_char_std_char_traits_char_std_allocator_char_long
  rA6 : ctx.mod.findRecord? "anon.6" = some rec_anon_6
  bPE : ctx.basePath 16 "apache::thrift::protocol::TProtocolException" "apache::thrift::TException" 0 = some [0]
  bTE : ctx.basePath 16 "apache::thrift::TException" "std::exception" 0 = some [0]
  pPE : ctx.vptrPath 16 "apache::thrift::protocol::TProtocolException" = some [0, 0, 0]
  pTE : ctx.vptrPath 16 "apache::thrift::TException" = some [0, 0]
  pSE : ctx.vptrPath 16 "std::exception" = some [0]

/-- (M) `F5 80 80 80 80 08` (`Spec.exNegSize`, size `2^31`): `readListBegin` reads the header byte and the varint32
`2^31` into its `int32_t` size, which is negative, and throws `TProtocolException(NEGATIVE_SIZE)`. -/
theorem readListBegin_exNegSize (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadListBegin = some fn_apache_thrift_protocol_TCompactProtocolT_readListBegin)
    (cirH_fb : ctx.mod.findFunc? symReadByte = some fn_apache_thrift_protocol_TCompactProtocolT_readByte)
    (cirH_f32 : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (cirH_rl : ctx.mod.findRecord? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList)
    (EP : ExnProgram ctx)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (fs : List Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, .agg fs⟩)
    (cirH_tr : fs[1]? = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bt bz : Nat) (hsrc : srcOf m = Spec.exNegSize.map UInt8.toNat) :
    Spec.readListHeader Spec.exNegSize = none ∧
    Calls ctx symReadListBegin [.ptr (.loc pb []), .ptr (.loc bt []), .ptr (.loc bz [])] m
      (fun e m' => ∃ x, e = .exn x ∧ x.typeinfo = "_ZTIN6apache6thrift8protocol18TProtocolExceptionE" ∧
        ∃ b fs', x.obj = .loc b [] ∧
          m'.blocks b = some ⟨.exn, true, .record "apache::thrift::protocol::TProtocolException", .agg fs'⟩ ∧
          fs'[1]? = some (.int 2)) := by
  refine ⟨Spec.exNegSize_malformed.2.2, ?_⟩
  obtain ⟨cirH_e1, cirH_e2, cirH_e3, cirH_e4, cirH_e5, cirH_e6, cirH_e7, cirH_e8, cirH_e9, cirH_e10, cirH_e11,
    cirH_e12, cirH_e13, cirH_e14, cirH_e15, cirH_e16, cirH_e17, cirH_e18, cirH_e19, cirH_e20, cirH_e21, cirH_e22⟩ := EP
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readListBegin.nothrow = false := rfl
  have cirH_specb : ∀ (m' : Mem) (pb' : Nat) (kp' : BlockKind) (v' : Val),
      m'.blocks pb' = some ⟨kp', true, .record recProto, v'⟩ → v'.get? [PathElem.idx 1] = some (.ptr tp) →
      pb' < m'.next → (∀ b, Fp b → b < m'.next) →
      ∀ (bo' : Nat) (ko' : BlockKind) (vo' : Val), m'.blocks bo' = some ⟨ko', true, .int true 8, vo'⟩ →
      ko' ≠ .readonly → bo' < m'.next → ¬ Fp bo' → srcOf m' = ((0xF5 : UInt8) :: [0x80, 0x80, 0x80, 0x80, 0x08]).map UInt8.toNat →
      Returns ctx symReadByte [.ptr (.loc pb' []), .ptr (.loc bo' [])] m'
        (fun r m'' => r = some (.int 1) ∧
          m''.blocks bo' = some ⟨ko', true, .int true 8, .int (wrap true 8 (0xF5 : UInt8).toNat)⟩ ∧
          srcOf m'' = ([0x80, 0x80, 0x80, 0x80, 0x08] : Spec.Bytes).map UInt8.toNat ∧ m'.next ≤ m''.next ∧
          ∀ b'', ¬ Fp b'' → b'' ≠ bo' → b'' < m'.next → m''.blocks b'' = m'.blocks b'') :=
    fun m' pb' kp' v' h1 h2 h3 h4 bo' ko' vo' h5 h6 h7 h8 h9 =>
      returns_mono (readByte_D ctx cirH_fb tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 bo' ko' vo' h5 h6 h7 h8
        (by rw [h9]; simp)) (fun r m'' ⟨e1, e2, e3, e4, e5⟩ => ⟨e1, by rw [e2, h9]; rfl, by rw [e3, h9]; rfl, e4, e5⟩)
  have cirH_spec32 := fun m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 h10 =>
    readVarint32_ok ctx cirH_f32 cirH_f64 tp Fp srcOf TR m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9
      [0x80, 0x80, 0x80, 0x80, 0x08] [] (2 ^ 31) (by decide) h10
  have cirH_rl' : ctx.record? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList := cirH_rl
  have cirH_tlinit : ctx.initVal 32 (.record "apache::thrift::protocol::TList") = .agg [.undef, .undef] := by
    simp [Ctx.initVal, Ctx.record?, cirH_rl, rec_apache_thrift_protocol_TList]
  have cirH_w : wrap true 32 ((2 ^ 31 : Nat) : Int) = -2147483648 := by decide
  have cirH_n1 : wrap true 8 (((0xF5 : UInt8).toNat : Nat) : Int) = -11 := by decide
  have cirH_n2 : wrap false 8 (-11) = 245 := by decide
  have cirH_n3 : wrap true 32 245 = 245 := by decide
  have cirH_n4 : (245 : Int) / 16 = 15 := by decide
  have cirH_n5 : bitwise true 32 (fun x1 x2 => x1 &&& x2) 15 15 = 15 := by decide
  have cirH_n6 : wrap true 32 2147483648 = -2147483648 := by decide
  have cirH_q8 : ctx.record? "apache::thrift::protocol::TProtocolException" =
      some rec_apache_thrift_protocol_TProtocolException := cirH_e8
  have cirH_q9 : ctx.record? "apache::thrift::TException" = some rec_apache_thrift_TException := cirH_e9
  have cirH_q10 : ctx.record? "std::exception" = some rec_std_exception := cirH_e10
  have cirH_q11 : ctx.record? "std::__1::string" = some rec_std_string := cirH_e11
  have cirH_q12 : ctx.record? "anon.4" = some rec_anon_4 := cirH_e12
  have cirH_q13 : ctx.record?
      "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep" =
      some rec_std_basic_string_char_std_char_traits_char_std_allocator_char_rep := cirH_e13
  have cirH_q14 : ctx.record?
      "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short" =
      some rec_std_basic_string_char_std_char_traits_char_std_allocator_char_short := cirH_e14
  have cirH_q15 : ctx.record? "anon.5" = some rec_anon_5 := cirH_e15
  have cirH_q16 : ctx.record?
      "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long" =
      some rec_std_basic_string_char_std_char_traits_char_std_allocator_char_long := cirH_e16
  have cirH_q17 : ctx.record? "anon.6" = some rec_anon_6 := cirH_e17
  have cirH_mm0 : rec_apache_thrift_protocol_TProtocolException.members = [(.data, (.record "apache::thrift::TException")), (.data, (.int false 32)), (.pad, (.array (.int false 8) 4))] := rfl
  have cirH_mm1 : rec_apache_thrift_TException.members = [(.data, (.record "std::exception")), (.data, (.record "std::__1::string"))] := rfl
  have cirH_mm2 : rec_std_exception.members = [(.data, .vptr)] := rfl
  have cirH_mm3 : rec_std_string.members = [(.data, (.record "anon.4"))] := rfl
  have cirH_mm4 : rec_anon_4.members = [(.data, (.record "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"))] := rfl
  have cirH_mm5 : rec_std_basic_string_char_std_char_traits_char_std_allocator_char_rep.members = [(.data, (.record "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short")), (.data, (.record "std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long"))] := rfl
  have cirH_mm6 : rec_std_basic_string_char_std_char_traits_char_std_allocator_char_short.members = [(.data, (.record "anon.5")), (.data, (.array (.int true 8) 23))] := rfl
  have cirH_mm7 : rec_anon_5.members = [(.bitfield, (.int false 8))] := rfl
  have cirH_mm8 : rec_std_basic_string_char_std_char_traits_char_std_allocator_char_long.members = [(.data, (.record "anon.6")), (.data, (.int false 64)), (.data, (.ptr (.int true 8)))] := rfl
  have cirH_mm9 : rec_anon_6.members = [(.bitfield, (.int false 64))] := rfl
  have cirH_peinit : ctx.initVal 32 (.record "apache::thrift::protocol::TProtocolException") =
      .agg [.agg [.agg [.undef], .agg [.agg [.agg [.agg [.agg [.undef], .arr (List.replicate 23 .undef)],
        .agg [.agg [.undef], .undef, .undef]]]]], .undef, .arr (List.replicate 4 .undef)] := by
    simp [Ctx.initVal, cirH_q8, cirH_q9, cirH_q10, cirH_q11, cirH_q12, cirH_q13, cirH_q14, cirH_q15, cirH_q16,
      cirH_q17, rec_apache_thrift_protocol_TProtocolException, rec_apache_thrift_TException, rec_std_exception,
      rec_std_string, rec_anon_4, rec_std_basic_string_char_std_char_traits_char_std_allocator_char_rep,
      rec_std_basic_string_char_std_char_traits_char_std_allocator_char_short, rec_anon_5,
      rec_std_basic_string_char_std_char_traits_char_std_allocator_char_long, rec_anon_6]
  unfold Spec.exNegSize at hsrc
  unfold Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  all_goals try omega
  all_goals try (rename_i b' hb'; have := hFp b' hb'; omega)
  all_goals try (rename_i h; simp at h; done)
  case h.hspec.refine'_13 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  case h.hspec.refine'_14 =>
    simp (disch := (apply cirH_nfp; omega)) only [srcU]
    rw [hstable cir_mem0 ⟨cir_mem0.blocks, cir_mem0.next⟩ (fun b _ => rfl), cirH_post0bba]; rfl
  case h.right.right => exact ⟨cir_mem4.next, _, rfl, upd_apply_same _ _ _, rfl⟩


end EquivLean.Demo.Thrift.Cpp
