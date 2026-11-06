import EquivLean.Demo.Thrift.Cpp.VarintRead32

/-!
# Thrift, C++ side: varint reads at end of input (M)

`EofContract`: the transport contract at end of input (`readAll` with no byte left throws the transport's
end-of-input exception).  `readVarint64_eof` / `readVarint32_eof`: on a source that ends inside a varint of at most
10 bytes (`Spec.VarintTruncated 10`), the exception comes out of the reader; `readVarint32_exVarint32Overlong`: the
spec's named input `80 80 80 80 80`.
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

/-- The C++ transport contract at end of input: `readAll(&c, 1)` with no byte left throws the transport's
end-of-input exception (`eofExn`; for Thrift's transports `TTransportException(END_OF_FILE)`). -/
structure EofContract (ctx : Ctx) (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (eofExn : Exn → Prop) :
    Prop where
  readAllEof : ∀ (m : Mem) (b : Nat) (kd : BlockKind) (v : Val), ¬ Fp b → kd ≠ .readonly →
    m.blocks b = some ⟨kd, true, .int false 8, v⟩ → srcOf m = [] →
    Calls ctx symReadAll [.ptr tp, .ptr (.loc b []), .int 1] m (fun e _ => ∃ x, e = .exn x ∧ eofExn x)

/-- (M) `readVarint64` on a source that ends inside a varint of at most 10 bytes (`Spec.VarintTruncated 10`):
`borrow` cannot give 10 bytes, the slow path reads them all, and the next `readAll` throws the transport's
end-of-input exception, which `readVarint64` passes on. -/
theorem readVarint64_eof (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (eofExn : Exn → Prop) (TE : EofContract ctx tp Fp srcOf eofExn)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 64, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (bs : Spec.Bytes) (htr : Spec.VarintTruncated 10 bs) (hsrc : srcOf m = bs.map UInt8.toNat) :
    Calls ctx symReadVarint64 [.ptr (.loc pb []), .ptr (.loc bi [])] m (fun e _ => ∃ x, e = .exn x ∧ eofExn x) := by
  have hstable := TR.stable
  have hB := TR.borrow
  have hR := TR.readAll1
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  have cirH_pbbi : pb ≠ bi := fun h => by subst h; rw [cirH_pb] at cirH_bi; simp at cirH_bi
  have cirH_bipb : bi ≠ pb := fun h => cirH_pbbi h.symm
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readVarint64.nothrow = false := rfl
  have cirH_ki := hki
  obtain ⟨hlen, hhi⟩ := htr
  unfold Calls
  rw [evalCall_body cirH_f rfl rfl]
  set_option cir.splitOr true in cir_run
  all_goals try exact absurd (by assumption :
    fn_apache_thrift_protocol_TCompactProtocolT_readVarint64.nothrow = true) (by decide)
  all_goals
    have hsrc0 : srcOf cir_mem0 = bs.map UInt8.toNat := by
      rw [cirH_post0bba, hstable m _ (fun b hb => by
          have := hFp b hb; dsimp only; simp (disch := omega) only [upd_apply_ne])]
      exact hsrc
  case h₁ =>
    rename_i hbad
    have hne : cir_w_cirH_post0bbb ≠ m.next + 8 := by
      rcases cirH_post0bbbppppppbbba with hF | hE
      · have := hFp _ hF; omega
      · omega
    rw [upd_apply_ne hne, cirH_post0bbbppppppbbbba] at hbad
    simp at hbad
  -- `borrow` cannot return a pointer: the transport holds fewer than 10 bytes
  case h.inl | h.inr =>
    exfalso
    simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM, hsrc, List.length_map] at cirH_post0bbbppppppbba
    omega
  case h =>
    -- `borrow` returned `NULL`: one `readAll(&byte, 1)` per byte, the last one at end of input
    cir_loop (fun rsize val shift (mem : Mem) => rsize ≤ bs.length ∧ shift = 7 * (rsize : Int) ∧
        srcOf mem = (bs.drop rsize).map UInt8.toNat ∧ m.next ≤ mem.next ∧
        MemAgree mem m (fun b => ¬ Fp b ∧ b < m.next))
      (fun rsize val shift (mem : Mem) => (10 : Int) - rsize)
    case cir_init_goal =>
      cir_run
      all_goals first
        | omega
        | (rw [srcU _ _ _ _ (cirH_nfp _ (by omega)), hstable cir_mem0 ⟨cir_mem0.blocks, cir_mem0.next⟩ (fun b _ => rfl),
            hsrc0])
        | (intro b ⟨hnf, hlt⟩
           dsimp only
           rw [upd_apply_ne (by omega), cirH_post0ba b hnf (by omega) (by omega) (by omega)]
           simp (disch := omega) only [upd_apply_ne])
    case cir_step_goal =>
      subst cir_nat0 cir_nat1 cirU_2
      have cirH_pblk : σ.mem.blocks pb = some ⟨kp, true, .record recProto, v⟩ := by
        rw [cirU_7 pb ⟨hpbF, hpb⟩]; exact cirH_pb
      have cirH_biblk : σ.mem.blocks bi = some ⟨ki, true, .int true 64, vi⟩ := by
        rw [cirU_7 bi ⟨hbiF, hbi⟩]; exact cirH_bi
      have cirH_srcB : ∀ o n, srcOf ⟨upd σ.mem.blocks σ.mem.next o, n⟩ = (bs.drop rsize).map UInt8.toNat :=
        fun o n => by
          rw [srcU _ _ _ _ (cirH_nfp _ (by omega)), hstable σ.mem ⟨σ.mem.blocks, n⟩ (fun b _ => rfl), cirU_4]
      have cirH_r9 : rsize ≤ 9 := by omega
      have cirH_sh : ¬ (7 * (rsize : Int) < 0 ∨ 64 ≤ 7 * (rsize : Int)) := by omega
      by_cases hlt : rsize < bs.length
      · -- a byte with the high bit set: the next iteration
        have cirH_ne := rv_ne_nil hlt
        have cirH_head := rv_head bs rsize
        have hy : 128 ≤ (bs.map UInt8.toNat).getD rsize 0 := by
          rw [rv_byte hlt]; exact hhi _ (List.getElem_mem hlt)
        have hy256 := rv_byte_lt bs rsize
        have cirH_a7f : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int)
            127 = (((bs.map UInt8.toNat).getD rsize 0 % 128 : Nat) : Int) := by
          rw [bitwise_and127_s32 (by omega) (by omega)]; omega
        have cirH_a80 : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int)
            128 = 128 := by
          rw [bitwise_and128_s32 (by omega) (by omega)]; split <;> omega
        have cirH_r8 : rsize + 1 < 10 := by omega
        cir_run
        all_goals try rw [cirH_srcB, rv_tail] at cirH_post3bba
        case h => exfalso; omega
        case h.left.left.left => cir_strip_mdata; omega
        case h.left.right.left =>
          cir_strip_mdata; exact inRange_of_bounds (by simp only [intMin, intMax, Nat.reduceSub, Int.reducePow]; omega)
        case h.left.right.right.left =>
          cir_strip_mdata; exact inRange_of_bounds (by simp only [intMin, intMax, Nat.reduceSub, Int.reducePow]; omega)
        case h.left.right.right.right.left => omega
        case h.left.right.right.right.right.left => cir_strip_mdata; omega
        case h.left.right.right.right.right.right.left =>
          rw [hstable cir_mem3 _ (fun b hb => by
            have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), cirH_post3bba]
        case h.left.right.right.right.right.right.right.left => omega
        case h.left.right.right.right.right.right.right.right =>
          intro b ⟨hnf, hlt'⟩
          dsimp only
          simp (disch := omega) only [killRange_of_lt, upd_apply_ne]
          rw [cirH_post3bbbb b hnf (by omega) (by omega)]
          simp (disch := omega) only [upd_apply_ne]
          exact cirU_7 b ⟨hnf, hlt'⟩
        case h.right => cir_strip_mdata; omega
      · -- end of input: `readAll` throws, and `readVarint64` passes the exception on
        have hrs : rsize = bs.length := by omega
        have cirH_nil : (bs.drop rsize).map UInt8.toNat = [] := by rw [hrs, List.drop_length]; rfl
        have hE := TE.readAllEof
        clear hR
        cir_run
        refine Res.holds_mono (hE _ _ .stack .undef ?_ (by decide) ?_ ?_) ?_
        · exact cirH_nfp _ (by omega)
        · simp
        · rw [cirH_srcB, cirH_nil]
        · rintro ⟨e, m'⟩ ⟨x, he, hx⟩
          dsimp only at he
          subst he
          cir_run
          exact hx

/-- (M) `readVarint32` on a source that ends inside a varint of at most 10 bytes: the transport's end-of-input
exception, from `readVarint64`. -/
theorem readVarint32_eof (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (eofExn : Exn → Prop) (TE : EofContract ctx tp Fp srcOf eofExn)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (bs : Spec.Bytes) (htr : Spec.VarintTruncated 10 bs) (hsrc : srcOf m = bs.map UInt8.toNat) :
    Calls ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m (fun e _ => ∃ x, e = .exn x ∧ eofExn x) := by
  have hstable := TR.stable
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  have h64 := fun m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 h10 =>
    readVarint64_eof ctx cirH_f64 tp Fp srcOf TR eofExn TE m' pb' kp' v' h1 h2 h3 h4 h5 bi' ki' vi' h6 h7 h8 h9 bs htr h10
  clear cirH_f64
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readVarint32.nothrow = false := rfl
  have srcU : ∀ (bs : Nat → Option MemBlock) (k : Nat) (o : Option MemBlock) (n : Nat), ¬ Fp k →
      srcOf ⟨upd bs k o, n⟩ = srcOf ⟨bs, n⟩ :=
    fun bs k o n hk => hstable _ _ (fun b hb => by
      show upd bs k o b = bs b
      rw [upd_apply_ne (by rintro rfl; exact hk hb)])
  have srcM : ∀ n, srcOf ⟨m.blocks, n⟩ = srcOf m := fun n => hstable _ _ (fun b hb => rfl)
  unfold Calls
  rw [evalCall_body cirH_f rfl rfl]
  cir_run
  refine Res.holds_mono (h64 _ pb kp v ?_ cirH_tr ?_ hpbF ?_ _ .stack .undef ?_ (by decide) ?_ ?_ ?_) ?_
  all_goals try (simp (disch := omega) only [upd_apply_ne]; first | exact cirH_pb | simp)
  all_goals try omega
  case refine_2 => dsimp only; omega
  case refine_3 => intro b hb; have := hFp b hb; dsimp only; omega
  case refine_6 => exact cirH_nfp _ (by omega)
  case refine_7 => simp (disch := (apply cirH_nfp; omega)) only [srcU, srcM]; exact hsrc
  case refine_8 =>
    intro e m' x he hx
    subst he
    cir_run
    exact hx

/-- (M) `80 80 80 80 80` and nothing after (`Spec.exVarint32Overlong`; the spec: `VarintOverlong 5`): C++'s
`readVarint32` reads the 5 bytes and the transport's end-of-input exception comes out of it
(`Spec.exVarint32Overlong_truncated10`: as a varint of at most 10 bytes, the input is truncated). -/
theorem readVarint32_exVarint32Overlong (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint32)
    (cirH_f64 : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (eofExn : Exn → Prop) (TE : EofContract ctx tp Fp srcOf eofExn)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next) (bi : Nat)
    (hsrc : srcOf m = Spec.exVarint32Overlong.map UInt8.toNat) :
    Spec.readVarint32 Spec.exVarint32Overlong = none ∧
    Calls ctx symReadVarint32 [.ptr (.loc pb []), .ptr (.loc bi [])] m (fun e _ => ∃ x, e = .exn x ∧ eofExn x) :=
  ⟨Spec.exVarint32Overlong_malformed.2, readVarint32_eof ctx cirH_f cirH_f64 tp Fp srcOf TR eofExn TE m pb kp v
    cirH_pb cirH_tr hpb hpbF hFp bi Spec.exVarint32Overlong Spec.exVarint32Overlong_truncated10 hsrc⟩

end EquivLean.Demo.Thrift.Cpp
