import EquivLean.Demo.Thrift.Cpp.ReadLemmas
import EquivLean.Demo.Thrift.Cpp.Varint

/-!
# Thrift, C++ side: compact varint64 read (D and the accepted malformed inputs of M)

`readVarint64_ok`: `TCompactProtocolT<TTransport>::readVarint64(i64)` on a transport whose source `bs`
satisfies `Spec.readVarint 10 bs = some (x, rest)` (a varint of at most 10 bytes, its value `x` not bounded)
returns the number of bytes read, stores `x` modulo `2^64` (as an `int64_t`) and leaves exactly `rest`, for
every transport satisfying the read contract `ReadContract`, whichever way `borrow` answers:
* a pointer into the transport's own buffers, or into the caller's `buf` (the fast path: the bytes are read
  through the pointer and `consume`d at the end),
* `NULL` (the slow path: one `readAll(&byte, 1)` per byte).
Corollaries: `readVarint64_D` (the spec's varint of every `x < 2^64`), and `readVarint64_exceeds` (M: a varint
of at most 10 bytes whose value is `2^64` or more, which the spec rejects, is accepted modulo `2^64`).
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

def symReadVarint64 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE12readVarint64ERl"

set_option hygiene false in
/-- The facts a fast-path iteration reads, at the loop head `σ`: the borrowed block `B`, the protocol object,
`i64`'s block, the source, the bounds of the byte read and of the shift. -/
macro "fast_facts " B:term:max : tactic => `(tactic| (
  have cirH_bblk : σ.mem.blocks $B = some ⟨cir_w_cirH_post0bbbppp, true,
      .array (.int false 8) cir_w_cirH_post0bbbpppp, .arr cir_w_cirH_post0bbbppppp⟩ := by
    rw [cirH_frame _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by omega), cirH_s0]
    dsimp only
    rw [upd_apply_ne (by omega)]
    exact cirH_post0bbbppppppbbbba
  have cirH_pblk : σ.mem.blocks pb = some ⟨kp, true, .record recProto, v⟩ := by
    rw [cirH_frame _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by omega), cirH_s0]
    dsimp only
    rw [upd_apply_ne (by omega), cirH_post0ba _ hpbF (by omega) (by omega) (by omega)]
    simp (disch := omega) only [upd_apply_ne]
    exact cirH_pb
  have cirH_biblk : σ.mem.blocks bi = some ⟨ki, true, .int true 64, vi⟩ := by
    rw [cirH_frame _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by omega), cirH_s0]
    dsimp only
    rw [upd_apply_ne (by omega), cirH_post0ba _ hbiF (by omega) (by omega) (by omega)]
    simp (disch := omega) only [upd_apply_ne]
    exact cirH_bi
  have hsrcσ : srcOf σ.mem = bs.map UInt8.toNat := by
    rw [hstable σ₀.mem σ.mem (fun b hb => cirH_frame b
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; have := hFp b hb; omega)
      (by have := hFp b hb; omega)), cirH_s0]
    dsimp only
    rw [srcU _ _ _ _ (cirH_nfp _ (by omega)), hstable cir_mem0 ⟨cir_mem0.blocks, cir_mem0.next⟩ (fun b _ => rfl),
      hsrc0]
  have cirH_r9 := hr9
  have cirH_inb : 0 ≤ (cir_w_cirH_post0bbbp : Int) + (rsize : Int) ∧
      (cir_w_cirH_post0bbbp : Int) + (rsize : Int) ≤ (cir_w_cirH_post0bbbppppp.length : Int) :=
    ⟨by omega, by omega⟩
  have cirH_sh : ¬ (7 * (rsize : Int) < 0 ∨ 64 ≤ 7 * (rsize : Int)) := by omega
  have hy256 := rv_byte_lt bs rsize
  have hv' : val < 2 ^ (7 * rsize) := by rw [Nat.pow_mul]; exact hrv.1))

set_option hygiene false in
/-- The fast path's loop, reading through the pointer `borrow` returned into block `B` (`M`, `H`: the memory after
`consume` and its source, as `cir_run` names them). -/
macro "fast_loop " B:term:max M:ident H:ident : tactic => `(tactic| (
  cir_loop (fun rsize val shift => rsize ≤ 9 ∧ shift = 7 * (rsize : Int) ∧ RV bs rest x rsize val)
    (fun rsize val shift => (10 : Int) - rsize)
  case cir_init_goal =>
    cir_run
    all_goals first | omega | exact rv_start hrd
  case cir_step_goal =>
    obtain ⟨hr9, hsh, hrv⟩ := cirH_user
    subst cir_nat0 cir_nat1 hsh
    have cirH_byte := cirH_post0bbbppppppbbbbbb rsize (by omega)
    simp (disch := exact cirH_nfp _ (by omega)) only [srcU, srcM, hsrc] at cirH_byte
    have cirH_byte' : cir_w_cirH_post0bbbppppp[((cir_w_cirH_post0bbbp : Int) + (rsize : Int)).toNat]? =
        some (.int ((bs.map UInt8.toNat).getD rsize 0)) := by
      rw [show ((cir_w_cirH_post0bbbp : Int) + (rsize : Int)).toNat = cir_w_cirH_post0bbbp + rsize by omega]
      exact cirH_byte
    by_cases hb : (bs.map UInt8.toNat).getD rsize 0 < 128
    · -- the last byte: `i64 = val; trans_->consume(rsize); return rsize;`
      fast_facts $B
      have cirH_a7f : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int) 127 =
          (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int) := by
        rw [bitwise_and127_s32 (by omega) (by omega)]; omega
      have cirH_a80 : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int) 128 =
          0 := by
        rw [bitwise_and128_s32 (by omega) (by omega)]; split <;> omega
      obtain ⟨hx, hrest⟩ := rv_exit hrv hb
      have hlt := (rv_lt hrv).1
      cir_run
      case h.hspec.refine'_1 => omega
      case h.hspec.refine'_2 =>
        rw [hstable σ.mem _ (fun b hb => by
          have := hFp b hb; dsimp only
          simp (disch := first | omega | exact neFp _ hb) only [upd_apply_ne]), hsrcσ, List.length_map]
        omega
      case h.left => rw [hrest, rv_len hlt]; omega
      case h.right.left =>
        rw [or_shl7 hv' hr9, wrap_s64_mod, hx, show 2 ^ (7 * rsize) = 128 ^ rsize by rw [Nat.pow_mul],
          Nat.mul_comm _ (128 ^ rsize)]
      case h.right.right.left =>
        rw [hstable $M _ (fun b hb => by
          have := hFp b hb; dsimp only; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]), $H:ident,
          hstable σ.mem _ (fun b hb => by
          have := hFp b hb; dsimp only
          simp (disch := first | omega | exact neFp _ hb) only [upd_apply_ne]), hsrcσ,
          show (↑rsize + 1 : Int).toNat = rsize + 1 by omega, rv_drop, ← hrest]
      case h.right.right.right.left => omega
    · -- a byte with the high bit set: at most 9 of them (no throw), the next iteration
      fast_facts $B
      have cirH_a7f : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int) 127 =
          (((bs.map UInt8.toNat).getD rsize 0 % 128 : Nat) : Int) := by
        rw [bitwise_and127_s32 (by omega) (by omega)]; omega
      have cirH_a80 : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int) 128 =
          128 := by
        rw [bitwise_and128_s32 (by omega) (by omega)]; split <;> omega
      obtain ⟨cirH_r8, hrv'⟩ := rv_step hrv hb
      cir_run
      case h => exfalso; omega
      case h.left.left.left => cir_strip_mdata; omega
      case h.left.right.left =>
        cir_strip_mdata; exact inRange_of_bounds (by simp only [intMin, intMax, Nat.reduceSub, Int.reducePow]; omega)
      case h.left.right.right.left =>
        cir_strip_mdata; exact inRange_of_bounds (by simp only [intMin, intMax, Nat.reduceSub, Int.reducePow]; omega)
      case h.left.right.right.right.left => cir_strip_mdata; omega
      case h.left.right.right.right.right =>
        have hP : 2 ^ (7 * rsize) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
        have := Nat.mul_le_mul (show (bs.map UInt8.toNat).getD rsize 0 % 128 ≤ 127 by omega) hP
        rw [or_shl7 hv' hr9, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega),
          show 2 ^ (7 * rsize) = 128 ^ rsize by rw [Nat.pow_mul]]
        exact hrv'
      case h.right => cir_strip_mdata; omega))

/-- (D, and M where C++ accepts) `readVarint64` on a source whose first at most 10 bytes are a varint of value
`x` followed by `rest`: returns the byte count, stores `x` modulo `2^64` into `i64`, leaves exactly `rest`, and
changes no block outside the transport's footprint but `i64`'s. -/
theorem readVarint64_ok (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 64, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (bs rest : Spec.Bytes) (x : Nat) (hrd : Spec.readVarint 10 bs = some (x, rest))
    (hsrc : srcOf m = bs.map UInt8.toNat) :
    Returns ctx symReadVarint64 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (bs.length - rest.length : Nat)) ∧
        m'.blocks bi = some ⟨ki, true, .int true 64, .int (wrap true 64 x)⟩ ∧ srcOf m' = rest.map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ bi → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TR.stable
  have hB := TR.borrow
  have hC := TR.consume
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
  have neFp : ∀ b, Fp b → b ≠ bi := fun b hb h => hbiF (h ▸ hb)
  have cirH_nothrow : fn_apache_thrift_protocol_TCompactProtocolT_readVarint64.nothrow = false := rfl
  have cirH_ki := hki
  unfold Returns Calls
  rw [evalCall_body cirH_f rfl rfl]
  set_option cir.splitOr true in cir_run
  -- the copies where an exception would escape a `noexcept` function: readVarint64 is not `noexcept`
  all_goals try exact absurd (by assumption :
    fn_apache_thrift_protocol_TCompactProtocolT_readVarint64.nothrow = true) (by decide)
  all_goals
    have hsrc0 : srcOf cir_mem0 = bs.map UInt8.toNat := by
      rw [cirH_post0bba, hstable m _ (fun b hb => by
          have := hFp b hb; dsimp only; simp (disch := omega) only [upd_apply_ne])]
      exact hsrc
  case h₁ =>
    -- the pointer `borrow` returned is to a live block
    rename_i hbad
    have hne : cir_w_cirH_post0bbb ≠ m.next + 8 := by
      rcases cirH_post0bbbppppppbbba with hF | hE
      · have := hFp _ hF; omega
      · omega
    rw [upd_apply_ne hne, cirH_post0bbbppppppbbbba] at hbad
    simp at hbad
  case h.inl =>
    -- `borrow` returned a pointer into the transport's own buffers
    have cirH_bpl : cir_w_cirH_post0bbb < m.next := hFp _ cirH_post0bbbppppppbbba
    fast_loop cir_w_cirH_post0bbb cir_mem9 cirH_post9ba
  case h.inr =>
    -- `borrow` copied the bytes into the caller's `buf`
    fast_loop (m.next + 6) cir_mem8 cirH_post8ba
  case h =>
    -- `borrow` returned `NULL`: one `readAll(&byte, 1)` per byte
    cir_loop (fun rsize val shift (mem : Mem) => rsize ≤ 9 ∧ shift = 7 * (rsize : Int) ∧ RV bs rest x rsize val ∧
        srcOf mem = (bs.drop rsize).map UInt8.toNat ∧ m.next ≤ mem.next ∧
        MemAgree mem m (fun b => ¬ Fp b ∧ b < m.next))
      (fun rsize val shift (mem : Mem) => (10 : Int) - rsize)
    case cir_init_goal =>
      cir_run
      · omega
      · exact rv_start hrd
      · rw [srcU _ _ _ _ (cirH_nfp _ (by omega)), hstable cir_mem0 ⟨cir_mem0.blocks, cir_mem0.next⟩ (fun b _ => rfl),
          hsrc0]
      · omega
      · intro b ⟨hnf, hlt⟩
        dsimp only
        rw [upd_apply_ne (by omega), cirH_post0ba b hnf (by omega) (by omega) (by omega)]
        simp (disch := omega) only [upd_apply_ne]
    case cir_step_goal =>
      subst cir_nat0 cir_nat1 cirU_2
      have ⟨hlt, hr10⟩ := rv_lt cirU_4
      have cirH_pblk : σ.mem.blocks pb = some ⟨kp, true, .record recProto, v⟩ := by
        rw [cirU_9 pb ⟨hpbF, hpb⟩]; exact cirH_pb
      have cirH_biblk : σ.mem.blocks bi = some ⟨ki, true, .int true 64, vi⟩ := by
        rw [cirU_9 bi ⟨hbiF, hbi⟩]; exact cirH_bi
      have cirH_srcB : ∀ o n, srcOf ⟨upd σ.mem.blocks σ.mem.next o, n⟩ = (bs.drop rsize).map UInt8.toNat :=
        fun o n => by
          rw [srcU _ _ _ _ (cirH_nfp _ (by omega)), hstable σ.mem ⟨σ.mem.blocks, n⟩ (fun b _ => rfl), cirU_6]
      have cirH_ne := rv_ne_nil hlt
      have cirH_head := rv_head bs rsize
      have cirH_r9 := cirU_0
      have cirH_sh : ¬ (7 * (rsize : Int) < 0 ∨ 64 ≤ 7 * (rsize : Int)) := by omega
      have hy256 := rv_byte_lt bs rsize
      have hv' : val < 2 ^ (7 * rsize) := by rw [Nat.pow_mul]; exact cirU_4.1
      by_cases hb : (bs.map UInt8.toNat).getD rsize 0 < 128
      · -- the last byte: `i64 = val; return rsize;`
        have cirH_a7f : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int)
            127 = (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int) := by
          rw [bitwise_and127_s32 (by omega) (by omega)]; omega
        have cirH_a80 : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int)
            128 = 0 := by
          rw [bitwise_and128_s32 (by omega) (by omega)]; split <;> omega
        obtain ⟨hx, hrest⟩ := rv_exit cirU_4 hb
        cir_run
        all_goals try rw [cirH_srcB, rv_tail] at cirH_post3bba
        case h.left => rw [hrest, rv_len hlt]; omega
        case h.right.left =>
          rw [or_shl7 hv' cirH_r9, wrap_s64_mod, hx, show 2 ^ (7 * rsize) = 128 ^ rsize by rw [Nat.pow_mul],
            Nat.mul_comm _ (128 ^ rsize)]
        case h.right.right.left =>
          rw [hstable cir_mem3 _ (fun b hb => by
            have := hFp b hb; dsimp only
            simp (disch := first | omega | exact neFp _ hb) only [killRange_of_lt, upd_apply_ne]), cirH_post3bba,
            ← hrest]
        case h.right.right.right.left => omega
        case h.right.right.right.right => exact cirU_9 _ ⟨by assumption, by assumption⟩
      · -- a byte with the high bit set: at most 9 of them (no throw), the next iteration
        have cirH_a7f : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int)
            127 = (((bs.map UInt8.toNat).getD rsize 0 % 128 : Nat) : Int) := by
          rw [bitwise_and127_s32 (by omega) (by omega)]; omega
        have cirH_a80 : bitwise true 32 (fun x1 x2 => x1 &&& x2) (((bs.map UInt8.toNat).getD rsize 0 : Nat) : Int)
            128 = 128 := by
          rw [bitwise_and128_s32 (by omega) (by omega)]; split <;> omega
        obtain ⟨cirH_r8, hrv'⟩ := rv_step cirU_4 hb
        cir_run
        all_goals try rw [cirH_srcB, rv_tail] at cirH_post3bba
        case h => exfalso; omega
        case h.left.left.left => cir_strip_mdata; omega
        case h.left.right.left =>
          cir_strip_mdata; exact inRange_of_bounds (by simp only [intMin, intMax, Nat.reduceSub, Int.reducePow]; omega)
        case h.left.right.right.left =>
          cir_strip_mdata; exact inRange_of_bounds (by simp only [intMin, intMax, Nat.reduceSub, Int.reducePow]; omega)
        case h.left.right.right.right.left => cir_strip_mdata; omega
        case h.left.right.right.right.right.left =>
          have hP : 2 ^ (7 * rsize) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
          have := Nat.mul_le_mul (show (bs.map UInt8.toNat).getD rsize 0 % 128 ≤ 127 by omega) hP
          rw [or_shl7 hv' cirH_r9, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega),
            show 2 ^ (7 * rsize) = 128 ^ rsize by rw [Nat.pow_mul]]
          exact hrv'
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
          exact cirU_9 b ⟨hnf, hlt'⟩
        case h.right => cir_strip_mdata; omega

theorem returns_mono {ctx : Ctx} {sym : String} {args : List Val} {m : Mem} {P Q : Option Val → Mem → Prop}
    (h : Returns ctx sym args m P) (hPQ : ∀ r m', P r m' → Q r m') : Returns ctx sym args m Q := by
  unfold Returns Calls at *
  refine Res.holds_mono h ?_
  rintro ⟨e, m'⟩ he
  cases e with
  | ret v => exact hPQ v m' he
  | _ => exact he

/-- (D) The spec's varint of every `x < 2^64`, then any bytes `rest`: `readVarint64` returns its length, stores
`x` (as an `int64_t`) and leaves exactly `rest`. -/
theorem readVarint64_D (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 64, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (x : Nat) (hx : x < 2 ^ 64) (rest : Spec.Bytes) (hsrc : srcOf m = (Spec.varint x ++ rest).map UInt8.toNat) :
    Returns ctx symReadVarint64 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (Spec.varint x).length) ∧
        m'.blocks bi = some ⟨ki, true, .int true 64, .int (wrap true 64 x)⟩ ∧ srcOf m' = rest.map UInt8.toNat ∧
        m.next ≤ m'.next ∧ ∀ b, ¬ Fp b → b ≠ bi → b < m.next → m'.blocks b = m.blocks b) := by
  have h := readVarint64_ok ctx cirH_f tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki vi cirH_bi hki
    hbi hbiF (Spec.varint x ++ rest) rest x
    (Spec.readVarint_varint 10 x rest (Spec.varint_length_le10 hx)) hsrc
  rwa [List.length_append, Nat.add_sub_cancel] at h

/-- (M) A varint of at most 10 bytes whose value `x` is `2^64` or more (`Spec.readVarint64` rejects it,
`VarintExceeds 10 (2^64)`): C++'s `readVarint64` accepts it and stores `x` modulo `2^64`. -/
theorem readVarint64_exceeds (ctx : Ctx)
    (cirH_f : ctx.mod.findFunc? symReadVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_readVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) (TR : ReadContract ctx tp Fp srcOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp)) (hpb : pb < m.next) (hpbF : ¬ Fp pb)
    (hFp : ∀ b, Fp b → b < m.next)
    (bi : Nat) (ki : BlockKind) (vi : Val) (cirH_bi : m.blocks bi = some ⟨ki, true, .int true 64, vi⟩)
    (hki : ki ≠ .readonly) (hbi : bi < m.next) (hbiF : ¬ Fp bi)
    (bs rest : Spec.Bytes) (x : Nat) (hrd : Spec.readVarint 10 bs = some (x, rest)) (hx : 2 ^ 64 ≤ x)
    (hsrc : srcOf m = bs.map UInt8.toNat) :
    Spec.readVarint64 bs = none ∧
    Returns ctx symReadVarint64 [.ptr (.loc pb []), .ptr (.loc bi [])] m
      (fun r m' => r = some (.int (bs.length - rest.length : Nat)) ∧
        m'.blocks bi = some ⟨ki, true, .int true 64, .int (wrap true 64 (x % 2 ^ 64 : Nat))⟩ ∧
        srcOf m' = rest.map UInt8.toNat) := by
  refine ⟨by unfold Spec.readVarint64; rw [hrd, Option.bind_some]; dsimp only; rw [ite_eq_left hx], ?_⟩
  refine returns_mono (readVarint64_ok ctx cirH_f tp Fp srcOf TR m pb kp v cirH_pb cirH_tr hpb hpbF hFp bi ki
    vi cirH_bi hki hbi hbiF bs rest x hrd hsrc) ?_
  rintro r m' ⟨h1, h2, h3, -, -⟩
  exact ⟨h1, by rw [h2, wrap_s64_mod], h3⟩

end EquivLean.Demo.Thrift.Cpp
