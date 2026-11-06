import EquivLean.Bridge.TS.Tactic
import EquivLean.Bridge.TS.Corr
import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.TS.FnvBytes
import EquivLean.Demo.Gen.Aeneas.Bits.Funs

/-!
# Demo: TypeScript ↔ Rust migration, FNV-1a over bytes, lockstep loops

* TypeScript: `examples/ts/fnv_bytes.ts` (`h ^= data[i]; h = Math.imul(h, 0x01000193) >>> 0`
  over a `Uint8Array`), translated by the pinned StrictTS front end to
  `EquivLean/Demo/Gen/TS/FnvBytes.lean`;
* Rust: `examples/rust/bits/src/lib.rs` (`h ^= data[i] as u32; h = h.wrapping_mul(0x0100_0193)`
  over `&[u8]`, with a checked `i += 1`), translated by Charon + Aeneas to
  `EquivLean/Demo/Gen/Aeneas/Bits/Funs.lean` (`bits.fnv1a32`).

`fnv_equiv`: for a `Uint8Array` and a byte slice holding the same bytes (`BytesCorr`), the
TypeScript call and the Rust function are equivalent: the TypeScript function returns the
`number` holding the Rust `u32` result and leaves the world unchanged, and the two are safe
on the same inputs (neither panics nor diverges).  Each direction pairs the TypeScript `for`
loop with the Aeneas `loop` in lockstep (`wp_loop_rel`, no variant: the source loop
terminates when it is safe, `loopTerminates` / `Aeneas.loop_terminates`); the coupling
invariant says that the TypeScript loop variables are the doubles of the Rust ones
(`i` as a safe integer, `h` as a uint32).  The pairing is done by `ts_lockstep_x` (a TypeScript
loop against another encoding's `LoopShape`).  The one-step arithmetic is the int32 bridge of
`Bridge/TS/Corr.lean` on the TypeScript side and Aeneas' `bv` lemmas on the Rust side.
-/

namespace EquivLean.Demo.TS.FnvXLang
open EquivLean EquivLean.TS StrictTS
open _root_.Aeneas _root_.Aeneas.Std
open EquivLean.Demo.Gen.TS

abbrev TT := FnvBytes.TT

/-- The `Uint8Array` contents (the heap cell of kind `.tarr .u8`) and the Rust slice hold the
same bytes. -/
def BytesCorr (bytes : Array (BitVec TAKind.u8.width)) (d : Slice U8) : Prop :=
  bytes.size = d.val.length ∧
    ∀ i (h₁ : i < bytes.size) (h₂ : i < d.val.length), bytes[i].toNat = d.val[i].val

/-- The TypeScript outcome holds the Rust `u32` (`Corr F64 (BitVec 32)`: `number` = uint32) and
the world is unchanged. -/
def FnvRel (w : World TT) (o : Out TT (Val TT .num)) (r : Except Error U32) : Prop :=
  ∃ h : U32, r = .ok h ∧ o = (.ok (.num (F64.ofUint32 h.bv)), w)

/-- One TypeScript iteration on doubles: the int32 bridge. -/
theorem ts_step (x : BitVec 32) (b : BitVec TAKind.u8.width) :
    (((F64.ofUint32 x).bxor (F64.ofUintN b)).imul (F64.ofNat 16777619)).shr (F64.ofNat 0) =
      F64.ofUint32 ((x ^^^ BitVec.ofNat 32 b.toNat) * BitVec.ofNat 32 16777619) := by
  have hb : b.toNat < 256 := b.isLt
  rw [ofUintN_eq_ofNat, bxor_ofUint32_ofNat x (by omega), imul_ofInt32_ofNat _ (by omega),
    shr_zero_ofInt32]

/-- One Rust iteration on bit vectors. -/
theorem rust_step (h : U32) (x : U8) :
    (core.num.U32.wrapping_mul (h ^^^ UScalar.cast .U32 x) 16777619#u32).bv =
      ((h.bv : BitVec 32) ^^^ BitVec.ofNat 32 x.val) * BitVec.ofNat 32 16777619 := by
  simp only [core.num.U32.wrapping_mul_bv_eq, UScalar.bv_xor, UScalar.cast_bv_eq]
  have e1 : U32.bv 16777619#u32 = 16777619#32 := rfl
  have e2 : BitVec.ofNat 32 x.val = BitVec.setWidth 32 x.bv := BitVec.ofNat_toNat 32 x.bv
  rw [e1, e2]
  rfl

/-- Coupling invariant: the TypeScript loop state `([i, h, data], w)` and the Rust loop state
`(h, i)`. -/
def fnvJ (a : Nat) (bytes : Array (BitVec TAKind.u8.width)) (w : World TT)
    (s₁ : Env TT [⟨.num, true⟩, ⟨.num, true⟩, ⟨.tarr .u8, false⟩] × World TT) (s₂ : U32 × Usize) :
    Prop :=
  s₁.2 = w ∧ s₂.2.val ≤ bytes.size ∧
    s₁.1 = .cons (.num (F64.ofNat s₂.2.val)) (.cons (.num (F64.ofUint32 s₂.1.bv))
      (.cons (.tarr a) .nil))

/-- Both loops leave with the same hash. -/
def fnvLoopR (a : Nat) (bytes : Array (BitVec TAKind.u8.width)) (w : World TT)
    (o₁ : Out TT (Completion TT .num × Env TT [⟨.num, true⟩, ⟨.num, true⟩, ⟨.tarr .u8, false⟩]))
    (o₂ : Except Error U32) : Prop :=
  ∃ h : U32, o₂ = .ok h ∧
    o₁ = (.ok (.normal, .cons (.num (F64.ofNat bytes.size)) (.cons (.num (F64.ofUint32 h.bv))
      (.cons (.tarr a) .nil))), w)

section
variable (I : Impl) (a : Nat) (bytes : Array (BitVec TAKind.u8.width)) (d : Slice U8)
  (w : World TT)

/-- **TypeScript ⊑ Rust**: wherever the Rust function is safe, the TypeScript call is safe
and returns the same hash. -/
theorem fnv_ts_sim_rust (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Sim (FnvRel w) (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w)
      (bits.fnv1a32 d) := by
  obtain ⟨hsize, hget⟩ := hc
  refine sim_iff_wp.2 fun Q hs => ?_
  simp only [call, FnvBytes.fnv1a32_call, FnvBytes.fnv1a32Def, ts_sym, wp_exec_match, wp_some]
  unfold bits.fnv1a32 bits.fnv1a32_loop at hs
  ts_lockstep_x fnvJ a bytes w, fnvLoopR a bytes w
    using EquivLean.Aeneas.loop_shape _, EquivLean.Aeneas.loop_terminates _
  case init =>
    refine ⟨rfl, by simp, ?_⟩
    simp [F64.ofUint32_eq, F64.ofNat_eq_ofInt]
  case step =>
    clear hs
    rintro ⟨env, w₁⟩ ⟨h, i⟩ ⟨h₁, hi, h₂⟩
    dsimp only at h₁ hi h₂; subst w₁ env
    have hmax : d.val.length ≤ Usize.max := d.property
    by_cases hlt : i.val < bytes.size
    · ts_step_simp [hw, hlt]
      refine sim_some_of_wp ?_
      aeneas_wp [bits.fnv1a32_loop.body]
      have hlt' : i.val < d.val.length := hsize ▸ hlt
      have hmax' : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt', hmax', _root_.dite_true, ite_true, StepRel, stepCls_inr,
        EquivLean.Aeneas.loopCls_cont, fnvJ, UScalar.ofNatCore_val_eq, true_and, ts_step,
        rust_step, hget i.val hlt hlt']
      exact ⟨by omega, trivial⟩
    · have hn : i.val = bytes.size := by omega
      ts_step_simp [hw, hlt]
      refine sim_some_of_wp ?_
      aeneas_wp [bits.fnv1a32_loop.body]
      have hlt' : ¬ i.val < d.val.length := by omega
      simp only [hlt', ite_false, StepRel, stepCls_inl, EquivLean.Aeneas.loopCls_done, fnvLoopR]
      exact ⟨h, rfl, by rw [hn]⟩
  case exit =>
    rintro _ _ ⟨h, rfl, rfl⟩ hK
    simp only [ts_sym, wp_some] at hK ⊢
    exact ⟨_, hK, h, rfl, rfl⟩

/-- **Rust ⊑ TypeScript**: wherever the TypeScript call is safe, the Rust function is safe and
returns the same hash. -/
theorem fnv_rust_sim_ts (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Sim (fun r o => FnvRel w o r) (bits.fnv1a32 d)
      (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w) := by
  obtain ⟨hsize, hget⟩ := hc
  refine sim_iff_wp.2 fun Q hs => ?_
  simp only [call, FnvBytes.fnv1a32_call, FnvBytes.fnv1a32Def, ts_sym, wp_exec_match, wp_some]
    at hs
  unfold bits.fnv1a32 bits.fnv1a32_loop
  ts_lockstep_x (fun s₂ s₁ => fnvJ a bytes w s₁ s₂), (fun o₂ o₁ => fnvLoopR a bytes w o₁ o₂)
    using EquivLean.Aeneas.loop_shape _
  case init =>
    refine ⟨rfl, by simp, ?_⟩
    simp [F64.ofUint32_eq, F64.ofNat_eq_ofInt]
  case step =>
    clear hs
    rintro ⟨h, i⟩ ⟨env, w₁⟩ ⟨h₁, hi, h₂⟩
    dsimp only at h₁ hi h₂; subst w₁ env
    have hmax : d.val.length ≤ Usize.max := d.property
    by_cases hlt : i.val < bytes.size
    · ts_step_simp [hw, hlt]
      rw [sim_some_iff]
      aeneas_wp [bits.fnv1a32_loop.body]
      have hlt' : i.val < d.val.length := hsize ▸ hlt
      have hmax' : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt', hmax', _root_.dite_true, ite_true, StepRel, stepCls_inr,
        EquivLean.Aeneas.loopCls_cont, fnvJ, UScalar.ofNatCore_val_eq, true_and, ts_step,
        rust_step, hget i.val hlt hlt']
      exact ⟨by omega, trivial⟩
    · have hn : i.val = bytes.size := by omega
      ts_step_simp [hw, hlt]
      rw [sim_some_iff]
      aeneas_wp [bits.fnv1a32_loop.body]
      have hlt' : ¬ i.val < d.val.length := by omega
      simp only [hlt', ite_false, StepRel, stepCls_inl, EquivLean.Aeneas.loopCls_done, fnvLoopR]
      exact ⟨h, rfl, by rw [hn]⟩
  case exit =>
    rintro _ _ ⟨h, rfl, rfl⟩ hK
    simp only [ts_sym, wp_some] at hK ⊢
    exact ⟨_, hK, h, rfl, rfl⟩

/-- **TypeScript ≈ Rust** (FNV-1a over the same bytes). -/
theorem fnv_equiv (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Equiv (FnvRel w) (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w)
      (bits.fnv1a32 d) :=
  ⟨fnv_ts_sim_rust I a bytes d w hw hc hlen, fnv_rust_sim_ts I a bytes d w hw hc hlen⟩

end

end EquivLean.Demo.TS.FnvXLang
