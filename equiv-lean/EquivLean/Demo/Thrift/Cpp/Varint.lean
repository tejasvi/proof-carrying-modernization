import EquivLean.Demo.Gen.Cir.Thrift.ProtoTT
import EquivLean.Demo.Thrift.Cpp.Bits
import EquivLean.Demo.Thrift.Cpp.Transport

/-!
# Thrift, C++ side: compact varint32 and varint64 writes (E)

`writeVarint32_E`, `writeVarint64_E`: `TCompactProtocolT<TTransport>::writeVarint32(n)` (`writeVarint64(n)`) for every
`uint32_t n` (`uint64_t n`) returns the number of bytes written and appends exactly the varint of `n` to the
transport's sink (the transport contract
`WriteContract`), changing no block outside the transport's footprint.  The loop runs by cirlean's loop rule
with `buf`'s bytes so far and the rest `n` behind its variables (`VInv`).
-/

open CIR EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

set_option maxHeartbeats 400000000

namespace EquivLean.Demo.Thrift.Cpp

def symWriteVarint32 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE13writeVarint32Ej"
def symWriteVarint64 : String :=
  "_ZN6apache6thrift8protocol17TCompactProtocolTINS0_9transport10TTransportEE13writeVarint64Em"
@[cir_exec] def recProto : String := "apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>"

/-- The unsigned varint (7-bit groups, least significant first, high bit = more). -/
def varint (n : Nat) : List Nat :=
  if n < 128 then [n] else (n % 128 + 128) :: varint (n / 128)
termination_by n
decreasing_by omega

/-- The state of `writeVarint32`'s loop: the bytes written to `buf` so far (`wsize` of them) and the varint of the
rest `n` make up the varint of `n0`. -/
def VInv (N n0 n wsize : Nat) (buf : List Val) : Prop :=
  ∃ pre : List Nat, pre.length = wsize ∧ varint n0 = pre ++ varint n ∧ buf.length = N ∧
    ∀ i, i < wsize → buf[i]? = some (.int (pre.getD i 0))

theorem varint_lt {n : Nat} (h : n < 128) : varint n = [n] := by rw [varint]; simp [h]

theorem varint_ge {n : Nat} (h : ¬ n < 128) : varint n = (n % 128 + 128) :: varint (n / 128) := by
  rw [varint]; simp [h]

theorem vinv_step {N n0 n w : Nat} {buf : List Val} (hv : VInv N n0 n w buf) (hn : ¬ n < 128) (hw : w < N) :
    VInv N n0 (n / 128) (w + 1) (buf.set w (.int ((n % 128 + 128 : Nat) : Int))) := by
  obtain ⟨pre, hpl, hvar, hbl, hbuf⟩ := hv
  refine ⟨pre ++ [n % 128 + 128], by simp [hpl], ?_, by simp [hbl], fun i hi => ?_⟩
  · rw [hvar, varint_ge hn]; simp
  · by_cases hiw : i < w
    · rw [List.getElem?_set_ne (by omega), hbuf i hiw]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < pre.length by omega)]
    · have hiw' : i = w := by omega
      subst hiw'
      rw [List.getElem?_set_self (by omega)]
      simp [List.getD_eq_getElem?_getD, hpl]

theorem vinv_exit {N n0 n w : Nat} {buf : List Val} (hv : VInv N n0 n w buf) (hn : n < 128) (hw : w < N) :
    bytesOf (buf.set w (.int (n : Int))) 0 (w + 1) = varint n0 ∧ (varint n0).length = w + 1 := by
  obtain ⟨pre, hpl, hvar, hbl, hbuf⟩ := hv
  rw [varint_lt hn] at hvar
  refine ⟨?_, by rw [hvar]; simp [hpl]⟩
  rw [hvar]
  apply List.ext_getElem
  · simp [bytesOf, hpl]
  · intro i h1 h2
    have hi : i < w + 1 := by simpa [bytesOf] using h1
    simp only [bytesOf, List.getElem_map, List.getElem_range, Nat.zero_add]
    by_cases hiw : i < w
    · rw [List.getElem?_set_ne (by omega), hbuf i hiw, List.getElem_append_left (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < pre.length by omega)]
    · have hiw' : i = w := by omega
      subst hiw'
      rw [List.getElem?_set_self (by omega), List.getElem_append_right (by omega)]
      simp [hpl]

theorem pow_step {n w : Nat} (hnb : n < 2 ^ (32 - 7 * w)) (hlt : ¬ n < 128) (hw : w ≤ 4) :
    w ≤ 3 ∧ n / 128 < 2 ^ (32 - 7 * (w + 1)) := by
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp at hnb ⊢ <;> omega

theorem writeVarint32_E (ctx : Ctx)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint32 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint32)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp))
    (hpb : pb < m.next) (hFp : ∀ b, Fp b → b < m.next)
    (n0 : Nat) (hn : n0 < 2 ^ 32) :
    Returns ctx symWriteVarint32 [.ptr (.loc pb []), .int n0] m
      (fun r m' => r = some (.int (varint n0).length) ∧ sinkOf m' = sinkOf m ++ varint n0 ∧ m.next ≤ m'.next ∧
        ∀ b, ¬ Fp b → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have hW := TW.write
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  unfold Returns Calls
  rw [evalCall_body cirH_fw rfl rfl]
  cir_run
  cir_loop (fun n wsize buf => wsize ≤ 4 ∧ n < 2 ^ (32 - 7 * wsize) ∧ VInv 5 n0 n wsize buf)
    (fun n wsize buf => (5 : Int) - wsize)
  case cir_init_goal =>
    cir_run
    all_goals first
      | omega
      | exact ⟨[], rfl, rfl, by simp, fun i hi => absurd hi (by omega)⟩
  case cir_step_goal =>
    obtain ⟨hw4, hnb, hv⟩ := cirH_user
    subst cir_nat0 cir_nat1
    have hn32 : n < 2 ^ 32 := Nat.lt_of_lt_of_le hnb (Nat.pow_le_pow_right (by decide) (by omega))
    by_cases hlt : n < 128
    · -- the last byte: `buf[wsize++] = n; break;`
      have cirH_c : bitwise false 32 (fun x1 x2 => x1 &&& x2) (n : Int) 4294967168 = 0 :=
        (bitwise_mask7_eq_zero (by omega) (by omega)).2 (by omega)
      have cirH_b : wrap false 8 (wrap true 8 (n : Int)) = (n : Int) := by rw [wrap_u8_s8]; omega
      obtain ⟨hbytes, hlen⟩ := vinv_exit hv hlt (by omega)
      cir_run
      all_goals (try (cir_strip_mdata; omega))
      · -- the sink: the bytes of `buf` appended
        refine (hstable cir_mem0 _ ?_).trans ?_
        · intro b hb; have := hFp b hb; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]
        rw [cirH_post0ba, show (↑wsize + 1 : Int).toNat = wsize + 1 by omega, hbytes]
        congr 1
        apply hstable m _
        intro b hb; have := hFp b hb
        simp (disch := omega) only [upd_apply_ne, killRange_of_lt]
        rw [cirH_frame b (by simp; omega) (by omega), cirH_s0]
        simp (disch := omega) only [upd_apply_ne]
    · -- `buf[wsize++] = (n & 0x7F) | 0x80; n >>= 7;`
      have cirH_c : ¬ bitwise false 32 (fun x1 x2 => x1 &&& x2) (n : Int) 4294967168 = 0 := fun h =>
        hlt (by have := (bitwise_mask7_eq_zero (by omega) (by omega)).1 h; omega)
      have cirH_b : wrap false 8 (wrap true 8 (bitwise false 32 (fun x1 x2 => x1 ||| x2)
          (bitwise false 32 (fun x1 x2 => x1 &&& x2) (n : Int) 127) 128)) = ((n % 128 + 128 : Nat) : Int) := by
        rw [bitwise_low7_or (by omega) (by omega), wrap_u8_s8]; omega
      obtain ⟨hw3, hn'⟩ := pow_step hnb hlt hw4
      have hv' := vinv_step hv hlt (by omega)
      cir_run
      all_goals (try (cir_strip_mdata; omega))
      all_goals (try (simp only [CIR.inRange_eq_true_iff, CIR.intMin_u, CIR.intMax_u32]; omega))
      all_goals (try (rw [show ((n : Int) / 128).toNat = n / 128 by omega]; first | exact hn' | exact hv'))
      all_goals (try cir_close')

theorem pow_step64 {n w : Nat} (hnb : n < 2 ^ (64 - 7 * w)) (hlt : ¬ n < 128) (hw : w ≤ 9) :
    w ≤ 8 ∧ n / 128 < 2 ^ (64 - 7 * (w + 1)) := by
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 ∨ w = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hnb ⊢ <;> omega

theorem writeVarint64_E (ctx : Ctx)
    (cirH_fw : ctx.mod.findFunc? symWriteVarint64 = some fn_apache_thrift_protocol_TCompactProtocolT_writeVarint64)
    (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) (TW : WriteContract ctx tp Fp sinkOf)
    (m : Mem) (pb : Nat) (kp : BlockKind) (v : Val)
    (cirH_pb : m.blocks pb = some ⟨kp, true, .record recProto, v⟩)
    (cirH_tr : v.get? [PathElem.idx 1] = some (.ptr tp))
    (hpb : pb < m.next) (hFp : ∀ b, Fp b → b < m.next)
    (n0 : Nat) (hn : n0 < 2 ^ 64) :
    Returns ctx symWriteVarint64 [.ptr (.loc pb []), .int n0] m
      (fun r m' => r = some (.int (varint n0).length) ∧ sinkOf m' = sinkOf m ++ varint n0 ∧ m.next ≤ m'.next ∧
        ∀ b, ¬ Fp b → b < m.next → m'.blocks b = m.blocks b) := by
  have hstable := TW.stable
  have hW := TW.write
  have cirH_nfp : ∀ b, m.next ≤ b → ¬ Fp b := fun b hb hf => absurd (hFp b hf) (by omega)
  unfold Returns Calls
  rw [evalCall_body cirH_fw rfl rfl]
  cir_run
  cir_loop (fun n wsize buf => wsize ≤ 9 ∧ n < 2 ^ (64 - 7 * wsize) ∧ VInv 10 n0 n wsize buf)
    (fun n wsize buf => (10 : Int) - wsize)
  case cir_init_goal =>
    cir_run
    all_goals first
      | omega
      | exact ⟨[], rfl, rfl, by simp, fun i hi => absurd hi (by omega)⟩
  case cir_step_goal =>
    obtain ⟨hw4, hnb, hv⟩ := cirH_user
    subst cir_nat0 cir_nat1
    have hn32 : n < 2 ^ 64 := Nat.lt_of_lt_of_le hnb (Nat.pow_le_pow_right (by decide) (by omega))
    by_cases hlt : n < 128
    · -- the last byte: `buf[wsize++] = n; break;`
      have cirH_c : bitwise false 64 (fun x1 x2 => x1 &&& x2) (n : Int) 18446744073709551488 = 0 :=
        (bitwise_mask7_eq_zero64 (by omega) (by omega)).2 (by omega)
      have cirH_b : wrap false 8 (wrap true 8 (n : Int)) = (n : Int) := by rw [wrap_u8_s8]; omega
      obtain ⟨hbytes, hlen⟩ := vinv_exit hv hlt (by omega)
      cir_run
      all_goals (try (cir_strip_mdata; omega))
      · -- the sink: the bytes of `buf` appended
        refine (hstable cir_mem0 _ ?_).trans ?_
        · intro b hb; have := hFp b hb; simp (disch := omega) only [killRange_of_lt, upd_apply_ne]
        rw [cirH_post0ba, show (↑wsize + 1 : Int).toNat = wsize + 1 by omega, hbytes]
        congr 1
        apply hstable m _
        intro b hb; have := hFp b hb
        simp (disch := omega) only [upd_apply_ne, killRange_of_lt]
        rw [cirH_frame b (by simp; omega) (by omega), cirH_s0]
        simp (disch := omega) only [upd_apply_ne]
    · -- `buf[wsize++] = (n & 0x7F) | 0x80; n >>= 7;`
      have cirH_c : ¬ bitwise false 64 (fun x1 x2 => x1 &&& x2) (n : Int) 18446744073709551488 = 0 := fun h =>
        hlt (by have := (bitwise_mask7_eq_zero64 (by omega) (by omega)).1 h; omega)
      have cirH_b : wrap false 8 (wrap true 8 (bitwise false 64 (fun x1 x2 => x1 ||| x2)
          (bitwise false 64 (fun x1 x2 => x1 &&& x2) (n : Int) 127) 128)) = ((n % 128 + 128 : Nat) : Int) := by
        rw [bitwise_low7_or64 (by omega) (by omega), wrap_u8_s8]; omega
      obtain ⟨hw3, hn'⟩ := pow_step64 hnb hlt hw4
      have hv' := vinv_step hv hlt (by omega)
      cir_run
      all_goals (try (cir_strip_mdata; omega))
      all_goals (try (simp only [CIR.inRange_eq_true_iff, CIR.intMin_u, CIR.intMax_u32]; omega))
      all_goals (try (rw [show ((n : Int) / 128).toNat = n / 128 by omega]; first | exact hn' | exact hv'))
      all_goals (try cir_close')

end EquivLean.Demo.Thrift.Cpp
