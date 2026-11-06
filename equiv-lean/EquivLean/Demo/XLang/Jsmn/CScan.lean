import EquivLean.Demo.XLang.Jsmn.CTok

/-!
# jsmn → model, C side: the final `JSMN_ERROR_PART` scan of `jsmn_parse`

After its main loop `jsmn_parse` runs (with `tokens != NULL`)

    for (i = parser->toknext - 1; i >= 0; i--)
      if (tokens[i].start != -1 && tokens[i].end == -1) return JSMN_ERROR_PART;

`final_scan_elim` takes this loop at its head in a hypothesis, as `cir_hrun_c` stops there in
`jsmn_parse`'s run, with `i = toknext - 1` and the token array `tokArr ts n` (`toknext =
ts.length`): it returns `JSMN_ERROR_PART` when the model's test `ts.any isOpen` holds, and otherwise
leaves the loop normally; nothing changes but `i` and the return slot.  The slots of `tokens`, `i`
and the return value (SSA values 9, 12 and 5 of `jsmn_parse`) are parameters.  `scanCond`,
`scanBody`, `scanStep` are the loop's regions as the Gen has them (`scan_loop_in_ops11`).
-/

open CIR EquivLean.Cir
open EquivLean.Demo.XLang.Jsmn (Tok isOpen dflt)
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx fn_jsmn_parse_ops11)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace EquivLean.Demo.XLang.Jsmn.C

/-- The condition region of the final scan: `i >= 0`. -/
def scanCond : Region := .mk [
  .mk [] [
    .load 29 12 (.int true 32),
    .const 30 (.int true 32) (.int 0),
    .cmp 31 .ge 29 30 (.int true 32),
    .condition 31]]

/-- The body region of the final scan: `if (tokens[i].start != -1 && tokens[i].end == -1) return -3;`. -/
def scanBody : Region := .mk [
  .mk [] [
    .scope none (.mk [
      .mk [] [
        .scope none (.mk [
          .mk [] [
            .load 29 9 (.ptr (.record "jsmntok")),
            .load 30 12 (.int true 32),
            .cast 31 .integral 30 (.int true 32) (.int true 64),
            .ptrStride 32 29 31 (.record "jsmntok") (.int true 64),
            .getMember 33 32 1 (.record "jsmntok") (.int true 32),
            .load 34 33 (.int true 32),
            .const 35 (.int true 32) (.int (-1)),
            .cmp 40 .ne 34 35 (.int true 32),
            .ternary (some 53) 40 (.mk [
              .mk [] [
                .load 54 9 (.ptr (.record "jsmntok")),
                .load 55 12 (.int true 32),
                .cast 56 .integral 55 (.int true 32) (.int true 64),
                .ptrStride 57 54 56 (.record "jsmntok") (.int true 64),
                .getMember 58 57 2 (.record "jsmntok") (.int true 32),
                .load 59 58 (.int true 32),
                .const 60 (.int true 32) (.int (-1)),
                .cmp 61 .eq 59 60 (.int true 32),
                .yield [61]]])
              (.mk [
              .mk [] [
                .const 54 .bool (.bool false),
                .yield [54]]]),
            .ifOp 53 (.mk [
              .mk [] [
                .const 54 (.int true 32) (.int (-3)),
                .store 54 5 (.int true 32),
                .load 55 5 (.int true 32),
                .ret (some 55)]])
              (.mk [])]])]]),
    .yield []]]

/-- The step region of the final scan: `i--`. -/
def scanStep : Region := .mk [
  .mk [] [
    .load 29 12 (.int true 32),
    .unop 30 .dec true 29 (.int true 32),
    .store 30 12 (.int true 32),
    .yield []]]

/-- The loop is the one in `jsmn_parse`'s last ops (after `if (tokens != NULL)` and `i = toknext - 1`). -/
theorem scan_loop_in_ops11 : fn_jsmn_parse_ops11 = [
    .scope none (.mk [
      .mk [] [
        .load 19 9 (.ptr (.record "jsmntok")),
        .const 20 (.ptr .void) .null,
        .cast 21 .bitcast 20 (.ptr .void) (.ptr (.record "jsmntok")),
        .cmp 22 .ne 19 21 (.ptr (.record "jsmntok")),
        .ifOp 22 (.mk [
          .mk [] [
            .scope none (.mk [
              .mk [] [
                .load 23 6 (.ptr (.record "jsmn_parser")),
                .getMember 24 23 1 (.record "jsmn_parser") (.int false 32),
                .load 25 24 (.int false 32),
                .const 26 (.int false 32) (.int 1),
                .binop 27 .sub false false 25 26 (.int false 32),
                .cast 28 .integral 27 (.int false 32) (.int true 32),
                .store 28 12 (.int true 32),
                .forOp ⟨444, 5⟩ scanCond scanBody scanStep none]])]])
          (.mk [])]]),
    .load 77 14 (.int true 32),
    .store 77 5 (.int true 32),
    .load 78 5 (.int true 32),
    .ret (some 78)] := rfl

/-- `i = toknext - 1` as the C computes it (`unsigned` subtraction, then `int`), for `toknext < 2^31`. -/
theorem scan_start_wrap (k : Nat) (hk : k < 2 ^ 31) :
    wrap true 32 (wrap false 32 ((k : Int) - 1)) = (k : Int) - 1 := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    decide
  · rw [wrap_of_bounds (s := false) (by decide) (by simp only [intMin_u, intMax_u32]; omega)]
    exact wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)

theorem any_isOpen_of_get {ts : List Tok} {k : Nat} (hk : k < ts.length) (h : isOpen (ts.getD k dflt) = true) :
    ts.any isOpen = true := by
  rw [List.any_eq_true]
  refine ⟨ts[k], List.getElem_mem hk, ?_⟩
  simpa [List.getD_eq_getElem?_getD, hk] using h

theorem any_isOpen_false {ts : List Tok} (h : ∀ j : Nat, j < ts.length → isOpen (ts.getD j dflt) = false) :
    ts.any isOpen = false := by
  rw [List.any_eq_false]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  have := h j hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  simp [this]

theorem isOpen_iff (t : Tok) : isOpen t = true ↔ t.start ≠ -1 ∧ t.stop = -1 := by
  unfold isOpen; simp

theorem getD_mem_of_lt {ts : List Tok} {k : Nat} (hk : k < ts.length) : ts.getD k dflt ∈ ts := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk

/-- **The final scan** at the head of its loop in a hypothesis, with `i = ts.length - 1` and the
token array `tokArr ts n`: `JSMN_ERROR_PART` returned when `ts.any isOpen`, otherwise a normal exit
from the loop; only `i` and the return slot change. -/
theorem final_scan_elim {σ : State} {K : Step × State → Prop} (ts : List Tok) (n : Nat)
    (bt bTok bI bRet : Nat) (kt : BlockKind) (vR : Val)
    (hs : (evalFor ctx scanCond scanBody scanStep none σ).holds K)
    (he9 : σ.env 9 = some (.ptr (.loc bTok []))) (he12 : σ.env 12 = some (.ptr (.loc bI [])))
    (he5 : σ.env 5 = some (.ptr (.loc bRet [])))
    (hTok : σ.mem.blocks bTok = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .ptr (.loc bt [.idx 0])⟩)
    (hI : σ.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((ts.length : Int) - 1)⟩)
    (hRet : σ.mem.blocks bRet = some ⟨.stack, true, .int true 32, vR⟩)
    (ht : σ.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩)
    (hts : ts.length < 2 ^ 31)
    (hrng : ∀ t ∈ ts, -2147483648 ≤ t.start ∧ t.start ≤ 2147483647 ∧ -2147483648 ≤ t.stop ∧ t.stop ≤ 2147483647)
    (h1 : bTok ≠ bI) (h4 : bI ≠ bRet) (h5 : bI ≠ bt) (h6 : bRet ≠ bt)
    (hlTok : bTok < σ.mem.next) (hlI : bI < σ.mem.next) (hlRet : bRet < σ.mem.next) (hlt : bt < σ.mem.next) :
    ∃ a, K a ∧ a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bRet → b < σ.mem.next → a.2.mem.blocks b = σ.mem.blocks b) ∧
      ((ts.any isOpen = true ∧ a.1 = .exit (.ret (some (.int (-3))))) ∨
        (ts.any isOpen = false ∧ a.1 = .next ∧ a.2.mem.blocks bRet = σ.mem.blocks bRet)) := by
  have cirH_e9 := he9
  have cirH_e12 := he12
  have cirH_e5 := he5
  have cirH_tok := hTok
  have cirH_ret := hRet
  have cirH_t := ht
  refine (fun hw => ?main) (holds_for_inv hs
    (fun σ' => σ'.env = σ.env ∧ σ'.names = σ.names ∧ σ.mem.next ≤ σ'.mem.next ∧
      (∀ b, b ≠ bI → b < σ.mem.next → σ'.mem.blocks b = σ.mem.blocks b) ∧
      ∃ i : Int, -1 ≤ i ∧ i < ts.length ∧ σ'.mem.blocks bI = some ⟨.stack, true, .int true 32, .int i⟩ ∧
        ∀ j : Nat, i < j → j < ts.length → isOpen (ts.getD j dflt) = false)
    (fun a => a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bRet → b < σ.mem.next → a.2.mem.blocks b = σ.mem.blocks b) ∧
      ((ts.any isOpen = true ∧ a.1 = .exit (.ret (some (.int (-3))))) ∨
        (ts.any isOpen = false ∧ a.1 = .next ∧ a.2.mem.blocks bRet = σ.mem.blocks bRet)))
    ?init ?step)
  case init =>
    exact ⟨rfl, rfl, Nat.le_refl _, fun b _ _ => rfl, (ts.length : Int) - 1, by omega, by omega, hI,
      fun j hj1 hj2 => absurd hj2 (by omega)⟩
  case step =>
    intro σ' ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, i, hi1, hi2, cirH_ii, hio⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    unfold forIter at hs2
    by_cases hi : 0 ≤ i
    · -- the body at `k = i`
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      have cirH_k : (0 + (k : Int)).toNat = k := by omega
      have cirH_tk := tokArr_get_lt ts n k (by omega)
      unfold tokV at cirH_tk
      have cirH_w64 : wrap true 64 (k : Int) = k :=
        wrap_of_bounds (by decide) (by simp only [intMin_s64, intMax_s64]; omega)
      have cirH_w32 : wrap true 32 ((k : Int) - 1) = (k : Int) - 1 :=
        wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)
      have hr := hrng _ (getD_mem_of_lt (show k < ts.length by omega))
      have cirH_rs : inRange true 32 (ts.getD k dflt).start = true := by
        rw [inRange_eq_true_iff]; simp only [intMin_s32, intMax_s32]; omega
      have cirH_re : inRange true 32 (ts.getD k dflt).stop = true := by
        rw [inRange_eq_true_iff]; simp only [intMin_s32, intMax_s32]; omega
      have hko := isOpen_iff (ts.getD k dflt)
      cir_hrun_c hs2
      all_goals subst hs2
      all_goals first
        | -- the loop test failing at `i = k ≥ 0`: no such run
          (exfalso; omega)
        | -- token `k` is open: `return JSMN_ERROR_PART`
          (refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 => ?_,
             Or.inl ⟨any_isOpen_of_get (k := k) (by omega) (hko.2 ⟨by omega, by omega⟩), rfl⟩⟩
           (try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
           exact cirH_frame b hb1 hb3)
        | -- not open: `i--`
          (refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 => ?_, (k : Int) - 1,
             by omega, by omega, ?_, fun j hj1 hj2 => ?_⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2)
           all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same])
           all_goals try (by_cases hjk : j = k
                          · subst hjk
                            cases hc : isOpen (ts.getD j dflt) with
                            | false => rfl
                            | true => exact absurd (hko.1 hc) (by omega)
                          · exact hio j (by omega) hj2)
           done)
    · -- `i = -1`: the loop ends
      have hi' : i = -1 := by omega
      subst hi'
      cir_hrun_c hs2
      all_goals subst hs2
      exact ⟨rfl, rfl, cirH_nx, fun b hb1 _ hb3 => cirH_frame b hb1 hb3,
        Or.inr ⟨any_isOpen_false (fun j hj => hio j (by omega) hj), rfl, cirH_frame bRet (Ne.symm h4) hlRet⟩⟩
  case main =>
    obtain ⟨a, hp, hk⟩ := hw
    exact ⟨a, hk, hp⟩

end EquivLean.Demo.XLang.Jsmn.C
