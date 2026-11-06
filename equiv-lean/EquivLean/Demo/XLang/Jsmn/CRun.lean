import EquivLean.Demo.XLang.Jsmn.CPMain

/-!
# jsmn → model, C side: the run from program start (`jsmn_parse_pspec`)

`jsmn_parse_pspec`: for the bytes `js` of a text shorter than `2^28` bytes and every `n`, a run of `jsmn_run`
(`jsmn_init`, then one `jsmn_parse` with `n` tokens) that returns has the model's return value `(parse js n).1`, and
the token array starts with the model's tokens `(parse js n).2` (`toksOf`). This is the statement `Equiv.lean`'s
`cspec_of_pspec` takes.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx module)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop isOpen dflt)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

theorem cMem_next (js : List Nat) (n : Nat) : (cMem js n).next = 3 := by
  simp [cMem, Mem.alloc, Module.initMem_next, module]

theorem cMem_blocks (js : List Nat) (n : Nat) (b : Nat) :
    (cMem js n).blocks b =
      upd (upd (upd module.initMem.blocks 0
        (some ⟨.stack, true, .record "jsmn_parser", .agg [.undef, .undef, .undef]⟩)) 1
        (some ⟨.readonly, true, .array (.int true 8) js.length, .arr (js.map fun b : Nat => Val.int (b : Int))⟩)) 2
        (some ⟨.stack, true, .array (.record "jsmntok") n, .arr (List.replicate n tok0)⟩) b := by
  simp [cMem, Mem.alloc, Module.initMem_next, module]

theorem tokArr_nil (n : Nat) : tokArr [] n = List.replicate n tok0 := by simp [tokArr]

theorem toksOf_nil (m : Mem) (kd : BlockKind) (al : Bool) (ty : Ty) (vs : List Val)
    (h : m.blocks 2 = some ⟨kd, al, ty, .arr vs⟩) : toksOf m 0 = some [] := by
  unfold toksOf; rw [h]; simp

set_option maxHeartbeats 2000000000 in
/-- **jsmn from program start, per the model**: for the bytes `js` of a text shorter than `2^28` bytes, every
outcome of `jsmn_run` (`jsmn_init`, one `jsmn_parse` with `n` tokens) returns the model's value and leaves the model's
tokens at the start of the token array. -/
theorem jsmn_parse_pspec (js : List Nat) (n : Nat) (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28)
    (a : Exit × Mem) (ha : cRun js n = .ok a) :
    a.1 = .ret (some (.int (Jsmn.parse js n).1)) ∧
      toksOf a.2 (Jsmn.parse js n).2.length = some (Jsmn.parse js n).2 := by
  have hs : (evalCall ctx "jsmn_run" [.ptr (.loc 0 []), .ptr (.loc 1 [.idx 0]), .int js.length,
      .ptr (.loc 2 [.idx 0]), .int n] (cMem js n)).holds (· = a) := by unfold cRun at ha; rw [ha]; rfl
  have cirH_cn : (cMem js n).next = 3 := cMem_next js n
  have cirH_cb := cMem_blocks js n
  rw [parse_eq_pres]
  by_cases hn : n < 2 ^ 32
  · -- `jsmn_init`, then the call of `jsmn_parse` on the parser `St.init`
    cir_hstep hs
    cir_hrun_c hs
    cir_hstep hs
    cir_hrun_c hs
    obtain ⟨⟨r1, r2⟩, -, ⟨hr1, ⟨ts, hts, hbt2, hor⟩, hfr⟩, hK⟩ := holds_pspec_elim hs
      (parse_pspec js n St.init 0 1 2 .stack .readonly .stack _ hjs hlen hn (Jsmn.wf_init js n)
        (by simp (disch := omega) only [upd_apply_ne, upd_apply_same]; try rfl) (fun h => nomatch h)
        (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, cirH_cb])
        (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, cirH_cb, St.init, tokArr_nil])
        (fun h => nomatch h) (by decide) (by decide) (by decide) (by simp) (by simp) (by simp))
    dsimp only at hr1 hbt2 hfr hK
    subst hr1
    have cirH_r3 : r2.blocks 3 = some ⟨.stack, true, .int true 32, .undef⟩ := by
      rw [hfr 3 (by simp) (by decide) (by decide)]
      simp (disch := omega) only [upd_apply_ne, upd_apply_same]
    have hv : -3 ≤ (pres js n St.init).1 ∧ (pres js n St.init).1 ≤ 2147483647 := by
      rcases Jsmn.parse_cases js n with ⟨h1, -⟩ | ⟨h1, -, h3, -⟩
      · rw [parse_eq_pres] at h1
        rcases h1 with h1 | h1 | h1 <;> rw [h1] <;> decide
      · rw [parse_eq_pres] at h1 h3
        omega
    have cirH_v : inRange true 32 (pres js n St.init).1 = true := by
      rw [inRange_eq_true_iff]; simp only [intMin_s32, intMax_s32]; omega
    -- `return` of `jsmn_parse`'s value through `__retval`
    cir_hrun_c hK
    all_goals (
      subst hK
      refine ⟨rfl, ?_⟩
      rcases hor with h0 | h0
      · rw [h0]
        exact toksOf_nil _ .stack true (.array (.record "jsmntok") n) (tokArr ts n)
          (by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, hbt2])
      · rw [h0]
        exact toksOf_tokArr _ .stack true (.array (.record "jsmntok") n) ts n
          (by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, hbt2]) hts)
  · -- `num_tokens` does not fit its `unsigned int` parameter: no outcome
    cir_hstep hs
    cir_hrun_c hs
    exfalso; omega

end EquivLean.Demo.XLang.Jsmn.C
