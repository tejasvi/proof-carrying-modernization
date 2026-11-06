import EquivLean.Demo.XLang.Jsmn.CScan

/-!
# jsmn → model, C side: the backward searches of `jsmn_parse`'s `}`/`]` and `,` cases

Three `for` loops of `jsmn_parse`'s main loop, each at its head in a hypothesis (where `cir_hrun_c`
stops in the run of `jsmn_parse`), in the style of `final_scan_elim`: the slots of `jsmn_parse`'s
locals and their SSA ids (`parser` 6, `tokens` 9, `i` 12, `token` 13, `type` 20, the return value 5)
are parameters, the parser block holds `parserV pos toknext toksuper` and the token array
`tokArr ts n`, and the posts are the model's searches.

* `close_first_elim`: `for (i = toknext - 1; i >= 0; i--)` up to the last open token
  (`Model.lastOpen ts ts.length`): `JSMN_ERROR_INVAL` if its type is not `type`, otherwise
  `toksuper = -1`, `end = pos + 1` and `break`; the loop's normal end leaves `i = -1`.
* `close_second_elim`: `for (; i >= 0; i--)` from that `i`: `toksuper` becomes the last open token at
  or below `i` (`lastOpen ts (i + 1)`), or keeps its value.
* `comma_search_elim`: the loop of the `,` case: `toksuper` becomes
  `lastOpenCont ts ts.length` when there is one.

The regions are the Gen's (copied from `fn_jsmn_parse_ops3`).
-/

open CIR EquivLean.Cir
open EquivLean.Demo.XLang.Jsmn (Tok isOpen dflt lastOpen lastOpenCont ARRAY OBJECT)
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace EquivLean.Demo.XLang.Jsmn.C

/-- `}`/`]`, first search: the condition `i >= 0`. -/
def closeCond1 : Region :=
              (.mk [
              .mk [] [
                .load 60 12 (.int true 32),
                .const 61 (.int true 32) (.int 0),
                .cmp 62 .ge 60 61 (.int true 32),
                .condition 62]])

/-- `}`/`]`, first search: the body. -/
def closeBody1 : Region :=
              (.mk [
              .mk [] [
                .scope none (.mk [
                  .mk [] [
                    .load 60 9 (.ptr (.record "jsmntok")),
                    .load 61 12 (.int true 32),
                    .cast 62 .integral 61 (.int true 32) (.int true 64),
                    .ptrStride 63 60 62 (.record "jsmntok") (.int true 64),
                    .store 63 13 (.ptr (.record "jsmntok")),
                    .scope none (.mk [
                      .mk [] [
                        .load 64 13 (.ptr (.record "jsmntok")),
                        .getMember 65 64 1 (.record "jsmntok") (.int true 32),
                        .load 66 65 (.int true 32),
                        .const 67 (.int true 32) (.int (-1)),
                        .cmp 68 .ne 66 67 (.int true 32),
                        .ternary (some 69) 68 (.mk [
                          .mk [] [
                            .load 70 13 (.ptr (.record "jsmntok")),
                            .getMember 71 70 2 (.record "jsmntok") (.int true 32),
                            .load 72 71 (.int true 32),
                            .const 73 (.int true 32) (.int (-1)),
                            .cmp 74 .eq 72 73 (.int true 32),
                            .yield [74]]])
                          (.mk [
                          .mk [] [
                            .const 70 .bool (.bool false),
                            .yield [70]]]),
                        .ifOp 69 (.mk [
                          .mk [] [
                            .scope none (.mk [
                              .mk [] [
                                .load 41 13 (.ptr (.record "jsmntok")),
                                .getMember 42 41 0 (.record "jsmntok") (.int false 32),
                                .load 43 42 (.int false 32),
                                .load 44 20 (.int false 32),
                                .cmp 45 .ne 43 44 (.int false 32),
                                .ifOp 45 (.mk [
                                  .mk [] [
                                    .const 46 (.int true 32) (.int (-2)),
                                    .store 46 5 (.int true 32),
                                    .load 47 5 (.int true 32),
                                    .ret (some 47)]])
                                  (.mk [])]]),
                            .const 70 (.int true 32) (.int (-1)),
                            .load 71 6 (.ptr (.record "jsmn_parser")),
                            .getMember 72 71 2 (.record "jsmn_parser") (.int true 32),
                            .store 70 72 (.int true 32),
                            .load 73 6 (.ptr (.record "jsmn_parser")),
                            .getMember 74 73 0 (.record "jsmn_parser") (.int false 32),
                            .load 75 74 (.int false 32),
                            .const 76 (.int false 32) (.int 1),
                            .binop 36 .add false false 75 76 (.int false 32),
                            .cast 37 .integral 36 (.int false 32) (.int true 32),
                            .load 38 13 (.ptr (.record "jsmntok")),
                            .getMember 39 38 2 (.record "jsmntok") (.int true 32),
                            .store 37 39 (.int true 32),
                            .brk]])
                          (.mk [])]])]]),
                .yield []]])

/-- `}`/`]`, first search: the step `i--`. -/
def closeStep1 : Region :=
              (.mk [
              .mk [] [
                .load 60 12 (.int true 32),
                .unop 61 .dec true 60 (.int true 32),
                .store 61 12 (.int true 32),
                .yield []]])

/-- `}`/`]`, second search: the condition `i >= 0`. -/
def closeCond2 : Region :=
              (.mk [
              .mk [] [
                .load 54 12 (.int true 32),
                .const 55 (.int true 32) (.int 0),
                .cmp 56 .ge 54 55 (.int true 32),
                .condition 56]])

/-- `}`/`]`, second search: the body. -/
def closeBody2 : Region :=
              (.mk [
              .mk [] [
                .scope none (.mk [
                  .mk [] [
                    .load 54 9 (.ptr (.record "jsmntok")),
                    .load 55 12 (.int true 32),
                    .cast 56 .integral 55 (.int true 32) (.int true 64),
                    .ptrStride 57 54 56 (.record "jsmntok") (.int true 64),
                    .store 57 13 (.ptr (.record "jsmntok")),
                    .scope none (.mk [
                      .mk [] [
                        .load 58 13 (.ptr (.record "jsmntok")),
                        .getMember 59 58 1 (.record "jsmntok") (.int true 32),
                        .load 60 59 (.int true 32),
                        .const 61 (.int true 32) (.int (-1)),
                        .cmp 62 .ne 60 61 (.int true 32),
                        .ternary (some 63) 62 (.mk [
                          .mk [] [
                            .load 64 13 (.ptr (.record "jsmntok")),
                            .getMember 65 64 2 (.record "jsmntok") (.int true 32),
                            .load 66 65 (.int true 32),
                            .const 67 (.int true 32) (.int (-1)),
                            .cmp 68 .eq 66 67 (.int true 32),
                            .yield [68]]])
                          (.mk [
                          .mk [] [
                            .const 64 .bool (.bool false),
                            .yield [64]]]),
                        .ifOp 63 (.mk [
                          .mk [] [
                            .load 64 12 (.int true 32),
                            .load 65 6 (.ptr (.record "jsmn_parser")),
                            .getMember 66 65 2 (.record "jsmn_parser") (.int true 32),
                            .store 64 66 (.int true 32),
                            .brk]])
                          (.mk [])]])]]),
                .yield []]])

/-- `}`/`]`, second search: the step `i--`. -/
def closeStep2 : Region :=
              (.mk [
              .mk [] [
                .load 54 12 (.int true 32),
                .unop 55 .dec true 54 (.int true 32),
                .store 55 12 (.int true 32),
                .yield []]])

/-- `,` search: the condition `i >= 0`. -/
def commaCond : Region :=
                      (.mk [
                      .mk [] [
                        .load 59 12 (.int true 32),
                        .const 60 (.int true 32) (.int 0),
                        .cmp 61 .ge 59 60 (.int true 32),
                        .condition 61]])

/-- `,` search: the body. -/
def commaBody : Region :=
                      (.mk [
                      .mk [] [
                        .scope none (.mk [
                          .mk [] [
                            .scope none (.mk [
                              .mk [] [
                                .load 59 9 (.ptr (.record "jsmntok")),
                                .load 60 12 (.int true 32),
                                .cast 61 .integral 60 (.int true 32) (.int true 64),
                                .ptrStride 62 59 61 (.record "jsmntok") (.int true 64),
                                .getMember 63 62 0 (.record "jsmntok") (.int false 32),
                                .load 64 63 (.int false 32),
                                .const 65 (.int false 32) (.int 2),
                                .cmp 66 .eq 64 65 (.int false 32),
                                .ternary (some 67) 66 (.mk [
                                  .mk [] [
                                    .const 68 .bool (.bool true),
                                    .yield [68]]])
                                  (.mk [
                                  .mk [] [
                                    .load 68 9 (.ptr (.record "jsmntok")),
                                    .load 69 12 (.int true 32),
                                    .cast 70 .integral 69 (.int true 32) (.int true 64),
                                    .ptrStride 71 68 70 (.record "jsmntok") (.int true 64),
                                    .getMember 72 71 0 (.record "jsmntok") (.int false 32),
                                    .load 73 72 (.int false 32),
                                    .const 74 (.int false 32) (.int 1),
                                    .cmp 75 .eq 73 74 (.int false 32),
                                    .yield [75]]]),
                                .ifOp 67 (.mk [
                                  .mk [] [
                                    .scope none (.mk [
                                      .mk [] [
                                        .load 68 9 (.ptr (.record "jsmntok")),
                                        .load 69 12 (.int true 32),
                                        .cast 70 .integral 69 (.int true 32) (.int true 64),
                                        .ptrStride 71 68 70 (.record "jsmntok") (.int true 64),
                                        .getMember 72 71 1 (.record "jsmntok") (.int true 32),
                                        .load 73 72 (.int true 32),
                                        .const 74 (.int true 32) (.int (-1)),
                                        .cmp 75 .ne 73 74 (.int true 32),
                                        .ternary (some 76) 75 (.mk [
                                          .mk [] [
                                            .load 36 9 (.ptr (.record "jsmntok")),
                                            .load 37 12 (.int true 32),
                                            .cast 38 .integral 37 (.int true 32) (.int true 64),
                                            .ptrStride 39 36 38 (.record "jsmntok") (.int true 64),
                                            .getMember 41 39 2 (.record "jsmntok") (.int true 32),
                                            .load 42 41 (.int true 32),
                                            .const 43 (.int true 32) (.int (-1)),
                                            .cmp 44 .eq 42 43 (.int true 32),
                                            .yield [44]]])
                                          (.mk [
                                          .mk [] [
                                            .const 36 .bool (.bool false),
                                            .yield [36]]]),
                                        .ifOp 76 (.mk [
                                          .mk [] [
                                            .load 36 12 (.int true 32),
                                            .load 37 6 (.ptr (.record "jsmn_parser")),
                                            .getMember 38 37 2 (.record "jsmn_parser") (.int true 32),
                                            .store 36 38 (.int true 32),
                                            .brk]])
                                          (.mk [])]])]])
                                  (.mk [])]])]]),
                        .yield []]])

/-- `,` search: the step `i--`. -/
def commaStep : Region :=
                      (.mk [
                      .mk [] [
                        .load 59 12 (.int true 32),
                        .unop 60 .dec true 59 (.int true 32),
                        .store 60 12 (.int true 32),
                        .yield []]])

/-- The token fields are values of their C types (`type` an `unsigned`, `start`/`end` `int`s). -/
def TokRange (ts : List Tok) : Prop :=
  ∀ t ∈ ts, 0 ≤ t.type ∧ t.type ≤ 4294967295 ∧ -2147483648 ≤ t.start ∧ t.start ≤ 2147483647 ∧
    -2147483648 ≤ t.stop ∧ t.stop ≤ 2147483647

theorem lastOpenCont_succ (ts : List Tok) (k : Nat) :
    lastOpenCont ts (k + 1) =
      if ((ts.getD k dflt).type = ARRAY ∨ (ts.getD k dflt).type = OBJECT) ∧ isOpen (ts.getD k dflt) = true
      then some k else lastOpenCont ts k := rfl

theorem lastOpen_succ (ts : List Tok) (k : Nat) :
    lastOpen ts (k + 1) = if isOpen (ts.getD k dflt) = true then some k else lastOpen ts k := rfl

/-- Setting token `i` does not change the search below `m ≤ i`. -/
theorem lastOpen_set_le (ts : List Tok) (i : Nat) (x : Tok) : ∀ m, m ≤ i → lastOpen (ts.set i x) m = lastOpen ts m
  | 0, _ => rfl
  | m + 1, h => by
    have hg : (ts.set i x).getD m dflt = ts.getD m dflt := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (show i ≠ m by omega)]
    rw [lastOpen_succ, lastOpen_succ, hg, lastOpen_set_le ts i x m (by omega)]

/-- The two searches of `}`/`]` compose to the model's: after `end = pos + 1` at the last open token
`i`, the second search from `i` finds the last open token below `i` (`lastOpen ts i`). -/
theorem lastOpen_close (ts : List Tok) (i : Nat) (e : Int) (he : e ≠ -1) (hi : i < ts.length) :
    lastOpen (ts.set i { ts.getD i dflt with stop := e }) (i + 1) = lastOpen ts i := by
  have hg : (ts.set i { ts.getD i dflt with stop := e }).getD i dflt = { ts.getD i dflt with stop := e } := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hi, Option.getD_some]
  have ho : isOpen { ts.getD i dflt with stop := e } = false := by
    unfold isOpen; simp [he]
  rw [lastOpen_succ, hg, ho]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact lastOpen_set_le ts i _ i (Nat.le_refl _)

/-- **The `,` search** at the head of its loop in a hypothesis, with `i = toknext - 1`: `toksuper`
becomes the last open object or array (`lastOpenCont ts ts.length`) if there is one; the loop exits
normally; only `i` and the parser change. -/
theorem comma_search_elim {σ : State} {K : Step × State → Prop} (ts : List Tok) (n pos : Nat) (sup : Int)
    (bp bt bPar bTok bI : Nat) (kp kt : BlockKind)
    (hs : (evalFor ctx commaCond commaBody commaStep none σ).holds K)
    (he6 : σ.env 6 = some (.ptr (.loc bPar []))) (he9 : σ.env 9 = some (.ptr (.loc bTok [])))
    (he12 : σ.env 12 = some (.ptr (.loc bI [])))
    (hPar : σ.mem.blocks bPar = some ⟨.stack, true, (Ty.record "jsmn_parser").ptr, .ptr (.loc bp [])⟩)
    (hTok : σ.mem.blocks bTok = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .ptr (.loc bt [.idx 0])⟩)
    (hI : σ.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((ts.length : Int) - 1)⟩)
    (hp : σ.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV pos ts.length sup⟩)
    (ht : σ.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩) (hkp : kp ≠ .readonly)
    (hts : ts.length < 2 ^ 31) (hrng : TokRange ts)
    (h1 : bPar ≠ bI) (h2 : bTok ≠ bI) (h3 : bp ≠ bI) (h4 : bt ≠ bI)
    (hlPar : bPar < σ.mem.next) (hlTok : bTok < σ.mem.next) (hlI : bI < σ.mem.next)
    (hlp : bp < σ.mem.next) (hlt : bt < σ.mem.next) :
    ∃ a, K a ∧ a.1 = .next ∧ a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bp → b < σ.mem.next → a.2.mem.blocks b = σ.mem.blocks b) ∧
      (∃ v, a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, v⟩) ∧
      a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
        parserV pos ts.length (match lastOpenCont ts ts.length with | some i => (i : Int) | none => sup)⟩ := by
  have cirH_e6 := he6
  have cirH_e9 := he9
  have cirH_e12 := he12
  have cirH_par := hPar
  have cirH_tok := hTok
  have cirH_t := ht
  have cirH_kp := hkp
  unfold parserV at hp ⊢
  refine (fun hw => ?main) (holds_for_inv hs
    (fun σ' => σ'.env = σ.env ∧ σ'.names = σ.names ∧ σ.mem.next ≤ σ'.mem.next ∧
      (∀ b, b ≠ bI → b < σ.mem.next → σ'.mem.blocks b = σ.mem.blocks b) ∧
      ∃ m : Nat, m ≤ ts.length ∧ σ'.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((m : Int) - 1)⟩ ∧
        lastOpenCont ts m = lastOpenCont ts ts.length)
    (fun a => a.1 = .next ∧ a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bp → b < σ.mem.next → a.2.mem.blocks b = σ.mem.blocks b) ∧
      (∃ v, a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, v⟩) ∧
      a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", .agg [.int pos, .int ts.length,
        .int (match lastOpenCont ts ts.length with | some i => (i : Int) | none => sup)]⟩)
    ?init ?step)
  case init =>
    exact ⟨rfl, rfl, Nat.le_refl _, fun b _ _ => rfl, ts.length, Nat.le_refl _, hI, rfl⟩
  case step =>
    intro σ' ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, m, hm1, cirH_ii, hlo⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    unfold forIter at hs2
    rcases m with _ | k
    · -- `i = -1`: the loop ends; no open object or array
      have h0 : ((0 : Nat) : Int) - 1 = -1 := by omega
      rw [h0] at cirH_ii
      cir_hrun_c hs2
      all_goals subst hs2
      have hnone : lastOpenCont ts ts.length = none := by rw [← hlo]; rfl
      refine ⟨rfl, rfl, rfl, cirH_nx, fun b hb1 _ hb3 => cirH_frame b hb1 hb3, ⟨_, cirH_ii⟩, ?_⟩
      rw [hnone, cirH_frame bp h3 hlp, hp]
    · -- `i = k`
      have hk : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
      rw [hk] at cirH_ii
      have cirH_k : (0 + (k : Int)).toNat = k := by omega
      have cirH_tk := tokArr_get_lt ts n k (by omega)
      unfold tokV at cirH_tk
      have cirH_w64 : wrap true 64 (k : Int) = k :=
        wrap_of_bounds (by decide) (by simp only [intMin_s64, intMax_s64]; omega)
      have cirH_w32 : wrap true 32 ((k : Int) - 1) = (k : Int) - 1 :=
        wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)
      have hr := hrng _ (getD_mem_of_lt (show k < ts.length by omega))
      have cirH_rty : inRange false 32 (ts.getD k dflt).type = true := by
        rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u32]; omega
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
        | -- an open object or array at `k`: `toksuper = i; break`
          (have hf : lastOpenCont ts ts.length = some k := by
             rw [← hlo, lastOpenCont_succ, ite_eq_left]
             exact ⟨by simp only [ARRAY, OBJECT]; omega, hko.2 ⟨by omega, by omega⟩⟩
           refine ⟨rfl, rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 => ?_,
             ⟨.int k, ?_⟩, ?_⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb3)
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_ii)
           all_goals try (rw [hf]; simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same])
           done)
        | -- none at `k`: `i--`
          (have hn : lastOpenCont ts k = lastOpenCont ts ts.length := by
             rw [← hlo, lastOpenCont_succ, ite_eq_right]
             intro ⟨hc1, hc2⟩
             have := hko.1 hc2
             simp only [ARRAY, OBJECT] at hc1
             omega
           refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 => ?_, k, by omega, ?_, hn⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2)
           all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same])
           done)
  case main =>
    obtain ⟨a, hp', hk⟩ := hw
    exact ⟨a, hk, hp'⟩

/-- **The second search of `}`/`]`** (`for (; i >= 0; i--)`) at the head of its loop in a hypothesis,
with `i = m0 - 1`: `toksuper` becomes the last open token below `m0` (`lastOpen ts m0`) if there is
one; the loop exits normally; only `i`, `token` and the parser change. -/
theorem close_second_elim {σ : State} {K : Step × State → Prop} (ts : List Tok) (n pos : Nat) (sup : Int)
    (m0 : Nat) (bp bt bPar bTok bI bToken : Nat) (kp kt : BlockKind) (vTk : Val)
    (hs : (evalFor ctx closeCond2 closeBody2 closeStep2 none σ).holds K)
    (he6 : σ.env 6 = some (.ptr (.loc bPar []))) (he9 : σ.env 9 = some (.ptr (.loc bTok [])))
    (he12 : σ.env 12 = some (.ptr (.loc bI []))) (he13 : σ.env 13 = some (.ptr (.loc bToken [])))
    (hPar : σ.mem.blocks bPar = some ⟨.stack, true, (Ty.record "jsmn_parser").ptr, .ptr (.loc bp [])⟩)
    (hTok : σ.mem.blocks bTok = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .ptr (.loc bt [.idx 0])⟩)
    (hI : σ.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((m0 : Int) - 1)⟩)
    (hToken : σ.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, vTk⟩)
    (hp : σ.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV pos ts.length sup⟩)
    (ht : σ.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩) (hkp : kp ≠ .readonly)
    (hm0 : m0 ≤ ts.length) (hts : ts.length < 2 ^ 31) (hrng : TokRange ts)
    (h1 : bPar ≠ bI) (h2 : bTok ≠ bI) (h3 : bp ≠ bI) (h4 : bt ≠ bI) (h5 : bToken ≠ bI)
    (h6 : bPar ≠ bToken) (h7 : bTok ≠ bToken) (h8 : bp ≠ bToken) (h9 : bt ≠ bToken)
    (hlPar : bPar < σ.mem.next) (hlTok : bTok < σ.mem.next) (hlI : bI < σ.mem.next)
    (hlToken : bToken < σ.mem.next) (hlp : bp < σ.mem.next) (hlt : bt < σ.mem.next) :
    ∃ a, K a ∧ a.1 = .next ∧ a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bToken → b ≠ bp → b < σ.mem.next → a.2.mem.blocks b = σ.mem.blocks b) ∧
      (∃ v, a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, v⟩) ∧
      (∃ v, a.2.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩) ∧
      a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
        parserV pos ts.length (match lastOpen ts m0 with | some j => (j : Int) | none => sup)⟩ := by
  have cirH_e6 := he6
  have cirH_e9 := he9
  have cirH_e12 := he12
  have cirH_e13 := he13
  have cirH_par := hPar
  have cirH_tok := hTok
  have cirH_t := ht
  have cirH_kp := hkp
  unfold parserV at hp ⊢
  refine (fun hw => ?main) (holds_for_inv hs
    (fun σ' => σ'.env = σ.env ∧ σ'.names = σ.names ∧ σ.mem.next ≤ σ'.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bToken → b < σ.mem.next → σ'.mem.blocks b = σ.mem.blocks b) ∧
      (∃ v, σ'.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩) ∧
      ∃ m : Nat, m ≤ m0 ∧ σ'.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((m : Int) - 1)⟩ ∧
        lastOpen ts m = lastOpen ts m0)
    (fun a => a.1 = .next ∧ a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bToken → b ≠ bp → b < σ.mem.next → a.2.mem.blocks b = σ.mem.blocks b) ∧
      (∃ v, a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, v⟩) ∧
      (∃ v, a.2.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩) ∧
      a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", .agg [.int pos, .int ts.length,
        .int (match lastOpen ts m0 with | some j => (j : Int) | none => sup)]⟩)
    ?init ?step)
  case init =>
    exact ⟨rfl, rfl, Nat.le_refl _, fun b _ _ _ => rfl, ⟨vTk, hToken⟩, m0, Nat.le_refl _, hI, rfl⟩
  case step =>
    intro σ' ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, ⟨vk, cirH_tkn⟩, m, hm1, cirH_ii, hlo⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    unfold forIter at hs2
    rcases m with _ | k
    · -- `i = -1`: the loop ends; no open token below `m0`
      have h0 : ((0 : Nat) : Int) - 1 = -1 := by omega
      rw [h0] at cirH_ii
      cir_hrun_c hs2
      all_goals subst hs2
      have hnone : lastOpen ts m0 = none := by rw [← hlo]; rfl
      refine ⟨rfl, rfl, rfl, cirH_nx, fun b hb1 hb2 _ hb4 => cirH_frame b hb1 hb2 hb4, ⟨_, cirH_ii⟩,
        ⟨vk, cirH_tkn⟩, ?_⟩
      rw [hnone, cirH_frame bp h3 h8 hlp, hp]
    · -- `i = k`
      have hk : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
      rw [hk] at cirH_ii
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
        | -- an open token at `k`: `toksuper = i; break`
          (have hf : lastOpen ts m0 = some k := by
             rw [← hlo, lastOpen_succ, ite_eq_left]
             exact hko.2 ⟨by omega, by omega⟩
           refine ⟨rfl, rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 hb4 => ?_,
             ⟨.int k, ?_⟩, ⟨.ptr (.loc bt [.idx k]), ?_⟩, ?_⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2 hb4)
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_ii)
           all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
                          done)
           all_goals try (rw [hf]; simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same])
           done)
        | -- none at `k`: `i--`
          (have hn : lastOpen ts k = lastOpen ts m0 := by
             rw [← hlo, lastOpen_succ, ite_eq_right]
             intro hc
             have := hko.1 hc
             omega
           refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 => ?_,
             ⟨.ptr (.loc bt [.idx k]), ?_⟩, k, by omega, ?_, hn⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2 hb3)
           all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])
           done)
  case main =>
    obtain ⟨a, hp', hk⟩ := hw
    exact ⟨a, hk, hp'⟩

/-- **The first search of `}`/`]`** (`for (i = toknext - 1; i >= 0; i--)`, with `type` the bracket's
token type) at the head of its loop in a hypothesis: at the last open token `k = lastOpen ts
ts.length`, `JSMN_ERROR_INVAL` if its type is not `type`, else `toksuper = -1`, `tokens[k].end =
pos + 1` and the loop is left with `i = k`; with no open token the loop ends with `i = -1`. -/
theorem close_first_elim {σ : State} {K : Step × State → Prop} (ts : List Tok) (n pos : Nat) (sup ty : Int)
    (bp bt bPar bTok bI bToken bType bRet : Nat) (kp kt : BlockKind) (vTk vR : Val)
    (hs : (evalFor ctx closeCond1 closeBody1 closeStep1 none σ).holds K)
    (he5 : σ.env 5 = some (.ptr (.loc bRet []))) (he6 : σ.env 6 = some (.ptr (.loc bPar [])))
    (he9 : σ.env 9 = some (.ptr (.loc bTok []))) (he12 : σ.env 12 = some (.ptr (.loc bI [])))
    (he13 : σ.env 13 = some (.ptr (.loc bToken []))) (he20 : σ.env 20 = some (.ptr (.loc bType [])))
    (hPar : σ.mem.blocks bPar = some ⟨.stack, true, (Ty.record "jsmn_parser").ptr, .ptr (.loc bp [])⟩)
    (hTok : σ.mem.blocks bTok = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .ptr (.loc bt [.idx 0])⟩)
    (hI : σ.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((ts.length : Int) - 1)⟩)
    (hToken : σ.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, vTk⟩)
    (hType : σ.mem.blocks bType = some ⟨.stack, true, .int false 32, .int ty⟩)
    (hRet : σ.mem.blocks bRet = some ⟨.stack, true, .int true 32, vR⟩)
    (hp : σ.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV pos ts.length sup⟩)
    (ht : σ.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩) (hkp : kp ≠ .readonly)
    (hkt : kt ≠ .readonly) (hts : ts.length < 2 ^ 31) (hpos : pos + 1 < 2 ^ 31) (hty : 0 ≤ ty ∧ ty ≤ 4294967295)
    (hrng : TokRange ts)
    (f : Nat) (hfRet : bRet = f) (hfPar : bPar = f + 1) (hfTok : bTok = f + 4) (hfI : bI = f + 7)
    (hfToken : bToken = f + 8) (hfType : f + 9 < bType) (hfp : bp < f) (hft : bt < f) (hpt : bp ≠ bt)
    (hlPar : bPar < σ.mem.next) (hlTok : bTok < σ.mem.next) (hlType : bType < σ.mem.next)
    (hlRet : bRet < σ.mem.next) (hlp : bp < σ.mem.next) (hlt : bt < σ.mem.next) :
    ∃ a, K a ∧ a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bToken → b ≠ bRet → b ≠ bp → b ≠ bt → b < σ.mem.next →
        a.2.mem.blocks b = σ.mem.blocks b) ∧
      match lastOpen ts ts.length with
      | none => a.1 = .next ∧ a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, .int (-1)⟩ ∧
          a.2.mem.blocks bp = σ.mem.blocks bp ∧ a.2.mem.blocks bt = σ.mem.blocks bt ∧
          a.2.mem.blocks bRet = σ.mem.blocks bRet ∧
          (∃ v, a.2.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩)
      | some k =>
        if (ts.getD k dflt).type = ty then
          a.1 = .next ∧ a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, .int k⟩ ∧
          a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV pos ts.length (-1)⟩ ∧
          a.2.mem.blocks bt =
            some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr (ts.set k { ts.getD k dflt with stop := (pos : Int) + 1 }) n)⟩ ∧
          a.2.mem.blocks bRet = σ.mem.blocks bRet ∧
          (∃ v, a.2.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩)
        else a.1 = .exit (.ret (some (.int (-2)))) ∧ a.2.mem.blocks bp = σ.mem.blocks bp ∧
          a.2.mem.blocks bt = σ.mem.blocks bt := by
  let tyT : Ty := .array (.record "jsmntok") n
  have cirH_e5 := he5
  have cirH_e6 := he6
  have cirH_e9 := he9
  have cirH_e12 := he12
  have cirH_e13 := he13
  have cirH_e20 := he20
  have cirH_par := hPar
  have cirH_tok := hTok
  have cirH_type := hType
  have cirH_ret := hRet
  have cirH_t := ht
  have cirH_kp := hkp
  have cirH_kt := hkt
  have cirH_rty0 : inRange false 32 ty = true := by
    rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u32]; omega
  have cirH_wp1 : wrap false 32 ((pos : Int) + 1) = (pos : Int) + 1 :=
    wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u32]; omega)
  have cirH_wp2 : wrap true 32 ((pos : Int) + 1) = (pos : Int) + 1 :=
    wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)
  unfold parserV at hp ⊢
  refine (fun hw => ?main) (holds_for_inv hs
    (fun σ' => σ'.env = σ.env ∧ σ'.names = σ.names ∧ σ.mem.next ≤ σ'.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bToken → b < σ.mem.next → σ'.mem.blocks b = σ.mem.blocks b) ∧
      (∃ v, σ'.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩) ∧
      ∃ m : Nat, m ≤ ts.length ∧ σ'.mem.blocks bI = some ⟨.stack, true, .int true 32, .int ((m : Int) - 1)⟩ ∧
        lastOpen ts m = lastOpen ts ts.length)
    (fun a => a.2.env = σ.env ∧ a.2.names = σ.names ∧ σ.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bI → b ≠ bToken → b ≠ bRet → b ≠ bp → b ≠ bt → b < σ.mem.next →
        a.2.mem.blocks b = σ.mem.blocks b) ∧
      match lastOpen ts ts.length with
      | none => a.1 = .next ∧ a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, .int (-1)⟩ ∧
          a.2.mem.blocks bp = σ.mem.blocks bp ∧ a.2.mem.blocks bt = σ.mem.blocks bt ∧
          a.2.mem.blocks bRet = σ.mem.blocks bRet ∧
          (∃ v, a.2.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩)
      | some k =>
        if (ts.getD k dflt).type = ty then
          a.1 = .next ∧ a.2.mem.blocks bI = some ⟨.stack, true, .int true 32, .int k⟩ ∧
          a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", .agg [.int pos, .int ts.length, .int (-1)]⟩ ∧
          a.2.mem.blocks bt =
            some ⟨kt, true, tyT, .arr (tokArr (ts.set k { ts.getD k dflt with stop := (pos : Int) + 1 }) n)⟩ ∧
          a.2.mem.blocks bRet = σ.mem.blocks bRet ∧
          (∃ v, a.2.mem.blocks bToken = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩)
        else a.1 = .exit (.ret (some (.int (-2)))) ∧ a.2.mem.blocks bp = σ.mem.blocks bp ∧
          a.2.mem.blocks bt = σ.mem.blocks bt)
    ?init ?step)
  case init =>
    exact ⟨rfl, rfl, Nat.le_refl _, fun b _ _ _ => rfl, ⟨vTk, hToken⟩, ts.length, Nat.le_refl _, hI, rfl⟩
  case step =>
    intro σ' ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, ⟨vk, cirH_tkn⟩, m, hm1, cirH_ii, hlo⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    unfold forIter at hs2
    rcases m with _ | k
    · -- `i = -1`: the loop ends; no open token
      have h0 : ((0 : Nat) : Int) - 1 = -1 := by omega
      rw [h0] at cirH_ii
      cir_hrun_c hs2
      all_goals subst hs2
      have hnone : lastOpen ts ts.length = none := by rw [← hlo]; rfl
      refine ⟨rfl, rfl, cirH_nx, fun b hb1 hb2 _ _ _ hb6 => cirH_frame b hb1 hb2 hb6, ?_⟩
      rw [hnone]
      exact ⟨rfl, cirH_ii, cirH_frame bp (by omega) (by omega) hlp, cirH_frame bt (by omega) (by omega) hlt,
        cirH_frame bRet (by omega) (by omega) hlRet, ⟨vk, cirH_tkn⟩⟩
    · -- `i = k`
      have hk : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
      rw [hk] at cirH_ii
      have cirH_k : (0 + (k : Int)).toNat = k := by omega
      have cirH_tk := tokArr_get_lt ts n k (by omega)
      unfold tokV at cirH_tk
      have cirH_w64 : wrap true 64 (k : Int) = k :=
        wrap_of_bounds (by decide) (by simp only [intMin_s64, intMax_s64]; omega)
      have cirH_w32 : wrap true 32 ((k : Int) - 1) = (k : Int) - 1 :=
        wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)
      have hr := hrng _ (getD_mem_of_lt (show k < ts.length by omega))
      have cirH_rty : inRange false 32 (ts.getD k dflt).type = true := by
        rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u32]; omega
      have cirH_rs : inRange true 32 (ts.getD k dflt).start = true := by
        rw [inRange_eq_true_iff]; simp only [intMin_s32, intMax_s32]; omega
      have cirH_re : inRange true 32 (ts.getD k dflt).stop = true := by
        rw [inRange_eq_true_iff]; simp only [intMin_s32, intMax_s32]; omega
      have hko := isOpen_iff (ts.getD k dflt)
      have htset : (tokArr ts n).set k (.agg [.int (ts.getD k dflt).type, .int (ts.getD k dflt).start,
          .int ((pos : Int) + 1), .int (ts.getD k dflt).size]) =
          tokArr (ts.set k { ts.getD k dflt with stop := (pos : Int) + 1 }) n :=
        tokArr_set ts n k { ts.getD k dflt with stop := (pos : Int) + 1 } (by omega)
      cir_hrun_c hs2
      all_goals subst hs2
      all_goals first
        | -- the loop test failing at `i = k ≥ 0`: no such run
          (exfalso; omega)
        | -- token `k` not open: `i--`
          (have hn : lastOpen ts k = lastOpen ts ts.length := by
             rw [← hlo, lastOpen_succ, ite_eq_right]
             intro hc
             have := hko.1 hc
             omega
           refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 => ?_,
             ⟨.ptr (.loc bt [.idx k]), ?_⟩, k, by omega, ?_, hn⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2 hb3)
           all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])
           done)
        | -- the last open token, of another type: `return JSMN_ERROR_INVAL`
          (have hf : lastOpen ts ts.length = some k := by
             rw [← hlo, lastOpen_succ, ite_eq_left]
             exact hko.2 ⟨by omega, by omega⟩
           have hne : ¬ (ts.getD k dflt).type = ty := by omega
           refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 hb4 hb5 hb6 => ?_, ?_⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2 hb6)
           rw [hf]
           show (if (ts.getD k dflt).type = ty then _ else _)
           rw [ite_eq_right hne]
           refine ⟨rfl, ?_, ?_⟩
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
             exact cirH_frame bp (by omega) (by omega) hlp
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
             exact cirH_frame bt (by omega) (by omega) hlt)
        | -- the last open token, of the bracket's type: `toksuper = -1; token->end = pos + 1; break`
          (have hf : lastOpen ts ts.length = some k := by
             rw [← hlo, lastOpen_succ, ite_eq_left]
             exact hko.2 ⟨by omega, by omega⟩
           have heq : (ts.getD k dflt).type = ty := by omega
           refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b hb1 hb2 hb3 hb4 hb5 hb6 => ?_, ?_⟩
           all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                          exact cirH_frame b hb1 hb2 hb6)
           rw [hf]
           show (if (ts.getD k dflt).type = ty then _ else _)
           rw [ite_eq_left heq]
           refine ⟨rfl, ?_, ?_, ?_, ?_, ⟨.ptr (.loc bt [.idx k]), ?_⟩⟩
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
             exact cirH_ii
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same]
             rw [htset]
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
             exact cirH_frame bRet (by omega) (by omega) hlRet
           · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])
  case main =>
    obtain ⟨a, hp', hk⟩ := hw
    exact ⟨a, hk, hp'⟩

end EquivLean.Demo.XLang.Jsmn.C
