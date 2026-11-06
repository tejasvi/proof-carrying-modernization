import EquivLean.Bridge.Cir.Obs
import EquivLean.Bridge.Cir.Loops
import EquivLean.Bridge.Cir.PtrLemmas

/-!
# `equiv_cir`: relational symbolic execution of two CIR functions

A goal `Sim R t s` between two CIR computations is turned (`sim_res_res`) into

    ∀ os, s.holds (· = os) → t.holds (fun ot => R ot os)

* the **source** runs first, in the hypothesis `hs : s.holds (· = os)`: `cir_hrun hs` is a
  hypothesis version of cirlean's `cir_step` (same simp sets, simprocs, discharger and
  lookups; the continuation is generalized away during each focused `simp`, as `cir_head`
  does in the goal).  Branches of the source become case splits `cirH_brN`, which
  cirlean's `cir_vcg` then uses as rewrite rules to decide the target's branches.  A path on
  which the source has undefined behaviour closes (`hs` becomes `False`).  At the end
  `hs : (e, m') = os` is substituted.
* the **target** then runs in the goal with cirlean's `cir_vcg` itself;
* the leaves `R ot os` are closed by `cir_obs_close` (`ObsEq`: equal exits, equal blocks
  below the caller's `next`, by the lookup simprocs and `omega`).

Loops: `cir_hrun` stops at a loop of the source (`hs : wp (L₂ s₂) K₂`), `cir_vcg` at the
target's; `cir_loop_pair` applies `wp_loop_rel` with a user-supplied coupling invariant.

User-facing tactics:
* `equiv_cir`: `Equiv R t s` or `Sim R t s` between two loop-free CIR computations;
* `equiv_cir using inv` / `cir_sim_loop inv`: the same with one loop on each side, paired in
  lockstep by the coupling invariant `inv` (binders: `x` the target's variable, `x'` the
  source's);
* building blocks: `cir_hrun h`, `cir_sim`, `cir_loop_pair h inv`, `cir_pair_step`,
  `cir_obs_close`.
-/

namespace EquivLean.Cir

open CIR
attribute [cir_exec] List.isEmpty_nil List.isEmpty_cons

/-! ### Elimination forms of cirlean's structural rules (for hypotheses) -/

section
variable {α β : Type}

theorem holds_bind_elim {x : Res α} {f : α → Res β} {Q : β → Prop}
    (h : (x >>= f).holds Q) : x.holds fun a => (f a).holds Q := Res.holds_bind.mp h
theorem holds_ok_elim {a : α} {Q : α → Prop} (h : (Res.ok a).holds Q) : Q a := h
theorem holds_pure_elim {a : α} {Q : α → Prop} (h : (pure a : Res α).holds Q) : Q a := h
theorem holds_ub_elim {m : String} {Q : α → Prop} {P : Prop} (h : (Res.ub m : Res α).holds Q) :
    P := h.elim
theorem holds_div_elim {Q : α → Prop} {P : Prop} (h : (Res.div : Res α).holds Q) : P := h.elim
/-- The decidability instance is an implicit argument (never re-synthesized). -/
theorem holds_ite_pos_elim {c : Prop} {inst : Decidable c} {x y : Res α} {Q : α → Prop}
    (h : (@ite _ c inst x y).holds Q) (hc : c) : x.holds Q := by
  cases inst with
  | isTrue _ => exact h
  | isFalse hn => exact absurd hc hn
theorem holds_ite_neg_elim {c : Prop} {inst : Decidable c} {x y : Res α} {Q : α → Prop}
    (h : (@ite _ c inst x y).holds Q) (hc : ¬c) : y.holds Q := by
  cases inst with
  | isTrue hp => exact absurd hp hc
  | isFalse _ => exact h

end

theorem holds_evalOps_cons_elim {ctx : Ctx} {op : Op} {ops : List Op} {σ : State}
    {Q : Step × State → Prop} (h : (evalOps ctx (op :: ops) σ).holds Q) :
    (evalOp ctx op σ >>= fun x => match x with
      | (s, σ) => match s with
        | .next => evalOps ctx ops σ
        | s => pure (s, σ)).holds Q := by
  rw [evalOps.eq_2] at h; exact h

theorem holds_evalOps_nil_elim {ctx : Ctx} {σ : State} {Q : Step × State → Prop}
    (h : (evalOps ctx [] σ).holds Q) : Q (.exit (.yield []), σ) := by
  rw [evalOps.eq_1] at h; exact h

theorem holds_evalRegion_cons_elim {ctx : Ctx} {b : Block} {bs : List Block} {args : List Val}
    {σ : State} {Q : Exit × State → Prop} (h : (evalRegion ctx (.mk (b :: bs)) args σ).holds Q) :
    (evalBlock ctx (b :: bs) 0 args σ >>= fun x => match x with
      | (e, σ') => pure (e, { mem := e.leaveMem σ'.mem σ.mem.next, env := σ.env, names := σ.names })).holds Q := by
  rw [evalRegion.eq_2] at h; exact h

theorem leaveMem_halt (code : Int) (m : Mem) (lo : Nat) : (Exit.halt code).leaveMem m lo = m := rfl
theorem leaveMem_yield (vs : List Val) (m : Mem) (lo : Nat) : (Exit.yield vs).leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_cond (b : Bool) (m : Mem) (lo : Nat) : (Exit.cond b).leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_brk (m : Mem) (lo : Nat) : Exit.brk.leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_cont (m : Mem) (lo : Nat) : Exit.cont.leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_ret (v : Option Val) (m : Mem) (lo : Nat) : (Exit.ret v).leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_exn (e : Exn) (m : Mem) (lo : Nat) : (Exit.exn e).leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_goto (l : String) (m : Mem) (lo : Nat) : (Exit.goto l).leaveMem m lo = m.endScope lo := rfl
theorem leaveMem_longjmp (t : Nat) (v : Int) (m : Mem) (lo : Nat) : (Exit.longjmp t v).leaveMem m lo = m.endScope lo := rfl

theorem holds_evalRegion_nil_elim {ctx : Ctx} {args : List Val} {σ : State}
    {Q : Exit × State → Prop} (h : (evalRegion ctx (.mk []) args σ).holds Q) : Q (.yield [], σ) := by
  rw [evalRegion.eq_1] at h; exact h

theorem holds_evalBlock_zero_elim {ctx : Ctx} {params : List VId} {ops : List Op}
    {bs : List Block} {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (h : (evalBlock ctx (.mk params ops :: bs) 0 args σ).holds Q) :
    (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit (.goto l) =>
        match labelBlock? l (.mk params ops :: bs) with
        | some j => evalBlock ctx (.mk params ops :: bs) j [] σ
        | none => pure (.goto l, σ)
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx (.mk params ops :: bs) j vs σ
      | .next => .ub "fell off the end of a block").holds Q := by
  rw [evalBlock_zero] at h; exact h

def opMayJump : Op → Bool
  | .br .. | .brcond .. | .forOp .. | .whileOp .. | .doWhileOp .. | .switch .. | .setjmp .. | .setjmpRun .. => true
  | _ => false

def blockNoLabel : List Block → Bool
  | [.mk _ (.label _ :: _)] => false
  | [_] => true
  | _ => false

theorem labelBlock?_of_noLabel {params : List VId} {ops : List Op}
    (h : blockNoLabel [.mk params ops] = true) (l : String) :
    labelBlock? l [.mk params ops] = none := by
  cases ops with
  | nil => rfl
  | cons op rest => cases op <;> first | rfl | cases h

theorem step_next_ne_jump : ∀ j vs, Step.next ≠ Step.jump j vs := fun _ _ h => by cases h
theorem step_exit_ne_jump (e : Exit) : ∀ j vs, Step.exit e ≠ Step.jump j vs := fun _ _ h => by cases h

theorem finishRegion_not_jump (e : Exit) (σ : State) {P : Step × State → Prop}
    (h : (finishRegion e σ).holds P) :
    (finishRegion e σ).holds (fun x => (∀ j vs, x.1 ≠ .jump j vs) ∧ P x) := by
  cases e with
  | yield vs =>
    cases vs with
    | nil => exact ⟨step_next_ne_jump, h⟩
    | cons _ _ => exact h
  | cond _ => exact h
  | _ => exact ⟨step_exit_ne_jump _, h⟩

theorem evalOp_not_jump {ctx : Ctx} {op : Op} {σ : State} {P : Step × State → Prop}
    (hmj : opMayJump op = false) (h : (evalOp ctx op σ).holds P) :
    (evalOp ctx op σ).holds (fun x => (∀ j vs, x.1 ≠ .jump j vs) ∧ P x) := by
  cases op <;> try (cases hmj; done)
  case ret r =>
    cases r <;> simp only [evalOp, Res.holds_bind, Res.holds_pure] at h ⊢
    · exact ⟨step_exit_ne_jump _, h⟩
    · exact Res.holds_mono h (fun _ h1 => ⟨step_exit_ne_jump _, h1⟩)
  case throw obj _ ti =>
    cases obj <;> cases ti <;> simp only [evalOp, Res.holds_bind, Res.holds_pure, Res.holds_ub] at h ⊢
    all_goals first | exact holds_ub_elim h | exact Res.holds_mono h (fun _ h1 => ⟨step_exit_ne_jump _, h1⟩)
  all_goals try simp only [evalOp] at h ⊢
  all_goals
    repeat (first
      | exact finishRegion_not_jump _ _ h
      | exact ⟨step_next_ne_jump, h⟩
      | exact ⟨step_exit_ne_jump _, h⟩
      | exact holds_ub_elim h
      | (rw [Res.holds_bind] at h ⊢; refine Res.holds_mono h (fun a h => ?_))
      | (revert h; split <;> intro h))

theorem evalOps_not_jump {ctx : Ctx} {ops : List Op} {σ : State} {P : Step × State → Prop}
    (hmj : (ops.any opMayJump) = false) (h : (evalOps ctx ops σ).holds P) :
    (evalOps ctx ops σ).holds (fun x => (∀ j vs, x.1 ≠ .jump j vs) ∧ P x) := by
  induction ops generalizing σ with
  | nil =>
    rw [evalOps.eq_1] at h ⊢
    exact ⟨step_exit_ne_jump _, h⟩
  | cons op ops ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hmj
    rw [evalOps.eq_2, Res.holds_bind] at h ⊢
    refine Res.holds_mono (evalOp_not_jump hmj.1 h) (fun ⟨s, σ'⟩ ⟨hne, hs⟩ => ?_)
    cases s with
    | next => exact ih hmj.2 hs
    | exit e => exact ⟨step_exit_ne_jump _, hs⟩
    | jump j vs => exact absurd rfl (hne j vs)

theorem holds_evalCall_body_elim {ctx : Ctx} {sym : String} {fd : FuncDecl} {body : Region}
    {args : List Val} {m : Mem} {Q : Exit × Mem → Prop}
    (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none) (hb : fd.body = some body)
    (hs : fd.special ≠ .dtor := by decide)
    (h : (evalCall ctx sym args m).holds Q) :
    (do
      let (e, σ) ← evalRegion ctx body args ⟨m, fun _ => none, []⟩
      match e with
      | .ret v => pure (Exit.ret v, σ.mem)
      | .exn x => if fd.nothrow then Res.ub "exception escaped a noexcept function" else pure (Exit.exn x, σ.mem)
      | .halt n => pure (Exit.halt n, σ.mem)
      | .longjmp t v => pure (Exit.longjmp t v, σ.mem)
      | _ => Res.ub "function body exited without cir.return" : Res (Exit × Mem)).holds Q := by
  rw [evalCall_body hf hm hb hs] at h; exact h

theorem holds_evalCall_dtor_elim {ctx : Ctx} {sym : String} {fd : FuncDecl} {body : Region}
    {args : List Val} {m : Mem} {Q : Exit × Mem → Prop}
    (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none) (hb : fd.body = some body)
    (hs : fd.special = .dtor := by rfl)
    (h : (evalCall ctx sym args m).holds Q) :
    (do
      let (e, σ) ← evalRegion ctx body args ⟨m, fun _ => none, []⟩
      match e with
      | .ret v => pure (Exit.ret v, endLifetime ctx args σ.mem)
      | .exn x => if fd.nothrow then Res.ub "exception escaped a noexcept function" else pure (Exit.exn x, σ.mem)
      | .halt n => pure (Exit.halt n, σ.mem)
      | .longjmp t v => pure (Exit.longjmp t v, σ.mem)
      | _ => Res.ub "function body exited without cir.return" : Res (Exit × Mem)).holds Q := by
  rw [evalCall_dtor hf hm hb hs] at h; exact h

theorem holds_evalCall_model_elim {ctx : Ctx} {sym : String} {fd : FuncDecl} {mdl : Model}
    {args : List Val} {m : Mem} {Q : Exit × Mem → Prop}
    (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = some mdl)
    (h : (evalCall ctx sym args m).holds Q) : (Std.runModel ctx mdl args m).holds Q := by
  rw [evalCall_model hf hm] at h; exact h

theorem holds_evalCall_none_elim {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {Q : Exit × Mem → Prop} {P : Prop}
    (hf : ctx.mod.findFunc? sym = none) (h : (evalCall ctx sym args m).holds Q) : P := by
  rw [evalCall.eq_1, hf] at h; exact False.elim h

theorem holds_evalCall_ext_elim {ctx : Ctx} {sym : String} {fd : FuncDecl}
    {args : List Val} {m : Mem} {Q : Exit × Mem → Prop} {P : Prop}
    (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none) (hb : fd.body = none)
    (h : (evalCall ctx sym args m).holds Q) : P := by
  rw [evalCall.eq_1, hf] at h; simp only [hm, hb] at h; exact False.elim h

theorem holds_evalBlock_structured_elim {ctx : Ctx} {params : List VId} {ops : List Op}
    {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (hl : blockNoLabel [.mk params ops] = true)
    (hmj : (ops.any opMayJump) = false)
    (h : (evalBlock ctx [.mk params ops] 0 args σ).holds Q) :
    (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit e => pure (e, σ)
      | _ => .ub "fell off the end of a block").holds Q := by
  have h0 := holds_evalBlock_zero_elim h
  simp only [Res.holds_bind] at h0 ⊢
  refine Res.holds_mono h0 (fun σ1 h1 => ?_)
  refine Res.holds_mono (evalOps_not_jump hmj h1) (fun ⟨s, σ2⟩ ⟨hne, h2⟩ => ?_)
  cases s with
  | exit e =>
    cases e <;> try exact h2
    dsimp only at h2
    rw [labelBlock?_of_noLabel hl] at h2
    exact h2
  | jump j vs => exact absurd rfl (hne j vs)
  | next => exact h2

theorem holds_evalBlock_nolabel_elim {ctx : Ctx} {params : List VId} {ops : List Op}
    {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (hl : blockNoLabel [.mk params ops] = true)
    (h : (evalBlock ctx [.mk params ops] 0 args σ).holds Q) :
    (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx [.mk params ops] j vs σ
      | .next => .ub "fell off the end of a block").holds Q := by
  have h0 := holds_evalBlock_zero_elim h
  simp only [Res.holds_bind] at h0 ⊢
  refine Res.holds_mono h0 (fun σ1 h1 => Res.holds_mono h1 (fun ⟨s, σ2⟩ h2 => ?_))
  cases s with
  | exit e =>
    cases e <;> try exact h2
    dsimp only at h2
    rw [labelBlock?_of_noLabel hl] at h2
    exact h2
  | jump j vs => exact h2
  | next => exact h2

theorem holds_evalOp_scope_elim {ctx : Ctx} {res : Option VId} {body : Region} {σ : State} {K : Step × State → Prop}
    (h : (evalOp ctx (.scope res body) σ).holds K) :
    (evalRegion ctx body [] σ).holds (fun p =>
      (match p.1 with
      | .yield vs => do pure (Step.next, ← p.2.setResults res vs)
      | .cond _ => .ub "cir.condition outside a loop condition"
      | e => pure (Step.exit e, p.2)).holds K) := by
  rw [evalOp.eq_def] at h; exact holds_bind_elim h

theorem holds_evalOp_whileOp_elim {ctx : Ctx} {loc : Loc} {c b : Region} {cl : Option (CleanupKind × Region)}
    {σ : State} {K : Step × State → Prop}
    (h : (evalOp ctx (.whileOp loc c b cl) σ).holds K) :
    (evalWhile ctx c b cl σ).holds K := by
  rw [evalOp.eq_def] at h; exact h

/-! ### Closing `ObsEq` leaves -/

theorem obsEq_intro {m₀ : Mem} {e₁ e₂ : Exit} {m₁ m₂ : Mem} (he : e₁ = e₂)
    (hb : ∀ b, b < m₀.next → m₁.blocks b = m₂.blocks b) : ObsEq m₀ (e₁, m₁) (e₂, m₂) :=
  ⟨he, hb⟩

theorem killRange_lt_apply {lo hi b : Nat} {bs : Nat → Option MemBlock} (h : b < lo) :
    killRange lo hi bs b = bs b := CIR.killRange_lt lo hi bs b h

theorem upd_ne_apply {f : Nat → Option MemBlock} {a b : Nat} {v : Option MemBlock} (h : b ≠ a) :
    upd f a v b = f b := CIR.upd_ne f a v b h

end EquivLean.Cir

namespace EquivLean.Cir.Tactic

open Lean Meta Elab Tactic
open CIR.Tactic (execNames fallbackNames simpArgs cirHyps lookupEq?)

/-- The local declaration of the hypothesis named `h`. -/
def hypDecl (h : Name) : TacticM LocalDecl := do
  let g ← getMainGoal
  g.withContext do
    match (← getLCtx).findFromUserName? h with
    | some d => return d
    | none => throwError "cir_hstep: no hypothesis {h}"

/-- The head computation and the continuation of `h : Res.holds X K`. -/
def hypHolds? (h : Name) : TacticM (Option (Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let some d := (← getLCtx).findFromUserName? h | return none
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``CIR.Res.holds 3 then
      return some ((← instantiateMVars (t.getArg! 1)).consumeMData, t.getArg! 2)
    return none

/-- Number of local hypotheses whose name starts with `pre`. -/
def countPrefix (pre : String) : TacticM Nat := do
  let g ← getMainGoal
  return (← g.getDecl).lctx.foldl (init := 0) fun acc d =>
    if d.userName.toString.startsWith pre then acc + 1 else acc

/-- `simp` lemma list: the given names and the `cirH_…` facts (other than `h`). -/
def hypSimpArgs (h : Name) (names : Array Name) :
    TacticM (Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") := do
  let fv? := (← hypDecl h).fvarId
  let hyps ← CIR.Tactic.cirHypsExcept (some fv?)
  CIR.Tactic.simpArgsLazy names hyps

/-- One focused `simp` of the head of `h : Res.holds X K`: `K` is generalized, so that only
the head computation and the state are simplified (the hypothesis version of `cir_head`). -/
def hypHeadSimp (h : Name) (names : Array Name) : TacticM Unit := do
  let some (x, k) ← hypHolds? h | throwError "cir_hstep: {h} is not `Res.holds _ _`"
  let hI := mkIdent h
  -- element pointer arithmetic (`cir_iter`) only when the head mentions it, as `cir_vcg` does
  let usesIter := (x.find? fun e => e.isConst && CIR.Tactic.iterConsts.contains e.constName!).isSome
  let names := if usesIter then names.push `cir_iter else names
  let args ← hypSimpArgs h names
  if k.isFVar then
    evalTactic (← `(tactic| simp (disch := cir_disch) only [$args,*] at $hI:ident))
    return
  let g ← getMainGoal
  let kS ← g.withContext <| Lean.Elab.Term.exprToSyntax k
  let kv := mkIdent (← mkFreshUserName `K)
  let hK := mkIdent (← mkFreshUserName `hK)
  evalTactic (← `(tactic| generalize $hK:ident : ($kS) = $kv:ident at $hI:ident))
  evalTactic (← `(tactic| simp (disch := cir_disch) only [$args,*] at $hI:ident))
  -- the goal may have been closed (the head is undefined behaviour)
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| subst $hK:ident))

/-- Case split on the proposition `p` (named `cirH_brN`, as cirlean names its splits). -/
def splitOn (p : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let pS ← g.withContext <| Lean.Elab.Term.exprToSyntax p
  let n ← countPrefix "cirH_br"
  let hb := mkIdent (Name.mkSimple s!"cirH_br{n}")
  evalTactic (← `(tactic| by_cases $hb:ident : $pS))
  -- an arithmetic copy of a range check, for `omega` (the original stays a rewrite rule)
  let ha := mkIdent (Name.mkSimple s!"cirA_br{n}")
  evalTactic (← `(tactic| all_goals (try (have $ha:ident := $hb:ident; simp only [CIR.inRange_eq_true_iff,
    CIR.inRange_eq_false_iff, Bool.not_eq_true, Bool.not_eq_false, CIR.intMin_s8, CIR.intMax_s8,
    CIR.intMin_s16, CIR.intMax_s16, CIR.intMin_s32, CIR.intMax_s32, CIR.intMin_s64, CIR.intMax_s64,
    CIR.intMin_u, CIR.intMax_u8, CIR.intMax_u16, CIR.intMax_u32, CIR.intMax_u64] at $ha:ident))))

/-- Inline the call at the head of `h` (body or library model), using cirlean's native
lookup of the function. -/
def hypCallInline (h : Name) (x : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let hI := mkIdent h
  let ctx := x.getArg! 0
  let sym := x.getArg! 1
  let look ← mkAppM ``CIR.Module.findFunc? #[← mkAppM ``CIR.Ctx.mod #[ctx], sym]
  let some (fdOpt, hfind) ← lookupEq? look
    | throwError "cir_hstep: cannot look up {sym} in the module"
  let_expr Option.some _ fd := fdOpt
    | throwError "cir_hstep: function {sym} is not in the module"
  let fdS ← Lean.Elab.Term.exprToSyntax fd
  let hfindS ← Lean.Elab.Term.exprToSyntax hfind
  let mdlOpt ← whnfD (← mkAppM ``CIR.FuncDecl.model #[fd])
  match_expr mdlOpt with
  | Option.some _ mdl =>
    let mdlS ← Lean.Elab.Term.exprToSyntax mdl
    evalTactic (← `(tactic| replace $hI:ident :=
      EquivLean.Cir.holds_evalCall_model_elim (fd := $fdS) (mdl := $mdlS) $hfindS rfl $hI))
  | _ =>
    let bodyOpt ← whnfD (← mkAppM ``CIR.FuncDecl.body #[fd])
    let_expr Option.some _ body := bodyOpt
      | throwError "cir_hstep: {sym} has neither a body nor a library model"
    let bodyS ← Lean.Elab.Term.exprToSyntax body
    let spec ← whnfD (← mkAppM ``CIR.FuncDecl.special #[fd])
    if spec.isConstOf ``CIR.SpecialMember.dtor then
      evalTactic (← `(tactic| replace $hI:ident :=
        EquivLean.Cir.holds_evalCall_dtor_elim (fd := $fdS) (body := $bodyS) $hfindS rfl rfl rfl $hI))
    else
      evalTactic (← `(tactic| replace $hI:ident :=
        EquivLean.Cir.holds_evalCall_body_elim (fd := $fdS) (body := $bodyS) $hfindS rfl rfl (by decide) $hI))

/-- Unfold `Std.runModel ctx mdl args m` at the head of `h` (definitional). -/
def hypModelUnfold (h : Name) (x : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let d ← hypDecl h
  let t ← whnfR (← instantiateMVars d.type)
  let some x1 ← unfoldDefinition? x | throwError "cir_hstep: cannot unfold runModel"
  let x2 ← whnfCore x1
  if x2.isAppOf ``CIR.Std.runModel then throwError "cir_hstep: no matching model case"
  let t' := mkAppN t.getAppFn #[t.getArg! 0, x2, t.getArg! 2]
  let g' ← g.replaceLocalDeclDefEq d.fvarId t'
  replaceMainGoal [g']

/-- Try a tactic; restore the state on failure. -/
def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try tac; return true
  catch _ => s.restore; return false

/-! ### Pointer arguments

A pointer argument `x` comes with a bound `cirP_ptrN : ∀ b p, x = .loc b p → b < M.next`
(`cir_ptr_intro`, `EquivLean.Bridge.Cir.PtrArgs`).  It is split when the source first inspects it
(`splitPtrVar`), so that the cases multiply only what follows; afterwards the source's case
splits on caller memory are named (`cirH_rd…`) for the target's `cir_vcg`. -/

/-- Pointer mode: a bounded pointer argument in context, or one already split. -/
def ptrMode : TacticM Bool := do
  let g ← getMainGoal
  return (← g.getDecl).lctx.any fun d =>
    let n := d.userName.toString
    n.startsWith "cirH_blk" || n.startsWith "cirP_ptr" || n.startsWith "cirH_caller"

/-- `(x, M)` of a bound `∀ b p, x = Ptr.loc b p → b < M.next` on a pointer variable `x`. -/
def ptrBoundOf? (ty : Expr) : MetaM (Option (Expr × Expr)) :=
  forallTelescopeReducing ty fun xs body => do
    if xs.size != 3 then return none
    let some (_, lhs, rhs) := (← inferType xs[2]!).eq? | return none
    unless lhs.isFVar && rhs.isAppOfArity ``CIR.Ptr.loc 2 do return none
    let some (_, _, _, ub) := body.app4? ``LT.lt | return none
    unless ub.isAppOfArity ``CIR.Mem.next 1 do return none
    let mem := ub.appArg!
    if mem.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then return none
    return some (lhs, mem)

/-- The bounded pointer variables: `(x, its bound cirP_ptrN, M)`. -/
def ptrVars : TacticM (Array (Expr × LocalDecl × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || !d.userName.toString.startsWith "cirP_ptr" then continue
      if let some (x, mem) ← ptrBoundOf? (← instantiateMVars d.type) then
        out := out.push (x, d, mem)
    return out

/-- Functions that are stuck on a pointer variable (and comparisons: `p != null` decides the
kind of `p`, which the other program may inspect differently). -/
def ptrInspectors : Array Name := #[``CIR.Ctx.typedLoad, ``CIR.Ctx.typedStore, ``CIR.Ctx.punnedMember, ``CIR.loadPtr, ``CIR.loadTy, ``CIR.storeTy, ``CIR.Mem.read?,
  ``CIR.Mem.write?, ``CIR.ptrValid, ``CIR.Mem.ptrEq?, ``CIR.Mem.stride?, ``CIR.Mem.elemPos?,
  ``CIR.Mem.diff?, ``CIR.Mem.ptrLt?, ``CIR.Mem.isPastEnd, ``CIR.Ctx.ptrEq?, ``CIR.Ctx.stride?,
  ``CIR.Ctx.diff?, ``CIR.Ctx.evalCmpB, ``CIR.castVal, ``CIR.evalCast, ``bne, ``BEq.beq, ``Eq, ``Ne]

/-- The condition of an `ite`, or the discriminants of a `match`. -/
def splitDiscrs (env : Environment) (e : Expr) : Array Expr :=
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then #[e.getArg! 1]
  else match Lean.Meta.isMatcherAppCore? env e with
    | some info =>
      e.getAppArgs.extract info.getFirstDiscrPos (info.getFirstDiscrPos + info.numDiscrs)
    | none => #[]

/-- A bounded pointer variable that `e` inspects (argument of a pointer function, or a `match`
discriminant). -/
def inspectedPtr? (env : Environment) (vars : Array (Expr × LocalDecl × Expr)) (e : Expr) :
    Option (Expr × LocalDecl × Expr) :=
  vars.find? fun (x, _, _) => (e.find? fun t =>
    (ptrInspectors.any t.isAppOf && t.getAppArgs.contains x) || (splitDiscrs env t).contains x).isSome

/-- Split the bounded pointer variable `x`: `null`, `loc b p`, `fn s`, `vtable s i k`, `addr a`.
For `loc`:
`cirH_ltN : b < M.next`, `cirH_callerN : IsCaller b`; `b` is one of the caller blocks split
before (substituted) or a new one (`¬ b = b₀` for the others, and `cirH_blkN : M.blocks b = none`
or `= some ⟨kind, alive, ty, val⟩`). -/
def splitPtrVar (x : Expr) (hb : LocalDecl) (mem : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let (xn, olds, memS, n) ← g.withContext do
    let lctx ← getLCtx
    let some xd := lctx.find? x.fvarId! | throwError "splitPtrVar: lost the pointer variable"
    let olds ← lctx.foldlM (init := #[]) fun acc d => do
      if d.userName.toString.startsWith "cirH_caller" then
        let ty ← instantiateMVars d.type
        if ty.isAppOfArity ``EquivLean.Cir.IsCaller 1 then return acc.push ty.appArg!
      return acc
    let n := lctx.foldl (init := 0) fun acc d =>
      if d.userName.toString.startsWith "cirH_lt" then acc + 1 else acc
    return (xd.userName, olds, ← Lean.Elab.Term.exprToSyntax mem, n)
  let g ← if xn.hasMacroScopes then g.rename x.fvarId! (Name.mkSimple s!"cir_parg{n}") else pure g
  replaceMainGoal [g]
  let xI := mkIdent (if xn.hasMacroScopes then Name.mkSimple s!"cir_parg{n}" else xn)
  let hI := mkIdent hb.userName
  let nm (s : String) : Ident := mkIdent (Name.mkSimple s!"{s}{n}")
  evalTactic (← `(tactic| rcases $xI:ident with _ | ⟨$(nm "cir_pb"):ident, $(nm "cir_pp"):ident⟩ |
    $(nm "cir_ps"):ident | ⟨$(nm "cir_pv"):ident, $(nm "cir_pi"):ident, $(nm "cir_pk"):ident⟩ |
    $(nm "cir_pa"):ident | ⟨$(nm "cir_plf"):ident, $(nm "cir_pll"):ident⟩))
  let gs ← getGoals
  let some gLoc := gs[1]? | throwError "splitPtrVar: unexpected cases"
  setGoals [gLoc]
  let bI := nm "cir_pb"
  evalTactic (← `(tactic| have $(nm "cirH_lt"):ident := $hI:ident $bI:ident $(nm "cir_pp"):ident rfl))
  evalTactic (← `(tactic| have $(nm "cirH_caller"):ident : EquivLean.Cir.IsCaller $bI:ident := trivial))
  -- the same block as an earlier caller pointer, or a different one
  let mut fresh : List MVarId := [← getMainGoal]
  let mut done : List MVarId := []
  for (b₀, j) in olds.toList.zipIdx do
    let mut next : List MVarId := []
    for g in fresh do
      setGoals [g]
      let b₀S ← g.withContext <| Lean.Elab.Term.exprToSyntax b₀
      let he := mkIdent (Name.mkSimple s!"cirH_beq{n}_{j}")
      evalTactic (← `(tactic| by_cases $he:ident : $bI:ident = $b₀S))
      let [gp, gn] ← getGoals | throwError "splitPtrVar: by_cases"
      setGoals [gp]
      evalTactic (← `(tactic| subst $he:ident))
      done := done ++ (← getGoals)
      next := next ++ [gn]
    fresh := next
  let mut blk : List MVarId := []
  for g in fresh do
    setGoals [g]
    evalTactic (← `(tactic| rcases $(nm "cirH_blk"):ident : ($memS).blocks $bI:ident with
      _ | ⟨$(nm "cir_kind"):ident, _ | _, $(nm "cir_ty"):ident, $(nm "cir_val"):ident⟩))
    blk := blk ++ (← getGoals)
  setGoals ([gs[0]!] ++ done ++ blk ++ gs.drop 2)
  evalTactic (← `(tactic| all_goals (try clear $hI:ident)))

/-- Pointer mode: name the equations `split` leaves about the source's reads of caller memory
(`heq✝ : val.get? p = some v✝`, …) `cirH_rdN`; cirlean's `cir_vcg` then rewrites the target's
identical reads with them. -/
def nameSplitEqs : TacticM Unit := do
  let mut out := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let g' ← g.withContext do
      let lctx ← getLCtx
      let mut g := g
      let mut n := lctx.foldl (init := 0) fun acc d =>
        if d.userName.toString.startsWith "cirH_rd" then acc + 1 else acc
      for d in lctx do
        if d.isImplementationDetail || !d.userName.hasMacroScopes then continue
        if (← instantiateMVars d.type).isAppOfArity ``Eq 3 then
          g ← g.rename d.fvarId (Name.mkSimple s!"cirH_rd{n}")
          n := n + 1
      return g
    out := out.push g'
  setGoals out.toList

/-- `e` mentions a lookup in a symbolic state (decided by the eager fallback, not split). -/
def mentionsLookup (e : Expr) : Bool :=
  (e.find? fun x => x.isAppOf ``CIR.upd || x.isAppOf ``CIR.killRange).isSome

/-- A split candidate: an `ite` or `match` on data with free variables (no loose bound
variables, no state lookups). -/
def isSplitCand (env : Environment) (e : Expr) : Bool :=
  let ds := splitDiscrs env e
  !ds.isEmpty && ds.all (fun d => !d.hasLooseBVars && !mentionsLookup d) && ds.any (·.hasFVar)

/-- The innermost split candidate of `e`: the first one (pre-order) whose discriminants contain
no candidate. -/
partial def innerSplit? (env : Environment) (e : Expr) : Option Expr := do
  let c ← e.find? (isSplitCand env)
  ((splitDiscrs env c).findSome? (innerSplit? env)).getD c

/-- After a split of a `match` with a constructor term among its discriminants (`match Ty.int true
32, v with …`): the equation `split` leaves between two constructor applications
(`Ty.int true 32 = Ty.int s w`) is solved by `cases` (`s`, `w` instantiated; a contradictory one
closes the goal), so that it is neither a rewrite rule for the target nor a hidden fact. -/
partial def casesCtorEqs (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail || !d.userName.hasMacroScopes then continue
    let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
    unless (← isConstructorApp l) && (← isConstructorApp r) do continue
    let s ← saveState
    try
      let gs ← g.cases d.fvarId
      return ← gs.toList.foldlM (init := []) fun acc sg => return acc ++ (← casesCtorEqs sg.mvarId)
    catch _ => s.restore
  return [g]

/-- Pointer mode: split the innermost `ite`/`match` on data of the head of `h` (e.g.
`match val.get? p with …`), so that the source's facts are about the smallest terms, which the
target's computation shares. -/
def splitInnerAt (h : Name) : TacticM Unit := do
  let some (x, _) ← hypHolds? h | throwError "cir_hstep: {h} is not `Res.holds _ _`"
  let some c := innerSplit? (← getEnv) x | throwError "cir_hstep: nothing to split"
  if c.isAppOfArity ``ite 5 || c.isAppOfArity ``dite 5 then
    splitOn (c.getArg! 1)
    return
  let g ← getMainGoal
  let d ← hypDecl h
  let gs ← g.withContext do
    let (fvs, g') ← g.revert #[d.fvarId]
    let gs ← Lean.Meta.Split.splitMatch g' c
    gs.mapM fun g => return (← g.introNP fvs.size).2
  setGoals (← gs.foldlM (init := []) fun acc g => return acc ++ (← casesCtorEqs g))
  nameSplitEqs

/-- The variables `v : Val` that the condition `c` inspects: `fitsTy ty v` (a typed load or
store), or a discriminant of a `match` (its unfolded form). -/
partial def valDiscrs (env : Environment) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``CIR.fitsTy 2 && (e.getArg! 1).isFVar then acc.push (e.getArg! 1)
    else acc ++ (splitDiscrs env e).filter (·.isFVar)
  match e with
  | .app f a => valDiscrs env a (valDiscrs env f acc)
  | .mdata _ b => valDiscrs env b acc
  | _ => acc

/-- Pointer mode: a value read from caller memory (`v : Val`) that the condition `c` of an `if`
inspects.  It is split on its constructor before the condition, so that the source's branch facts
are about its contents (`inRange true 32 x` for `v = .int x`, the typed load's check of cirlean's
`loadTy`, whose failure now reads an integer through the signed/unsigned counterpart), which the
target's identical reads decide. -/
def valToSplit? (c : Expr) : TacticM (Option Expr) := do
  let g ← getMainGoal
  g.withContext do
    for v in valDiscrs (← getEnv) c do
      if (← whnfR (← inferType v)).isConstOf ``CIR.Val then return some v
    return none

/-- `cases` on the value `v` (renamed `cir_rvN`). -/
def casesVal (v : Expr) : TacticM Unit := do
  let n ← countPrefix "cir_rv"
  let nm := Name.mkSimple s!"cir_rv{n}"
  replaceMainGoal [← (← getMainGoal).rename v.fvarId! nm]
  evalTactic (← `(tactic| cases $(mkIdent nm):ident))

/-- Pointer mode: split a bounded pointer variable that the head of `h` inspects, or that its
next step would inspect (the step is then redone on the split pointer: the split, with its block
facts, comes from `splitPtrVar`, not from a `match` on the pointer). -/
def splitPtrAt (h : Name) : TacticM Bool := do
  let vars ← ptrVars
  if vars.isEmpty then return false
  let some (x, _) ← hypHolds? h | return false
  let env ← getEnv
  if let some (v, hb, mem) := inspectedPtr? env vars x then
    splitPtrVar v hb mem
    return true
  let s ← saveState
  unless ← tryTac (hypHeadSimp h execNames) do return false
  if (← getGoals).isEmpty then s.restore; return false
  let some (x', _) ← hypHolds? h | s.restore; return false
  if let some (v, hb, mem) := inspectedPtr? env vars x' then
    s.restore
    splitPtrVar v hb mem
    return true
  s.restore
  return false

/-- One symbolic execution step of the hypothesis `h : Res.holds X K`. -/
def hypStepImpl (h : Name) : TacticM Unit := do
  let some (x, _) ← hypHolds? h | throwError "cir_hstep: {h} is not `Res.holds _ _`"
  let hI := mkIdent h
  match x.getAppFn.constName? with
  | some ``CIR.Res.ok =>
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_ok_elim $hI))
    if (← hypHolds? h).isNone then
      evalTactic (← `(tactic| try dsimp only [EquivLean.Cir.leaveMem_halt, EquivLean.Cir.leaveMem_yield,
        EquivLean.Cir.leaveMem_cond, EquivLean.Cir.leaveMem_brk, EquivLean.Cir.leaveMem_cont,
        EquivLean.Cir.leaveMem_ret, EquivLean.Cir.leaveMem_exn, EquivLean.Cir.leaveMem_goto,
        EquivLean.Cir.leaveMem_longjmp] at $hI:ident))
  | some ``Pure.pure =>
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_pure_elim $hI))
    if (← hypHolds? h).isNone then
      evalTactic (← `(tactic| try dsimp only [EquivLean.Cir.leaveMem_halt, EquivLean.Cir.leaveMem_yield,
        EquivLean.Cir.leaveMem_cond, EquivLean.Cir.leaveMem_brk, EquivLean.Cir.leaveMem_cont,
        EquivLean.Cir.leaveMem_ret, EquivLean.Cir.leaveMem_exn, EquivLean.Cir.leaveMem_goto,
        EquivLean.Cir.leaveMem_longjmp] at $hI:ident))
  | some ``CIR.Res.ub => evalTactic (← `(tactic| exact EquivLean.Cir.holds_ub_elim $hI))
  | some ``CIR.Res.div => evalTactic (← `(tactic| exact EquivLean.Cir.holds_div_elim $hI))
  | some ``Bind.bind => evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_bind_elim $hI))
  | some ``ite =>
    if ← tryTac (hypHeadSimp h execNames) then return
    if ← ptrMode then
      if let some v ← valToSplit? (x.getArg! 1) then
        casesVal v
        return
    splitOn (x.getArg! 1)
    evalTactic (← `(tactic| case' pos => replace $hI:ident := EquivLean.Cir.holds_ite_pos_elim $hI ‹_›))
    evalTactic (← `(tactic| case' neg => replace $hI:ident := EquivLean.Cir.holds_ite_neg_elim $hI ‹_›))
  | some ``CIR.evalOps =>
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalOps_cons_elim $hI))) then
      return
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalOps_nil_elim $hI))) then
      evalTactic (← `(tactic| try dsimp only [CIR.Exit.leaveMem] at $hI:ident))
      return
    hypHeadSimp h execNames
  | some ``CIR.evalRegion =>
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalRegion_cons_elim $hI))) then
      return
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalRegion_nil_elim $hI))
    evalTactic (← `(tactic| try dsimp only [CIR.Exit.leaveMem] at $hI:ident))
  | some ``CIR.evalBlock =>
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalBlock_zero_elim $hI))) then
      return
    hypHeadSimp h #[``CIR.evalBlock.eq_1, ``List.getElem?_cons_succ, ``List.getElem?_cons_zero]
  | some ``CIR.evalFor | some ``CIR.evalWhile | some ``CIR.evalDo =>
    throwError "cir_hstep: reached a loop of the source (pair it with cir_loop_pair)"
  | some ``CIR.evalCall => hypCallInline h x
  | some ``CIR.Std.runModel => hypModelUnfold h x
  | _ =>
    let ptr ← ptrMode
    if ptr then
      if ← splitPtrAt h then return
    if ← tryTac (hypHeadSimp h execNames) then return
    if ptr then
      if ← tryTac (splitInnerAt h) then return
    if ← tryTac (hypHeadSimp h fallbackNames) then return
    -- a data-dependent branch stuck at the head: case on its condition
    let dec? := (x.find? fun e => e.isAppOfArity ``Decidable.decide 2 && !e.hasLooseBVars &&
      (e.getArg! 0).hasFVar).orElse fun _ =>
      x.find? fun e => e.isAppOfArity ``ite 5 && !e.hasLooseBVars && (e.getArg! 1).hasFVar
    if let some d := dec? then
      let p := if d.isAppOf ``ite then d.getArg! 1 else d.getArg! 0
      if ← tryTac (splitOn p) then return
    evalTactic (← `(tactic| split at $hI:ident <;> (try simp only [decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false, reduceCtorEq, false_implies,
      implies_true, and_true, true_and] at *)))
    if ptr then nameSplitEqs

/-- `h : ∃ a, P a ∧ Q a` (from `Res.ofOption`): destructure it, keeping `h : Q a`. -/
def hypExists (h : Name) : TacticM Unit := do
  let d ← hypDecl h
  let t ← whnfR (← instantiateMVars d.type)
  unless t.isAppOfArity ``Exists 2 do throwError "cir_hstep: {h} is not an existential"
  let n ← countPrefix "cirH_ex"
  let a := mkIdent (Name.mkSimple s!"cir_x{n}")
  let he := mkIdent (Name.mkSimple s!"cirH_ex{n}")
  let hI := mkIdent h
  evalTactic (← `(tactic| obtain ⟨$a:ident, $he:ident, $hI:ident⟩ := $hI:ident))

/-- One symbolic execution step of a hypothesis `h : Res.holds X K`. -/
elab "cir_hstep " h:ident : tactic => Lean.Core.withCurrHeartbeats (hypStepImpl h.getId)

/-- Run the hypothesis `h` as far as possible on every goal: until it is no longer of the
form `Res.holds X K` (the source finished), its head is a loop, or no step applies. -/
elab "cir_hrun " h:ident : tactic => do
  let mut work := (← getGoals)
  let mut done : Array MVarId := #[]
  let mut fuel := (← getOptions).get `cir.fuel (100000 : Nat)
  while !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let g := work.head!
    work := work.tail!
    if ← g.isAssigned then continue
    setGoals [g]
    let some (x, _) ← hypHolds? h.getId |
      -- a partial operation left `∃ a, o = some a ∧ K a`: name the value and continue
      if ← tryTac (hypExists h.getId) then work := (← getGoals) ++ work
      else done := done.push g
      continue
    if x.isAppOf ``CIR.evalFor || x.isAppOf ``CIR.evalWhile || x.isAppOf ``CIR.evalDo then
      done := done.push g; continue
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do
        Lean.Core.withCurrHeartbeats (hypStepImpl h.getId)
        pure true)
      fun e => do
        s.restore
        if e.isRuntime then
          logWarning m!"cir_hrun: a step exceeded a resource limit: {e.toMessageData}"
        pure false
    if ok then work := (← getGoals) ++ work
    else done := done.push g
  setGoals (done.toList ++ work)

end EquivLean.Cir.Tactic

namespace EquivLean.Cir.Tactic

open Lean Elab Tactic in
/-- `m₁.blocks b = m₂.blocks b` for a block `b` older than the call: both calls' allocations
are above it (`killRange`/`upd` lookups decided by `omega`), and after a loop the frame facts
`cirH_frame…`/`cirH_s0…` of `cir_loop_pair` take it back to the entry memory. -/
elab "cir_obs_blocks" : tactic => do
  let hyps ← CIR.Tactic.cirHyps
  let args ← CIR.Tactic.simpArgs #[``EquivLean.Cir.killRange_lt_apply, ``EquivLean.Cir.upd_ne_apply,
    ``CIR.upd_same, ``CIR.Mem.endScope_blocks, ``CIR.Mem.mk_blocks, ``CIR.Mem.endScope_next,
    ``CIR.Mem.mk_next, ``CIR.Mem.setBlock_blocks, ``CIR.Mem.setBlock_next, ``CIR.State.mk_mem] hyps
  evalTactic (← `(tactic| simp (disch := cir_disch) only [$args,*]))

/-- Close a leaf `ObsEq m₀ (e₁, m₁) (e₂, m₂)`: the exits are equal (`rfl`, or injectivity and
`omega`), and every block below `m₀.next` is untouched by the allocations of both calls
(`killRange`/`upd` lookups decided by `omega`); blocks of the caller that both calls wrote (through
pointer arguments, possibly in another order) are compared case by case (`cir_upd_cases`). -/
macro "cir_obs_close" : tactic => `(tactic| (
  try dsimp only
  refine EquivLean.Cir.obsEq_intro ?_ ?_
  · first
      | rfl
      | (simp only [CIR.Exit.ret.injEq, CIR.Exit.exn.injEq, Option.some.injEq, CIR.Val.int.injEq,
          CIR.Val.bool.injEq]; first | rfl | omega)
  · intro b hb
    cir_obs_blocks
    all_goals (repeat (first | rfl | (cir_upd_cases <;> (try cir_obs_blocks))))))

open Lean Meta Elab Tactic in
/-- On `Cir.EquivOn Bad ctxNew fNew ctxOld fOld` where `Bad args m` unfolds to
`¬ ∃ x…, args = [v…] ∧ P x…` (or `¬ ∃ x…, args = [v…]`): introduce the call and its argument
values, with `P x…` as a hypothesis. -/
elab "cir_equivOn_intro" : tactic => do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOf ``EquivLean.Cir.EquivOn do throwError "cir_equivOn_intro: not a `Cir.EquivOn` goal"
  let hb := mkIdent `hbad
  evalTactic (← `(tactic| intro $(mkIdent `args):ident $(mkIdent `m):ident $hb:ident))
  -- `hbad : ¬ Bad args m` with `Bad args m` unfolding to `¬ Q`: get `hbad : Q`
  let g ← getMainGoal
  let q ← g.withContext do
    let some d := (← getLCtx).findFromUserName? `hbad | throwError "cir_equivOn_intro: lost hbad"
    let ty ← instantiateMVars d.type
    let_expr Not p := ty | throwError "cir_equivOn_intro: unexpected hypothesis {ty}"
    let p ← whnfD p
    let q ← match_expr p with
      | Not q => pure q
      | _ =>
        if p.isArrow && p.bindingBody!.isConstOf ``False then pure p.bindingDomain!
        else throwError "cir_equivOn_intro: `Bad` is not a negation: {p}"
    Lean.Elab.Term.exprToSyntax q
  evalTactic (← `(tactic| replace $hb:ident : $q := Classical.not_not.mp $hb:ident))
  -- destructure `∃ x…, args = l ∧ P`
  let mut n := 0
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext do
      let some d := (← getLCtx).findFromUserName? `hbad | return none
      return some (← whnfR (← instantiateMVars d.type))
    let some ty := ty | break
    if ty.isAppOfArity ``Exists 2 then
      let x := mkIdent (Name.mkSimple s!"cir_arg{n}"); n := n + 1
      evalTactic (← `(tactic| obtain ⟨$x:ident, $hb:ident⟩ := $hb:ident))
    else if ty.isAppOfArity ``And 2 && (ty.getArg! 0).isAppOfArity ``Eq 3 then
      -- (a quoted `rfl` pattern would be hygienic: name the equation and substitute it)
      let he := mkIdent `cirH_args
      evalTactic (← `(tactic| obtain ⟨$he:ident, $hb:ident⟩ := $hb:ident))
      evalTactic (← `(tactic| subst $he:ident))
    else if ty.isAppOfArity ``Eq 3 then
      evalTactic (← `(tactic| subst $hb:ident))
      break
    else break

open Lean Meta Elab Tactic in
/-- A value that passes a typed load is a leaf: a scalar constructor (`.int x`, by definition), or
`Val.isLeaf_of_fitsTy h` for some hypothesis `h` (a branch fact `fitsTy ty a = true`, in unfolded
form). -/
elab "cir_leaf" : tactic => do
  if ← tryTac (evalTactic (← `(tactic| exact trivial))) then return
  let g ← getMainGoal
  let hs ← g.withContext do
    return (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail || !d.userName.toString.startsWith "cirH_br" then acc
      else acc.push d.userName
  for h in hs do
    if ← tryTac (evalTactic (← `(tactic| exact EquivLean.Cir.Val.isLeaf_of_fitsTy $(mkIdent h)))) then
      return
  throwError "cir_leaf: no typed-load fact for this value"

open Lean Meta Elab Tactic in
/-- Pointer mode, after the source ran: for two writes of the source into one caller value at two
leaf positions it read before (`cirH_rd… : V.set? P X = some W₁`, `W₁.set? Q Y = some W₂`,
`V.get? P = some A`, `V.get? Q = some B`), add the facts of the other order (`V.set? Q Y = some W₁'`,
`W₁'.set? P X = some W₂`, by `Val.set?_swap`), for a target that writes them in that order.  The
positions are compared through the reads: equal positions hold equal values. -/
elab "cir_ptr_saturate" : tactic => do
  let g ← getMainGoal
  let (sets, gets) ← g.withContext do
    let mut sets : Array (Name × Expr × Expr × Expr × Expr) := #[]
    let mut gets : Array (Name × Expr × Expr) := #[]
    for d in (← getLCtx) do
      unless d.userName.toString.startsWith "cirH_rd" do continue
      let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
      let (lhs, rhs) := (lhs.consumeMData, rhs.consumeMData)
      unless rhs.isAppOfArity ``Option.some 2 do continue
      if lhs.isAppOfArity ``CIR.Val.set? 3 then
        sets := sets.push (d.userName, lhs.getArg! 0, lhs.getArg! 1, lhs.getArg! 2, rhs.appArg!)
      else if lhs.isAppOfArity ``CIR.Val.get? 2 then
        gets := gets.push (d.userName, lhs.getArg! 0, lhs.getArg! 1)
    return (sets, gets)
  let mut k := 0
  for (s1, v, p, _, w1) in sets do
    for (s2, v2, q, _, _) in sets do
      unless v2 == w1 do continue
      let some (r1, _, _) := gets.find? fun (_, v', p') => v' == v && p' == p | continue
      let some (r2, _, _) := gets.find? fun (_, v', q') => v' == v && q' == q | continue
      let n ← countPrefix "cirH_rd"
      let w := mkIdent (Name.mkSimple s!"cir_w{k}")
      let t1 := mkIdent (Name.mkSimple s!"cirH_rd{n}")
      let t2 := mkIdent (Name.mkSimple s!"cirH_rd{n+1}")
      let (r1I, r2I, s1I, s2I) := (mkIdent r1, mkIdent r2, mkIdent s1, mkIdent s2)
      let ok ← tryTac (evalTactic (← `(tactic|
        obtain ⟨$w:ident, $t1:ident, $t2:ident⟩ := EquivLean.Cir.Val.set?_swap $r1I $r2I
          (by cir_leaf) (by cir_leaf)
          (by
            intro hpq
            subst hpq
            have hab := ($r1I).symm.trans $r2I
            simp only [Option.some.injEq] at hab
            first
              | (subst hab; rfl)
              | exact hab
              | exact hab.symm
              -- two integers read at one position: the same branches of the typed loads
              | (simp only [CIR.Val.int.injEq] at hab; subst hab; first | rfl | (exfalso; omega)))
          $s1I $s2I)))
      if ok then k := k + 1

/-- `Sim R t s` between two CIR computations (typically two calls `evalCall ctx f args m`):
the source runs in a hypothesis, then the target with `cir_vcg`; `ObsEq` leaves are closed.
Goals that remain (loops, leaves it cannot close) are left for the user. -/
macro "cir_sim" : tactic => `(tactic| (
  rw [EquivLean.Cir.sim_res_res]
  intro os hs
  cir_hrun hs
  all_goals (try cir_ptr_saturate)
  all_goals (try subst hs)
  all_goals (try cir_call_inline)
  all_goals (try cir_vcg)
  all_goals (try cir_obs_close)))

/-- `equiv_cir` proves `Sim R t s`, `Equiv R t s` or `Cir.EquivOn Bad …` between two CIR
computations, both directions with `cir_sim` (for `ObsEq`, the reversed relation is `ObsEq`
again; an `EquivOn` goal is introduced by `cir_equivOn_intro`). -/
macro "equiv_cir" : tactic => `(tactic| (
  try cir_equivOn_intro
  first
  | (refine ⟨?_, ?_⟩
     · cir_sim
     · (try rw [EquivLean.Cir.obsEq_flip]); cir_sim)
  | cir_sim))

end EquivLean.Cir.Tactic

/-! ### Pairing two loops: `cir_loop_pair` -/

namespace EquivLean.Cir.Tactic

open Lean Meta Elab Tactic
open CIR.Tactic (collectStores collectCallArgs envSlot? readNames funBinders holdsHead? typedLambda)

open Lean Elab Tactic in
/-- Split `cirH_user` (conjunctions; equations `x = e` substituted), as cirlean does for
postconditions of specifications. -/
elab "cir_split_user" : tactic => CIR.Tactic.splitFact `cirH_user

/-- One side of a loop pair. -/
structure LoopSide where
  shape : Name
  term : Name
  /-- `ctx` and the regions (and cleanup) of the loop -/
  args : Array Expr
  σ₀ : Expr

def loopSide? (x : Expr) : Option LoopSide :=
  let a := x.getAppArgs
  match x.getAppFn.constName? with
  | some ``CIR.evalFor => if a.size == 6 then
      some ⟨``EquivLean.Cir.loopShape_for, ``EquivLean.Cir.terminates_for, a.extract 0 5, a[5]!⟩
    else none
  | some ``CIR.evalWhile => if a.size == 5 then
      some ⟨``EquivLean.Cir.loopShape_while, ``EquivLean.Cir.terminates_while, a.extract 0 4, a[4]!⟩
    else none
  | some ``CIR.evalDo => if a.size == 4 then
      some ⟨``EquivLean.Cir.loopShape_do, ``EquivLean.Cir.terminates_do, a.extract 0 3, a[3]!⟩
    else none
  | _ => none

/-- The local variables (stack slots) a loop stores to, and those whose address it passes to
a call (the hidden iterator of a range-`for`): block, type, C++ name. -/
def loopSlots (side : LoopSide) :
    MetaM (Array (Expr × Expr × String) × Array (Expr × Expr × String)) := do
  let names ← readNames side.σ₀
  let nameOf (blk : Expr) : MetaM String := do
    return ((← names.findM? fun (_, b') => isDefEq blk b').map (·.1)).getD ""
  let mut stored : Array (Expr × Expr × String) := #[]
  let mut passed : Array (Expr × Expr × String) := #[]
  for r in side.args.extract 1 side.args.size do
    for (addr, ty) in ← collectStores r do
      if let some blk ← envSlot? side.σ₀ addr then
        unless ← stored.anyM (fun (b, _, _) => isDefEq b blk) do
          stored := stored.push (blk, ty, ← nameOf blk)
    for (addr, ty) in ← collectCallArgs r do
      if let some blk ← envSlot? side.σ₀ addr then
        unless ← passed.anyM (fun (b, _, _) => isDefEq b blk) do
          passed := passed.push (blk, ty, ← nameOf blk)
  return (stored, passed)

/-- A leaf of a loop pairing (`StepRel …`), handled by `cir_pair_step`: stepping it with
`cir_vcg` would run cirlean's eager fallback on both final states (tens of seconds) for nothing. -/
def isRelLeaf (t : Expr) : Bool := t.isAppOf ``EquivLean.StepRel

/-- The goal is not a loop-pairing leaf. -/
elab "cir_not_leaf" : tactic => do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  if isRelLeaf t then throwError "cir_not_leaf: a loop-pairing leaf"

/-- cirlean's `cir_run` worklist driver, leaving loop-pairing leaves untouched. -/
elab "cir_run_tgt" : tactic => do
  let mut work := (← getGoals)
  let mut stuck : Array MVarId := #[]
  let mut deferred : Array MVarId := #[]
  let mut retried := false
  let mut fuel := (← getOptions).get `cir.fuel (100000 : Nat)
  while (!work.isEmpty || (!deferred.isEmpty && !retried)) && fuel > 0 do
    fuel := fuel - 1
    if work.isEmpty then
      work := deferred.toList
      deferred := #[]
      retried := true
    let g := work.head!
    work := work.tail!
    if ← g.isAssigned then continue
    if !(← isProp (← g.getType)) then
      stuck := stuck.push g
      continue
    if isRelLeaf (← g.withContext do whnfR (← instantiateMVars (← g.getType))) then
      stuck := stuck.push g
      continue
    setGoals [g]
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do
        evalTactic (← `(tactic| cir_step))
        pure true)
      fun e => do
        s.restore
        if e.isRuntime then
          logWarning m!"cir_run: a step exceeded a resource limit (goal left stuck): {e.toMessageData}"
        pure false
    if ok then
      work := (← getGoals) ++ work
    else if !retried && (← instantiateMVars (← g.getType)).hasExprMVar then
      deferred := deferred.push g
    else
      stuck := stuck.push g
  setGoals (stuck.toList ++ deferred.toList ++ work)

/-- `cir_vcg` for the target of a paired iteration: loop-pairing leaves are left as they are. -/
macro "cir_vcg_tgt" : tactic =>
  `(tactic| (cir_run_tgt; all_goals (try cir_subst_nat); all_goals (try (cir_not_leaf; cir_close'))))

/-- `cir_loop_pair hs inv`: the goal's head is the target loop `L₁ σ₀t`, the head of the
hypothesis `hs` the source loop `L₂ σ₀s` (as left by `cir_vcg` and `cir_hrun`).  Applies
`wp_loop_rel` (lockstep, termination from the source: no variant) with the coupling invariant

    LoopFrame σ₀t modsT σt ∧ slots of σt … ∧ LoopFrame σ₀s modsS σs ∧ slots of σs … ∧ inv …

The binders of `inv` name the variables the loops modify, as for cirlean's `cir_loop`: `x`
the target's variable `x`, `x'` the source's; a signed integer is an `Int`, an unsigned one a
`Nat`, and a binder that is not a variable name stands for the hidden iterator of a
range-`for` (a `Nat`, its element index).  Other variables the loops assign are assigned
before use in each iteration.  The loop outcome relation is "the continuations agree"
(`K₂ o₂ → K₁ o₁`), so the code after the loops is executed inside the iteration that leaves
them.  Leaves: the invariant at entry (`cir_init`) and one paired iteration (`cir_step`). -/
syntax (name := cirLoopPair) "cir_loop_pair " ident term:max : tactic

/-- Keep the facts of an enclosing loop pair usable: rename its `cirH_…` facts and states
with a level suffix, so that the names `cir_loop_pair` introduces do not shadow them. -/
def renameOuterLoopFacts : TacticM Unit := do
  let g ← getMainGoal
  let fixed := #["σt", "σs", "σ₀t", "σ₀s"]
  let lvl := (← g.getDecl).lctx.foldl (init := 0) fun acc d =>
    if d.userName.toString.startsWith "σ₀t_L" then acc + 1 else acc
  let mut g := g
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    let n := d.userName.toString
    let isLoopFact := (n.startsWith "cirH_" && !n.startsWith "cirH_br" && !n.startsWith "cirH_ex") ||
      fixed.contains n
    if isLoopFact then
      g ← g.rename d.fvarId (Name.mkSimple s!"{n}_L{lvl}")
  replaceMainGoal [g]

@[tactic cirLoopPair] def evalCirLoopPair : Tactic := fun stx => Lean.Core.withCurrHeartbeats do
  let hs : Ident := ⟨stx[1]⟩
  let invStx : Term := ⟨stx[2]⟩
  renameOuterLoopFacts
  let g ← getMainGoal
  let (sT, sS, slotsT, slotsS) ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let some x := holdsHead? t | throwError "cir_loop_pair: the goal is not `Res.holds _ _`"
    let some sT := loopSide? (← instantiateMVars x)
      | throwError "cir_loop_pair: the head of the goal is not a loop"
    let some (y, _) ← hypHolds? hs.getId | throwError "cir_loop_pair: {hs} is not `Res.holds _ _`"
    let some sS := loopSide? y | throwError "cir_loop_pair: the head of {hs} is not a loop"
    return (sT, sS, ← loopSlots sT, ← loopSlots sS)
  let (binders, _) ← funBinders invStx
  -- binders: `x` is the target's variable `x`, `x'` the source's
  let mut order : Array (Bool × Expr × Expr × CIR.Tactic.SlotKind) := #[]
  for bn in binders do
    let s := bn.getId.toString
    let isSrc := s.endsWith "'"
    let base := if isSrc then (s.dropEnd 1).toString else s
    let (stored, passed) := if isSrc then slotsS else slotsT
    let byName := (stored ++ passed).find? (·.2.2 == base)
    let found ← match byName with
      | some sl => pure (some sl)
      | none => g.withContext <| passed.findM? fun (b, ty, n) => do
          return n.startsWith "__begin" && (← CIR.Tactic.slotKindOf? ty) == some .iter &&
            !(← order.anyM fun (s', b', _, _) => return s' == isSrc && (← isDefEq b b'))
    let some (blk, ty, _) := found
      | throwError "cir_loop_pair: `{s}`: the {if isSrc then "source" else "target"} loop does not modify a variable `{base}`; it modifies {stored.map (·.2.2)}"
    let some kind ← g.withContext <| CIR.Tactic.slotKindOf? ty
      | throwError "cir_loop_pair: `{s}`: unsupported variable type {ty} (integers and iterators)"
    order := order.push (isSrc, blk, ty, kind)
  -- modified variables that are not named: assigned before use in each iteration
  let scratchOf (src : Bool) (slots : Array (Expr × Expr × String)) : MetaM (Array (Expr × Expr)) :=
    g.withContext do
      let mut out := #[]
      for (b, ty, _) in slots do
        unless ← order.anyM (fun (s', b', _, _) => return s' == src && (← isDefEq b b')) do
          out := out.push (b, ty)
      return out
  let scrT ← scratchOf false slotsT.1
  let scrS ← scratchOf true slotsS.1
  let nm (s : String) : Ident := mkIdent (Name.mkSimple s)
  -- name the entry states
  let σ₀tS ← g.withContext <| Lean.Elab.Term.exprToSyntax sT.σ₀
  let σ₀sS ← g.withContext <| Lean.Elab.Term.exprToSyntax sS.σ₀
  let nextT ← g.withContext do
    let e ← whnfR (← mkAppM ``CIR.Mem.next #[← whnfR (← mkAppM ``CIR.State.mem #[sT.σ₀])])
    Lean.Elab.Term.exprToSyntax e
  let nextS ← g.withContext do
    let e ← whnfR (← mkAppM ``CIR.Mem.next #[← whnfR (← mkAppM ``CIR.State.mem #[sS.σ₀])])
    Lean.Elab.Term.exprToSyntax e
  evalTactic (← `(tactic| generalize $(nm "cirH_genT"):ident : $σ₀tS = $(nm "σ₀t"):ident))
  evalTactic (← `(tactic| have $(nm "cirH_s0T"):ident := ($(nm "cirH_genT")).symm))
  evalTactic (← `(tactic| clear $(nm "cirH_genT"):ident))
  evalTactic (← `(tactic| generalize $(nm "cirH_genS"):ident : $σ₀sS = $(nm "σ₀s"):ident at $hs:ident))
  evalTactic (← `(tactic| have $(nm "cirH_s0S"):ident := ($(nm "cirH_genS")).symm))
  evalTactic (← `(tactic| clear $(nm "cirH_genS"):ident))
  let s0t := nm "σ₀t"
  let s0s := nm "σ₀s"
  let hs0T := nm "cirH_s0T"
  let hs0S := nm "cirH_s0S"
  let hn0T' := nm "cirH_n0T"
  let hn0S' := nm "cirH_n0S"
  evalTactic (← `(tactic| have $hn0T':ident : ($s0t : CIR.State).mem.next = $nextT := by subst $hs0T:ident; rfl))
  evalTactic (← `(tactic| have $hn0S':ident : ($s0s : CIR.State).mem.next = $nextS := by subst $hs0S:ident; rfl))
  -- the continuations
  let g ← getMainGoal
  let (k₁S, k₂S, argsTS, argsSS) ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let some (_, k₂) ← hypHolds? hs.getId | throwError "cir_loop_pair: lost {hs}"
    let a1 ← sT.args.mapM fun e => Lean.Elab.Term.exprToSyntax e
    let a2 ← sS.args.mapM fun e => Lean.Elab.Term.exprToSyntax e
    return (← Lean.Elab.Term.exprToSyntax (t.getArg! 2), ← Lean.Elab.Term.exprToSyntax k₂, a1, a2)
  -- the coupling invariant
  let σt := mkIdent `σt
  let σs := mkIdent `σs
  let blkS : Array Term ← g.withContext <| order.mapM fun p => Lean.Elab.Term.exprToSyntax p.2.1
  let tyS : Array Term ← g.withContext <| order.mapM fun p => Lean.Elab.Term.exprToSyntax p.2.2.1
  let srcs : Array Bool := order.map (·.1)
  let kinds : Array CIR.Tactic.SlotKind := order.map (·.2.2.2)
  let mut vals : Array Term := #[]
  let mut binderTys : Array Term := #[]
  for i in [0:order.size] do
    let b := blkS[i]!
    let st := if srcs[i]! then σs else σt
    match kinds[i]! with
    | .iter =>
      vals := vals.push (← `(CIR.State.iterAt $st $b))
      binderTys := binderTys.push (← `(Nat))
    | .nat =>
      vals := vals.push (← `((CIR.State.intAt $st $b).toNat))
      binderTys := binderTys.push (← `(Nat))
    | _ =>
      vals := vals.push (← `(CIR.State.intAt $st $b))
      binderTys := binderTys.push (← `(Int))
  let invFn ← typedLambda invStx binderTys
  let mut inv ← `(($invFn) $vals*)
  let scrTS : Array (Term × Term) ← g.withContext <| scrT.mapM fun p => do
    return (← Lean.Elab.Term.exprToSyntax p.1, ← Lean.Elab.Term.exprToSyntax p.2)
  let scrSS : Array (Term × Term) ← g.withContext <| scrS.mapM fun p => do
    return (← Lean.Elab.Term.exprToSyntax p.1, ← Lean.Elab.Term.exprToSyntax p.2)
  let slotConj (st σ₀ : Ident) (i : Nat) : TacticM Term :=
    if kinds[i]! == .iter then `(CIR.IterSlot $σ₀ $st $(blkS[i]!))
    else `(CIR.IntSlot $st $(blkS[i]!) $(tyS[i]!))
  -- source side (inner), then target side (outer)
  for (b, ty) in scrSS.reverse do inv ← `(CIR.ScratchSlot $σs $b $ty ∧ $inv)
  for i in (List.range order.size).reverse do
    if srcs[i]! then inv ← `($(← slotConj σs s0s i) ∧ $inv)
  let mut modsS : Array Term := #[]
  for i in [0:order.size] do
    if srcs[i]! then modsS := modsS.push blkS[i]!
  modsS := modsS ++ scrSS.map (·.1)
  inv ← `(CIR.LoopFrame $s0s [$modsS,*] $σs ∧ $inv)
  for (b, ty) in scrTS.reverse do inv ← `(CIR.ScratchSlot $σt $b $ty ∧ $inv)
  for i in (List.range order.size).reverse do
    if !srcs[i]! then inv ← `($(← slotConj σt s0t i) ∧ $inv)
  let mut modsT : Array Term := #[]
  for i in [0:order.size] do
    if !srcs[i]! then modsT := modsT.push blkS[i]!
  modsT := modsT ++ scrTS.map (·.1)
  inv ← `(CIR.LoopFrame $s0t [$modsT,*] $σt ∧ $inv)
  let invFun ← `(fun ($σt : CIR.State) ($σs : CIR.State) => $inv)
  let shapeT := mkIdent sT.shape
  let shapeS := mkIdent sS.shape
  let termS := mkIdent sS.term
  evalTactic (← `(tactic| refine EquivLean.Cir.holds_of_wp (EquivLean.wp_loop_rel ($shapeT $argsTS*) ($shapeS $argsSS*) ($termS $argsSS*) (R := fun o₁ o₂ => $k₂S o₂ → $k₁S o₁) $invFun (EquivLean.Cir.wp_of_holds $hs) ?cir_init ?cir_step (fun _ _ hR hK => hR hK))))
  -- the iteration: name the facts as `cir_loop` does, on both sides
  evalTactic (← `(tactic| case' cir_step => intro $σt:ident $σs:ident $(nm "cirH_inv"):ident))
  let mut cur := nm "cirH_inv"
  let mut k := 0
  let decompose (side : String) (idxs : Array Nat) (scr : Array (Term × Term))
      (cur : Ident) (k : Nat) : TacticM (Ident × Nat) := do
    let mut cur := cur
    let mut k := k
    let rest := nm s!"cirH_rest{k}"; k := k + 1
    let he := nm s!"cirH_env{side}"
    let hn := nm s!"cirH_names{side}"
    let hx := nm s!"cirH_next{side}"
    let hf := nm s!"cirH_frame{side}"
    evalTactic (← `(tactic| case' cir_step => obtain ⟨⟨$he:ident, $hn:ident, $hx:ident, $hf:ident⟩, $rest:ident⟩ := $cur:ident))
    cur := rest
    for i in idxs do
      let rest := nm s!"cirH_rest{k}"; k := k + 1
      let hsl := nm s!"cirH_slot{side}{i}"
      if kinds[i]! == .iter then
        evalTactic (← `(tactic| case' cir_step => obtain ⟨$hsl:ident, $rest:ident⟩ := $cur:ident))
      else
        let hr := nm s!"cirH_range{side}{i}"
        evalTactic (← `(tactic| case' cir_step => obtain ⟨⟨$hsl:ident, $hr:ident⟩, $rest:ident⟩ := $cur:ident))
        evalTactic (← `(tactic| case' cir_step => simp only [CIR.fitsTy, CIR.inRange_eq_true_iff, CIR.intMin_s8, CIR.intMax_s8, CIR.intMin_s16, CIR.intMax_s16, CIR.intMin_s32, CIR.intMax_s32, CIR.intMin_s64, CIR.intMax_s64, CIR.intMin_u, CIR.intMax_u8, CIR.intMax_u16, CIR.intMax_u32, CIR.intMax_u64] at $hr:ident))
      cur := rest
    for j in [0:scr.size] do
      let rest := nm s!"cirH_rest{k}"; k := k + 1
      let v := nm s!"cir_scratch{side}{j}"
      let hsc := nm s!"cirH_scratch{side}{j}"
      evalTactic (← `(tactic| case' cir_step => obtain ⟨⟨$v:ident, $hsc:ident⟩, $rest:ident⟩ := $cur:ident))
      cur := rest
    return (cur, k)
  let idxT := (List.range order.size).toArray.filter fun i => !srcs[i]!
  let idxS := (List.range order.size).toArray.filter fun i => srcs[i]!
  (cur, k) ← decompose "T" idxT scrTS cur k
  (cur, k) ← decompose "S" idxS scrSS cur k
  let _ := k
  let hu := nm "cirH_user"
  evalTactic (← `(tactic| case' cir_step => have $hu:ident := $cur:ident))
  evalTactic (← `(tactic| case' cir_step => clear $cur:ident))
  let hnxT := nm "cirH_nxT"
  let hn0T := nm "cirH_n0T"
  let hnextT := nm "cirH_nextT"
  let hnxS := nm "cirH_nxS"
  let hn0S := nm "cirH_n0S"
  let hnextS := nm "cirH_nextS"
  evalTactic (← `(tactic| case' cir_step => have $hnxT:ident : $nextT ≤ ($σt:ident).mem.next := $hn0T:ident ▸ $hnextT:ident))
  evalTactic (← `(tactic| case' cir_step => have $hnxS:ident : $nextS ≤ ($σs:ident).mem.next := $hn0S:ident ▸ $hnextS:ident))
  -- caller blocks below the entry `next`s lie below the current ones (fast key comparisons)
  let g ← getMainGoal
  let bounds ← g.withContext do
    let mut out : Array Expr := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, _, lhs, _) := ty.app4? ``LT.lt then
        if lhs.isFVar && (← inferType lhs).isConstOf ``Nat then
          unless out.contains lhs do out := out.push lhs
    return out
  for (b, idx) in bounds.zipIdx do
    let bS ← g.withContext <| Lean.Elab.Term.exprToSyntax b
    let hbT := nm s!"cirH_ltT{idx}"
    let hbS := nm s!"cirH_ltS{idx}"
    evalTactic (← `(tactic| case' cir_step => try have $hbT:ident : $bS < ($σt:ident).mem.next := by omega))
    evalTactic (← `(tactic| case' cir_step => try have $hbS:ident : $bS < ($σs:ident).mem.next := by omega))
  -- the variables' values, under the user's names
  for i in [0:order.size] do
    let x := binders[i]!
    let st := if srcs[i]! then σs else σt
    let side := if srcs[i]! then "S" else "T"
    let hv := nm s!"cirH_val{i}"
    let bi := blkS[i]!
    match kinds[i]! with
    | .iter =>
      let hsl := nm s!"cirH_slot{side}{i}"
      evalTactic (← `(tactic| case' cir_step => cir_simp_hyp $hsl:ident))
      evalTactic (← `(tactic| case' cir_step => generalize $hv:ident : CIR.State.iterAt $st:ident $bi = $x:ident at *))
    | .nat =>
      let v := nm s!"cir_v{i}"
      let hx := nm s!"cir_nat{i}"
      evalTactic (← `(tactic| case' cir_step => generalize $hv:ident : CIR.State.intAt $st:ident $bi = $v:ident at *))
      evalTactic (← `(tactic| case' cir_step => obtain ⟨$x:ident, $hx:ident⟩ : ∃ n : Nat, $v:ident = (n : Int) := ⟨($v:ident).toNat, by omega⟩))
      evalTactic (← `(tactic| case' cir_step => simp only [$hx:ident, Int.toNat_natCast] at $hu:ident))
    | _ =>
      evalTactic (← `(tactic| case' cir_step => generalize $hv:ident : CIR.State.intAt $st:ident $bi = $x:ident at *))
  evalTactic (← `(tactic| case' cir_step => try dsimp only at $(nm "cirH_user"):ident))
  -- split the user's relation; equations between variables are substituted, so both sides
  -- share the variables and the source's branch facts decide the target's branches
  evalTactic (← `(tactic| case' cir_step => cir_split_user))

/-- The goal is `Res.holds _ _ → Res.holds _ _` (continuations after two loops). -/
elab "cir_is_cont_goal" : tactic => do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isArrow && t.bindingDomain!.isAppOfArity ``CIR.Res.holds 3 &&
      t.bindingBody!.isAppOfArity ``CIR.Res.holds 3 do
    throwError "cir_is_cont_goal: not an implication between two `Res.holds`"

/-- The code after two loops (leaf `K₂ o₂ → K₁ o₁` of a paired iteration): the source's
rest in a hypothesis, then the target's. -/
macro "cir_pair_cont" : tactic => `(tactic| (
  cir_is_cont_goal
  intro hk
  try dsimp only at hk
  cir_hrun hk
  all_goals (try subst hk)
  all_goals (try cir_vcg)
  all_goals (try cir_obs_close)))

/-- Run one paired iteration (after `cir_loop_pair`, on the `cir_step` goal): the source
iteration in a hypothesis, the target's with `cir_vcg`, then the `StepRel` leaves: the
invariant (`cir_vcg`), the continuations after the loops (`cir_pair_cont`), contradictions. -/
macro "cir_pair_step" : tactic => `(tactic| (
  rw [EquivLean.Cir.sim_res_res]
  intro os hsi
  cir_hrun hsi
  all_goals (try subst hsi)
  all_goals (try cir_vcg_tgt)
  all_goals (try simp only [EquivLean.StepRel, EquivLean.Cir.loopCls, id])
  all_goals (first | cir_pair_cont | (try cir_vcg))))

end EquivLean.Cir.Tactic

namespace EquivLean.Cir.Tactic

open Lean Elab Tactic in
/-- The goal is a `Sim` judgement. -/
elab "cir_is_sim_goal" : tactic => do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOf ``EquivLean.Sim do throwError "cir_is_sim_goal: not a `Sim` goal: {t}"

/-- `Sim R t s` between two CIR computations with one loop each, paired in lockstep with the
coupling invariant `inv` (binders: `x` the target's variable, `x'` the source's): run both
sides to their loops, `cir_loop_pair`, then the entry condition and one paired iteration
(which includes the code after the loops). -/
syntax "cir_sim_loop " term:max : tactic
macro_rules
  | `(tactic| cir_sim_loop $inv) => `(tactic| (
      rw [EquivLean.Cir.sim_res_res]
      intro os hs
      cir_hrun hs
      all_goals (try cir_call_inline)
      all_goals (try cir_vcg)
      cir_loop_pair hs $inv
      all_goals (first | (cir_is_sim_goal; cir_pair_step) | cir_vcg)))

/-- `equiv_cir using inv`: `Equiv R t s` (or `Sim`) between two CIR computations with one loop
each, both directions with `cir_sim_loop inv` (for `ObsEq`, the reversed relation is `ObsEq`
again; `inv` is used with `x` the target's and `x'` the source's variable in each direction). -/
syntax "equiv_cir " "using " term:max : tactic
macro_rules
  | `(tactic| equiv_cir using $inv) => `(tactic| (
      try cir_equivOn_intro
      first
      | (refine ⟨?_, ?_⟩
         · cir_sim_loop $inv
         · (try rw [EquivLean.Cir.obsEq_flip]); cir_sim_loop $inv)
      | cir_sim_loop $inv))

end EquivLean.Cir.Tactic

/-! ### Several loops in sequence -/

namespace EquivLean.Cir.Tactic

/-- `cir_pair_step` for a function with several loops in sequence: the continuations after the
first pair of loops (leaves `K₂ o₂ → K₁ o₁`) run up to the next pair of loops, which is paired
with the next invariant of the list. -/
syntax "cir_pair_step_with " "[" term,* "]" : tactic
/-- The continuation leaf of `cir_pair_step_with`. -/
syntax "cir_pair_cont_with " "[" term,* "]" : tactic

macro_rules
  | `(tactic| cir_pair_cont_with [$invs,*]) => do
    let xs := invs.getElems
    if xs.isEmpty then `(tactic| cir_pair_cont) else
    let inv := xs[0]!
    let rest : Lean.Syntax.TSepArray `term "," := .ofElems (xs.extract 1 xs.size)
    `(tactic| (
      cir_is_cont_goal
      intro hk
      try dsimp only at hk
      cir_hrun hk
      all_goals (try subst hk)
      all_goals (try cir_vcg)
      all_goals (try cir_obs_close)
      all_goals (try (cir_loop_pair hk $inv
                      all_goals (first | (cir_is_sim_goal; cir_pair_step_with [$rest,*]) | cir_vcg)))))

macro_rules
  | `(tactic| cir_pair_step_with [$invs,*]) => `(tactic| (
      rw [EquivLean.Cir.sim_res_res]
      intro os hsi
      cir_hrun hsi
      all_goals (try subst hsi)
      all_goals (try cir_vcg_tgt)
      all_goals (try simp only [EquivLean.StepRel, EquivLean.Cir.loopCls, id])
      all_goals (first | cir_pair_cont_with [$invs,*] | (try cir_vcg))))

/-- `cir_sim_loop` for several loops in sequence, one coupling invariant per pair of loops. -/
syntax "cir_sim_loops " "[" term,+ "]" : tactic
macro_rules
  | `(tactic| cir_sim_loops [$invs,*]) => do
    let xs := invs.getElems
    let inv := xs[0]!
    let rest : Lean.Syntax.TSepArray `term "," := .ofElems (xs.extract 1 xs.size)
    `(tactic| (
      rw [EquivLean.Cir.sim_res_res]
      intro os hs
      cir_hrun hs
      all_goals (try cir_call_inline)
      all_goals (try cir_vcg)
      cir_loop_pair hs $inv
      all_goals (first | (cir_is_sim_goal; cir_pair_step_with [$rest,*]) | cir_vcg)))

/-- `equiv_cir using [inv₁, …]`: several loops in sequence, one coupling invariant per pair. -/
macro_rules
  | `(tactic| equiv_cir using [$invs,*]) => `(tactic| (
      try cir_equivOn_intro
      first
      | (refine ⟨?_, ?_⟩
         · cir_sim_loops [$invs,*]
         · (try rw [EquivLean.Cir.obsEq_flip]); cir_sim_loops [$invs,*])
      | cir_sim_loops [$invs,*]))

end EquivLean.Cir.Tactic

/-! ### A CIR loop against a loop of any encoding: `equiv_cir_loop` -/

namespace EquivLean.Cir.Tactic

open Lean Meta Elab Tactic
open CIR.Tactic (funBinders holdsHead? typedLambda)

/-- `equiv_cir_loop inv using h₂shape, h₂term`: the goal's head is a CIR loop `L₁ σ₀t`
(`Res.holds (L₁ σ₀t) K₁` as left by `cir_vcg`, or `wp (L₁ σ₀t) K₁`); a hypothesis
`wp (L₂ s₂) K₂` holds the source loop of any encoding, whose shape and termination are the
terms `h₂shape : LoopShape L₂ iter₂ cls₂` and `h₂term : LoopShape.Terminates L₂ iter₂ cls₂`.
Applies `wp_loop_rel` with the coupling invariant

    LoopFrame σ₀t mods σt ∧ slots of σt … ∧ inv (values of the C variables) s₂

built as `cir_loop` builds its invariant: all binders of `inv` but the last name C variables
of the target loop (`int` an `Int`, `size_t` a `Nat`, a non-variable binder the iterator of
a range-`for`), the last one is the source state.  The loop outcome relation is "the
continuations agree" (`K₂ o₂ → K₁ o₁`).  Goals: `cir_init` (the invariant at entry;
`cir_vcg` proves its CIR part) and `cir_step` (one lockstep iteration, a `Sim` goal on
`iter₁ σt` and `iter₂ s₂`, with the target's loop-head facts named as by `cir_loop` and the
user's relation as `cirH_user`). -/
syntax (name := equivCirLoop) "equiv_cir_loop " term:max " using " term:max ", " term:max : tactic

@[tactic equivCirLoop] def evalEquivCirLoop : Tactic := fun stx => Lean.Core.withCurrHeartbeats do
  let invStx : Term := ⟨stx[1]⟩
  let shape₂ : Term := ⟨stx[3]⟩
  let term₂ : Term := ⟨stx[5]⟩
  renameOuterLoopFacts
  let g ← getMainGoal
  let (sT, slotsT, isHolds, hsS, k₂S, s₂TyS) ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let (x, isHolds) ← match holdsHead? t with
      | some x => pure (x, true)
      | none =>
        if t.isAppOfArity ``EquivLean.wp 5 then pure (t.getArg! 3, false)
        else throwError "equiv_cir_loop: the goal is neither `Res.holds (L σ) K` nor `wp (L σ) K`"
    let some sT := loopSide? (← instantiateMVars x)
      | throwError "equiv_cir_loop: the head of the goal is not a CIR loop"
    -- the source loop function `L₂` and state type, from the shape
    let shapeE ← Lean.Elab.Term.elabTerm shape₂ none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let shapeTy ← whnfR (← instantiateMVars (← inferType shapeE))
    unless shapeTy.isAppOfArity ``EquivLean.LoopShape 10 do
      throwError "equiv_cir_loop: {shape₂} is not a `LoopShape` proof: {shapeTy}"
    let L₂ := shapeTy.getArg! 7
    let s₂Ty := shapeTy.getArg! 0
    -- the hypothesis `wp (L₂ s₂) K₂`
    let mut found : Option (Expr × Expr) := none
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``EquivLean.wp 5 then
        let c := ty.getArg! 3
        if c.isApp && (← isDefEq c.appFn! L₂) then found := some (d.toExpr, ty.getArg! 4)
    let some (hs, k₂) := found
      | throwError "equiv_cir_loop: no hypothesis `wp ({L₂} _) _` for the source loop"
    return (sT, ← loopSlots sT, isHolds, ← Lean.Elab.Term.exprToSyntax hs,
      ← Lean.Elab.Term.exprToSyntax k₂, ← Lean.Elab.Term.exprToSyntax s₂Ty)
  let (binders, _) ← funBinders invStx
  if binders.isEmpty then throwError "equiv_cir_loop: the last binder of the invariant is the source state"
  let tBinders := binders.extract 0 (binders.size - 1)
  let sBinder := binders[binders.size - 1]!
  -- target variables, by C name (or the hidden iterator of a range-`for`)
  let mut order : Array (Expr × Expr × CIR.Tactic.SlotKind) := #[]
  for bn in tBinders do
    let base := bn.getId.toString
    let (stored, passed) := slotsT
    let byName := (stored ++ passed).find? (·.2.2 == base)
    let found ← match byName with
      | some sl => pure (some sl)
      | none => g.withContext <| passed.findM? fun (b, ty, n) => do
          return n.startsWith "__begin" && (← CIR.Tactic.slotKindOf? ty) == some .iter &&
            !(← order.anyM fun (b', _, _) => isDefEq b b')
    let some (blk, ty, _) := found
      | throwError "equiv_cir_loop: `{base}`: the target loop does not modify a variable `{base}`; it modifies {stored.map (·.2.2)}"
    let some kind ← g.withContext <| CIR.Tactic.slotKindOf? ty
      | throwError "equiv_cir_loop: `{base}`: unsupported variable type {ty} (integers and iterators)"
    order := order.push (blk, ty, kind)
  let scrT ← g.withContext do
    let mut out := #[]
    for (b, ty, _) in slotsT.1 do
      unless ← order.anyM (fun (b', _, _) => isDefEq b b') do out := out.push (b, ty)
    return out
  let nm (s : String) : Ident := mkIdent (Name.mkSimple s)
  -- name the entry state of the target loop
  let σ₀tS ← g.withContext <| Lean.Elab.Term.exprToSyntax sT.σ₀
  let nextT ← g.withContext do
    let e ← whnfR (← mkAppM ``CIR.Mem.next #[← whnfR (← mkAppM ``CIR.State.mem #[sT.σ₀])])
    Lean.Elab.Term.exprToSyntax e
  let s0t := nm "σ₀t"
  let hs0T := nm "cirH_s0T"
  let hgen := nm "cirH_genT"
  let hn0T := nm "cirH_n0T"
  evalTactic (← `(tactic| generalize $hgen:ident : $σ₀tS = $s0t:ident))
  evalTactic (← `(tactic| have $hs0T:ident := ($hgen:ident).symm))
  evalTactic (← `(tactic| clear $hgen:ident))
  evalTactic (← `(tactic| have $hn0T:ident : ($s0t : CIR.State).mem.next = $nextT := by subst $hs0T:ident; rfl))
  let g ← getMainGoal
  let (k₁S, argsTS) ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let k₁ := if isHolds then t.getArg! 2 else t.getArg! 4
    return (← Lean.Elab.Term.exprToSyntax k₁, ← sT.args.mapM fun e => Lean.Elab.Term.exprToSyntax e)
  -- the coupling invariant
  let σt := mkIdent `σt
  let blkS : Array Term ← g.withContext <| order.mapM fun p => Lean.Elab.Term.exprToSyntax p.1
  let tyS : Array Term ← g.withContext <| order.mapM fun p => Lean.Elab.Term.exprToSyntax p.2.1
  let kinds := order.map (·.2.2)
  let mut vals : Array Term := #[]
  let mut binderTys : Array Term := #[]
  for i in [0:order.size] do
    let b := blkS[i]!
    match kinds[i]! with
    | .iter =>
      vals := vals.push (← `(CIR.State.iterAt $σt $b)); binderTys := binderTys.push (← `(Nat))
    | .nat =>
      vals := vals.push (← `((CIR.State.intAt $σt $b).toNat)); binderTys := binderTys.push (← `(Nat))
    | _ =>
      vals := vals.push (← `(CIR.State.intAt $σt $b)); binderTys := binderTys.push (← `(Int))
  let invFn ← typedLambda invStx (binderTys.push s₂TyS)
  let mut inv ← `(($invFn) $vals* $sBinder)
  let scrTS : Array (Term × Term) ← g.withContext <| scrT.mapM fun p => do
    return (← Lean.Elab.Term.exprToSyntax p.1, ← Lean.Elab.Term.exprToSyntax p.2)
  for (b, ty) in scrTS.reverse do inv ← `(CIR.ScratchSlot $σt $b $ty ∧ $inv)
  for i in (List.range order.size).reverse do
    if kinds[i]! == .iter then inv ← `(CIR.IterSlot $s0t $σt $(blkS[i]!) ∧ $inv)
    else inv ← `(CIR.IntSlot $σt $(blkS[i]!) $(tyS[i]!) ∧ $inv)
  let modsT : Array Term := blkS ++ scrTS.map (·.1)
  inv ← `(CIR.LoopFrame $s0t [$modsT,*] $σt ∧ $inv)
  let invFun ← `(fun ($σt : CIR.State) ($sBinder : $s₂TyS) => $inv)
  let shapeT := mkIdent sT.shape
  let rule ← `(EquivLean.wp_loop_rel ($shapeT $argsTS*) $shape₂ $term₂ (R := fun o₁ o₂ => $k₂S o₂ → $k₁S o₁) $invFun $hsS ?cir_init ?cir_step (fun _ _ hR hK => hR hK))
  if isHolds then evalTactic (← `(tactic| refine EquivLean.Cir.holds_of_wp $rule))
  else evalTactic (← `(tactic| refine $rule))
  -- the iteration: the target's loop-head facts, named as by `cir_loop`
  evalTactic (← `(tactic| case' cir_step => intro $σt:ident $sBinder:ident $(nm "cirH_inv"):ident))
  let mut cur := nm "cirH_inv"
  let mut k := 0
  let rest := nm s!"cirH_rest{k}"; k := k + 1
  let he := nm "cirH_envT"
  let hn := nm "cirH_namesT"
  let hx := nm "cirH_nextT"
  let hf := nm "cirH_frameT"
  evalTactic (← `(tactic| case' cir_step => obtain ⟨⟨$he:ident, $hn:ident, $hx:ident, $hf:ident⟩, $rest:ident⟩ := $cur:ident))
  cur := rest
  for i in [0:order.size] do
    let rest := nm s!"cirH_rest{k}"; k := k + 1
    let hsl := nm s!"cirH_slotT{i}"
    if kinds[i]! == .iter then
      evalTactic (← `(tactic| case' cir_step => obtain ⟨$hsl:ident, $rest:ident⟩ := $cur:ident))
    else
      let hr := nm s!"cirH_rangeT{i}"
      evalTactic (← `(tactic| case' cir_step => obtain ⟨⟨$hsl:ident, $hr:ident⟩, $rest:ident⟩ := $cur:ident))
      evalTactic (← `(tactic| case' cir_step => simp only [CIR.fitsTy, CIR.inRange_eq_true_iff, CIR.intMin_s8, CIR.intMax_s8, CIR.intMin_s16, CIR.intMax_s16, CIR.intMin_s32, CIR.intMax_s32, CIR.intMin_s64, CIR.intMax_s64, CIR.intMin_u, CIR.intMax_u8, CIR.intMax_u16, CIR.intMax_u32, CIR.intMax_u64] at $hr:ident))
    cur := rest
  for j in [0:scrTS.size] do
    let rest := nm s!"cirH_rest{k}"; k := k + 1
    let v := nm s!"cir_scratchT{j}"
    let hsc := nm s!"cirH_scratchT{j}"
    evalTactic (← `(tactic| case' cir_step => obtain ⟨⟨$v:ident, $hsc:ident⟩, $rest:ident⟩ := $cur:ident))
    cur := rest
  let hu := nm "cirH_user"
  evalTactic (← `(tactic| case' cir_step => have $hu:ident := $cur:ident))
  evalTactic (← `(tactic| case' cir_step => clear $cur:ident))
  let hnxT := nm "cirH_nxT"
  evalTactic (← `(tactic| case' cir_step => have $hnxT:ident : $nextT ≤ ($σt:ident).mem.next := $hn0T:ident ▸ $hx:ident))
  -- the variables' values, under the user's names
  for i in [0:order.size] do
    let x := tBinders[i]!
    let hv := nm s!"cirH_val{i}"
    let bi := blkS[i]!
    match kinds[i]! with
    | .iter =>
      let hsl := nm s!"cirH_slotT{i}"
      evalTactic (← `(tactic| case' cir_step => cir_simp_hyp $hsl:ident))
      evalTactic (← `(tactic| case' cir_step => generalize $hv:ident : CIR.State.iterAt $σt:ident $bi = $x:ident at *))
    | .nat =>
      let v := nm s!"cir_v{i}"
      let hxn := nm s!"cir_nat{i}"
      evalTactic (← `(tactic| case' cir_step => generalize $hv:ident : CIR.State.intAt $σt:ident $bi = $v:ident at *))
      evalTactic (← `(tactic| case' cir_step => obtain ⟨$x:ident, $hxn:ident⟩ : ∃ n : Nat, $v:ident = (n : Int) := ⟨($v:ident).toNat, by omega⟩))
      evalTactic (← `(tactic| case' cir_step => simp only [$hxn:ident, Int.toNat_natCast] at $hu:ident))
    | _ =>
      evalTactic (← `(tactic| case' cir_step => generalize $hv:ident : CIR.State.intAt $σt:ident $bi = $x:ident at *))
  evalTactic (← `(tactic| case' cir_step => try dsimp only at $hu:ident))

end EquivLean.Cir.Tactic

namespace EquivLean.Cir

open CIR Lean Meta Simp

theorem find?_rec_cons_false {name : String} (r : RecordDecl) (rs : List RecordDecl)
    (h : (r.name == name) = false) :
    List.find? (·.name == name) (r :: rs) = List.find? (·.name == name) rs := by
  simp [List.find?, h]

theorem typeAt_eq_of_record_eq {ctx₁ ctx₂ : Ctx}
    (h : ∀ name, ctx₁.record? name = ctx₂.record? name) (ty : Ty) (p : List PathElem) :
    ctx₁.typeAt ty p = ctx₂.typeAt ty p := by
  induction p generalizing ty with
  | nil => rfl
  | cons e p ih =>
    cases ty <;> cases e <;> try rfl
    · exact ih _
    · dsimp only [Ctx.typeAt]
      rw [h]
      split <;> try rfl
      split <;> try rfl
      exact ih _

open Lean Meta Elab Tactic in
elab "cir_prove_record_eq" : tactic => withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) do
  evalTactic (← `(tactic| intro $(mkIdent `name):ident))
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← g.withContext do instantiateMVars (← g.getType)).eq?
    | throwError "cir_prove_record_eq: not an equation"
  let ctx1 := lhs.getArg! 0
  let ctx2 := rhs.getArg! 0
  let M1 ← mkAppM ``CIR.Ctx.mod #[ctx1]
  let M2 ← mkAppM ``CIR.Ctx.mod #[ctx2]
  let rs1 ← mkAppM ``CIR.Module.records #[M1]
  let rs2 ← mkAppM ``CIR.Module.records #[M2]
  let some elems1 ← CIR.Tactic.listElems rs1 | throwError "cir_prove_record_eq: records 1 not a list"
  let some elems2 ← CIR.Tactic.listElems rs2 | throwError "cir_prove_record_eq: records 2 not a list"
  let names1 ← elems1.mapM fun e => do
    let some k ← CIR.Tactic.strLit? (← mkAppM ``CIR.RecordDecl.name #[e]) | throwError "not str"
    return k
  let names2 ← elems2.mapM fun e => do
    let some k ← CIR.Tactic.strLit? (← mkAppM ``CIR.RecordDecl.name #[e]) | throwError "not str"
    return k
  if names1 == names2 then
    evalTactic (← `(tactic| rfl))
    return
  let mut sfx := 0
  while sfx < names1.size && sfx < names2.size &&
        names1[names1.size - 1 - sfx]! == names2[names2.size - 1 - sfx]! do
    sfx := sfx + 1
  let n1 := names1.size - sfx
  let n2 := names2.size - sfx
  let mut mapH : Std.HashMap String Ident := {}
  for k in names1.extract 0 n1 ++ names2.extract 0 n2 do
    if mapH.contains k then continue
    let kLit := Syntax.mkStrLit k
    let hi := mkIdent (Name.mkSimple s!"hrec_{mapH.size}")
    mapH := mapH.insert k hi
    evalTactic (← `(tactic| by_cases $hi:ident : ($kLit == $(mkIdent `name):ident) = true))
    evalTactic (← `(tactic| case' pos => rw [beq_iff_eq] at $hi:ident; subst $hi:ident; rfl))
    evalTactic (← `(tactic| rw [Bool.not_eq_true] at $hi:ident))
  let ctx1I := mkIdent ctx1.constName!
  let ctx2I := mkIdent ctx2.constName!
  let mod1I := mkIdent (Name.str ctx1.constName!.getPrefix "module")
  let mod2I := mkIdent (Name.str ctx2.constName!.getPrefix "module")
  evalTactic (← `(tactic| dsimp only [CIR.Ctx.record?, CIR.Module.findRecord?, CIR.Ctx.ofModule, $ctx1I:ident, $ctx2I:ident, $mod1I:ident, $mod2I:ident]))
  for i in [0:n1] do
    let hi := mapH[names1[i]!]!
    let eS := mkIdent elems1[i]!.constName!
    evalTactic (← `(tactic| rw [EquivLean.Cir.find?_rec_cons_false $eS:ident _ $hi:ident]))
  for i in [0:n2] do
    let hi := mapH[names2[i]!]!
    let eS := mkIdent elems2[i]!.constName!
    evalTactic (← `(tactic| rw [EquivLean.Cir.find?_rec_cons_false $eS:ident _ $hi:ident]))
  evalTactic (← `(tactic| rfl))

open Lean Meta Elab Tactic in
elab "cir_typeAt_bridge" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOf ``EquivLean.Sim && t.getAppArgs.size >= 3 do return
    let args := t.getAppArgs
    let tgt := args[args.size - 2]!
    let src := args[args.size - 1]!
    unless tgt.isAppOfArity ``CIR.evalCall 4 && src.isAppOfArity ``CIR.evalCall 4 do return
    let ctxTgt := tgt.getArg! 0
    let ctxSrc := src.getArg! 0
    if ctxTgt == ctxSrc then return
    let ctxTgtS ← Lean.Elab.Term.exprToSyntax ctxTgt
    let ctxSrcS ← Lean.Elab.Term.exprToSyntax ctxSrc
    let _ ← tryTac (evalTactic (← `(tactic|
      have $(mkIdent `cirH_ta):ident : ∀ ty p, ($ctxTgtS).typeAt ty p = ($ctxSrcS).typeAt ty p := by
        apply EquivLean.Cir.typeAt_eq_of_record_eq
        cir_prove_record_eq)))

@[cir_exec] theorem isSome_ite_some_none {α : Type} (c : Bool) (x : α) :
    (if c then some x else none).isSome = c := by
  cases c <;> rfl

theorem runModel_eventBaseLoopbreak (ctx : Ctx) (p : Ptr) (m : Mem) :
    Std.runModel ctx .eventBaseLoopbreak [.ptr p] m =
      match p with
      | .null => Std.retv (.int (-1)) m
      | p =>
        if (Std.libObj? m "event_base" p).isSome then Std.retv (.int 0) m
        else .ub "event_base_loopbreak: not a live event_base" := by
  cases p <;> rfl

@[cir_exec] theorem splitLast_append_singleton (p : List PathElem) (e : PathElem) :
    splitLast (p ++ [e]) = some (p, e) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => rfl
    | cons b p' =>
      change (splitLast (b :: p' ++ [e])).map (fun (pre, l) => (a :: pre, l)) = some (a :: b :: p', e)
      rw [ih]; rfl

@[cir_exec ↓] theorem punnedAccess_record (m : Mem) (name : String) (p : Ptr) :
    m.punnedAccess (.record name) p = false := by
  cases p <;> simp only [Mem.punnedAccess]
  rename_i b path
  cases m.blocks b <;> simp only
  rename_i blk
  cases Ty.atPath blk.ty path <;> rfl

@[cir_exec ↓] theorem punnedMember_record (ctx : Ctx) (m : Mem) (name : String) (p : Ptr) :
    ctx.punnedMember m (.record name) p = false := by
  cases p <;> simp only [Ctx.punnedMember]
  rename_i b path
  cases m.blocks b <;> simp only
  rename_i blk
  cases Ty.atPath blk.ty path <;> simp only
  cases ctx.typeAt blk.ty path <;> rfl

theorem typeAt_eq_atPath_of_records_nil {ctx : Ctx} (h : ctx.mod.records = [])
    (bty : Ty) (path : List PathElem) :
    ctx.typeAt bty path = Ty.atPath bty path := by
  induction path generalizing bty with
  | nil => simp [Ctx.typeAt, Ty.atPath]
  | cons hd tl ih =>
    cases hd <;> cases bty <;> simp [Ctx.typeAt, Ty.atPath, Ctx.record?, Module.findRecord?, h, ih]

theorem punnedMember_of_records_nil {ctx : Ctx} {m : Mem} {ty : Ty} {p : Ptr}
    (h : ctx.mod.records = []) :
    ctx.punnedMember m ty p = false := by
  unfold Ctx.punnedMember
  cases p <;> try rfl
  rename_i b path
  dsimp only
  cases m.blocks b <;> try rfl
  rename_i blk
  dsimp only
  rw [typeAt_eq_atPath_of_records_nil h blk.ty path]
  cases Ty.atPath blk.ty path <;> rfl

simproc ↓ [cir_exec] reducePunnedMemberNoRecords (Ctx.punnedMember _ _ _ _) := fun e => do
  unless e.isAppOfArity ``Ctx.punnedMember 4 do return .continue
  let ctx := e.getArg! 0
  let lhs ← mkAppM ``Module.records #[← mkAppM ``Ctx.mod #[ctx]]
  let recs ← whnfD lhs
  unless recs.isAppOfArity ``List.nil 1 do return .continue
  let h ← mkExpectedTypeHint (← mkEqRefl recs) (← mkEq lhs recs)
  let pf ← mkAppOptM ``punnedMember_of_records_nil
    #[some ctx, some (e.getArg! 1), some (e.getArg! 2), some (e.getArg! 3), some h]
  return .done { expr := mkConst ``Bool.false, proof? := some pf }

simproc ↓ [cir_exec] reduceModCxx (CIR.Module.cxx _) := fun e => do
  unless e.isAppOfArity ``CIR.Module.cxx 1 do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let r ← whnfD e
  unless r.isConstOf ``Bool.true || r.isConstOf ``Bool.false do return .continue
  let pf ← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)
  return .done { expr := r, proof? := some pf }

end EquivLean.Cir
