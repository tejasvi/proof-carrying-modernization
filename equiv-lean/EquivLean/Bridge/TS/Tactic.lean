import EquivLean.Bridge.TS.Terminates

/-!
# StrictTS bridge: tactics for relational proofs

A relational proof between two translated TypeScript functions runs in three steps.

* `ts_start [defs…]` on `Sim R t s` (`t`, `s` closed runs `call …`/`JS.exec …`): moves to the
  weakest-precondition form (`sim_iff_wp`: a hypothesis `hs : wp s Q`, the goal
  `wp t (fun ot => ∃ os, Q os ∧ R ot os)`) and executes both sides symbolically with `ts_sym`
  and the given call lemmas / definitions (`f_call`, `fDef`).  Straight-line code is computed
  away; each side stops at its first loop, as `wp (JS.exec (loop …) w) K` (`wp_exec_match`).
  `equiv_ts [defs…]` does the same for both directions of an `Equiv` goal.
* `ts_lockstep J, R` pairs the target loop of the goal with the source loop of the hypothesis
  `hs` (`while`/`for`, `do … while` or `for … of`, in any combination) by `wp_loop_rel`, with
  the coupling invariant `J` on the loop states and the relation `R` between the loops'
  outcomes.  Loop states are `((i, env), w)` for `for … of` and `(env, w)` for the others.
  Goals: `init` (`J` holds at entry), `step` (one iteration of each loop keeps `J` or both
  leave with outcomes related by `R`: `Sim (StepRel stepCls stepCls R J) …`) and `exit` (the
  code after the loops turns `R`-related outcomes into the final relation).  The source loop
  needs no variant: it terminates whenever it is safe (`forOfTerminates`, …).
* `ts_lockstep_x J, R using sh, tm` pairs a TypeScript loop with a loop of another encoding
  (cross-language migrations; e.g. an Aeneas `loop` with `Aeneas.loop_shape`/`loop_terminates`).
* `ts_step_simp [facts…]` computes one iteration of both loops (`…Step`, `ts_sym`, the number
  bridge for counters, `StepRel`), with `omega` discharging the counter side conditions.
  Leaves are closed by `simp`, `omega`, `bv_decide` (`ts_int32`) or `grind`.
-/

namespace EquivLean.TS
open StrictTS

/-! ## Typed-array reads

The translator types `a[i]` on a numeric typed array as `Expr TT Γ .num`, while the builtin's
own index is `TAKind.elem k`; the two agree only after unfolding `TAKind.elem`, which `simp`
does not do, so the interpreter equation for `.builtin` does not fire.  These lemmas state the
read at index `.num` for every numeric kind (they are part of `ts_step_simp`). -/

section
variable {TT : TypeTable}

theorem evalE_taGet_i8 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .i8, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .i8) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .i8 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofIntN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_u8 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .u8, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .u8) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .u8 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofUintN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_u8c (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .u8c, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .u8c) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .u8c vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofUintN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_i16 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .i16, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .i16) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .i16 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofIntN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_u16 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .u16, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .u16) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .u16 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofUintN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_i32 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .i32, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .i32) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .i32 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofIntN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_u32 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .u32, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .u32) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .u32 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofUintN c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_f32 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .f32, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .f32) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .f32 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofF32Bits c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

theorem evalE_taGet_f64 (I : Impl) (P : Program TT) {Γ : Ctx} (args : Args TT Γ [.tarr .f64, .num])
    (env : Env TT Γ) :
    evalE I P (t := .num) (Expr.builtin (Builtin.taGet .f64) args) env = (do
      let vs ← evalArgs I P args env
      let c ← JS.readTA .f64 vs.a0.tarrAddr
      match JS.index? vs.a1 with
      | some i => if h : i < c.size then pure (Val.num (F64.ofBits c[i]))
                  else JS.panic "typed array index out of bounds"
      | none => JS.panic "typed array read at a non-index key") := by
  rw [evalE.eq_def]; rfl

end

set_option hygiene false in
/-- Start a relational proof of `Sim R t s` between closed TypeScript runs: `sim_iff_wp`, then
symbolic execution of both sides (`ts_sym`, the given lemmas).  Introduces `Q` and the source
hypothesis `hs`. -/
syntax (name := tsStart) "ts_start" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| ts_start) => `(tactic| (
      refine EquivLean.sim_iff_wp.2 fun Q hs => ?_
      simp only [EquivLean.TS.call, ts_sym, EquivLean.TS.wp_exec_match, EquivLean.wp_some]
        at hs ⊢))
  | `(tactic| ts_start [$ls,*]) => `(tactic| (
      refine EquivLean.sim_iff_wp.2 fun Q hs => ?_
      simp only [EquivLean.TS.call, ts_sym, EquivLean.TS.wp_exec_match, EquivLean.wp_some, $ls,*]
        at hs ⊢))

/-- `ts_start` on both directions of an `Equiv` goal (two goals). -/
syntax (name := equivTs) "equiv_ts" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| equiv_ts) => `(tactic| (refine ⟨?_, ?_⟩ <;> ts_start))
  | `(tactic| equiv_ts [$ls,*]) => `(tactic| (refine ⟨?_, ?_⟩ <;> ts_start [$ls,*]))

/-- One iteration of both loops: the step functions, `ts_sym`, the number bridge for natural
number counters (`omega` discharges `i ≤ 2^53`, `i < 2^32 - 1`), `StepRel` and `stepCls`. -/
syntax (name := tsStepSimp) "ts_step_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ts_step_simp) => `(tactic| ts_step_simp [])
  | `(tactic| ts_step_simp [$ls,*]) => `(tactic|
      simp (disch := omega) only [EquivLean.TS.forOfStep, EquivLean.TS.forOfStepWith,
        EquivLean.TS.loopStep, EquivLean.TS.loopStepWith, EquivLean.TS.doStep,
        EquivLean.TS.doStepWith, ts_sym, StrictTS.lt_ofNat, StrictTS.le_ofNat,
        StrictTS.Conv.arrayIndex?_ofNat, StrictTS.ofNat_add_one, StrictTS.F64.lit_eq_ofNat,
        EquivLean.TS.sim_some_some, EquivLean.StepRel, EquivLean.TS.stepCls_inr,
        EquivLean.TS.stepCls_inl, EquivLean.TS.stepCls_error, decide_true, decide_false,
        dite_true, dite_false, and_self, and_true, true_and, Bool.not_true, Bool.not_false,
        EquivLean.TS.evalE_taGet_i8,
        EquivLean.TS.evalE_taGet_u8, EquivLean.TS.evalE_taGet_u8c, EquivLean.TS.evalE_taGet_i16,
        EquivLean.TS.evalE_taGet_u16, EquivLean.TS.evalE_taGet_i32, EquivLean.TS.evalE_taGet_u32,
        EquivLean.TS.evalE_taGet_f32, EquivLean.TS.evalE_taGet_f64, $ls,*])

open Lean Elab Tactic Meta

/-- The `LoopShape`, `Terminates` proof and initial state of a loop run `JS.exec L w`. -/
private def loopParts (L w : Expr) : TacticM (Term × Term × Term) := do
  let args := L.getAppArgs
  let ws ← Term.exprToSyntax w
  if L.isAppOfArity ``StrictTS.evalForOf 10 then
    -- evalForOf {TT} I P {Γ} {ρ} {t} a i body env
    let I ← Term.exprToSyntax args[1]!
    let P ← Term.exprToSyntax args[2]!
    let a ← Term.exprToSyntax args[6]!
    let i ← Term.exprToSyntax args[7]!
    let body ← Term.exprToSyntax args[8]!
    let env ← Term.exprToSyntax args[9]!
    return (← `(EquivLean.TS.forOfShape $I $P $a $body),
      ← `(EquivLean.TS.forOfTerminates $I $P $a $body), ← `((($i, $env), $ws)))
  else if L.isAppOfArity ``StrictTS.evalLoop 9 then
    -- evalLoop {TT} I P {Γ} {ρ} c body step env
    let I ← Term.exprToSyntax args[1]!
    let P ← Term.exprToSyntax args[2]!
    let c ← Term.exprToSyntax args[5]!
    let body ← Term.exprToSyntax args[6]!
    let step ← Term.exprToSyntax args[7]!
    let env ← Term.exprToSyntax args[8]!
    return (← `(EquivLean.TS.loopShape $I $P $c $body $step),
      ← `(EquivLean.TS.loopTerminates $I $P $c $body $step), ← `(($env, $ws)))
  else if L.isAppOfArity ``StrictTS.evalDo 8 then
    -- evalDo {TT} I P {Γ} {ρ} body c env
    let I ← Term.exprToSyntax args[1]!
    let P ← Term.exprToSyntax args[2]!
    let body ← Term.exprToSyntax args[5]!
    let c ← Term.exprToSyntax args[6]!
    let env ← Term.exprToSyntax args[7]!
    return (← `(EquivLean.TS.doShape $I $P $body $c),
      ← `(EquivLean.TS.doTerminates $I $P $body $c), ← `(($env, $ws)))
  else
    throwError "ts_lockstep: not a loop run (evalForOf / evalLoop / evalDo): {L}"

/-- `wp (JS.exec L w) K` with `L` a loop: return `L` and `w`. -/
private def wpLoopRun? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  unless e.isAppOfArity ``EquivLean.wp 5 do return none
  -- @wp C O inst c Q
  let c := e.getAppArgs[3]!.cleanupAnnotations
  unless c.isAppOfArity ``StrictTS.JS.exec 4 do return none
  let L := (c.getArg! 2).cleanupAnnotations
  if L.isAppOf ``StrictTS.evalForOf || L.isAppOf ``StrictTS.evalLoop || L.isAppOf ``StrictTS.evalDo then
    return some (L, c.getArg! 3)
  return none

/-- `ts_lockstep J, R`: pair the loop at the head of the goal (target) with the loop at the head
of the source hypothesis (`hs`, or the first hypothesis of the form `wp (JS.exec loop w) K`)
by `wp_loop_rel`, with coupling invariant `J` and loop-outcome relation `R`.  Goals: `init`,
`step`, `exit`. -/
elab "ts_lockstep " J:term ", " R:term : tactic => withMainContext do
  let some (L₁, w₁) ← wpLoopRun? (← getMainTarget)
    | throwError "ts_lockstep: the goal is not `wp (JS.exec loop w) K`"
  let lctx ← getLCtx
  let mut src : Option (Name × Expr × Expr) := none
  for d in lctx do
    if d.isImplementationDetail then continue
    if let some (L₂, w₂) ← wpLoopRun? d.type then
      if src.isNone || d.userName == `hs then src := some (d.userName, L₂, w₂)
  let some (hn, L₂, w₂) := src
    | throwError "ts_lockstep: no source hypothesis `wp (JS.exec loop w) K`"
  let (sh₁, _, st₁) ← loopParts L₁ w₁
  let (sh₂, tm₂, st₂) ← loopParts L₂ w₂
  let h := mkIdent hn
  evalTactic (← `(tactic|
    refine EquivLean.wp_loop_rel $sh₁ $sh₂ $tm₂ (R := $R) $J (s₁ := $st₁) (s₂ := $st₂) $h
      ?init ?step ?exit))

/-- `wp c K` with an arbitrary computation `c` (the other encoding's loop): return `c`. -/
private def wpComp? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  unless e.isAppOfArity ``EquivLean.wp 5 do return none
  return some e.getAppArgs[3]!

/-- The implementation of `ts_lockstep_x`. -/
private def lockstepX (J R sh : Term) (tm? : Option Term) : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  let mut hsrc : Option Name := none
  for d in lctx do
    if d.isImplementationDetail then continue
    if (← wpComp? d.type).isSome && d.userName == `hs then hsrc := some d.userName
  let some hn := hsrc | throwError "ts_lockstep_x: no source hypothesis `hs : wp s K`"
  let h := mkIdent hn
  if let some (L₁, w₁) ← wpLoopRun? (← getMainTarget) then
    let some tm := tm? | throwError "ts_lockstep_x: the source loop needs its Terminates proof"
    let (sh₁, _, st₁) ← loopParts L₁ w₁
    evalTactic (← `(tactic|
      refine EquivLean.wp_loop_rel $sh₁ $sh $tm (R := $R) $J (s₁ := $st₁) (s₂ := _) $h
        ?init ?step ?exit))
  else
    let some d := lctx.findFromUserName? hn | throwError "ts_lockstep_x: no hypothesis {hn}"
    let some (L₂, w₂) ← wpLoopRun? d.type
      | throwError "ts_lockstep_x: neither the goal nor `hs` is headed by a TypeScript loop"
    let (sh₂, tm₂, st₂) ← loopParts L₂ w₂
    evalTactic (← `(tactic|
      refine EquivLean.wp_loop_rel $sh $sh₂ $tm₂ (R := $R) $J (s₁ := _) (s₂ := $st₂) $h
        ?init ?step ?exit))

/-- `ts_lockstep_x J, R using sh (, tm)?`: lockstep of a TypeScript loop with a loop of another
encoding (e.g. an Aeneas `loop`, `sh := EquivLean.Aeneas.loop_shape _`,
`tm := EquivLean.Aeneas.loop_terminates _`).  If the head of the goal is a TypeScript loop, it
is the target and the other loop (the head of `hs`) the source, whose `LoopShape` is `sh` and
whose termination proof is `tm`; otherwise the TypeScript loop at the head of `hs` is the
source and the goal's loop, with `LoopShape` `sh`, the target (`tm` is not needed).  The other
loop's state is found by unification.  Goals: `init`, `step`, `exit`. -/
syntax (name := tsLockstepX) "ts_lockstep_x " term ", " term " using " term (", " term)? : tactic

elab_rules : tactic
  | `(tactic| ts_lockstep_x $J, $R using $sh) => lockstepX J R sh none
  | `(tactic| ts_lockstep_x $J, $R using $sh, $tm) => lockstepX J R sh (some tm)

end EquivLean.TS
