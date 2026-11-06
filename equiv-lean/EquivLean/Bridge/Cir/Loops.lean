import EquivLean.Bridge.Cir.Behaves
import EquivLean.Core.Loop
import EquivLean.Tactic.LoopAttr

/-!
# cirlean bridge: loops

cirlean unfolds each structured loop into one non-recursive iteration and a continuation
(`CIR/Logic/Loops.lean`):

    evalFor ctx c b s cl σ = forIter ctx c b s cl σ >>= loopCont (evalFor ctx c b s cl)

with `forIter : State → Res (Sum (Step × State) State)` (`.inl r`: the loop ends with
`r`, `.inr σ'`: next iteration).  The same holds for `evalWhile`/`whileIter` and
`evalDo`/`doIter`.  Each is a `LoopShape` with the identity classification `loopCls`.
The shapes and the termination theorems are registered in the loop-shape database
(`@[equiv_loop_shape]`, `@[equiv_loop_term]`), so `equiv_loop_auto` pairs CIR loops with the
loops of any other registered encoding.
-/

namespace EquivLean.Cir

open CIR

/-- The classification of a CIR iteration result: it is already a `Sum`. -/
abbrev loopCls {α σ : Type} : Sum α σ → α ⊕ σ := id

/-- Any loop with cirlean's unfolding equation is a `LoopShape`. -/
theorem loopShape_of_unfold {α : Type} {iter : State → Res (Sum α State)} {loop : State → Res α}
    (hunfold : ∀ σ, loop σ = iter σ >>= loopCont loop) : LoopShape loop iter loopCls where
  safe_iff σ := by
    rw [hunfold σ]
    cases h : iter σ with
    | ok r =>
      cases r with
      | inl a =>
        simp only [loopCont, Res.ok_bind, safe_res, runs_res, Res.pure_eq, Res.ok.injEq]
        refine ⟨fun _ => ⟨⟨_, rfl⟩, fun r s' hr hc => ?_⟩, fun _ => ⟨a, rfl⟩⟩
        subst hr; cases hc
      | inr σ' =>
        simp only [loopCont, Res.ok_bind, safe_res, runs_res, Res.ok.injEq]
        refine ⟨fun hs => ⟨⟨_, rfl⟩, fun r s' hr hc => ?_⟩, fun h => h.2 _ _ rfl rfl⟩
        subst hr; cases hc; exact hs
    | ub m => simp [Res.ub_bind]
    | div => simp [Res.div_bind]
  runs_iff σ o := by
    rw [hunfold σ]
    cases h : iter σ with
    | ok r =>
      cases r with
      | inl a => simp [loopCont, Res.ok_bind, eq_comm]
      | inr σ' => simp [loopCont, Res.ok_bind]
    | ub m => simp [Res.ub_bind]
    | div => simp [Res.div_bind]

theorem loopShape_for (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region)) :
    LoopShape (evalFor ctx c b s cl) (forIter ctx c b s cl) loopCls :=
  loopShape_of_unfold (evalFor_unfold ctx c b s cl)

theorem loopShape_while (ctx : Ctx) (c b : Region) (cl : Option (CleanupKind × Region)) :
    LoopShape (evalWhile ctx c b cl) (whileIter ctx c b cl) loopCls :=
  loopShape_of_unfold (evalWhile_unfold ctx c b cl)

theorem loopShape_do (ctx : Ctx) (b c : Region) :
    LoopShape (evalDo ctx b c) (doIter ctx b c) loopCls :=
  loopShape_of_unfold (evalDo_unfold ctx b c)

end EquivLean.Cir

/-! ### Termination of safe loops

`LoopShape.Terminates`: a loop that runs to an `ok` result iterates finitely often.  The loop
functions are components of cirlean's single mutual `partial_fixpoint` block
`evalOps.mutual ctx = Lean.Order.fix F hF` (12 functions, flat order on `Res`).  We name `F`
(`evalF`), and prove by `Lean.Order.fix_induct` the admissible property

    x ⊑ evalOps.mutual ctx  ∧  (x.for σ = ok r → Acc Next σ)  ∧ … (while, do, and the
                                 auxiliary `forStep`/`doCond` functions)

The first conjunct transfers the `ok` results of the approximation's regions to the real
`evalRegion`, in terms of which `Next` (one real iteration) is stated.
-/

namespace EquivLean.Cir

open CIR Lean Order

open Lean Meta Elab Command in
/-- Names the functional of cirlean's mutual `partial_fixpoint` block:
`evalOps.mutual ctx = Lean.Order.fix (evalF ctx) (evalF_mono ctx)`. -/
elab "cir_name_functional%" : command => liftTermElabM do
  let info ← getConstInfo ``CIR.evalOps.mutual
  let .defnInfo d := info | throwError "evalOps.mutual is not a definition"
  let (F, hF, T, I) ← lambdaTelescope d.value fun xs body => do
    unless body.isAppOfArity ``Lean.Order.fix 4 do throwError "evalOps.mutual: unexpected form"
    let args := body.getAppArgs
    return (← mkLambdaFVars xs args[2]!, ← mkLambdaFVars xs args[3]!, args[0]!, args[1]!)
  let Tty ← inferType T
  addDecl (.defnDecl { name := `EquivLean.Cir.EvalFuns, levelParams := [], type := Tty, value := T, hints := .abbrev, safety := .safe })
  setReducibilityStatus `EquivLean.Cir.EvalFuns .reducible
  let Ity ← inferType I
  addDecl (.defnDecl { name := `EquivLean.Cir.instCCPOEvalFuns, levelParams := [], type := Ity, value := I, hints := .abbrev, safety := .safe })
  setReducibilityStatus `EquivLean.Cir.instCCPOEvalFuns .reducible
  addInstance `EquivLean.Cir.instCCPOEvalFuns .global 2000
  let Fty ← inferType F
  addDecl (.defnDecl { name := `EquivLean.Cir.evalF, levelParams := [], type := Fty, value := F, hints := .regular 0, safety := .safe })
  let hFty ← inferType hF
  addDecl (.thmDecl { name := `EquivLean.Cir.evalF_mono, levelParams := [], type := hFty, value := hF })

cir_name_functional%



theorem evalOps_mutual_eq (ctx : Ctx) :
    evalOps.mutual ctx = Lean.Order.fix (evalF ctx) (evalF_mono ctx) := rfl

theorem evalRegion_def (ctx : Ctx) : evalRegion ctx = (evalOps.mutual ctx).2.2.2.1 := by
  with_unfolding_all rfl
theorem evalIterCleanup_def (ctx : Ctx) :
    evalIterCleanup ctx = (evalOps.mutual ctx).2.2.2.2.2.2.2.2.1 := by with_unfolding_all rfl
theorem evalFor_def (ctx : Ctx) :
    evalFor ctx = (evalOps.mutual ctx).2.2.2.2.2.2.2.2.2.1 := by with_unfolding_all rfl
theorem evalForStep_def (ctx : Ctx) :
    evalForStep ctx = (evalOps.mutual ctx).2.2.2.2.2.2.2.2.2.2.1 := by with_unfolding_all rfl
theorem evalWhile_def (ctx : Ctx) :
    evalWhile ctx = (evalOps.mutual ctx).2.2.2.2.2.2.2.1 := by with_unfolding_all rfl
theorem evalDo_def (ctx : Ctx) : evalDo ctx = (evalOps.mutual ctx).2.2.2.2.2.1 := by
  with_unfolding_all rfl
theorem evalDoCond_def (ctx : Ctx) : evalDoCond ctx = (evalOps.mutual ctx).2.2.2.2.2.2.1 := by
  with_unfolding_all rfl

theorem res_le_ok {α : Type} {a b : Res α} (h : a ⊑ b) {v : α} (ha : a = .ok v) : b = .ok v := by
  change FlatOrder.rel a b at h
  cases h with
  | bot => cases ha
  | refl => exact ha

open Lean Meta Elab Tactic in
/-- On `admissible (fun x => B)` where `x : α ×' β` occurs in `B` only under one projection,
apply `admissible_pprod_fst`/`_snd`. -/
elab "cir_adm_proj" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  let_expr Lean.Order.admissible _ inst P := t | throwError "cir_adm_proj: not an admissibility goal"
  let .lam n ty body bi := P | throwError "cir_adm_proj: the predicate is not a lambda"
  let inst ← whnfR inst
  let (ia?, ib?) := match_expr inst with
    | Lean.Order.instCCPOPProd _ _ ia ib => (some ia, some ib)
    | _ => (none, none)
  withLocalDecl n bi ty fun x => do
    let B := body.instantiate1 x
    let isProj (fld : Nat) (e : Expr) : Bool := match e with
      | .proj _ i s => i == fld && s == x
      | _ => (fld == 1 && e.isAppOfArity ``PProd.snd 3 && e.appArg! == x) ||
             (fld == 0 && e.isAppOfArity ``PProd.fst 3 && e.appArg! == x)
    for fld in [1, 0] do
      let some sub := B.find? (isProj fld) | continue
      let yTy ← inferType sub
      let Q? ← withLocalDecl `y .default yTy fun y => do
        let B' := B.replace fun e => if isProj fld e then some y else none
        if B'.containsFVar x.fvarId! then return none
        return some (← mkLambdaFVars #[y] B')
      let some Q := Q? | continue
      let lem := if fld == 1 then ``Lean.Order.admissible_pprod_snd else ``Lean.Order.admissible_pprod_fst
      let pf ← mkAppOptM lem #[none, none, ia?, ib?, some Q]
      let gs ← g.apply pf
      replaceMainGoal gs
      return
    throwError "cir_adm_proj: the variable occurs outside a projection"

open Lean Meta Elab Tactic in
/-- On `admissible (fun f => ∀ x, B)` where `f` occurs in `B` only applied to `x`, apply
`admissible_pi_apply` and introduce `x`. -/
elab "cir_adm_pi" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  let_expr Lean.Order.admissible _ _ P := t | throwError "cir_adm_pi: not an admissibility goal"
  let .lam n ty body bi := P | throwError "cir_adm_pi: the predicate is not a lambda"
  let Q ← withLocalDecl n bi ty fun f => do
    let .forallE xn xty xbody xbi := body.instantiate1 f | throwError "cir_adm_pi: not a ∀"
    withLocalDecl xn xbi xty fun x => do
      let B := xbody.instantiate1 x
      let fx := mkApp f x
      let vTy ← inferType fx
      withLocalDecl `v .default vTy fun v => do
        let B' := B.replace fun e => if e == fx then some v else none
        if B'.containsFVar f.fvarId! then throwError "cir_adm_pi: f occurs outside f x"
        mkLambdaFVars #[x, v] B'
  let pf ← mkAppOptM ``Lean.Order.admissible_pi_apply #[none, none, none, some Q]
  let gs ← g.apply pf
  replaceMainGoal gs
  evalTactic (← `(tactic| intro))

/-- `admissible (fun f => ∀ args, ∀ r, f args = ok r → A args)`. -/
macro "cir_adm_flat" : tactic => `(tactic| (
  repeat cir_adm_pi
  refine Lean.Order.admissible_flatOrder (b := CIR.Res.div) _ ?_
  intro r h; cases h))

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1000000

def Pfor (ctx : Ctx) (x : EvalFuns) : Prop :=
  ∀ c b s cl σ r, x.2.2.2.2.2.2.2.2.2.1 c b s cl σ = Res.ok r →
    Acc (LoopShape.Next (forIter ctx c b s cl) loopCls) σ

theorem adm_Pfor (ctx : Ctx) : admissible (Pfor ctx) := by
  unfold Pfor
  repeat cir_adm_proj
  cir_adm_flat

def PforStep (ctx : Ctx) (x : EvalFuns) : Prop :=
  ∀ c b s cl σ r, x.2.2.2.2.2.2.2.2.2.2.1 c b s cl σ = Res.ok r →
    ∀ σ', forIter.forStepIter ctx s cl σ = Res.ok (.inr σ') →
      Acc (LoopShape.Next (forIter ctx c b s cl) loopCls) σ'

def Pwhile (ctx : Ctx) (x : EvalFuns) : Prop :=
  ∀ c b cl σ r, x.2.2.2.2.2.2.2.1 c b cl σ = Res.ok r →
    Acc (LoopShape.Next (whileIter ctx c b cl) loopCls) σ

def Pdo (ctx : Ctx) (x : EvalFuns) : Prop :=
  ∀ b c σ r, x.2.2.2.2.2.1 b c σ = Res.ok r → Acc (LoopShape.Next (doIter ctx b c) loopCls) σ

def PdoCond (ctx : Ctx) (x : EvalFuns) : Prop :=
  ∀ b c σ r, x.2.2.2.2.2.2.1 b c σ = Res.ok r →
    ∀ σ', doIter.doCondIter ctx c σ = Res.ok (.inr σ') →
      Acc (LoopShape.Next (doIter ctx b c) loopCls) σ'

theorem region_ok {ctx : Ctx} {x : EvalFuns} (hle : x ⊑ evalOps.mutual ctx) {r : Region}
    {args : List Val} {σ : State} {v : Exit × State} (h : x.2.2.2.1 r args σ = .ok v) :
    evalRegion ctx r args σ = .ok v := by
  rw [evalRegion_def]; exact res_le_ok (hle.2.2.2.1 r args σ) h

theorem cleanup_ok {ctx : Ctx} {x : EvalFuns} (hle : x ⊑ evalOps.mutual ctx)
    {cl : Option (CleanupKind × Region)} {e : Bool} {σ v : State}
    (h : x.2.2.2.2.2.2.2.2.1 cl e σ = .ok v) : evalIterCleanup ctx cl e σ = .ok v := by
  rw [evalIterCleanup_def]; exact res_le_ok (hle.2.2.2.2.2.2.2.2.1 cl e σ) h

theorem next_iff {α : Type} {iter : State → Res (Sum α State)} {σ' σ : State} :
    LoopShape.Next iter loopCls σ' σ ↔ iter σ = .ok (.inr σ') := by
  constructor
  · rintro ⟨r, hr, hc⟩
    simp only [loopCls, id] at hc; subst hc; exact hr
  · intro h; exact ⟨_, h, rfl⟩

theorem step_for (ctx : Ctx) (x : EvalFuns) (hle : x ⊑ evalOps.mutual ctx)
    (hstep : PforStep ctx x) : Pfor ctx (evalF ctx x) := by
  intro c b s cl σ r h
  dsimp only [evalF, loopHead] at h
  obtain ⟨⟨ec, σ1⟩, h1, h2⟩ := Res.bind_eq_ok.mp h
  have e1 := region_ok hle h1
  refine Acc.intro σ fun σ' hn => ?_
  rw [next_iff, forIter, e1, Res.ok_bind] at hn
  dsimp only at h2 hn
  cases ec with
  | cond bv =>
    cases bv with
    | false => simp [Res.bind_eq_ok] at hn
    | true =>
      obtain ⟨⟨eb, σ2⟩, h3, h4⟩ := Res.bind_eq_ok.mp h2
      have e3 := region_ok hle h3
      rw [e3, Res.ok_bind] at hn
      dsimp only at h4 hn
      cases eb with
      | yield vs =>
        cases vs with
        | nil => exact hstep c b s cl σ2 r h4 σ' hn
        | cons _ _ => simp at hn
      | cont => exact hstep c b s cl σ2 r h4 σ' hn
      | _ => simp [Res.bind_eq_ok] at hn
  | exn x => cases cl <;> simp at hn
  | _ => simp at hn

theorem step_forStep (ctx : Ctx) (x : EvalFuns) (hle : x ⊑ evalOps.mutual ctx)
    (hfor : Pfor ctx x) : PforStep ctx (evalF ctx x) := by
  intro c b s cl σ r h σ' hn
  dsimp only [evalF, loopHead] at h
  obtain ⟨⟨es, σ1⟩, h1, h2⟩ := Res.bind_eq_ok.mp h
  have e1 := region_ok hle h1
  rw [forIter.forStepIter, e1, Res.ok_bind] at hn
  dsimp only at h2 hn
  cases es with
  | yield vs =>
    cases vs with
    | nil =>
      obtain ⟨σ2, h3, h4⟩ := Res.bind_eq_ok.mp h2
      have e3 := cleanup_ok hle h3
      rw [e3] at hn
      simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq, Sum.inr.injEq] at hn
      subst hn
      exact hfor c b s cl σ2 r h4
    | cons _ _ => simp at hn
  | exn x => simp [Res.bind_eq_ok] at hn
  | _ => simp at hn

theorem step_while (ctx : Ctx) (x : EvalFuns) (hle : x ⊑ evalOps.mutual ctx)
    (hwhile : Pwhile ctx x) : Pwhile ctx (evalF ctx x) := by
  intro c b cl σ r h
  dsimp only [evalF, loopHead] at h
  obtain ⟨⟨ec, σ1⟩, h1, h2⟩ := Res.bind_eq_ok.mp h
  have e1 := region_ok hle h1
  refine Acc.intro σ fun σ' hn => ?_
  rw [next_iff, whileIter, e1, Res.ok_bind] at hn
  dsimp only at h2 hn
  cases ec with
  | cond bv =>
    cases bv with
    | false => simp [Res.bind_eq_ok] at hn
    | true =>
      obtain ⟨⟨eb, σ2⟩, h3, h4⟩ := Res.bind_eq_ok.mp h2
      have e3 := region_ok hle h3
      rw [e3, Res.ok_bind] at hn
      dsimp only at h4 hn
      cases eb with
      | yield vs =>
        cases vs with
        | nil =>
          obtain ⟨σ3, h5, h6⟩ := Res.bind_eq_ok.mp h4
          rw [cleanup_ok hle h5] at hn
          simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq, Sum.inr.injEq] at hn
          subst hn
          exact hwhile c b cl σ3 r h6
        | cons _ _ => simp at hn
      | cont =>
        obtain ⟨σ3, h5, h6⟩ := Res.bind_eq_ok.mp h4
        rw [cleanup_ok hle h5] at hn
        simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq, Sum.inr.injEq] at hn
        subst hn
        exact hwhile c b cl σ3 r h6
      | _ => simp [Res.bind_eq_ok] at hn
  | exn x => cases cl <;> simp at hn
  | _ => simp at hn

theorem step_do (ctx : Ctx) (x : EvalFuns) (hle : x ⊑ evalOps.mutual ctx)
    (hcond : PdoCond ctx x) : Pdo ctx (evalF ctx x) := by
  intro b c σ r h
  dsimp only [evalF, loopHead] at h
  obtain ⟨⟨eb, σ1⟩, h1, h2⟩ := Res.bind_eq_ok.mp h
  have e1 := region_ok hle h1
  refine Acc.intro σ fun σ' hn => ?_
  rw [next_iff, doIter, e1, Res.ok_bind] at hn
  dsimp only at h2 hn
  cases eb with
  | yield vs =>
    cases vs with
    | nil => exact hcond b c σ1 r h2 σ' hn
    | cons _ _ => simp at hn
  | cont => exact hcond b c σ1 r h2 σ' hn
  | _ => simp at hn

theorem step_doCond (ctx : Ctx) (x : EvalFuns) (hle : x ⊑ evalOps.mutual ctx)
    (hdo : Pdo ctx x) : PdoCond ctx (evalF ctx x) := by
  intro b c σ r h σ' hn
  dsimp only [evalF, loopHead] at h
  obtain ⟨⟨ec, σ1⟩, h1, h2⟩ := Res.bind_eq_ok.mp h
  have e1 := region_ok hle h1
  rw [doIter.doCondIter, e1, Res.ok_bind] at hn
  dsimp only at h2 hn
  cases ec with
  | cond bv =>
    cases bv with
    | true =>
      simp only [Res.pure_eq, Res.ok.injEq, Sum.inr.injEq] at hn
      subst hn
      exact hdo b c σ1 r h2
    | false => simp at hn
  | exn x => simp at hn
  | _ => simp at hn

theorem adm_le (y : EvalFuns) : admissible (fun x : EvalFuns => x ⊑ y) :=
  fun _ hc h => csup_le hc h

theorem adm_PforStep (ctx : Ctx) : admissible (PforStep ctx) := by
  unfold PforStep; repeat cir_adm_proj
  cir_adm_flat
theorem adm_Pwhile (ctx : Ctx) : admissible (Pwhile ctx) := by
  unfold Pwhile; repeat cir_adm_proj
  cir_adm_flat
theorem adm_Pdo (ctx : Ctx) : admissible (Pdo ctx) := by
  unfold Pdo; repeat cir_adm_proj
  cir_adm_flat
theorem adm_PdoCond (ctx : Ctx) : admissible (PdoCond ctx) := by
  unfold PdoCond; repeat cir_adm_proj
  cir_adm_flat

/-- Fixpoint induction over cirlean's interpreter: every safe run of a loop iterates finitely
often. -/
theorem loops_wf (ctx : Ctx) :
    Pfor ctx (evalOps.mutual ctx) ∧ Pwhile ctx (evalOps.mutual ctx) ∧ Pdo ctx (evalOps.mutual ctx) := by
  have h := Lean.Order.fix_induct (evalF_mono ctx)
    (fun x => x ⊑ evalOps.mutual ctx ∧ Pfor ctx x ∧ PforStep ctx x ∧ Pwhile ctx x ∧ Pdo ctx x ∧
      PdoCond ctx x)
    (admissible_and _ _ (adm_le _) (admissible_and _ _ (adm_Pfor ctx) (admissible_and _ _
      (adm_PforStep ctx) (admissible_and _ _ (adm_Pwhile ctx) (admissible_and _ _ (adm_Pdo ctx)
      (adm_PdoCond ctx))))))
    (fun x ⟨hle, hf, hfs, hw, hd, hdc⟩ =>
      ⟨PartialOrder.rel_trans (evalF_mono ctx _ _ hle)
          (PartialOrder.rel_of_eq (Lean.Order.fix_eq (evalF_mono ctx)).symm),
        step_for ctx x hle hfs, step_forStep ctx x hle hf, step_while ctx x hle hw,
        step_do ctx x hle hdc, step_doCond ctx x hle hd⟩)
  exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩


theorem terminates_for (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region)) :
    LoopShape.Terminates (evalFor ctx c b s cl) (forIter ctx c b s cl) loopCls := by
  intro σ hs
  obtain ⟨r, hr⟩ := (safe_res _).1 hs
  rw [evalFor_def] at hr
  exact (loops_wf ctx).1 c b s cl σ r hr

theorem terminates_while (ctx : Ctx) (c b : Region) (cl : Option (CleanupKind × Region)) :
    LoopShape.Terminates (evalWhile ctx c b cl) (whileIter ctx c b cl) loopCls := by
  intro σ hs
  obtain ⟨r, hr⟩ := (safe_res _).1 hs
  rw [evalWhile_def] at hr
  exact (loops_wf ctx).2.1 c b cl σ r hr

theorem terminates_do (ctx : Ctx) (b c : Region) :
    LoopShape.Terminates (evalDo ctx b c) (doIter ctx b c) loopCls := by
  intro σ hs
  obtain ⟨r, hr⟩ := (safe_res _).1 hs
  rw [evalDo_def] at hr
  exact (loops_wf ctx).2.2 b c σ r hr

attribute [equiv_loop_shape] loopShape_for loopShape_while loopShape_do
attribute [equiv_loop_term] terminates_for terminates_while terminates_do

end EquivLean.Cir
