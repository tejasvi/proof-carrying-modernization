import EquivLean.Bridge.TS.Loops

/-!
# StrictTS bridge: loops terminate whenever they are safe

`LoopShape.Terminates` for `while`/`for` (`evalLoop`), `do … while` (`evalDo`),
`for (const x of arr)` (`evalForOf`) and the iterations over `Map`s, `Set`s and strings
(`evalForOfMap`, `evalForOfSet`, `evalForOfStr`): a loop run that finishes (`JS.exec … = some _`)
iterates finitely often, i.e. its start state is accessible for the "one more iteration"
relation `LoopShape.Next` of the real interpreter.  With these, the lockstep rules
`sim_loop_of_terminates`/`wp_loop_rel` need no variant: the source loop's safety bounds the
number of iterations.

**Proof.**  The interpreter is one mutual `partial_fixpoint`,
`StrictTS.evalE.mutual I P = Lean.Order.fix F hF` over a `PProd` of 26 function spaces
(each loop function is a projection of it).  `ts_extract_mutual_fixpoint` reads the domain
`MutT`, its CCPO instance `mutInst` and the functional `mutF` off the definition of
`evalE.mutual` (they are far too large to write down), so `mut_eq_fix` holds by `rfl`.
Fixpoint induction (`Lean.Order.fix_induct`) then proves, for every approximant `x` of the
fixpoint,

    x ⊑ fix ∧ ForOfAcc (x's evalForOf) ∧ DoAcc (x's evalDo) ∧ LoopAcc (x's evalLoop)

where `ForOfAcc f` says: every terminating run of `f` starts in a state accessible for the
real loop's `Next` (`loops_acc`; `iters_acc` is the same induction for the three iterations).  The step unfolds `mutF x` definitionally into the copies
`forOfBodyWith`/`doBodyWith`/`loopBodyWith` of `Loops.lean`, splits off one iteration
(`exec_…BodyWith`), and transfers that iteration to the real interpreter by monotonicity in
the flat order (`x ⊑ fix` on the `evalE`/`evalB` components; `…StepWith_mono`).
Admissibility is proved through the projections and arguments explicitly
(`adm_proj_…`, `admissible_…Acc`, `admissible_exec`).
-/

-- the CCPO instances of the interpreter's function types are deeply nested `instCCPOPi`s
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace EquivLean.TS
open StrictTS

open Lean Meta Elab Command in
/-- Define `MutT`, `mutInst` and `mutF`: the domain, its CCPO instance and the functional of
the interpreter's mutual `partial_fixpoint` (`StrictTS.evalE.mutual = Lean.Order.fix mutF _`),
read off the definition of `evalE.mutual` (they are far too large to write by hand). -/
elab "ts_extract_mutual_fixpoint" : command => liftTermElabM do
  let info ← getConstInfoDefn ``StrictTS.evalE.mutual
  unless info.levelParams.isEmpty do throwError "unexpected universe parameters"
  let (tyV, instV, FV) ← lambdaTelescope info.value fun xs body => do
    unless body.isAppOfArity ``Lean.Order.fix 4 do throwError "evalE.mutual is not a Lean.Order.fix"
    unless xs.size == 3 do throwError "unexpected binders"
    let TT := xs[0]!
    let α := body.getArg! 0
    let inst := body.getArg! 1
    let F := body.getArg! 2
    let tyV ← mkLambdaFVars #[TT] α
    let instV ← mkLambdaFVars #[TT] inst
    let FV ← mkLambdaFVars xs F
    if tyV.hasFVar || instV.hasFVar || FV.hasFVar then throwError "unexpected free variables"
    pure (tyV, instV, FV)
  let tyT ← inferType tyV
  addDecl <| .defnDecl <| mkDefinitionValEx `EquivLean.TS.MutT [] tyT tyV
    ReducibilityHints.abbrev .safe [`EquivLean.TS.MutT]
  setReducibleAttribute `EquivLean.TS.MutT
  let instT ← inferType instV
  addDecl <| .defnDecl <| mkDefinitionValEx `EquivLean.TS.mutInst [] instT instV
    ReducibilityHints.abbrev .safe [`EquivLean.TS.mutInst]
  setReducibleAttribute `EquivLean.TS.mutInst
  let FT ← inferType FV
  addDecl <| .defnDecl <| mkDefinitionValEx `EquivLean.TS.mutF [] FT FV
    (ReducibilityHints.regular 0) .safe [`EquivLean.TS.mutF]

ts_extract_mutual_fixpoint

/-- The interpreter's mutual definition is the least fixpoint of `mutF`. -/
theorem mut_eq_fix {TT : TypeTable} (I : Impl) (P : Program TT) :
    ∃ hF, evalE.mutual I P = @Lean.Order.fix (MutT (TT := TT)) (mutInst (TT := TT)) (mutF I P) hF :=
  ⟨_, rfl⟩

/-! ## Order-theoretic helpers (instances are unified, never synthesized) -/

section order
open Lean.Order

theorem adm_pprod_fst {α β : Sort _} {iα : CCPO α} {iβ : CCPO β} (P : α → Prop)
    (h : @admissible α iα P) : @admissible (α ×' β) (@instCCPOPProd α β iα iβ) (fun x => P x.1) :=
  @admissible_pprod_fst α β iα iβ P h

theorem adm_pprod_snd {α β : Sort _} {iα : CCPO α} {iβ : CCPO β} (P : β → Prop)
    (h : @admissible β iβ P) : @admissible (α ×' β) (@instCCPOPProd α β iα iβ) (fun x => P x.2) :=
  @admissible_pprod_snd α β iα iβ P h

theorem adm_pi_apply {α : Sort _} {β : α → Sort _} {i : ∀ x, CCPO (β x)} (P : ∀ x, β x → Prop)
    (h : ∀ x, @admissible (β x) (i x) (P x)) :
    @admissible (∀ x, β x) (@instCCPOPi α β i) (fun f => ∀ x, P x (f x)) :=
  @admissible_pi_apply α β i P h

theorem adm_and {α : Sort _} {i : CCPO α} (P Q : α → Prop) (hP : @admissible α i P)
    (hQ : @admissible α i Q) : @admissible α i (fun x => P x ∧ Q x) :=
  @admissible_and α i P Q hP hQ

theorem rel_pprod_fst {α β : Sort _} {iα : PartialOrder α} {iβ : PartialOrder β} {a b : α ×' β}
    (h : @PartialOrder.rel (α ×' β) (@instPartialOrderPProd α β iα iβ) a b) :
    @PartialOrder.rel α iα a.1 b.1 := h.1

theorem rel_pprod_snd {α β : Sort _} {iα : PartialOrder α} {iβ : PartialOrder β} {a b : α ×' β}
    (h : @PartialOrder.rel (α ×' β) (@instPartialOrderPProd α β iα iβ) a b) :
    @PartialOrder.rel β iβ a.2 b.2 := h.2

theorem option_rel_some {α : Type} {a : α} {o : Option α} (h : PartialOrder.rel (some a) o) :
    o = some a := by
  cases h; rfl

end order

variable {TT : TypeTable}

theorem js_rel_exec {X : Type} {m₁ m₂ : JS TT X} (h : Lean.Order.PartialOrder.rel m₁ m₂) {w : World TT}
    {r : Out TT X} (h1 : JS.exec m₁ w = some r) : JS.exec m₂ w = some r :=
  option_rel_some (h1 ▸ h w)

/-- The last two levels of every termination predicate: a computation run on a world. -/
theorem admissible_exec {X : Type} (R : World TT → Prop) :
    Lean.Order.admissible (fun g : JS TT X => ∀ w y, JS.exec g w = some y → R w) :=
  Lean.Order.admissible_pi_apply (β := fun _ : World TT => Option (Except Exc X × World TT))
    (fun w o => ∀ y, o = some y → R w)
    (fun _ => Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)

/-! ## Termination predicates of the three loop components -/

/-- One iteration of the real `for … of` loop continues from the first state. -/
abbrev ForOfNext (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) :=
  LoopShape.Next (fun p : (Nat × Env TT Γ) × World TT => JS.exec (forOfStep I P a body p.1.1 p.1.2) p.2)
    (stepCls (TT := TT))

abbrev LoopNext (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) :=
  LoopShape.Next (fun p : Env TT Γ × World TT => JS.exec (loopStep I P c body step p.1) p.2)
    (stepCls (TT := TT))

abbrev DoNext (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ)
    (c : Expr TT Γ .bool) :=
  LoopShape.Next (fun p : Env TT Γ × World TT => JS.exec (doStep I P body c p.1) p.2)
    (stepCls (TT := TT))

/-- Every terminating run of the candidate `for … of` component `f` starts in a state from
which the real loop iterates finitely often. -/
def ForOfAcc (I : Impl) (P : Program TT)
    (f : {Γ : Ctx} → {ρ t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) : Prop :=
  ∀ (Γ : Ctx) (ρ t : Ty) (a i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ)
    (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
    JS.exec (f a i body env) w = some y → Acc (ForOfNext I P a body) ((i, env), w)

def LoopAcc (I : Impl) (P : Program TT)
    (f : {Γ : Ctx} → {ρ : Ty} → Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) : Prop :=
  ∀ (Γ : Ctx) (ρ : Ty) (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ)
    (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
    JS.exec (f c body step env) w = some y → Acc (LoopNext I P c body step) (env, w)

def DoAcc (I : Impl) (P : Program TT)
    (f : {Γ : Ctx} → {ρ : Ty} → Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) : Prop :=
  ∀ (Γ : Ctx) (ρ : Ty) (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ)
    (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
    JS.exec (f body c env) w = some y → Acc (DoNext I P body c) (env, w)

theorem admissible_forOfAcc (I : Impl) (P : Program TT) :
    Lean.Order.admissible (ForOfAcc (TT := TT) I P) := by
  unfold ForOfAcc
  refine adm_pi_apply (fun Γ (g : {ρ t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (ρ t : Ty) (a i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun Γ => ?_)
  refine adm_pi_apply (fun ρ (g : {t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (t : Ty) (a i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun ρ => ?_)
  refine adm_pi_apply (fun t (g : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (a i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun t => ?_)
  refine adm_pi_apply (fun a (g : Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g i body env) w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun a => ?_)
  refine adm_pi_apply (fun i (g : Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body env) w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun i => ?_)
  refine adm_pi_apply (fun body (g : Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g env) w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun body => ?_)
  refine adm_pi_apply (fun env (g : JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec g w = some y → Acc (ForOfNext I P a body) ((i, env), w))
    (fun env => ?_)
  exact admissible_exec _

theorem admissible_loopAcc (I : Impl) (P : Program TT) :
    Lean.Order.admissible (LoopAcc (TT := TT) I P) := by
  unfold LoopAcc
  refine adm_pi_apply (fun Γ (g : {ρ : Ty} → Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (ρ : Ty) (c : Expr TT Γ .bool)
      (body step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g c body step env) w = some y → Acc (LoopNext I P c body step) (env, w))
    (fun Γ => ?_)
  refine adm_pi_apply (fun ρ (g : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (c : Expr TT Γ .bool)
      (body step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g c body step env) w = some y → Acc (LoopNext I P c body step) (env, w))
    (fun ρ => ?_)
  refine adm_pi_apply (fun c (g : Block TT Γ ρ → Block TT Γ ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀
      (body step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body step env) w = some y → Acc (LoopNext I P c body step) (env, w))
    (fun c => ?_)
  refine adm_pi_apply (fun body (g : Block TT Γ ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀
      (step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g step env) w = some y → Acc (LoopNext I P c body step) (env, w))
    (fun body => ?_)
  refine adm_pi_apply (fun step (g : Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g env) w = some y → Acc (LoopNext I P c body step) (env, w))
    (fun step => ?_)
  refine adm_pi_apply (fun env (g : JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec g w = some y → Acc (LoopNext I P c body step) (env, w))
    (fun env => ?_)
  exact admissible_exec _

theorem admissible_doAcc (I : Impl) (P : Program TT) :
    Lean.Order.admissible (DoAcc (TT := TT) I P) := by
  unfold DoAcc
  refine adm_pi_apply (fun Γ (g : {ρ : Ty} → Block TT Γ ρ → Expr TT Γ .bool →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (ρ : Ty) (body : Block TT Γ ρ)
      (c : Expr TT Γ .bool) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body c env) w = some y → Acc (DoNext I P body c) (env, w))
    (fun Γ => ?_)
  refine adm_pi_apply (fun ρ (g : Block TT Γ ρ → Expr TT Γ .bool →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (body : Block TT Γ ρ)
      (c : Expr TT Γ .bool) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body c env) w = some y → Acc (DoNext I P body c) (env, w))
    (fun ρ => ?_)
  refine adm_pi_apply (fun body (g : Expr TT Γ .bool →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀
      (c : Expr TT Γ .bool) (env : Env TT Γ) (w : World TT)
      (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g c env) w = some y → Acc (DoNext I P body c) (env, w))
    (fun body => ?_)
  refine adm_pi_apply (fun c (g : Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g env) w = some y → Acc (DoNext I P body c) (env, w))
    (fun c => ?_)
  refine adm_pi_apply (fun env (g : JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec g w = some y → Acc (DoNext I P body c) (env, w))
    (fun env => ?_)
  exact admissible_exec _

theorem adm_proj_forOf {Q : ({Γ : Ctx} → {ρ t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop}
    (hQ : Lean.Order.admissible Q) :
    @Lean.Order.admissible (MutT (TT := TT)) mutInst (fun x => Q x.2.2.2.2.2.2.2.2.2.2.2.1) := by
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd y)))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd y))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd y)))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ y))) ?_
  exact adm_pprod_fst Q hQ

theorem adm_proj_do {Q : ({Γ : Ctx} → {ρ : Ty} → Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop}
    (hQ : Lean.Order.admissible Q) :
    @Lean.Order.admissible (MutT (TT := TT)) mutInst (fun x => Q x.2.2.2.2.2.2.2.2.2.2.2.2.1) := by
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd y)))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd y))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd y)))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ y))) ?_
  exact adm_pprod_fst Q hQ

theorem adm_proj_loop {Q : ({Γ : Ctx} → {ρ : Ty} → Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop}
    (hQ : Lean.Order.admissible Q) :
    @Lean.Order.admissible (MutT (TT := TT)) mutInst (fun x => Q x.2.2.2.2.2.2.2.2.2.2.2.2.2.1) := by
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd y)))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd y))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd y)))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ y))) ?_
  exact adm_pprod_fst Q hQ

/-! ## Flat-order refinement of `JS` computations and monotonicity of the loop steps -/

/-- `m₂` extends `m₁`: every terminating run of `m₁` is a run of `m₂` (the flat order of the
interpreter's fixpoint, pointwise in the world). -/
def Ext {X : Type} (m₁ m₂ : JS TT X) : Prop :=
  ∀ w r, JS.exec m₁ w = some r → JS.exec m₂ w = some r

theorem Ext.refl {X : Type} (m : JS TT X) : Ext m m := fun _ _ h => h

theorem Ext.bind {X Y : Type} {m₁ m₂ : JS TT X} {f₁ f₂ : X → JS TT Y} (hm : Ext m₁ m₂)
    (hf : ∀ a, Ext (f₁ a) (f₂ a)) : Ext (m₁ >>= f₁) (m₂ >>= f₂) := by
  intro w r h
  rw [JS.exec_bind] at h ⊢
  rcases h1 : JS.exec m₁ w with _ | ⟨_ | a, w'⟩
  · simp only [h1] at h; cases h
  · simp only [h1] at h; rw [hm _ _ h1]; exact h
  · simp only [h1] at h; rw [hm _ _ h1]; exact hf a w' r h

theorem Ext.catchThrown {X : Type} {m₁ m₂ : JS TT X} (hm : Ext m₁ m₂) :
    Ext (JS.catchThrown m₁) (JS.catchThrown m₂) := by
  intro w r h
  rw [JS.exec_catchThrown] at h ⊢
  rcases h1 : JS.exec m₁ w with _ | ⟨(e | msg) | a, w'⟩
  · simp only [h1] at h; cases h
  all_goals (simp only [h1] at h; rw [hm _ _ h1]; exact h)

section steps
variable {Γ : Ctx} {ρ t : Ty}

theorem forOfStepWith_mono
    {B₁ B₂ : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ))}
    (hB : ∀ b e, Ext (B₁ b e) (B₂ b e)) (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (i : Nat)
    (env : Env TT Γ) : Ext (forOfStepWith B₁ a body i env) (forOfStepWith B₂ a body i env) := by
  unfold forOfStepWith
  refine Ext.bind (Ext.refl _) (fun cell => ?_)
  by_cases hi : i < cell.size
  · simp only [hi, ↓reduceDIte]
    refine Ext.bind (hB _ _) (fun x => ?_)
    rcases x with ⟨cb, env1⟩
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> exact Ext.refl _
  · simp only [hi, ↓reduceDIte]; exact Ext.refl _

theorem loopStepWith_mono {E₁ E₂ : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool)}
    {B₁ B₂ : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)}
    (hE : ∀ e env, Ext (E₁ e env) (E₂ e env)) (hB : ∀ b env, Ext (B₁ b env) (B₂ b env))
    (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) :
    Ext (loopStepWith E₁ B₁ c body step env) (loopStepWith E₂ B₂ c body step env) := by
  unfold loopStepWith
  refine Ext.bind (Ext.catchThrown (hE _ _)) (fun r => ?_)
  rcases r with ex | v
  · exact Ext.refl _
  · by_cases hv : v.toBool = true
    · simp only [hv, ite_true]
      refine Ext.bind (hB _ _) (fun x => ?_)
      rcases x with ⟨cb, env1⟩
      rcases cb with _ | (_ | n) | (_ | n) | v | p | ex
      all_goals first
        | exact Ext.refl _
        | (refine Ext.bind (hB _ _) (fun y => ?_)
           rcases y with ⟨cs, env2⟩
           rcases cs with _ | (_ | n) | (_ | n) | v | p | ex <;> exact Ext.refl _)
    · simp only [hv, Bool.false_eq_true, ite_false]
      exact Ext.refl _

theorem doStepWith_mono {E₁ E₂ : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool)}
    {B₁ B₂ : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)}
    (hE : ∀ e env, Ext (E₁ e env) (E₂ e env)) (hB : ∀ b env, Ext (B₁ b env) (B₂ b env))
    (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ) :
    Ext (doStepWith E₁ B₁ body c env) (doStepWith E₂ B₂ body c env) := by
  unfold doStepWith
  refine Ext.bind (hB _ _) (fun x => ?_)
  rcases x with ⟨cb, env1⟩
  rcases cb with _ | (_ | n) | (_ | n) | v | p | ex
  all_goals first
    | exact Ext.refl _
    | exact Ext.bind (Ext.catchThrown (hE _ _)) (fun r => Ext.refl _)

end steps

/-- A state whose (real) iteration leaves the loop, or continues to states from which the loop
iterates finitely often, is itself such a state. -/
theorem acc_of_step {σ OD O : Type} {iter : σ → Option OD} {cls : OD → O ⊕ σ} {s : σ} {r : OD}
    (hr : iter s = some r) (h : ∀ s', cls r = .inr s' → Acc (LoopShape.Next iter cls) s') :
    Acc (LoopShape.Next iter cls) s :=
  Acc.intro s fun s' ⟨r', hr', hc⟩ => by
    have hrr : r' = r := Option.some.inj ((show iter s = some r' from hr').symm.trans hr)
    subst hrr
    exact h s' hc

/-! ## The interpreter's functions are components of its fixpoint -/

theorem evalE_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {t : Ty} (e : Expr TT Γ t)
    (env : Env TT Γ) : evalE I P e env = (evalE.mutual I P).1 e env := by
  with_unfolding_all rfl

theorem evalB_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ)
    (env : Env TT Γ) : evalB I P b env = (evalE.mutual I P).2.2.2.2.2.2.2.2.1 b env := by
  with_unfolding_all rfl

theorem evalForOf_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOf I P a i body env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.2.1 a i body env := by
  with_unfolding_all rfl

theorem evalDo_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ)
    (c : Expr TT Γ .bool) (env : Env TT Γ) :
    evalDo I P body c env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.2.2.1 body c env := by
  with_unfolding_all rfl

theorem evalLoop_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (env : Env TT Γ) :
    evalLoop I P c body step env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.2.2.2.1 c body step env := by
  with_unfolding_all rfl

/-! ## Fixpoint induction -/

theorem loops_acc (I : Impl) (P : Program TT) :
    ForOfAcc I P (evalForOf I P) ∧ DoAcc I P (evalDo I P) ∧ LoopAcc I P (evalLoop I P) := by
  obtain ⟨hF, heq⟩ := mut_eq_fix I P
  have key : @Lean.Order.PartialOrder.rel (MutT (TT := TT)) mutInst.toPartialOrder
        (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF)
        (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF) ∧
      ForOfAcc I P (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF).2.2.2.2.2.2.2.2.2.2.2.1 ∧
      DoAcc I P (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF).2.2.2.2.2.2.2.2.2.2.2.2.1 ∧
      LoopAcc I P (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF).2.2.2.2.2.2.2.2.2.2.2.2.2.1 := by
    refine @Lean.Order.fix_induct (MutT (TT := TT)) mutInst (mutF I P) hF
      (fun x => @Lean.Order.PartialOrder.rel (MutT (TT := TT)) mutInst.toPartialOrder x
          (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF) ∧
        ForOfAcc I P x.2.2.2.2.2.2.2.2.2.2.2.1 ∧ DoAcc I P x.2.2.2.2.2.2.2.2.2.2.2.2.1 ∧
        LoopAcc I P x.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?adm ?step
    case adm =>
      refine adm_and _ _ ?_ (adm_and _ _ ?_ (adm_and _ _ ?_ ?_))
      · exact fun c hc h => @Lean.Order.csup_le _ mutInst _ c hc h
      · exact adm_proj_forOf (admissible_forOfAcc I P)
      · exact adm_proj_do (admissible_doAcc I P)
      · exact adm_proj_loop (admissible_loopAcc I P)
    case step =>
      rintro x ⟨hle, hfor, hdo, hloop⟩
      have hBx : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ),
          Ext (x.2.2.2.2.2.2.2.2.1 b env) (evalB I P b env) := by
        intro Γ ρ b env w r h
        have h9 := rel_pprod_fst (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd
          (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd hle))))))))
        rw [evalB_eq_mut, heq]
        exact js_rel_exec (h9 Γ ρ b env) h
      have hEx : ∀ {Γ : Ctx} {t : Ty} (e : Expr TT Γ t) (env : Env TT Γ),
          Ext (x.1 e env) (evalE I P e env) := by
        intro Γ t e env w r h
        have h1 := rel_pprod_fst hle
        rw [evalE_eq_mut, heq]
        exact js_rel_exec (h1 Γ t e env) h
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := hF x _ hle
        rwa [← @Lean.Order.fix_eq _ mutInst _ hF] at h
      · intro Γ ρ t a i body env w y hy
        change JS.exec (forOfBodyWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e)
          (fun a i b e => x.2.2.2.2.2.2.2.2.2.2.2.1 a i b e) a i body env) w = some y at hy
        rw [exec_forOfBodyWith] at hy
        rcases hs : JS.exec (forOfStepWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e) a body i env) w
          with _ | r
        · rw [hs] at hy; cases hy
        · have hreal := forOfStepWith_mono (B₂ := evalB I P) (fun b e => hBx b e) a body i env w r hs
          refine acc_of_step (iter := fun p : (Nat × Env TT Γ) × World TT =>
            JS.exec (forOfStep I P a body p.1.1 p.1.2) p.2) (s := ((i, env), w)) hreal ?_
          intro s' hc
          rw [hs] at hy
          simp only [Option.bind_some, hc, Sum.elim_inr] at hy
          exact hfor Γ ρ t a s'.1.1 body s'.1.2 s'.2 y hy
      · intro Γ ρ body c env w y hy
        change JS.exec (doBodyWith (fun e env => x.1 e env) (fun b env => x.2.2.2.2.2.2.2.2.1 b env)
          (fun b c env => x.2.2.2.2.2.2.2.2.2.2.2.2.1 b c env) body c env) w = some y at hy
        rw [exec_doBodyWith] at hy
        rcases hs : JS.exec (doStepWith (fun e env => x.1 e env)
          (fun b env => x.2.2.2.2.2.2.2.2.1 b env) body c env) w with _ | r
        · rw [hs] at hy; cases hy
        · have hreal := doStepWith_mono (E₂ := evalE I P) (B₂ := evalB I P)
            (fun e env => hEx e env) (fun b env => hBx b env) body c env w r hs
          refine acc_of_step (iter := fun p : Env TT Γ × World TT =>
            JS.exec (doStep I P body c p.1) p.2) (s := (env, w)) hreal ?_
          intro s' hc
          rw [hs] at hy
          simp only [Option.bind_some, hc, Sum.elim_inr] at hy
          exact hdo Γ ρ body c s'.1 s'.2 y hy
      · intro Γ ρ c body step env w y hy
        change JS.exec (loopBodyWith (fun e env => x.1 e env) (fun b env => x.2.2.2.2.2.2.2.2.1 b env)
          (fun c b s env => x.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c b s env) c body step env) w = some y at hy
        rw [exec_loopBodyWith] at hy
        rcases hs : JS.exec (loopStepWith (fun e env => x.1 e env)
          (fun b env => x.2.2.2.2.2.2.2.2.1 b env) c body step env) w with _ | r
        · rw [hs] at hy; cases hy
        · have hreal := loopStepWith_mono (E₂ := evalE I P) (B₂ := evalB I P)
            (fun e env => hEx e env) (fun b env => hBx b env) c body step env w r hs
          refine acc_of_step (iter := fun p : Env TT Γ × World TT =>
            JS.exec (loopStep I P c body step p.1) p.2) (s := (env, w)) hreal ?_
          intro s' hc
          rw [hs] at hy
          simp only [Option.bind_some, hc, Sum.elim_inr] at hy
          exact hloop Γ ρ c body step s'.1 s'.2 y hy
  refine ⟨?_, ?_, ?_⟩
  · intro Γ ρ t a i body env w y hy
    dsimp only at hy
    rw [evalForOf_eq_mut, heq] at hy
    exact key.2.1 Γ ρ t a i body env w y hy
  · intro Γ ρ body c env w y hy
    dsimp only at hy
    rw [evalDo_eq_mut, heq] at hy
    exact key.2.2.1 Γ ρ body c env w y hy
  · intro Γ ρ c body step env w y hy
    dsimp only at hy
    rw [evalLoop_eq_mut, heq] at hy
    exact key.2.2.2 Γ ρ c body step env w y hy

/-! ## Termination of the three loop constructs -/

theorem forOfTerminates (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) :
    LoopShape.Terminates
      (fun p : (Nat × Env TT Γ) × World TT => JS.exec (evalForOf I P a p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfStep I P a body p.1.1 p.1.2) p.2) stepCls := by
  rintro ⟨⟨i, env⟩, w⟩ hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact (loops_acc I P).1 Γ ρ t a i body env w y hy

theorem loopTerminates (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) :
    LoopShape.Terminates (fun p : Env TT Γ × World TT => JS.exec (evalLoop I P c body step p.1) p.2)
      (fun p => JS.exec (loopStep I P c body step p.1) p.2) stepCls := by
  rintro ⟨env, w⟩ hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact (loops_acc I P).2.2 Γ ρ c body step env w y hy

theorem doTerminates (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ)
    (c : Expr TT Γ .bool) :
    LoopShape.Terminates (fun p : Env TT Γ × World TT => JS.exec (evalDo I P body c p.1) p.2)
      (fun p => JS.exec (doStep I P body c p.1) p.2) stepCls := by
  rintro ⟨env, w⟩ hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact (loops_acc I P).2.1 Γ ρ body c env w y hy


/-! ## The iterations over `Map`s, `Set`s and strings

The same induction for `evalForOfMap`, `evalForOfSet` and `evalForOfStr` (components 11, 10
and 8 of the fixpoint), with the step functions of `Loops.lean`. -/

section iters
variable {Γ : Ctx} {ρ t k v : Ty}

theorem forOfMapStepWith_mono
    {B₁ B₂ : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ →
      Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ))}
    (hB : ∀ b e, Ext (B₁ b e) (B₂ b e)) (a : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (i : Nat)
    (env : Env TT Γ) : Ext (forOfMapStepWith B₁ a body i env) (forOfMapStepWith B₂ a body i env) := by
  unfold forOfMapStepWith
  refine Ext.bind (Ext.refl _) (fun m => ?_)
  rcases m.nextFrom i with _ | ⟨j, key, val⟩
  · exact Ext.refl _
  · refine Ext.bind (hB _ _) (fun x => ?_)
    rcases x with ⟨cb, env1⟩
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> exact Ext.refl _

theorem forOfSetStepWith_mono
    {B₁ B₂ : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ))}
    (hB : ∀ b e, Ext (B₁ b e) (B₂ b e)) (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (i : Nat)
    (env : Env TT Γ) : Ext (forOfSetStepWith B₁ a body i env) (forOfSetStepWith B₂ a body i env) := by
  unfold forOfSetStepWith
  refine Ext.bind (Ext.refl _) (fun m => ?_)
  rcases m.nextFrom i with _ | ⟨j, x, u⟩
  · exact Ext.refl _
  · refine Ext.bind (hB _ _) (fun x => ?_)
    rcases x with ⟨cb, env1⟩
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> exact Ext.refl _

theorem forOfStrStepWith_mono
    {B₁ B₂ : Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT (⟨.str, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.str, false⟩ :: Γ))}
    (hB : ∀ b e, Ext (B₁ b e) (B₂ b e)) (body : Block TT (⟨.str, false⟩ :: Γ) ρ)
    (cps : List JSStr) (env : Env TT Γ) :
    Ext (forOfStrStepWith B₁ body cps env) (forOfStrStepWith B₂ body cps env) := by
  rcases cps with _ | ⟨ch, rest⟩
  · exact Ext.refl _
  · unfold forOfStrStepWith
    refine Ext.bind (hB _ _) (fun x => ?_)
    rcases x with ⟨cb, env1⟩
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> exact Ext.refl _

end iters

abbrev ForOfMapNext (I : Impl) (P : Program TT) {Γ : Ctx} {ρ k v : Ty} (a : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) :=
  LoopShape.Next
    (fun p : (Nat × Env TT Γ) × World TT => JS.exec (forOfMapStep I P a body p.1.1 p.1.2) p.2)
    (stepCls (TT := TT))

abbrev ForOfSetNext (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) :=
  LoopShape.Next
    (fun p : (Nat × Env TT Γ) × World TT => JS.exec (forOfSetStep I P a body p.1.1 p.1.2) p.2)
    (stepCls (TT := TT))

abbrev ForOfStrNext (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) :=
  LoopShape.Next
    (fun p : (List JSStr × Env TT Γ) × World TT => JS.exec (forOfStrStep I P body p.1.1 p.1.2) p.2)
    (stepCls (TT := TT))

def ForOfMapAcc (I : Impl) (P : Program TT)
    (f : {Γ : Ctx} → {ρ k v : Ty} → Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) : Prop :=
  ∀ (Γ : Ctx) (ρ k v : Ty) (a i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ)
    (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
    JS.exec (f a i body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w)

def ForOfSetAcc (I : Impl) (P : Program TT)
    (f : {Γ : Ctx} → {ρ t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) : Prop :=
  ∀ (Γ : Ctx) (ρ t : Ty) (a i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ)
    (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
    JS.exec (f a i body env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w)

def ForOfStrAcc (I : Impl) (P : Program TT)
    (f : {Γ : Ctx} → {ρ : Ty} → List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) : Prop :=
  ∀ (Γ : Ctx) (ρ : Ty) (cps : List JSStr) (body : Block TT (⟨.str, false⟩ :: Γ) ρ)
    (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
    JS.exec (f cps body env) w = some y → Acc (ForOfStrNext I P body) ((cps, env), w)

theorem admissible_forOfMapAcc (I : Impl) (P : Program TT) :
    Lean.Order.admissible (ForOfMapAcc (TT := TT) I P) := by
  unfold ForOfMapAcc
  refine adm_pi_apply (fun Γ (g : {ρ k v : Ty} → Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (ρ k v : Ty) (a i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun Γ => ?_)
  refine adm_pi_apply (fun ρ (g : {k v : Ty} → Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (k v : Ty) (a i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun ρ => ?_)
  refine adm_pi_apply (fun k (g : {v : Ty} → Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (v : Ty) (a i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun k => ?_)
  refine adm_pi_apply (fun v (g : Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (a i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun v => ?_)
  refine adm_pi_apply (fun a (g : Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g i body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun a => ?_)
  refine adm_pi_apply (fun i (g : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun i => ?_)
  refine adm_pi_apply (fun body (g : Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g env) w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun body => ?_)
  refine adm_pi_apply (fun env (g : JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec g w = some y → Acc (ForOfMapNext I P a body) ((i, env), w))
    (fun env => ?_)
  exact admissible_exec _

theorem admissible_forOfSetAcc (I : Impl) (P : Program TT) :
    Lean.Order.admissible (ForOfSetAcc (TT := TT) I P) := by
  unfold ForOfSetAcc
  refine adm_pi_apply (fun Γ (g : {ρ t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (ρ t : Ty) (a i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun Γ => ?_)
  refine adm_pi_apply (fun ρ (g : {t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (t : Ty) (a i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun ρ => ?_)
  refine adm_pi_apply (fun t (g : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (a i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g a i body env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun t => ?_)
  refine adm_pi_apply (fun a (g : Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (i : Nat)
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g i body env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun a => ?_)
  refine adm_pi_apply (fun i (g : Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀
      (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun i => ?_)
  refine adm_pi_apply (fun body (g : Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g env) w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun body => ?_)
  refine adm_pi_apply (fun env (g : JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec g w = some y → Acc (ForOfSetNext I P a body) ((i, env), w))
    (fun env => ?_)
  exact admissible_exec _

theorem admissible_forOfStrAcc (I : Impl) (P : Program TT) :
    Lean.Order.admissible (ForOfStrAcc (TT := TT) I P) := by
  unfold ForOfStrAcc
  refine adm_pi_apply (fun Γ (g : {ρ : Ty} → List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (ρ : Ty) (cps : List JSStr)
      (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g cps body env) w = some y → Acc (ForOfStrNext I P body) ((cps, env), w))
    (fun Γ => ?_)
  refine adm_pi_apply (fun ρ (g : List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀ (cps : List JSStr)
      (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g cps body env) w = some y → Acc (ForOfStrNext I P body) ((cps, env), w))
    (fun ρ => ?_)
  refine adm_pi_apply (fun cps (g : Block TT (⟨.str, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) => ∀
      (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g body env) w = some y → Acc (ForOfStrNext I P body) ((cps, env), w))
    (fun cps => ?_)
  refine adm_pi_apply (fun body (g : Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (env : Env TT Γ) (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec (g env) w = some y → Acc (ForOfStrNext I P body) ((cps, env), w))
    (fun body => ?_)
  refine adm_pi_apply (fun env (g : JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ (w : World TT) (y : Out TT (Completion TT ρ × Env TT Γ)),
      JS.exec g w = some y → Acc (ForOfStrNext I P body) ((cps, env), w))
    (fun env => ?_)
  exact admissible_exec _

theorem adm_proj_forOfMap {Q : ({Γ : Ctx} → {ρ k v : Ty} → Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop}
    (hQ : Lean.Order.admissible Q) :
    @Lean.Order.admissible (MutT (TT := TT)) mutInst (fun x => Q x.2.2.2.2.2.2.2.2.2.2.1) := by
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd y)))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd y))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd y)))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ y))) ?_
  exact adm_pprod_fst Q hQ

theorem adm_proj_forOfSet {Q : ({Γ : Ctx} → {ρ t : Ty} → Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop}
    (hQ : Lean.Order.admissible Q) :
    @Lean.Order.admissible (MutT (TT := TT)) mutInst (fun x => Q x.2.2.2.2.2.2.2.2.2.1) := by
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd y)))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd y))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd y)))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ y))) ?_
  exact adm_pprod_fst Q hQ

theorem adm_proj_forOfStr {Q : ({Γ : Ctx} → {ρ : Ty} → List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop}
    (hQ : Lean.Order.admissible Q) :
    @Lean.Order.admissible (MutT (TT := TT)) mutInst (fun x => Q x.2.2.2.2.2.2.2.1) := by
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd (PProd.snd y)))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd (PProd.snd y))))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd (PProd.snd y)))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd (PProd.snd y))))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ (PProd.snd y)))) ?_
  refine adm_pprod_snd (fun y => Q (no_implicit_lambda% (@PProd.fst _ _ y))) ?_
  exact adm_pprod_fst Q hQ

theorem evalForOfMap_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ k v : Ty} (a i : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOfMap I P a i body env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.1 a i body env := by
  with_unfolding_all rfl

theorem evalForOfSet_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOfSet I P a i body env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.1 a i body env := by
  with_unfolding_all rfl

theorem evalForOfStr_eq_mut (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cps : List JSStr)
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOfStr I P cps body env = (evalE.mutual I P).2.2.2.2.2.2.2.1 cps body env := by
  with_unfolding_all rfl

theorem iters_acc (I : Impl) (P : Program TT) :
    ForOfMapAcc I P (evalForOfMap I P) ∧ ForOfSetAcc I P (evalForOfSet I P) ∧
      ForOfStrAcc I P (evalForOfStr I P) := by
  obtain ⟨hF, heq⟩ := mut_eq_fix I P
  have key : @Lean.Order.PartialOrder.rel (MutT (TT := TT)) mutInst.toPartialOrder
        (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF)
        (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF) ∧
      ForOfMapAcc I P (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF).2.2.2.2.2.2.2.2.2.2.1 ∧
      ForOfSetAcc I P (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF).2.2.2.2.2.2.2.2.2.1 ∧
      ForOfStrAcc I P (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF).2.2.2.2.2.2.2.1 := by
    refine @Lean.Order.fix_induct (MutT (TT := TT)) mutInst (mutF I P) hF
      (fun x => @Lean.Order.PartialOrder.rel (MutT (TT := TT)) mutInst.toPartialOrder x
          (@Lean.Order.fix (MutT (TT := TT)) mutInst (mutF I P) hF) ∧
        ForOfMapAcc I P x.2.2.2.2.2.2.2.2.2.2.1 ∧ ForOfSetAcc I P x.2.2.2.2.2.2.2.2.2.1 ∧
        ForOfStrAcc I P x.2.2.2.2.2.2.2.1) ?adm ?step
    case adm =>
      refine adm_and _ _ ?_ (adm_and _ _ ?_ (adm_and _ _ ?_ ?_))
      · exact fun c hc h => @Lean.Order.csup_le _ mutInst _ c hc h
      · exact adm_proj_forOfMap (admissible_forOfMapAcc I P)
      · exact adm_proj_forOfSet (admissible_forOfSetAcc I P)
      · exact adm_proj_forOfStr (admissible_forOfStrAcc I P)
    case step =>
      rintro x ⟨hle, hmap, hset, hstr⟩
      have hBx : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ),
          Ext (x.2.2.2.2.2.2.2.2.1 b env) (evalB I P b env) := by
        intro Γ ρ b env w r h
        have h9 := rel_pprod_fst (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd
          (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd (rel_pprod_snd hle))))))))
        rw [evalB_eq_mut, heq]
        exact js_rel_exec (h9 Γ ρ b env) h
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := hF x _ hle
        rwa [← @Lean.Order.fix_eq _ mutInst _ hF] at h
      · intro Γ ρ k v a i body env w y hy
        change JS.exec (forOfMapBodyWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e)
          (fun a i b e => x.2.2.2.2.2.2.2.2.2.2.1 a i b e) a i body env) w = some y at hy
        rw [exec_forOfMapBodyWith] at hy
        rcases hs : JS.exec (forOfMapStepWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e) a body i env) w
          with _ | r
        · rw [hs] at hy; cases hy
        · have hreal := forOfMapStepWith_mono (B₂ := evalB I P) (fun b e => hBx b e)
            a body i env w r hs
          refine acc_of_step (iter := fun p : (Nat × Env TT Γ) × World TT =>
            JS.exec (forOfMapStep I P a body p.1.1 p.1.2) p.2) (s := ((i, env), w)) hreal ?_
          intro s' hc
          rw [hs] at hy
          simp only [Option.bind_some, hc, Sum.elim_inr] at hy
          exact hmap Γ ρ k v a s'.1.1 body s'.1.2 s'.2 y hy
      · intro Γ ρ t a i body env w y hy
        change JS.exec (forOfSetBodyWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e)
          (fun a i b e => x.2.2.2.2.2.2.2.2.2.1 a i b e) a i body env) w = some y at hy
        rw [exec_forOfSetBodyWith] at hy
        rcases hs : JS.exec (forOfSetStepWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e) a body i env) w
          with _ | r
        · rw [hs] at hy; cases hy
        · have hreal := forOfSetStepWith_mono (B₂ := evalB I P) (fun b e => hBx b e)
            a body i env w r hs
          refine acc_of_step (iter := fun p : (Nat × Env TT Γ) × World TT =>
            JS.exec (forOfSetStep I P a body p.1.1 p.1.2) p.2) (s := ((i, env), w)) hreal ?_
          intro s' hc
          rw [hs] at hy
          simp only [Option.bind_some, hc, Sum.elim_inr] at hy
          exact hset Γ ρ t a s'.1.1 body s'.1.2 s'.2 y hy
      · intro Γ ρ cps body env w y hy
        change JS.exec (forOfStrBodyWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e)
          (fun cps b e => x.2.2.2.2.2.2.2.1 cps b e) cps body env) w = some y at hy
        rw [exec_forOfStrBodyWith] at hy
        rcases hs : JS.exec (forOfStrStepWith (fun b e => x.2.2.2.2.2.2.2.2.1 b e) body cps env) w
          with _ | r
        · rw [hs] at hy; cases hy
        · have hreal := forOfStrStepWith_mono (B₂ := evalB I P) (fun b e => hBx b e)
            body cps env w r hs
          refine acc_of_step (iter := fun p : (List JSStr × Env TT Γ) × World TT =>
            JS.exec (forOfStrStep I P body p.1.1 p.1.2) p.2) (s := ((cps, env), w)) hreal ?_
          intro s' hc
          rw [hs] at hy
          simp only [Option.bind_some, hc, Sum.elim_inr] at hy
          exact hstr Γ ρ s'.1.1 body s'.1.2 s'.2 y hy
  refine ⟨?_, ?_, ?_⟩
  · intro Γ ρ k v a i body env w y hy
    dsimp only at hy
    rw [evalForOfMap_eq_mut, heq] at hy
    exact key.2.1 Γ ρ k v a i body env w y hy
  · intro Γ ρ t a i body env w y hy
    dsimp only at hy
    rw [evalForOfSet_eq_mut, heq] at hy
    exact key.2.2.1 Γ ρ t a i body env w y hy
  · intro Γ ρ cps body env w y hy
    dsimp only at hy
    rw [evalForOfStr_eq_mut, heq] at hy
    exact key.2.2.2 Γ ρ cps body env w y hy

theorem forOfMapTerminates (I : Impl) (P : Program TT) {Γ : Ctx} {ρ k v : Ty} (a : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) :
    LoopShape.Terminates
      (fun p : (Nat × Env TT Γ) × World TT => JS.exec (evalForOfMap I P a p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfMapStep I P a body p.1.1 p.1.2) p.2) stepCls := by
  rintro ⟨⟨i, env⟩, w⟩ hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact (iters_acc I P).1 Γ ρ k v a i body env w y hy

theorem forOfSetTerminates (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) :
    LoopShape.Terminates
      (fun p : (Nat × Env TT Γ) × World TT => JS.exec (evalForOfSet I P a p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfSetStep I P a body p.1.1 p.1.2) p.2) stepCls := by
  rintro ⟨⟨i, env⟩, w⟩ hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact (iters_acc I P).2.1 Γ ρ t a i body env w y hy

theorem forOfStrTerminates (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) :
    LoopShape.Terminates
      (fun p : (List JSStr × Env TT Γ) × World TT => JS.exec (evalForOfStr I P p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfStrStep I P body p.1.1 p.1.2) p.2) stepCls := by
  rintro ⟨⟨cps, env⟩, w⟩ hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact (iters_acc I P).2.2 Γ ρ cps body env w y hy

end EquivLean.TS
