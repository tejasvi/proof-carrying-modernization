/-
StrictTS proof layer: partial correctness of loops.

`evalLoop_inv` proves that a loop terminates (it needs a variant). The rules here need only an
invariant: `evalLoop_partial` concludes that every run of a `while`/counted-`for` loop that
terminates ends normally in a state satisfying the exit condition, so properties of code whose
termination is unknown (or false) can be proved; `evalLoop_noFault` gives `JS.NoFault`.

Method. The interpreter is one `partial_fixpoint`: its 26 functions are the components of
`evalE.mutual I P = fix F hF`, a least fixpoint on a product (`Interp TT`) of function spaces
ordered pointwise by the flat order of `Option` (`none` below every result). We do fixpoint
induction on the packed fixpoint with the extra hypothesis that the approximant lies below the
fixpoint (`interp_induct`). One unfolding of the loop (`evalLoopStep`) runs approximants of
`evalE`/`evalB`, and an approximant either diverges or returns exactly what the real function
returns (`JS.exec_le_cases`); so the invariant, stated about the real functions, applies to it.
The monotonicity of `F` is the proof Lean produced when it compiled the definition
(`interpStep_mono`), so no per-function argument is needed.

The same method gives `evalDo_partial` (`do … while`) and `evalForOf_partial` (`for … of` over
an array the body may grow). A rule for another loop form (the async `loopA`, `for … of` over
a `Map`, …) takes four pieces: its projection equation (`evalLoop_eq_proj`), one unfolding with
approximants (`evalLoopStep`, checked by `rfl` in `interpStep_loop`), the admissibility of its
motive (`admissible_proj_loop`, `admissible_loop_pc`) and the case analysis of one iteration.
-/
import StrictTS.Proof.Contract
import StrictTS.Proof.Unfold

namespace StrictTS
open Lean.Order JS

universe u v

variable {TT : TypeTable}

/-! ### The packed interpreter

`evalE.mutual I P` is `fix F hF` for the functional `F` and the monotonicity proof `hF` that
Lean built when it compiled the mutual `partial_fixpoint` block. The command below names the
pieces (the packed type, its order, `F` and `hF`) by reading the definition, so nothing is
restated by hand. -/

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let info ← getConstInfoDefn ``evalE.mutual
  lambdaTelescope info.value fun xs body => do
    let_expr Lean.Order.fix α inst F hmono := body
      | throwError "evalE.mutual is not a least fixpoint"
    let tt := xs[0]!
    let dependsOnIP (e : Lean.Expr) := e.containsFVar xs[1]!.fvarId! || e.containsFVar xs[2]!.fvarId!
    if dependsOnIP α || dependsOnIP inst then
      throwError "the packed type of evalE.mutual depends on Impl or Program"
    let env ← getEnv
    let interpVal := Lean.mkLambda `TT .default (← inferType tt) (α.abstract #[tt])
    addDecl <| .defnDecl <| mkDefinitionValEx `StrictTS.Interp [] (← inferType interpVal) interpVal
      .abbrev .safe [`StrictTS.Interp]
    setReducibleAttribute `StrictTS.Interp
    addDocStringCore `StrictTS.Interp
      "The tuple of all 26 functions of the interpreter's `partial_fixpoint` block (the type of `evalE.mutual I P`)."
    let interpTT := mkApp (mkConst `StrictTS.Interp) tt
    let instVal ← mkLambdaFVars #[tt] inst
    let instTy ← mkForallFVars #[tt] (mkApp (mkConst ``Lean.Order.CCPO [1]) interpTT)
    addDecl <| .defnDecl <| mkDefinitionValEx `StrictTS.instCCPOInterp [] instTy instVal
      (.regular (getMaxHeight env instVal + 1)) .safe [`StrictTS.instCCPOInterp]
    setReducibilityStatus `StrictTS.instCCPOInterp .instanceReducible
    addInstance `StrictTS.instCCPOInterp .global 1000
    addDocStringCore `StrictTS.instCCPOInterp
      "The order of the interpreter's fixpoint: componentwise, pointwise, flat on `Option`."
    let stepTy ← mkForallFVars xs (← mkArrow interpTT interpTT)
    let stepVal ← mkLambdaFVars xs F
    addDecl <| .defnDecl <| mkDefinitionValEx `StrictTS.interpStep [] stepTy stepVal
      (.regular (getMaxHeight env stepVal + 1)) .safe [`StrictTS.interpStep]
    modifyEnv (addNoncomputable · `StrictTS.interpStep)
    addDocStringCore `StrictTS.interpStep
      "One unfolding of the whole interpreter: `evalE.mutual I P = fix (interpStep I P) _`."
    let_expr Lean.Order.monotone a i b j _ := ← inferType hmono
      | throwError "unexpected monotonicity proof in evalE.mutual"
    let monoTy ← mkForallFVars xs <|
      mkAppN (mkConst ``Lean.Order.monotone [1, 1]) #[a, i, b, j, mkAppN (mkConst `StrictTS.interpStep) xs]
    let monoVal ← mkLambdaFVars xs hmono
    addDecl <| .thmDecl { name := `StrictTS.interpStep_mono, levelParams := [], type := monoTy, value := monoVal }
    addDocStringCore `StrictTS.interpStep_mono "Lean's monotonicity proof for the interpreter's functional."

theorem evalE_mutual_eq (I : Impl) (P : Program TT) :
    evalE.mutual I P = fix (interpStep I P) (interpStep_mono I P) := rfl

theorem evalE_eq_proj (I : Impl) (P : Program TT) {Γ : Ctx} {t : Ty} (e : Expr TT Γ t) (env : Env TT Γ) :
    evalE I P e env = (evalE.mutual I P).1 e env := by
  delta evalE; rfl

theorem evalB_eq_proj (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) :
    evalB I P b env = (evalE.mutual I P).2.2.2.2.2.2.2.2.1 b env := by
  delta evalB; rfl

theorem evalLoop_eq_proj (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (env : Env TT Γ) :
    evalLoop I P c body step env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.2.2.2.1 c body step env := by
  delta evalLoop; rfl

theorem evalDo_eq_proj (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ)
    (c : Expr TT Γ .bool) (env : Env TT Γ) :
    evalDo I P body c env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.2.2.1 body c env := by
  delta evalDo; rfl

theorem evalForOf_eq_proj (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOf I P a i body env = (evalE.mutual I P).2.2.2.2.2.2.2.2.2.2.2.1 a i body env := by
  delta evalForOf; rfl

/-! ### Fixpoint induction with the fixpoint in scope -/

/-- Fixpoint induction where the step may also use that the approximant lies below the
fixpoint. -/
theorem fix_induct_le {α : Sort u} [CCPO α] {f : α → α} (hf : monotone f) (motive : α → Prop)
    (hadm : admissible motive) (h : ∀ x, x ⊑ fix f hf → motive x → motive (f x)) :
    motive (fix f hf) :=
  (fix_induct hf (fun x => x ⊑ fix f hf ∧ motive x)
    (admissible_and _ _ (fun _ hc hx => csup_le hc hx) hadm)
    (fun x hx => ⟨PartialOrder.rel_trans (hf _ _ hx.1) (PartialOrder.rel_of_eq (fix_eq hf).symm),
      h x hx.1 hx.2⟩)).2

/-- **Fixpoint induction over the interpreter.** An admissible property of the tuple of
interpreter functions holds of the interpreter if one unfolding preserves it, for approximants
below the interpreter (so the step may compare them with the real functions). -/
theorem interp_induct (I : Impl) (P : Program TT) (motive : Interp TT → Prop)
    (hadm : admissible motive)
    (h : ∀ x, x ⊑ evalE.mutual I P → motive x → motive (interpStep I P x)) :
    motive (evalE.mutual I P) := by
  rw [evalE_mutual_eq] at h ⊢
  exact fix_induct_le _ motive hadm h

/-! ### The flat order on runs -/

theorem option_le_cases {β : Type} {o o' : Option β} (h : o ⊑ o') : o = none ∨ o = o' := by
  cases h with
  | bot => exact .inl rfl
  | refl => exact .inr rfl

/-- A computation below another one either diverges or has the same result. -/
theorem JS.exec_le_cases {α : Type} {m m' : JS TT α} (h : m ⊑ m') (w : World TT) :
    exec m w = none ∨ exec m w = exec m' w :=
  option_le_cases (h w)

/-! ### Admissibility of partial-correctness properties -/

/-- Applying a function to a fixed argument preserves admissibility. -/
theorem admissible_app {α : Sort u} {β : α → Sort v} [∀ x, CCPO (β x)] (a : α) {P : β a → Prop}
    (hadm : admissible P) : admissible (fun f : (∀ x, β x) => P (f a)) := by
  intro c hc h
  rw [← fun_csup_eq]
  apply hadm _ (chain_apply hc a)
  rintro _ ⟨f, hcf, rfl⟩
  exact h f hcf

/-- "Every result of the run from `w` satisfies `Q`" is admissible. -/
theorem admissible_exec {α : Type} (w : World TT) (Q : Except Exc α → World TT → Prop) :
    admissible (fun m : JS TT α => ∀ r w', exec m w = some (r, w') → Q r w') :=
  admissible_app (β := fun _ => Option (Except Exc α × World TT)) w
    (admissible_pi _ fun _ => admissible_pi _ fun _ => Option.admissible_eq_some _ _)

set_option synthInstance.maxSize 100000 in
theorem admissible_proj_loop (R : (∀ {Γ : Ctx} {ρ : Ty}, Expr TT Γ .bool → Block TT Γ ρ →
      Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) → Prop) (hR : admissible R) :
    admissible (fun x : Interp TT => R x.2.2.2.2.2.2.2.2.2.2.2.2.2.1) :=
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_fst _ hR

set_option synthInstance.maxSize 100000 in
theorem admissible_loop_pc {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool) (body step : Block TT Γ ρ)
    (Pre : Env TT Γ → World TT → Prop) (Q : Except Exc (Completion TT ρ × Env TT Γ) → World TT → Prop) :
    admissible (fun L : (∀ {Γ : Ctx} {ρ : Ty}, Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ →
        Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ env w, Pre env w → ∀ r w', exec (L c body step env) w = some (r, w') → Q r w') := by
  refine admissible_pi _ fun env => admissible_pi _ fun w => admissible_pi _ fun _ => ?_
  have h6 := admissible_exec (TT := TT) w Q
  have h5 := admissible_app (β := fun _ : Env TT Γ => JS TT (Completion TT ρ × Env TT Γ)) env h6
  have h4 := admissible_app (β := fun _ : Block TT Γ ρ => Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    step h5
  have h3 := admissible_app
    (β := fun _ : Block TT Γ ρ => Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) body h4
  have h2 := admissible_app (β := fun _ : Expr TT Γ .bool =>
    Block TT Γ ρ → Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) c h3
  have h1 := admissible_app (β := fun ρ' : Ty =>
    Expr TT Γ .bool → Block TT Γ ρ' → Block TT Γ ρ' → Env TT Γ → JS TT (Completion TT ρ' × Env TT Γ)) ρ h2
  exact admissible_app (β := fun Γ' : Ctx => ∀ {ρ' : Ty}, Expr TT Γ' .bool → Block TT Γ' ρ' →
    Block TT Γ' ρ' → Env TT Γ' → JS TT (Completion TT ρ' × Env TT Γ')) Γ h1

/-! ### `while` and counted `for` -/

/-- One unfolding of `evalLoop`, with `E`, `B` and `L` in place of `evalE`, `evalB` and the
recursive call. -/
def evalLoopStep (E : ∀ {Γ : Ctx} {t : Ty}, Expr TT Γ t → Env TT Γ → JS TT (Val TT t))
    (B : ∀ {Γ : Ctx} {ρ : Ty}, Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (L : ∀ {Γ : Ctx} {ρ : Ty}, Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  match ← JS.catchThrown (E c env) with
  | .error ex => pure (.exc ex, env)
  | .ok v =>
    if v.toBool then do
      let (cb, env1) ← B body env
      match cb with
      | .normal | .cont 0 => do
        let (cs, env2) ← B step env1
        match cs with
        | .normal => L c body step env2
        | other => pure (other, env2)
      | .brk 0 => pure (.normal, env1)
      | .brk (n + 1) => pure (.brk n, env1)
      | .cont (n + 1) => pure (.cont n, env1)
      | other => pure (other, env1)
    else pure (.normal, env)

/-- The loop component of `interpStep` is `evalLoopStep` (checked by the kernel: `evalLoopStep`
is a faithful copy of the body of `evalLoop`). -/
theorem interpStep_loop (I : Impl) (P : Program TT) (x : Interp TT) {Γ : Ctx} {ρ : Ty}
    (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) :
    (interpStep I P x).2.2.2.2.2.2.2.2.2.2.2.2.2.1 c body step env =
      evalLoopStep x.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c body step env := rfl

/-- **Partial-correctness rule** for `while (c) body` / `for (; c; step) body`: an invariant
`Inv` and an exit condition `Post`, no variant. The step obligation is that of `evalLoop_inv`
without the decrease, in weakest-precondition form (`simp [ts_sym]` computes it), and a
diverging condition, body or step is allowed (`none => True`). Conclusion: every run from an
`Inv` state that terminates ends normally in a state satisfying `Post`. -/
theorem evalLoop_partial (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (Inv Post : Env TT Γ → World TT → Prop)
    (hstep : ∀ env w, Inv env w →
      match exec (evalE I P c env) w with
      | some (.ok b, w₀) =>
        (b.toBool = false → Post env w₀) ∧
        (b.toBool = true →
          match exec (evalB I P body env) w₀ with
          | some (.ok (.normal, env1), w1) =>
            match exec (evalB I P step env1) w1 with
            | some (.ok (.normal, env2), w2) => Inv env2 w2
            | none => True
            | _ => False
          | none => True
          | _ => False)
      | none => True
      | _ => False) :
    ∀ env w, Inv env w → ∀ r w', exec (evalLoop I P c body step env) w = some (r, w') →
      ∃ env', r = .ok (.normal, env') ∧ Post env' w' := by
  have key := interp_induct I P
    (fun x => ∀ env w, Inv env w → ∀ r w',
      exec (x.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c body step env) w = some (r, w') →
      ∃ env', r = .ok (.normal, env') ∧ Post env' w')
    (admissible_proj_loop _ (admissible_loop_pc c body step Inv _)) ?step
  · intro env w hinv r w' hrun
    rw [evalLoop_eq_proj] at hrun
    exact key env w hinv r w' hrun
  case step =>
    intro x hx ih env w hinv r w' hrun
    rw [interpStep_loop] at hrun
    -- the approximants of `evalE` and `evalB` diverge or agree with the real functions
    have hE : ∀ {Γ : Ctx} {t : Ty} (e : Expr TT Γ t) (env : Env TT Γ) (w : World TT),
        exec (x.1 e env) w = none ∨ exec (x.1 e env) w = exec (evalE I P e env) w := by
      intro Γ t e env w
      rw [evalE_eq_proj]
      exact exec_le_cases (hx.1 Γ t e env) w
    have hB : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) (w : World TT),
        exec (x.2.2.2.2.2.2.2.2.1 b env) w = none ∨
          exec (x.2.2.2.2.2.2.2.2.1 b env) w = exec (evalB I P b env) w := by
      intro Γ ρ b env w
      rw [evalB_eq_proj]
      exact exec_le_cases (hx.2.2.2.2.2.2.2.2.1 Γ ρ b env) w
    have hs := hstep env w hinv
    simp only [evalLoopStep, exec_bind, exec_catchThrown] at hrun
    rcases hE c env w with h0 | h0
    · simp [h0] at hrun
    rw [h0] at hrun
    split at hs
    · next b w₀ hc =>
      rw [hc] at hrun
      simp only at hrun
      cases hb : b.toBool
      · simp only [hb, Bool.false_eq_true, ite_false, exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨env, rfl, hs.1 hb⟩
      · simp only [hb, ite_true, exec_bind] at hrun
        have hs2 := hs.2 hb
        rcases hB body env w₀ with h1 | h1
        · simp [h1] at hrun
        rw [h1] at hrun
        split at hs2
        · next env1 w1 hb1 =>
          rw [hb1] at hrun
          simp only [exec_bind] at hrun
          rcases hB step env1 w1 with h2 | h2
          · simp [h2] at hrun
          rw [h2] at hrun
          split at hs2
          · next env2 w2 hs1 =>
            rw [hs1] at hrun
            exact ih env2 w2 hs2 r w' hrun
          · next hnone => simp [hnone] at hrun
          · exact hs2.elim
        · next hnone => simp [hnone] at hrun
        · exact hs2.elim
    · next hnone => simp [hnone] at hrun
    · exact hs.elim

/-- `evalLoop_partial` as a case split on the run (the form used by `ts_while_partial`): the
loop diverges, or it ends normally in a state satisfying `Post`. -/
theorem evalLoop_partial_cases (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (Inv Post : Env TT Γ → World TT → Prop)
    (hstep : ∀ env w, Inv env w →
      match exec (evalE I P c env) w with
      | some (.ok b, w₀) =>
        (b.toBool = false → Post env w₀) ∧
        (b.toBool = true →
          match exec (evalB I P body env) w₀ with
          | some (.ok (.normal, env1), w1) =>
            match exec (evalB I P step env1) w1 with
            | some (.ok (.normal, env2), w2) => Inv env2 w2
            | none => True
            | _ => False
          | none => True
          | _ => False)
      | none => True
      | _ => False)
    (env : Env TT Γ) (w : World TT) (hinv : Inv env w) :
    exec (evalLoop I P c body step env) w = none ∨
      ∃ env' w', exec (evalLoop I P c body step env) w = some (.ok (.normal, env'), w') ∧
        Post env' w' := by
  rcases h : exec (evalLoop I P c body step env) w with _ | ⟨r, w'⟩
  · exact .inl rfl
  · obtain ⟨env', rfl, hp⟩ := evalLoop_partial I P c body step Inv Post hstep env w hinv r w' h
    exact .inr ⟨env', w', rfl, hp⟩

/-- A loop whose iterations never panic or throw from `Inv` states never faults, even if it
runs forever (take `Post := fun _ _ => True`). -/
theorem evalLoop_noFault (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (Inv Post : Env TT Γ → World TT → Prop)
    (hstep : ∀ env w, Inv env w →
      match exec (evalE I P c env) w with
      | some (.ok b, w₀) =>
        (b.toBool = false → Post env w₀) ∧
        (b.toBool = true →
          match exec (evalB I P body env) w₀ with
          | some (.ok (.normal, env1), w1) =>
            match exec (evalB I P step env1) w1 with
            | some (.ok (.normal, env2), w2) => Inv env2 w2
            | none => True
            | _ => False
          | none => True
          | _ => False)
      | none => True
      | _ => False)
    (env : Env TT Γ) (w : World TT) (hinv : Inv env w) :
    NoFault (evalLoop I P c body step env) w := by
  intro r w' h
  obtain ⟨env', rfl, -⟩ := evalLoop_partial I P c body step Inv Post hstep env w hinv r w' h
  exact ⟨_, rfl⟩

/-- `NoFault` through a bind: the first computation does not fault, and the rest does not fault
after any of its results. With `evalLoop_noFault` this gives `NoFault` for code around a loop. -/
theorem JS.NoFault.bind {α β : Type} {m : JS TT α} {f : α → JS TT β} {w : World TT}
    (hm : NoFault m w) (hf : ∀ a w', exec m w = some (.ok a, w') → NoFault (f a) w') :
    NoFault (m >>= f) w := by
  intro r w'' h
  rw [exec_bind] at h
  rcases hmw : exec m w with _ | ⟨_ | a, w'⟩
  · rw [hmw] at h; cases h
  · obtain ⟨a, ha⟩ := hm _ _ hmw
    cases ha
  · rw [hmw] at h
    exact hf a w' hmw r w'' h

/-! ### `do … while` -/

/-- One unfolding of `evalDo`, with `E`, `B` and `D` in place of `evalE`, `evalB` and the
recursive call. -/
def evalDoStep (E : ∀ {Γ : Ctx} {t : Ty}, Expr TT Γ t → Env TT Γ → JS TT (Val TT t))
    (B : ∀ {Γ : Ctx} {ρ : Ty}, Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (D : ∀ {Γ : Ctx} {ρ : Ty}, Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  let (cb, env1) ← B body env
  match cb with
  | .normal | .cont 0 => do
    match ← JS.catchThrown (E c env1) with
    | .error ex => pure (.exc ex, env1)
    | .ok v => if v.toBool then D body c env1 else pure (.normal, env1)
  | .brk 0 => pure (.normal, env1)
  | .brk (n + 1) => pure (.brk n, env1)
  | .cont (n + 1) => pure (.cont n, env1)
  | other => pure (other, env1)

theorem interpStep_do (I : Impl) (P : Program TT) (x : Interp TT) {Γ : Ctx} {ρ : Ty}
    (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ) :
    (interpStep I P x).2.2.2.2.2.2.2.2.2.2.2.2.1 body c env =
      evalDoStep x.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2.1 body c env := rfl

set_option synthInstance.maxSize 100000 in
theorem admissible_proj_do (R : (∀ {Γ : Ctx} {ρ : Ty}, Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ)) → Prop) (hR : admissible R) :
    admissible (fun x : Interp TT => R x.2.2.2.2.2.2.2.2.2.2.2.2.1) :=
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_fst _ hR

set_option synthInstance.maxSize 100000 in
theorem admissible_do_pc {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ) (c : Expr TT Γ .bool)
    (Pre : Env TT Γ → World TT → Prop) (Q : Except Exc (Completion TT ρ × Env TT Γ) → World TT → Prop) :
    admissible (fun D : (∀ {Γ : Ctx} {ρ : Ty}, Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ →
        JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ env w, Pre env w → ∀ r w', exec (D body c env) w = some (r, w') → Q r w') := by
  refine admissible_pi _ fun env => admissible_pi _ fun w => admissible_pi _ fun _ => ?_
  have h5 := admissible_app (β := fun _ : Env TT Γ => JS TT (Completion TT ρ × Env TT Γ)) env
    (admissible_exec (TT := TT) w Q)
  have h4 := admissible_app (β := fun _ : Expr TT Γ .bool => Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    c h5
  have h3 := admissible_app
    (β := fun _ : Block TT Γ ρ => Expr TT Γ .bool → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) body h4
  have h2 := admissible_app (β := fun ρ' : Ty =>
    Block TT Γ ρ' → Expr TT Γ .bool → Env TT Γ → JS TT (Completion TT ρ' × Env TT Γ)) ρ h3
  exact admissible_app (β := fun Γ' : Ctx => ∀ {ρ' : Ty},
    Block TT Γ' ρ' → Expr TT Γ' .bool → Env TT Γ' → JS TT (Completion TT ρ' × Env TT Γ')) Γ h2

/-- **Partial-correctness rule** for `do body while (c)`: `Inv` holds before each run of the
body; every run from an `Inv` state that terminates ends normally in a state satisfying `Post`. -/
theorem evalDo_partial (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ)
    (c : Expr TT Γ .bool) (Inv Post : Env TT Γ → World TT → Prop)
    (hstep : ∀ env w, Inv env w →
      match exec (evalB I P body env) w with
      | some (.ok (.normal, env1), w1) =>
        match exec (evalE I P c env1) w1 with
        | some (.ok b, w2) => (b.toBool = false → Post env1 w2) ∧ (b.toBool = true → Inv env1 w2)
        | none => True
        | _ => False
      | none => True
      | _ => False) :
    ∀ env w, Inv env w → ∀ r w', exec (evalDo I P body c env) w = some (r, w') →
      ∃ env', r = .ok (.normal, env') ∧ Post env' w' := by
  have key := interp_induct I P
    (fun x => ∀ env w, Inv env w → ∀ r w',
      exec (x.2.2.2.2.2.2.2.2.2.2.2.2.1 body c env) w = some (r, w') →
      ∃ env', r = .ok (.normal, env') ∧ Post env' w')
    (admissible_proj_do _ (admissible_do_pc body c Inv _)) ?step
  · intro env w hinv r w' hrun
    rw [evalDo_eq_proj] at hrun
    exact key env w hinv r w' hrun
  case step =>
    intro x hx ih env w hinv r w' hrun
    rw [interpStep_do] at hrun
    have hE : ∀ {Γ : Ctx} {t : Ty} (e : Expr TT Γ t) (env : Env TT Γ) (w : World TT),
        exec (x.1 e env) w = none ∨ exec (x.1 e env) w = exec (evalE I P e env) w := by
      intro Γ t e env w
      rw [evalE_eq_proj]
      exact exec_le_cases (hx.1 Γ t e env) w
    have hB : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) (w : World TT),
        exec (x.2.2.2.2.2.2.2.2.1 b env) w = none ∨
          exec (x.2.2.2.2.2.2.2.2.1 b env) w = exec (evalB I P b env) w := by
      intro Γ ρ b env w
      rw [evalB_eq_proj]
      exact exec_le_cases (hx.2.2.2.2.2.2.2.2.1 Γ ρ b env) w
    have hs := hstep env w hinv
    simp only [evalDoStep, exec_bind] at hrun
    rcases hB body env w with h0 | h0
    · simp [h0] at hrun
    rw [h0] at hrun
    split at hs
    · next env1 w1 hb1 =>
      rw [hb1] at hrun
      simp only [exec_bind, exec_catchThrown] at hrun
      rcases hE c env1 w1 with h1 | h1
      · simp [h1] at hrun
      rw [h1] at hrun
      split at hs
      · next b w2 hc =>
        rw [hc] at hrun
        simp only at hrun
        cases hb : b.toBool
        · simp only [hb, Bool.false_eq_true, ite_false, exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          exact ⟨env1, rfl, hs.1 hb⟩
        · simp only [hb, ite_true] at hrun
          exact ih env1 w2 (hs.2 hb) r w' hrun
      · next hnone => simp [hnone] at hrun
      · exact hs.elim
    · next hnone => simp [hnone] at hrun
    · exact hs.elim

/-! ### `for (const x of arr)` over a live array -/

/-- One unfolding of `evalForOf`, with `B` and `F` in place of `evalB` and the recursive call. -/
def evalForOfStep (B : ∀ {Γ : Ctx} {ρ : Ty}, Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (F : ∀ {Γ : Ctx} {ρ t : Ty}, Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    {Γ : Ctx} {ρ t : Ty} (a i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  let cell ← JS.readArr t a
  if h : i < cell.size then do
    let (cb, env1) ← B body (.cons cell[i] env)
    match cb with
    | .normal | .cont 0 => F a (i + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)
  else pure (.normal, env)

theorem interpStep_forOf (I : Impl) (P : Program TT) (x : Interp TT) {Γ : Ctx} {ρ t : Ty} (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    (interpStep I P x).2.2.2.2.2.2.2.2.2.2.2.1 a i body env =
      evalForOfStep x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.1 a i body env := rfl

set_option synthInstance.maxSize 100000 in
theorem admissible_proj_forOf (R : (∀ {Γ : Ctx} {ρ t : Ty}, Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ →
      Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) → Prop) (hR : admissible R) :
    admissible (fun x : Interp TT => R x.2.2.2.2.2.2.2.2.2.2.2.1) :=
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <|
  admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_snd _ <| admissible_pprod_fst _ hR

set_option synthInstance.maxSize 100000 in
theorem admissible_forOf_pc {Γ : Ctx} {ρ t : Ty} (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ)
    (Pre : Nat → Env TT Γ → World TT → Prop)
    (Q : Except Exc (Completion TT ρ × Env TT Γ) → World TT → Prop) :
    admissible (fun F : (∀ {Γ : Ctx} {ρ t : Ty}, Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ →
        JS TT (Completion TT ρ × Env TT Γ)) =>
      ∀ i env w, Pre i env w → ∀ r w', exec (F a i body env) w = some (r, w') → Q r w') := by
  refine admissible_pi _ fun i => admissible_pi _ fun env => admissible_pi _ fun w =>
    admissible_pi _ fun _ => ?_
  have h6 := admissible_app (β := fun _ : Env TT Γ => JS TT (Completion TT ρ × Env TT Γ)) env
    (admissible_exec (TT := TT) w Q)
  have h5 := admissible_app (β := fun _ : Block TT (⟨t, false⟩ :: Γ) ρ =>
    Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) body h6
  have h4 := admissible_app (β := fun _ : Nat =>
    Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) i h5
  have h3 := admissible_app (β := fun _ : Nat =>
    Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) a h4
  have h2 := admissible_app (β := fun t' : Ty =>
    Nat → Nat → Block TT (⟨t', false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)) t h3
  have h1 := admissible_app (β := fun ρ' : Ty => ∀ {t' : Ty},
    Nat → Nat → Block TT (⟨t', false⟩ :: Γ) ρ' → Env TT Γ → JS TT (Completion TT ρ' × Env TT Γ)) ρ h2
  exact admissible_app (β := fun Γ' : Ctx => ∀ {ρ' t' : Ty},
    Nat → Nat → Block TT (⟨t', false⟩ :: Γ') ρ' → Env TT Γ' → JS TT (Completion TT ρ' × Env TT Γ')) Γ h1

/-- **Partial-correctness rule** for `for (const x of arr)` over a live array (the body may
change the array, e.g. push to it, so the loop may run forever): `Inv i env w` holds before the
iteration with index `i`; the iteration reads the array cell anew. Every run from an `Inv` state
that terminates ends normally in a state satisfying `Post`. -/
theorem evalForOf_partial (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (Inv : Nat → Env TT Γ → World TT → Prop)
    (Post : Env TT Γ → World TT → Prop)
    (hstep : ∀ i env w, Inv i env w →
      match w.heap.get? (.arr t, a) with
      | some xs =>
        (xs.size ≤ i → Post env w) ∧
        (∀ h : i < xs.size,
          match exec (evalB I P body (.cons xs[i] env)) w with
          | some (.ok (.normal, env1), w1) => Inv (i + 1) env1.tail w1
          | none => True
          | _ => False)
      | none => False) :
    ∀ i env w, Inv i env w → ∀ r w', exec (evalForOf I P a i body env) w = some (r, w') →
      ∃ env', r = .ok (.normal, env') ∧ Post env' w' := by
  have key := interp_induct I P
    (fun x => ∀ i env w, Inv i env w → ∀ r w',
      exec (x.2.2.2.2.2.2.2.2.2.2.2.1 a i body env) w = some (r, w') →
      ∃ env', r = .ok (.normal, env') ∧ Post env' w')
    (admissible_proj_forOf _ (admissible_forOf_pc a body Inv _)) ?step
  · intro i env w hinv r w' hrun
    rw [evalForOf_eq_proj] at hrun
    exact key i env w hinv r w' hrun
  case step =>
    intro x hx ih i env w hinv r w' hrun
    rw [interpStep_forOf] at hrun
    have hB : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) (w : World TT),
        exec (x.2.2.2.2.2.2.2.2.1 b env) w = none ∨
          exec (x.2.2.2.2.2.2.2.2.1 b env) w = exec (evalB I P b env) w := by
      intro Γ ρ b env w
      rw [evalB_eq_proj]
      exact exec_le_cases (hx.2.2.2.2.2.2.2.2.1 Γ ρ b env) w
    have hs := hstep i env w hinv
    simp only [evalForOfStep, exec_bind, exec_readArr] at hrun
    split at hs
    · next xs hxs =>
      rw [hxs] at hrun
      simp only at hrun
      by_cases hi : i < xs.size
      · simp only [hi, dite_true, exec_bind] at hrun
        have hs2 := hs.2 hi
        rcases hB body (.cons xs[i] env) w with h1 | h1
        · simp [h1] at hrun
        rw [h1] at hrun
        split at hs2
        · next env1 w1 hb1 =>
          rw [hb1] at hrun
          simp only at hrun
          exact ih (i + 1) env1.tail w1 hs2 r w' hrun
        · next hnone => simp [hnone] at hrun
        · exact hs2.elim
      · simp only [hi, dite_false, exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨env, rfl, hs.1 (by omega)⟩
    · exact hs.elim

/-! ### Tactic -/

open Lean Elab Tactic Meta in
/-- `ts_while_partial Inv, Post` finds the loop `exec (evalLoop I P c body step env) w` (a
`while` or counted `for`) in the goal and applies `evalLoop_partial_cases` with invariant `Inv`
and exit condition `Post`: the main goal continues with the loop's run replaced by
`some (.ok (.normal, env'), w')` and `hpost : Post env' w'`. The divergence case (the run
replaced by `none`) is closed by `simp` when the goal is a partial-correctness statement
(`∀ r w', exec … = some (r, w') → …`, e.g. an unfolded `JS.NoFault`); otherwise it remains as
goal `diverge`.
Remaining goals: `step` (one iteration, in weakest-precondition form) and `init`. -/
elab "ts_while_partial " inv:term ", " post:term : tactic => withMainContext do
  let goal ← getMainTarget
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop &&
      !e.hasLooseBVars)
    | throwError "ts_while_partial: no loop (evalLoop) in the goal"
  let loop := e.getArg! 2
  let args := loop.getAppArgs
  -- evalLoop {TT} I P {Γ} {ρ} c body step env
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let c ← Term.exprToSyntax args[5]!
  let body ← Term.exprToSyntax args[6]!
  let step ← Term.exprToSyntax args[7]!
  let env ← Term.exprToSyntax args[8]!
  let ws ← Term.exprToSyntax (e.getArg! 3)
  let tag ← (← getMainGoal).getTag
  evalTactic (← `(tactic|
    have hloop := StrictTS.evalLoop_partial_cases $I $P $c $body $step $inv $post ?step $env $ws ?init))
  let hrunI := mkIdent `hrun
  let envI := mkIdent `env'
  let wI := mkIdent `w'
  let hpostI := mkIdent `hpost
  evalTactic (← `(tactic| rcases hloop with $hrunI:ident | ⟨$envI, $wI, $hrunI, $hpostI⟩))
  -- goals: divergence case, exit case, step, init
  let gs ← getGoals
  match gs with
  | gdiv :: gexit :: rest =>
    setGoals [gdiv]
    evalTactic (← `(tactic| rw [$hrunI:ident]))
    let saved ← saveState
    let closed ← try
        evalTactic (← `(tactic| simp))
        pure (← getGoals).isEmpty
      catch _ => pure false
    unless closed do saved.restore
    let divGoals ← getGoals
    divGoals.forM fun g => g.setTag `diverge
    setGoals [gexit]
    evalTactic (← `(tactic| rw [$hrunI:ident]))
    let exitGoals ← getGoals
    exitGoals.forM fun g => g.setTag tag
    setGoals (exitGoals ++ rest ++ divGoals)
  | _ => throwError "ts_while_partial: unexpected goals after the case split"

end StrictTS
