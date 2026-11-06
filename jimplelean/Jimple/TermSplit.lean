/-
  Jimple/TermSplit.lean

  Termination from partial correctness. `TermVC` (`Jimple/Termination.lean`) checks invariants, callee
  preconditions and variants on the same paths. When the method's partial-correctness VC (`MethodVC`)
  is proved, the *thin* VC `ThinVC` suffices: from each cut point the variant decreases and no call is
  stuck; the invariants and the callee preconditions come from `MethodVC` (`TermVC.of_thin`, via the
  product lemma `bodyWP_and`). `jthin` proves `ThinVC` goals with the `jvc` loop.
-/
import Jimple.Termination

namespace Jimple

/-! ## Termination from partial correctness: the split VC

`TermVC` checks invariants, callee preconditions and variants on the same paths. When a method's
partial-correctness VC (`MethodVC`) is proved, a *thin* VC suffices: on the paths from each cut
point, the variant decreases and no call is stuck (`callWPThin`, `callWPT` without the callee
preconditions); the invariants and preconditions come from `MethodVC` (`TermVC.of_thin`). -/

/-- Answering a call request in the thin VC: as `callWPT`, without the checks `callWP` makes. -/
def callWPThin (P : Program) (Γ : SpecEnv) : Nat → Handler
  | d, sig, callee, args, σ, K =>
    match Γ sig, callee with
    | some S, .method _ => ∀ o, S.post args σ o → K o
    | some S, .virtual c => P.concrete c = true ∧ ∀ o, S.post args σ o → K o
    | none, .method m =>
      match d with
      | 0 => False
      | d + 1 =>
        match m.decl.body with
        | some b => bodyWP P (callWPThin P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
        | none => K (.wrong "abstract or native method")
    | none, .virtual c =>
      match d with
      | 0 => False
      | d + 1 =>
        match P.selectVirtual c sig.sub with
        | .jimple m =>
          match m.decl.body with
          | some b => bodyWP P (callWPThin P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
        | .native lc =>
          match args with
          | .ref a :: rest =>
            match σ.heap a with
            | some (.plain c' fs) =>
              c' = c ∧
              match Native.plainInst P sig lc a c fs rest σ with
              | some r => wpR (callWPThin P Γ d) r (fun ev => K ev.toOutcome)
              | none => K (.wrong "no model for library method")
            | _ => False
          | _ => False
        | .none why => P.concrete c = true ∧ K (.wrong why)

section Split
variable {P : Program}

/-- Two `wpR`s give a third when their handlers do. -/
theorem wpR_and {H₁ H₂ H₃ : Handler}
    (hH : ∀ sig c args σ (K₁ K₂ K₃ : Outcome → Prop), (∀ o, K₁ o → K₂ o → K₃ o) →
      H₁ sig c args σ K₁ → H₂ sig c args σ K₂ → H₃ sig c args σ K₃)
    {α : Type} : ∀ (r : Res α) (Q₁ Q₂ Q₃ : α → Prop), (∀ a, Q₁ a → Q₂ a → Q₃ a) →
      wpR H₁ r Q₁ → wpR H₂ r Q₂ → wpR H₃ r Q₃
  | .ret a, _, _, _, hQ, h₁, h₂ => hQ a h₁ h₂
  | .call sig c args σ k, Q₁, Q₂, Q₃, hQ, h₁, h₂ =>
    hH sig c args σ _ _ _ (fun o ho₁ ho₂ => wpR_and hH (k o) Q₁ Q₂ Q₃ hQ ho₁ ho₂) h₁ h₂
  | .choose k, Q₁, Q₂, Q₃, hQ, h₁, h₂ => fun n => wpR_and hH (k n) Q₁ Q₂ Q₃ hQ (h₁ n) (h₂ n)

/-- Cut lists with the same cut points, the third's assertions implied by the first two's. -/
def CutsAnd (I₁ I₂ I₃ : Cuts) : Prop :=
  ∀ pc, match I₃.lookup pc with
    | some A₃ => ∃ A₁ A₂, I₁.lookup pc = some A₁ ∧ I₂.lookup pc = some A₂ ∧
        ∀ fr σ, A₁ fr σ → A₂ fr σ → A₃ fr σ
    | none => I₁.lookup pc = none ∧ I₂.lookup pc = none

theorem CutsAnd.map {β : Type} (f₁ f₂ f₃ : β → Frame → State → Prop)
    (hf : ∀ y fr σ, f₁ y fr σ → f₂ y fr σ → f₃ y fr σ) :
    ∀ l : List (Nat × β),
      CutsAnd (l.map fun p => (p.1, f₁ p.2)) (l.map fun p => (p.1, f₂ p.2)) (l.map fun p => (p.1, f₃ p.2))
  | [] => fun pc => by simp
  | (b, y) :: l => fun pc => by
    have ih := CutsAnd.map f₁ f₂ f₃ hf l pc
    simp only [List.map_cons, List.lookup_cons]
    by_cases hb : pc = b
    · subst hb
      simp only [beq_self_eq_true]
      exact ⟨_, _, rfl, rfl, hf y⟩
    · have hb' : (pc == b) = false := by simpa using hb
      simp only [hb']
      exact ih

theorem CutsAnd.nil : CutsAnd [] [] [] := fun pc => by simp

/-- As `CutsAnd.map`, the assertions depending on the cut point too. -/
theorem CutsAnd.mapPc {β : Type} :
    ∀ (l : List (Nat × β)) (f₁ f₂ f₃ : Nat → β → Frame → State → Prop),
      (∀ pc y fr σ, f₁ pc y fr σ → f₂ pc y fr σ → f₃ pc y fr σ) →
      CutsAnd (l.map fun p => (p.1, f₁ p.1 p.2)) (l.map fun p => (p.1, f₂ p.1 p.2))
        (l.map fun p => (p.1, f₃ p.1 p.2))
  | [], _, _, _, _ => fun pc => by simp
  | (b, y) :: l, f₁, f₂, f₃, hf => fun pc => by
    have ih := CutsAnd.mapPc l f₁ f₂ f₃ hf pc
    simp only [List.map_cons, List.lookup_cons]
    by_cases hb : pc = b
    · subst hb
      simp only [beq_self_eq_true]
      exact ⟨_, _, rfl, rfl, hf pc y⟩
    · have hb' : (pc == b) = false := by simpa using hb
      simp only [hb']
      exact ih

/-- Two `bodyWP`s give a third when their handlers, cuts and postconditions do. -/
theorem bodyWP_and {H₁ H₂ H₃ : Handler}
    (hH : ∀ sig c args σ (K₁ K₂ K₃ : Outcome → Prop), (∀ o, K₁ o → K₂ o → K₃ o) →
      H₁ sig c args σ K₁ → H₂ sig c args σ K₂ → H₃ sig c args σ K₃)
    (b : Body) {I₁ I₂ I₃ : Cuts} (hI : CutsAnd I₁ I₂ I₃) (Post₁ Post₂ Post₃ : Outcome → Prop)
    (hPost : ∀ o, Post₁ o → Post₂ o → Post₃ o) :
    ∀ n pc fr σ, bodyWP P H₁ b I₁ Post₁ n pc fr σ → bodyWP P H₂ b I₂ Post₂ n pc fr σ →
      bodyWP P H₃ b I₃ Post₃ n pc fr σ
  | 0, _, _, _, h, _ => h
  | n + 1, pc, fr, σ, h₁, h₂ => by
    simp only [bodyWP] at h₁ h₂ ⊢
    refine wpR_and hH _ _ _ _ (fun r hr₁ hr₂ => ?_) h₁ h₂
    revert hr₁ hr₂
    cases afterStep P b pc fr r with
    | done o => exact hPost o
    | cont pc' fr' σ' =>
      simp only
      have hc := hI pc'
      cases h3 : I₃.lookup pc' with
      | some A₃ =>
        rw [h3] at hc
        obtain ⟨A₁, A₂, e1, e2, hA⟩ := hc
        rw [e1, e2]
        exact hA fr' σ'
      | none =>
        rw [h3] at hc
        rw [hc.1, hc.2]
        exact bodyWP_and hH b hI Post₁ Post₂ Post₃ hPost n pc' fr' σ'

/-- A partial-correctness answer and a thin answer give a termination answer. -/
theorem callWP_thin (Γ : SpecEnv) :
    ∀ d sig c args σ (K₁ K₂ K₃ : Outcome → Prop), (∀ o, K₁ o → K₂ o → K₃ o) →
      callWP P Γ d sig c args σ K₁ → callWPThin P Γ d sig c args σ K₂ → callWPT P Γ d sig c args σ K₃ := by
  intro d
  induction d with
  | zero =>
    intro sig c args σ K₁ K₂ K₃ hK h₁ h₂
    unfold callWP at h₁; unfold callWPThin at h₂; unfold callWPT
    cases hΓ : Γ sig <;> cases c <;> simp only [hΓ] at h₁ h₂ ⊢
    all_goals first
      | exact h₁.elim
      | exact ⟨h₁.1, h₁.2.1, fun o ho => hK o (h₁.2.2 o ho) (h₂ o ho)⟩
      | exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₂.1, h₁.2.2.2.1, fun o ho => hK o (h₁.2.2.2.2 o ho) (h₂.2 o ho)⟩
  | succ d ih =>
    intro sig c args σ K₁ K₂ K₃ hK h₁ h₂
    unfold callWP at h₁; unfold callWPThin at h₂; unfold callWPT
    cases hΓ : Γ sig with
    | some S =>
      cases c <;> simp only [hΓ] at h₁ h₂ ⊢
      · exact ⟨h₁.1, h₁.2.1, fun o ho => hK o (h₁.2.2 o ho) (h₂ o ho)⟩
      · exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₂.1, h₁.2.2.2.1, fun o ho => hK o (h₁.2.2.2.2 o ho) (h₂.2 o ho)⟩
    | none =>
      cases c with
      | method m =>
        simp only [hΓ] at h₁ h₂ ⊢
        cases hb : m.decl.body with
        | none => simp only [hb] at h₁ h₂ ⊢; exact hK _ h₁ h₂
        | some b =>
          simp only [hb] at h₁ h₂ ⊢
          exact bodyWP_and ih b CutsAnd.nil K₁ K₂ K₃ hK inlineFuel 0 _ σ h₁ h₂
      | virtual c =>
        simp only [hΓ] at h₁ h₂ ⊢
        cases hsel : P.selectVirtual c sig.sub with
        | jimple m =>
          simp only [hsel] at h₁ h₂ ⊢
          cases hb : m.decl.body with
          | none => simp only [hb] at h₁ h₂ ⊢; exact hK _ h₁ h₂
          | some b =>
            simp only [hb] at h₁ h₂ ⊢
            exact bodyWP_and ih b CutsAnd.nil K₁ K₂ K₃ hK inlineFuel 0 _ σ h₁ h₂
        | native lc =>
          simp only [hsel] at h₁ h₂ ⊢
          rcases args with _ | ⟨v, rest⟩
          · exact h₂.elim
          · cases v with
            | ref a =>
              simp only at h₁ h₂ ⊢
              cases hh : σ.heap a with
              | none => simp only [hh] at h₂
              | some o =>
                cases o with
                | plain c' fs =>
                  simp only [hh] at h₁ h₂ ⊢
                  obtain ⟨hc, h₂⟩ := h₂
                  refine ⟨hc, ?_⟩
                  have h₁ := h₁ hc
                  cases hp : Native.plainInst P sig lc a c fs rest σ with
                  | none => simp only [hp] at h₁ h₂ ⊢; exact hK _ h₁ h₂
                  | some r =>
                    simp only [hp] at h₁ h₂ ⊢
                    exact wpR_and ih r _ _ _ (fun ev h1 h2 => hK _ h1 h2) h₁ h₂
                | _ => simp only [hh] at h₂
            | _ => exact h₂.elim
        | none why =>
          simp only [hsel] at h₁ h₂ ⊢
          exact ⟨h₂.1, hK _ (h₁ h₂.1) h₂.2⟩

/-- Loop invariants with a variant per cut point (`vs pc`). -/
def Invariants.withVariants (I : Invariants) (vs : Nat → List Value → State → Frame → State → Nat) :
    TermCuts :=
  I.map fun p => (p.1, p.2, vs p.1)

/-- The thin VC of method `m` with invariants `I` and variants `vs` (one per cut point): the entry path
    (cut assertions trivial) and from every cut point `pc` the paths to the next cut points `pc'`,
    where `vs pc'` is below the value `vs pc` had; calls answered by `callWPThin P Γ d`. -/
def ThinVC (P : Program) (Γ : SpecEnv) (d : Nat) (m : MethodRef) (S : Spec) (I : Invariants)
    (vs : Nat → List Value → State → Frame → State → Nat) (fuel : Nat) : Prop :=
  ∃ b, m.decl.body = some b ∧
  ∀ args σ0, S.pre args σ0 →
    (let fr0 := Frame.init m.decl.mods.isStatic args
     match (I.inst args σ0).lookup 0 with
     | some _ => True
     | none => bodyWP P (callWPThin P Γ d) b (I.map fun p => (p.1, fun _ _ => True)) (fun _ => True)
        fuel 0 fr0 σ0) ∧
    ∀ p ∈ I, ∀ fr σ, p.2 args σ0 fr σ →
      bodyWP P (callWPThin P Γ d) b
        (I.map fun q => (q.1, fun fr' σ' => vs q.1 args σ0 fr' σ' < vs p.1 args σ0 fr σ)) (fun _ => True)
        fuel p.1 fr σ

/-- **Split termination VC**: a partial-correctness VC and a thin VC with the same invariants give
    the termination VC (all contracts of `Γ` below rank `r`). -/
theorem TermVC.of_thin {Γ : SpecEnv} {rank : MethodSig → Nat} {r d : Nat} {m : MethodRef} {S : Spec}
    {I : Invariants} {vs : Nat → List Value → State → Frame → State → Nat} {fuel : Nat}
    (hΓ : Γ.below rank r = Γ) (hV : MethodVC P Γ d m S I fuel) (hT : ThinVC P Γ d m S I vs fuel) :
    TermVC P Γ rank r d m S (I.withVariants vs) fuel := by
  obtain ⟨b, hb, hV⟩ := hV
  obtain ⟨b', hb', hT⟩ := hT
  rw [hb] at hb'
  cases hb'
  refine ⟨b, hb, fun args σ0 hpre => ?_⟩
  obtain ⟨hV0, hVc⟩ := hV args σ0 hpre
  obtain ⟨hT0, hTc⟩ := hT args σ0 hpre
  rw [hΓ]
  have hinv : (I.withVariants vs).inv args σ0 = I.inst args σ0 := by
    simp only [TermCuts.inv, Invariants.withVariants, Invariants.inst, List.map_map]; rfl
  have hH := callWP_thin (P := P) Γ d
  refine ⟨?_, ?_⟩
  · rw [hinv]
    simp only at hV0 hT0 ⊢
    revert hV0 hT0
    cases h0 : (I.inst args σ0).lookup 0 with
    | some a => exact fun h _ => h
    | none =>
      intro hV0 hT0
      dsimp only at hV0 hT0 ⊢
      exact bodyWP_and hH b
        (by
          unfold Invariants.inst
          exact CutsAnd.map (β := List Value → State → Frame → State → Prop) (fun y => y args σ0)
            (fun _ _ _ => True) (fun y => y args σ0) (fun _ _ _ h _ => h) I)
        (S.post args σ0) (fun _ => True) (fun _ => True) (fun _ _ _ => trivial) fuel 0 _ σ0 hV0 hT0
  · intro p hp fr σ hpI
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have h1 := hVc (q.1, q.2 args σ0) (List.mem_map.mpr ⟨q, hq, rfl⟩) fr σ hpI
    have h2 := hTc q hq fr σ hpI
    have hdec : (I.withVariants vs).dec args σ0 (vs q.1 args σ0 fr σ) =
        I.map fun p => (p.1, (fun pc (y : List Value → State → Frame → State → Prop) fr' σ' =>
          y args σ0 fr' σ' ∧ vs pc args σ0 fr' σ' < vs q.1 args σ0 fr σ) p.1 p.2) := by
      simp only [TermCuts.dec, Invariants.withVariants, List.map_map]; rfl
    show bodyWP P (callWPT P Γ d) b ((I.withVariants vs).dec args σ0 (vs q.1 args σ0 fr σ)) (fun _ => True)
      fuel q.1 fr σ
    rw [hdec]
    exact bodyWP_and hH b
      (CutsAnd.mapPc I (fun _ y => y args σ0)
        (fun pc _ fr' σ' => vs pc args σ0 fr' σ' < vs q.1 args σ0 fr σ)
        (fun pc y fr' σ' => y args σ0 fr' σ' ∧ vs pc args σ0 fr' σ' < vs q.1 args σ0 fr σ)
        (fun _ _ _ _ h1 h2 => ⟨h1, h2⟩))
      _ _ _ (fun _ _ _ => trivial) fuel q.1 fr σ h1 h2

/-- A contract's termination carries over to a contract with a stronger precondition (`ContractTerm`
    unfolds to a conjunction: write `ContractTerm.mono h hpre`, not `h.mono`). -/
theorem ContractTerm.mono {sig : MethodSig} {S S' : Spec} (h : ContractTerm P sig S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ) : ContractTerm P sig S' :=
  ⟨fun m ht args σ hp => h.1 m ht args σ (hpre args σ hp),
   fun c h1 h2 h3 h4 args σ hp => h.2 c h1 h2 h3 h4 args σ (hpre args σ hp)⟩

/-- All contracts below rank `r`. -/
theorem SpecEnv.below_const (Γ : SpecEnv) (r : Nat) (h : 0 < r) : Γ.below (fun _ => 0) r = Γ := by
  funext sig; simp [SpecEnv.below, h]

end Split

/-! ## Automation: `jthin` proves `ThinVC` goals with the `jvc` loop -/

@[jsimp] theorem callWPThin_def (P : Program) (Γ : SpecEnv) (d : Nat) (sig : MethodSig) (callee : Callee)
    (args : List Value) (σ : State) (K : Outcome → Prop) :
    callWPThin P Γ d sig callee args σ K =
      match Γ sig, callee with
      | some S, .method _ => ∀ o, S.post args σ o → K o
      | some S, .virtual c => P.concrete c = true ∧ ∀ o, S.post args σ o → K o
      | none, .method m =>
        match d with
        | 0 => False
        | d + 1 =>
          match m.decl.body with
          | some b => bodyWP P (callWPThin P Γ d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
      | none, .virtual c =>
        match d with
        | 0 => False
        | d + 1 =>
          match P.selectVirtual c sig.sub with
          | .jimple m =>
            match m.decl.body with
            | some b => bodyWP P (callWPThin P Γ d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
            | none => K (.wrong "abstract or native method")
          | .native lc =>
            match args with
            | .ref a :: rest =>
              match σ.heap a with
              | some (.plain c' fs) =>
                c' = c ∧
                match Native.plainInst P sig lc a c fs rest σ with
                | some r => wpR (callWPThin P Γ d) r (fun ev => K ev.toOutcome)
                | none => K (.wrong "no model for library method")
              | _ => False
            | _ => False
          | .none why => P.concrete c = true ∧ K (.wrong why) := by
  rw [callWPThin.eq_def]; rfl

open Lean Meta Elab Tactic in
/-- `jnorm_lits`: raw natural-number literals, as the ground evaluation of `jvc` leaves them in
    hypotheses, back to numerals in the goal and the hypotheses, so that `omega` reads them (for a
    variant goal closed after `jvc`). -/
elab "jnorm_lits" : tactic => do
  let fix (e : Lean.Expr) : Lean.Expr := e.replace fun t =>
    if t.isAppOf ``OfNat.ofNat then some t
    else match t with
      | .lit (.natVal n) => some (mkNatLit n)
      | _ => none
  liftMetaTactic fun g => do
    let mut g := g
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let ty' := fix ty
      if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
    let tgt ← instantiateMVars (← g.getType)
    let tgt' := fix tgt
    if tgt' != tgt then g ← g.replaceTargetDefEq tgt'
    return [g]

open Lean Elab Tactic in
/-- `jthin`: prove `ThinVC P Γ d m S I var fuel` — selects the body, unfolds the contract, the
    invariants, the variant and the environment, and runs `jvc`. -/
syntax (name := jthinTac) "jthin" (" [" ident,* "]")? : tactic

open Lean Elab Tactic in
@[tactic jthinTac] def evalJthin : Tactic := fun stx => do
  let extra : Array Ident := optIdents stx[1]
  let g ← getMainGoal
  let consts ← g.withContext do vcConstants (← g.getType)
  let tgt ← instantiateMVars (← g.getType)
  let args := tgt.getAppArgs
  let pick (i : Nat) (c : Name) : Bool :=
    match args[i]?.bind (·.getAppFn.constName?) with | some s => s == c | none => false
  let keep := consts.filter fun c => args.size == 8 && (pick 4 c || pick 5 c || pick 6 c || pick 1 c)
  let ids := keep.map mkIdent ++ extra
  if jimple.trace.get (← getOptions) then logInfo m!"jthin: unfolding {ids}"
  withJimpleHeartbeats do
  evalTactic (← `(tactic| refine ⟨_, rfl, ?_⟩))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    out := out ++ (← jvcGoal ids 400 g)
  setGoals out

end Jimple

