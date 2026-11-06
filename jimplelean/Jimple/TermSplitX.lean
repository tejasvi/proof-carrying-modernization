import Jimple.TermSplit

/-!
# Termination against strengthened callee contracts (`TermVC.of_thinX`)

`TermVC.of_thin` pairs a method's `MethodVC` against contracts `Γ` with a thin VC against the same `Γ`.
Some callees terminate only under a stronger precondition than their partial-correctness contract
states: a virtual call answered by a contract needs the receiver's runtime class to be concrete
(`callWPT`), and the contract may not say so. Here the thin VC also checks an extra premise
`X sig args σ` at every contracted call (`callWPThinX`), and `TermVC.of_thinX` gives the termination VC
against `Γ.strengthen X`: the same contracts with `X sig` added to their preconditions. Their validity
follows from `Γ`'s (`Valid.strengthen`); their termination is each callee's own result under the
stronger precondition (`MethodVC.strengthen`).

`ThinVCX.mk` splits the thin VC into its entry path and its cut points' paths, and `jvc_body` /
`jthinx_body` prove them for an arbitrary program with facts, as `jverify_body` does. This module is the
equiv-lean T4 package's `Term/TermX.lean` (t4-java-total 613c77c) under its JimpleLean name; the
patterns it was used with are in `docs/TERMINATION.md`.
-/

namespace Jimple

/-- `S` with its precondition strengthened by `X`. -/
def Spec.strengthen (S : Spec) (X : List Value → State → Prop) : Spec :=
  ⟨fun args σ => S.pre args σ ∧ X args σ, S.post⟩

/-- Every contract of `Γ`, its precondition strengthened by `X sig`. -/
def SpecEnv.strengthen (Γ : SpecEnv) (X : MethodSig → List Value → State → Prop) : SpecEnv :=
  fun sig => (Γ sig).map fun S => S.strengthen (X sig)

section Strengthen
variable {P : Program}

theorem Sat.strengthen {m : MethodRef} {S : Spec} (X : List Value → State → Prop) (h : Sat P m S) :
    Sat P m (S.strengthen X) :=
  fun args σ o hp hx => h args σ o hp.1 hx

theorem VSat.strengthen {sig : MethodSig} {c : ClassName} {S : Spec} (X : List Value → State → Prop)
    (h : VSat P sig c S) : VSat P sig c (S.strengthen X) :=
  fun args σ o hp hx => h args σ o hp.1 hx

theorem SpecEnv.strengthen_some {Γ : SpecEnv} {X : MethodSig → List Value → State → Prop}
    {sig : MethodSig} {S : Spec} (h : Γ.strengthen X sig = some S) :
    ∃ S0, Γ sig = some S0 ∧ S = S0.strengthen (X sig) := by
  unfold SpecEnv.strengthen at h
  cases h0 : Γ sig with
  | none => rw [h0] at h; cases h
  | some S0 =>
    rw [h0] at h
    exact ⟨S0, rfl, (Option.some.inj h).symm⟩

theorem Valid.strengthen {Γ : SpecEnv} (X : MethodSig → List Value → State → Prop) (hV : Valid P Γ) :
    Valid P (Γ.strengthen X) := by
  intro sig S h
  obtain ⟨S0, h0, rfl⟩ := SpecEnv.strengthen_some h
  obtain ⟨h1, h2⟩ := hV sig S0 h0
  exact ⟨fun m ht => (h1 m ht).strengthen _, fun c hc hs hst => (h2 c hc hs hst).strengthen _⟩

/-- A method's partial-correctness VC holds for any stronger precondition. -/
theorem MethodVC.strengthen {Γ : SpecEnv} {d : Nat} {m : MethodRef} {S : Spec} {A : Invariants}
    {fuel : Nat} (X : List Value → State → Prop) (h : MethodVC P Γ d m S A fuel) :
    MethodVC P Γ d m (S.strengthen X) A fuel := by
  obtain ⟨b, hb, h⟩ := h
  exact ⟨b, hb, fun args σ0 hpre => h args σ0 hpre.1⟩

/-- The callees' termination under the strengthened contracts, from a termination fact for every
    contract of `Γ` strengthened by `X`. -/
theorem SpecEnv.strengthen_term {Γ : SpecEnv} {X : MethodSig → List Value → State → Prop}
    (h : ∀ sig S, Γ sig = some S → ContractTerm P sig (S.strengthen (X sig))) (rank : MethodSig → Nat)
    (r : Nat) : ∀ sig S, ((Γ.strengthen X).below rank r) sig = some S → ContractTerm P sig S := by
  intro sig S hs
  unfold SpecEnv.below at hs
  split at hs
  · obtain ⟨S0, h0, rfl⟩ := SpecEnv.strengthen_some hs
    exact h sig S0 h0
  · cases hs

end Strengthen

/-- Answering a call request in the thin VC with extra callee premises: as `callWPThin`, and every
    contracted call also checks `X sig args σ`. -/
def callWPThinX (P : Program) (Γ : SpecEnv) (X : MethodSig → List Value → State → Prop) : Nat → Handler
  | d, sig, callee, args, σ, K =>
    match Γ sig, callee with
    | some S, .method _ => X sig args σ ∧ ∀ o, S.post args σ o → K o
    | some S, .virtual c => X sig args σ ∧ P.concrete c = true ∧ ∀ o, S.post args σ o → K o
    | none, .method m =>
      match d with
      | 0 => False
      | d + 1 =>
        match m.decl.body with
        | some b => bodyWP P (callWPThinX P Γ X d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
        | none => K (.wrong "abstract or native method")
    | none, .virtual c =>
      match d with
      | 0 => False
      | d + 1 =>
        match P.selectVirtual c sig.sub with
        | .jimple m =>
          match m.decl.body with
          | some b => bodyWP P (callWPThinX P Γ X d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
        | .native lc =>
          match args with
          | .ref a :: rest =>
            match σ.heap a with
            | some (.plain c' fs) =>
              c' = c ∧
              match Native.plainInst P sig lc a c fs rest σ with
              | some r => wpR (callWPThinX P Γ X d) r (fun ev => K ev.toOutcome)
              | none => K (.wrong "no model for library method")
            | _ => False
          | _ => False
        | .none why => P.concrete c = true ∧ K (.wrong why)

section SplitX
variable {P : Program}

/-- A partial-correctness answer and a thin answer with extra premises give a termination answer
    against the strengthened contracts. -/
theorem callWP_thinX (Γ : SpecEnv) (X : MethodSig → List Value → State → Prop) :
    ∀ d sig c args σ (K₁ K₂ K₃ : Outcome → Prop), (∀ o, K₁ o → K₂ o → K₃ o) →
      callWP P Γ d sig c args σ K₁ → callWPThinX P Γ X d sig c args σ K₂ →
        callWPT P (Γ.strengthen X) d sig c args σ K₃ := by
  intro d
  induction d with
  | zero =>
    intro sig c args σ K₁ K₂ K₃ hK h₁ h₂
    unfold callWP at h₁; unfold callWPThinX at h₂; unfold callWPT
    cases hΓ : Γ sig <;> cases c <;> simp only [hΓ, SpecEnv.strengthen, Option.map] at h₁ h₂ ⊢
    all_goals first
      | exact h₁.elim
      | exact ⟨h₁.1, ⟨h₁.2.1, h₂.1⟩, fun o ho => hK o (h₁.2.2 o ho) (h₂.2 o ho)⟩
      | exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₂.2.1, ⟨h₁.2.2.2.1, h₂.1⟩,
          fun o ho => hK o (h₁.2.2.2.2 o ho) (h₂.2.2 o ho)⟩
  | succ d ih =>
    intro sig c args σ K₁ K₂ K₃ hK h₁ h₂
    unfold callWP at h₁; unfold callWPThinX at h₂; unfold callWPT
    cases hΓ : Γ sig with
    | some S =>
      cases c <;> simp only [hΓ, SpecEnv.strengthen, Option.map] at h₁ h₂ ⊢
      · exact ⟨h₁.1, ⟨h₁.2.1, h₂.1⟩, fun o ho => hK o (h₁.2.2 o ho) (h₂.2 o ho)⟩
      · exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₂.2.1, ⟨h₁.2.2.2.1, h₂.1⟩,
          fun o ho => hK o (h₁.2.2.2.2 o ho) (h₂.2.2 o ho)⟩
    | none =>
      cases c with
      | method m =>
        simp only [hΓ, SpecEnv.strengthen, Option.map] at h₁ h₂ ⊢
        cases hb : m.decl.body with
        | none => simp only [hb] at h₁ h₂ ⊢; exact hK _ h₁ h₂
        | some b =>
          simp only [hb] at h₁ h₂ ⊢
          exact bodyWP_and ih b CutsAnd.nil K₁ K₂ K₃ hK inlineFuel 0 _ σ h₁ h₂
      | virtual c =>
        simp only [hΓ, SpecEnv.strengthen, Option.map] at h₁ h₂ ⊢
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

/-- The thin VC with extra callee premises `X`: as `ThinVC`, calls answered by `callWPThinX`. -/
def ThinVCX (P : Program) (Γ : SpecEnv) (X : MethodSig → List Value → State → Prop) (d : Nat)
    (m : MethodRef) (S : Spec) (I : Invariants) (vs : Nat → List Value → State → Frame → State → Nat)
    (fuel : Nat) : Prop :=
  ∃ b, m.decl.body = some b ∧
  ∀ args σ0, S.pre args σ0 →
    (let fr0 := Frame.init m.decl.mods.isStatic args
     match (I.inst args σ0).lookup 0 with
     | some _ => True
     | none => bodyWP P (callWPThinX P Γ X d) b (I.map fun p => (p.1, fun _ _ => True)) (fun _ => True)
        fuel 0 fr0 σ0) ∧
    ∀ p ∈ I, ∀ fr σ, p.2 args σ0 fr σ →
      bodyWP P (callWPThinX P Γ X d) b
        (I.map fun q => (q.1, fun fr' σ' => vs q.1 args σ0 fr' σ' < vs p.1 args σ0 fr σ)) (fun _ => True)
        fuel p.1 fr σ

/-- **Split termination VC against strengthened contracts.** -/
theorem TermVC.of_thinX {Γ : SpecEnv} {X : MethodSig → List Value → State → Prop}
    {rank : MethodSig → Nat} {r d : Nat} {m : MethodRef} {S : Spec} {I : Invariants}
    {vs : Nat → List Value → State → Frame → State → Nat} {fuel : Nat}
    (hΓ : (Γ.strengthen X).below rank r = Γ.strengthen X) (hV : MethodVC P Γ d m S I fuel)
    (hT : ThinVCX P Γ X d m S I vs fuel) :
    TermVC P (Γ.strengthen X) rank r d m S (I.withVariants vs) fuel := by
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
  have hH := callWP_thinX (P := P) Γ X d
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
    show bodyWP P (callWPT P (Γ.strengthen X) d) b ((I.withVariants vs).dec args σ0 (vs q.1 args σ0 fr σ))
      (fun _ => True) fuel q.1 fr σ
    rw [hdec]
    exact bodyWP_and hH b
      (CutsAnd.mapPc I (fun _ y => y args σ0)
        (fun pc _ fr' σ' => vs pc args σ0 fr' σ' < vs q.1 args σ0 fr σ)
        (fun pc y fr' σ' => y args σ0 fr' σ' ∧ vs pc args σ0 fr' σ' < vs q.1 args σ0 fr σ)
        (fun _ _ _ _ h1 h2 => ⟨h1, h2⟩))
      _ _ _ (fun _ _ _ => trivial) fuel q.1 fr σ h1 h2

theorem SpecEnv.strengthen_below_const (Γ : SpecEnv) (X : MethodSig → List Value → State → Prop) (r : Nat)
    (h : 0 < r) : (Γ.strengthen X).below (fun _ => 0) r = Γ.strengthen X :=
  SpecEnv.below_const _ r h

/-- A thin VC from its entry path and its cut points' paths, when no cut point is at statement 0. -/
theorem ThinVCX.mk {Γ : SpecEnv} {X : MethodSig → List Value → State → Prop} {d : Nat} {m : MethodRef}
    {S : Spec} {I : Invariants} {vs : Nat → List Value → State → Frame → State → Nat} {fuel : Nat}
    {b : Body} (hb : m.decl.body = some b) (h0 : ∀ args σ0, (I.inst args σ0).lookup 0 = none)
    (hentry : ∀ args σ0, S.pre args σ0 →
      bodyWP P (callWPThinX P Γ X d) b (I.map fun p => (p.1, fun _ _ => True)) (fun _ => True) fuel 0
        (Frame.init m.decl.mods.isStatic args) σ0)
    (hcut : ∀ args σ0, S.pre args σ0 → ∀ p ∈ I, ∀ fr σ, p.2 args σ0 fr σ →
      bodyWP P (callWPThinX P Γ X d) b
        (I.map fun q => (q.1, fun fr' σ' => vs q.1 args σ0 fr' σ' < vs p.1 args σ0 fr σ)) (fun _ => True)
        fuel p.1 fr σ) :
    ThinVCX P Γ X d m S I vs fuel := by
  refine ⟨b, hb, fun args σ0 hpre => ⟨?_, hcut args σ0 hpre⟩⟩
  show match (I.inst args σ0).lookup 0 with
    | some _ => True
    | none => bodyWP P (callWPThinX P Γ X d) b (I.map fun p => (p.1, fun _ _ => True)) (fun _ => True)
        fuel 0 (Frame.init m.decl.mods.isStatic args) σ0
  rw [h0 args σ0]
  exact hentry args σ0 hpre

end SplitX

/-- The per-program thin VC (the form of `BodyVCP`). -/
def ThinVCPX (F : Program → Prop) (Γ : Program → SpecEnv)
    (X : Program → MethodSig → List Value → State → Prop) (d : Nat) (m : MethodRef) (S : Program → Spec)
    (I : Invariants) (vs : Nat → List Value → State → Frame → State → Nat) (fuel : Nat) : Prop :=
  ∀ P, F P → ThinVCX P (Γ P) (X P) d m (S P) I vs fuel

@[jsimp] theorem callWPThinX_def (P : Program) (Γ : SpecEnv) (X : MethodSig → List Value → State → Prop)
    (d : Nat) (sig : MethodSig) (callee : Callee) (args : List Value) (σ : State) (K : Outcome → Prop) :
    callWPThinX P Γ X d sig callee args σ K =
      match Γ sig, callee with
      | some S, .method _ => X sig args σ ∧ ∀ o, S.post args σ o → K o
      | some S, .virtual c => X sig args σ ∧ P.concrete c = true ∧ ∀ o, S.post args σ o → K o
      | none, .method m =>
        match d with
        | 0 => False
        | d + 1 =>
          match m.decl.body with
          | some b => bodyWP P (callWPThinX P Γ X d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
      | none, .virtual c =>
        match d with
        | 0 => False
        | d + 1 =>
          match P.selectVirtual c sig.sub with
          | .jimple m =>
            match m.decl.body with
            | some b => bodyWP P (callWPThinX P Γ X d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
            | none => K (.wrong "abstract or native method")
          | .native lc =>
            match args with
            | .ref a :: rest =>
              match σ.heap a with
              | some (.plain c' fs) =>
                c' = c ∧
                match Native.plainInst P sig lc a c fs rest σ with
                | some r => wpR (callWPThinX P Γ X d) r (fun ev => K ev.toOutcome)
                | none => K (.wrong "no model for library method")
              | _ => False
            | _ => False
          | .none why => P.concrete c = true ∧ K (.wrong why) := by
  rw [callWPThinX.eq_def]; rfl

open Lean Elab Tactic in
/-- `jthinx [defs]`: prove `ThinVCX P Γ X d m S I vs fuel` — as `jthin`. -/
syntax (name := jthinxTac) "jthinx" (" [" ident,* "]")? : tactic

open Lean Elab Tactic in
@[tactic jthinxTac] def evalJthinx : Tactic := fun stx => do
  let extra : Array Ident := optIdents stx[1]
  let g ← getMainGoal
  let consts ← g.withContext do vcConstants (← g.getType)
  let tgt ← instantiateMVars (← g.getType)
  let args := tgt.getAppArgs
  let pick (i : Nat) (c : Name) : Bool :=
    match args[i]?.bind (·.getAppFn.constName?) with | some s => s == c | none => false
  let keep := consts.filter fun c => args.size == 9 &&
    (pick 5 c || pick 6 c || pick 7 c || pick 1 c || pick 2 c)
  let ids := keep.map mkIdent ++ extra
  if jimple.trace.get (← getOptions) then logInfo m!"jthinx: unfolding {ids}"
  withJimpleHeartbeats do
  evalTactic (← `(tactic| refine ⟨_, rfl, ?_⟩))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    out := out ++ (← jvcGoal ids 400 g)
  setGoals out

/-- `jvc_body [defs]`: `jvc` with the lookups on an abstract program unfolded (as `jverify_body`), for
    the entry and cut-point goals of `ThinVCX.mk`. -/
syntax (name := jvcBodyTac) "jvc_body" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| jvc_body [$ids,*]) => `(tactic| jvc [findHandler, Program.subtype, Program.isSubclass,
      Program.supers, supersN_succ_eq, supersFold, Program.fuel, Program.lookup, fieldKey,
      Program.resolveField, resolveFieldN_succ_eq, resolveIfaces, Program.isProgClass,
      Program.selectStatic, Program.chainN, Program.selectSpecial, Program.staticDecl, Targets, Shapes,
      ShapeIs, SpecEnv.strengthen, Spec.strengthen, $ids,*])

/-- `jthinx_body [defs]`: prove `ThinVCPX F Γ X d m S I vs fuel` for an arbitrary program with the facts
    `F`, as `jverify_body` does for `BodyVCP`. -/
syntax (name := jthinxBodyTac) "jthinx_body" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| jthinx_body) => `(tactic| (unfold ThinVCPX; intro P hF; (try dsimp only); jthinx [findHandler,
      Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq, supersFold, Program.fuel,
      Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq, resolveIfaces,
      Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial, Program.staticDecl,
      Targets, Shapes, ShapeIs, SpecEnv.strengthen, Spec.strengthen]))
  | `(tactic| jthinx_body [$ids,*]) => `(tactic| (unfold ThinVCPX; intro P hF; (try dsimp only); jthinx [
      findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq, supersFold,
      Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq, resolveIfaces,
      Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial, Program.staticDecl,
      Targets, Shapes, ShapeIs, SpecEnv.strengthen, Spec.strengthen, $ids,*]))

end Jimple
