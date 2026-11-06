import Jimple.Verify

/-!
# Termination and total correctness

`Sat P m S` (Jimple/Logic.lean) is partial correctness: `MExec` is a big-step relation, so a
diverging execution has no derivation and satisfies every contract. This module adds the other half.

* `MTerm P m args σ` (with `VTerm`, `RTerm`, `BTerm`): every execution of the call terminates, every
  nondeterministic choice included, and some execution exists (no call is stuck). `MTerm.run`
  gives an outcome.
* `TermVC`: the verification condition of termination for one method. It is `bodyWP` with
  postcondition `True`, whose calls are answered by `callWPT`: the contracts of callees of lower
  rank, or inlining. Each loop cut point carries an invariant and a natural-number variant; a
  path from a cut point to the next one must decrease the variant.
* `AllTermVC.term`: if the contracts `Γ` hold (`Valid P Γ`, from the partial-correctness proofs)
  and every contract has its termination VC, every call on arguments satisfying a precondition
  terminates. Contracts are ordered by a rank (callees strictly lower), so there is no recursion
  through contracts.
-/

namespace Jimple

/-! ## Must-termination -/

mutual
/-- `MTerm P m args σ`: every execution of the selected method `m` on `args` from `σ` terminates,
    and one exists. -/
inductive MTerm (P : Program) : MethodRef → List Value → State → Prop
  | body {m : MethodRef} {args σ b} :
      m.decl.body = some b → BTerm P b 0 (Frame.init m.decl.mods.isStatic args) σ → MTerm P m args σ
  | noBody {m : MethodRef} {args σ} : m.decl.body = none → MTerm P m args σ

/-- `VTerm P sig c args σ`: every execution of a virtual call of `sig` on runtime class `c`
    terminates, and one exists. -/
inductive VTerm (P : Program) : MethodSig → ClassName → List Value → State → Prop
  | jimple {sig c m args σ} : P.selectVirtual c sig.sub = .jimple m → MTerm P m args σ →
      VTerm P sig c args σ
  | native {sig c lc a rest fs σ} : P.selectVirtual c sig.sub = .native lc →
      σ.heap a = some (.plain c fs) →
      (∀ r, Native.plainInst P sig lc a c fs rest σ = some r → RTerm P r) →
      VTerm P sig c (.ref a :: rest) σ
  | none {sig c why args σ} : P.selectVirtual c sig.sub = .none why → P.concrete c = true →
      VTerm P sig c args σ

/-- `RTerm P r`: every branch of the request tree `r` terminates, and one exists. -/
inductive RTerm (P : Program) : {α : Type} → Res α → Prop
  | ret {α} {a : α} : RTerm P (.ret a)
  | callM {α} {sig m args σ} {k : Outcome → Res α} :
      MTerm P m args σ → (∀ o, MExec P m args σ o → RTerm P (k o)) →
      RTerm P (.call sig (.method m) args σ k)
  | callV {α} {sig c args σ} {k : Outcome → Res α} :
      VTerm P sig c args σ → (∀ o, VExec P sig c args σ o → RTerm P (k o)) →
      RTerm P (.call sig (.virtual c) args σ k)
  | choose {α} {k : Nat → Res α} : (∀ n, RTerm P (k n)) → RTerm P (.choose k)

/-- `BTerm P b pc fr σ`: every execution of body `b` from `pc` terminates, and one exists. -/
inductive BTerm (P : Program) : Body → Nat → Frame → State → Prop
  | mk {b pc fr σ} : RTerm P (step P b pc fr σ) →
      (∀ r pc' fr' σ', RExec P (step P b pc fr σ) r → afterStep P b pc fr r = .cont pc' fr' σ' →
        BTerm P b pc' fr' σ') → BTerm P b pc fr σ
end

section Run
variable {P : Program}

mutual
/-- A terminating call has an outcome. -/
theorem MTerm.run : ∀ {m args σ}, MTerm P m args σ → ∃ o, MExec P m args σ o
  | _, _, _, .body hb hB => let ⟨o, h⟩ := BTerm.run hB; ⟨o, .body hb h⟩
  | _, _, _, .noBody hb => ⟨_, .noBody hb⟩

theorem VTerm.run : ∀ {sig c args σ}, VTerm P sig c args σ → ∃ o, VExec P sig c args σ o
  | _, _, _, _, .jimple hsel hm => let ⟨o, h⟩ := MTerm.run hm; ⟨o, .jimple hsel h⟩
  | sig, c, _, σ, .native (lc := lc) (a := a) (rest := rest) (fs := fs) hsel hheap hr => by
    rcases hp : Native.plainInst P sig lc a c fs rest σ with _ | r
    · exact ⟨_, .noModel hsel hheap hp⟩
    · obtain ⟨ev, hev⟩ := RTerm.run (hr r hp)
      exact ⟨_, .native hsel hheap hp hev⟩
  | _, _, _, _, .none hsel hconc => ⟨_, .none hsel hconc⟩

theorem RTerm.run : ∀ {α} {r : Res α}, RTerm P r → ∃ a, RExec P r a
  | _, _, .ret => ⟨_, .ret⟩
  | _, _, .callM hm hk => by
    obtain ⟨o, ho⟩ := MTerm.run hm
    obtain ⟨a, ha⟩ := RTerm.run (hk o ho)
    exact ⟨a, .callM ho ha⟩
  | _, _, .callV hv hk => by
    obtain ⟨o, ho⟩ := VTerm.run hv
    obtain ⟨a, ha⟩ := RTerm.run (hk o ho)
    exact ⟨a, .callV ho ha⟩
  | _, _, .choose hk => by
    obtain ⟨a, ha⟩ := RTerm.run (hk 0)
    exact ⟨a, .choose 0 ha⟩

theorem BTerm.run : ∀ {b pc fr σ}, BTerm P b pc fr σ → ∃ o, BExec P b pc fr σ o
  | b, pc, fr, σ, .mk hr hk => by
    obtain ⟨r, hrx⟩ := RTerm.run hr
    rcases ha : afterStep P b pc fr r with ⟨pc', fr', σ'⟩ | o
    · obtain ⟨o, ho⟩ := BTerm.run (hk r pc' fr' σ' hrx ha)
      exact ⟨o, .cont hrx ha ho⟩
    · exact ⟨o, .done hrx ha⟩
end

end Run

/-! ## The termination VC -/

/-- The contracts of `Γ` whose method has rank below `r` (the callees a method of rank `r` may
    use by contract). -/
def SpecEnv.below (Γ : SpecEnv) (rank : MethodSig → Nat) (r : Nat) : SpecEnv :=
  fun sig => if rank sig < r then Γ sig else none

/-- Answering a call request for termination: as `callWP`, and a call must not be stuck: a
    virtual call answered by a contract is on a concrete class; an inlined virtual call of a
    library method has its receiver object of that class; failing method selection is on a
    concrete class. -/
def callWPT (P : Program) (Γ : SpecEnv) : Nat → Handler
  | d, sig, callee, args, σ, K =>
    match Γ sig, callee with
    | some S, .method m => Targets P sig m ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
    | some S, .virtual c => P.isProgClass c = true ∧ P.isSubclass c sig.cls = some true ∧
        P.staticDecl sig = false ∧ P.concrete c = true ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
    | none, .method m =>
      match d with
      | 0 => False
      | d + 1 =>
        match m.decl.body with
        | some b => bodyWP P (callWPT P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
        | none => K (.wrong "abstract or native method")
    | none, .virtual c =>
      match d with
      | 0 => False
      | d + 1 =>
        match P.selectVirtual c sig.sub with
        | .jimple m =>
          match m.decl.body with
          | some b => bodyWP P (callWPT P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
        | .native lc =>
          match args with
          | .ref a :: rest =>
            match σ.heap a with
            | some (.plain c' fs) =>
              c' = c ∧
              match Native.plainInst P sig lc a c fs rest σ with
              | some r => wpR (callWPT P Γ d) r (fun ev => K ev.toOutcome)
              | none => K (.wrong "no model for library method")
            | _ => False
          | _ => False
        | .none why => P.concrete c = true ∧ K (.wrong why)

/-! ### `callWPT` is stronger than `callWP` -/

section Mono
variable {P : Program}

/-- `wpR` is monotone in the handler and the postcondition. -/
theorem wpR_le {H₁ H₂ : Handler}
    (hH : ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H₁ sig c args σ K → H₂ sig c args σ K')
    {α : Type} : ∀ (r : Res α) (Q Q' : α → Prop), (∀ a, Q a → Q' a) → wpR H₁ r Q → wpR H₂ r Q'
  | .ret a, Q, Q', hQ, h => hQ a h
  | .call sig c args σ k, Q, Q', hQ, h =>
    hH sig c args σ _ _ (fun o ho => wpR_le hH (k o) Q Q' hQ ho) h
  | .choose k, Q, Q', hQ, h => fun n => wpR_le hH (k n) Q Q' hQ (h n)

/-- `bodyWP` is monotone in the handler and the postcondition. -/
theorem bodyWP_le {H₁ H₂ : Handler}
    (hH : ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H₁ sig c args σ K → H₂ sig c args σ K')
    (b : Body) (I : Cuts) (Post Post' : Outcome → Prop) (hPost : ∀ o, Post o → Post' o) :
    ∀ n pc fr σ, bodyWP P H₁ b I Post n pc fr σ → bodyWP P H₂ b I Post' n pc fr σ
  | 0, _, _, _, h => h
  | n + 1, pc, fr, σ, h => by
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact hPost o
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact bodyWP_le hH b I Post Post' hPost n pc' fr' σ'

/-- A termination answer is a partial-correctness answer. -/
theorem callWPT_le (Γ : SpecEnv) :
    ∀ d sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) →
      callWPT P Γ d sig c args σ K → callWP P Γ d sig c args σ K' := by
  intro d
  induction d with
  | zero =>
    intro sig c args σ K K' hK h
    unfold callWPT at h; unfold callWP
    cases hΓ : Γ sig <;> cases c <;> simp only [hΓ] at h ⊢
    all_goals first
      | exact h.elim
      | exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
      | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, fun o ho => hK o (h.2.2.2.2.2 o ho)⟩
  | succ d ih =>
    intro sig c args σ K K' hK h
    unfold callWPT at h; unfold callWP
    cases hΓ : Γ sig with
    | some S =>
      cases c <;> simp only [hΓ] at h ⊢
      · exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
      · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, fun o ho => hK o (h.2.2.2.2.2 o ho)⟩
    | none =>
      cases c with
      | method m =>
        simp only [hΓ] at h ⊢
        cases hb : m.decl.body with
        | none => simp only [hb] at h ⊢; exact hK _ h
        | some b => simp only [hb] at h ⊢; exact bodyWP_le ih b [] K K' hK inlineFuel 0 _ σ h
      | virtual c =>
        simp only [hΓ] at h ⊢
        cases hsel : P.selectVirtual c sig.sub with
        | jimple m =>
          simp only [hsel] at h ⊢
          cases hb : m.decl.body with
          | none => simp only [hb] at h ⊢; exact hK _ h
          | some b => simp only [hb] at h ⊢; exact bodyWP_le ih b [] K K' hK inlineFuel 0 _ σ h
        | native lc =>
          simp only [hsel] at h ⊢
          rcases args with _ | ⟨v, rest⟩
          · exact h.elim
          · cases v with
            | ref a =>
              simp only at h ⊢
              cases hh : σ.heap a with
              | none => simp only [hh] at h
              | some o =>
                cases o with
                | plain c' fs =>
                  simp only [hh] at h ⊢
                  intro hc
                  obtain ⟨-, h2⟩ := h
                  cases hp : Native.plainInst P sig lc a c fs rest σ with
                  | none => simp only [hp] at h2 ⊢; exact hK _ h2
                  | some r =>
                    simp only [hp] at h2 ⊢
                    exact wpR_le ih r _ _ (fun ev hev => hK _ hev) h2
                | _ => simp only [hh] at h
            | _ => exact h.elim
        | none why =>
          simp only [hsel] at h ⊢
          exact fun _ => hK _ h.2

end Mono

/-! ### The verification condition -/

/-- Termination annotations of a method's loops: per cut point an invariant and a variant (a natural
    number), both functions of the entry arguments and the entry state. -/
abbrev TermCuts := List (Nat × (List Value → State → Frame → State → Prop) ×
  (List Value → State → Frame → State → Nat))

/-- The cut assertions of the entry path: the invariants. -/
def TermCuts.inv (A : TermCuts) (args : List Value) (σ0 : State) : Cuts :=
  A.map fun p => (p.1, p.2.1 args σ0)

/-- The cut assertions of the paths from a cut point whose variant had the value `v`: the next cut
    point's invariant, and a smaller variant. -/
def TermCuts.dec (A : TermCuts) (args : List Value) (σ0 : State) (v : Nat) : Cuts :=
  A.map fun p => (p.1, fun fr σ => p.2.1 args σ0 fr σ ∧ p.2.2 args σ0 fr σ < v)

/-- Termination VC of method `m` at rank `r`: the entry path, and from every cut point the paths to
    the next cut points (the variant decreasing) or out of the method, each explored for at most
    `fuel` statements; calls answered by `callWPT` with the contracts of rank below `r`. -/
def TermVC (P : Program) (Γ : SpecEnv) (rank : MethodSig → Nat) (r d : Nat) (m : MethodRef)
    (S : Spec) (A : TermCuts) (fuel : Nat) : Prop :=
  ∃ b, m.decl.body = some b ∧
  ∀ args σ0, S.pre args σ0 →
    (let fr0 := Frame.init m.decl.mods.isStatic args
     match (A.inv args σ0).lookup 0 with
     | some a => a fr0 σ0
     | none => bodyWP P (callWPT P (Γ.below rank r) d) b (A.inv args σ0) (fun _ => True) fuel 0 fr0 σ0) ∧
    ∀ p ∈ A, ∀ fr σ, p.2.1 args σ0 fr σ →
      bodyWP P (callWPT P (Γ.below rank r) d) b (A.dec args σ0 (p.2.2 args σ0 fr σ)) (fun _ => True)
        fuel p.1 fr σ

/-- Termination VC of a library method selected for a virtual call on application class `c`: the
    receiver is an object of class `c`, and the model's callbacks terminate. -/
def NativeTermVC (P : Program) (Γ : SpecEnv) (rank : MethodSig → Nat) (r d : Nat) (sig : MethodSig)
    (c lc : ClassName) (S : Spec) : Prop :=
  ∀ args σ, S.pre args σ → ∃ a rest fs, args = .ref a :: rest ∧ σ.heap a = some (.plain c fs) ∧
    ∀ rq, Native.plainInst P sig lc a c fs rest σ = some rq →
      wpR (callWPT P (Γ.below rank r) d) rq (fun _ => True)

/-- Termination annotations of a program fragment. -/
structure TermAnnotations where
  cuts : MethodRef → TermCuts := fun _ => []
  fuel : MethodRef → Nat := fun _ => 1000

/-- Termination VCs of every implementation of every contract in `Γ`, each method at the rank of its
    contract. -/
def AllTermVC (P : Program) (Γ : SpecEnv) (rank : MethodSig → Nat) (d : Nat) (Ann : TermAnnotations) :
    Prop :=
  ∀ sig S, Γ sig = some S →
    (∀ m, Targets P sig m → TermVC P Γ rank (rank sig) d m S (Ann.cuts m) (Ann.fuel m)) ∧
    (∀ c, P.isProgClass c = true → P.isSubclass c sig.cls = some true → P.staticDecl sig = false →
      P.concrete c = true →
      match P.selectVirtual c sig.sub with
      | .jimple m => TermVC P Γ rank (rank sig) d m S (Ann.cuts m) (Ann.fuel m)
      | .native lc => NativeTermVC P Γ rank (rank sig) d sig c lc S
      | .none _ => True)

/-- Every call answered by the contract `S` of `sig` terminates. -/
def ContractTerm (P : Program) (sig : MethodSig) (S : Spec) : Prop :=
  (∀ m, Targets P sig m → ∀ args σ, S.pre args σ → MTerm P m args σ) ∧
  (∀ c, P.isProgClass c = true → P.isSubclass c sig.cls = some true → P.staticDecl sig = false →
    P.concrete c = true → ∀ args σ, S.pre args σ → VTerm P sig c args σ)

/-! ### Soundness -/

section TermSound
variable {P : Program}

theorem valid_below {Γ : SpecEnv} (rank : MethodSig → Nat) (r : Nat) (hV : Valid P Γ) :
    Valid P (Γ.below rank r) := by
  intro sig S h
  unfold SpecEnv.below at h
  split at h
  · exact hV sig S h
  · cases h

theorem lookup_map_mem {β γ : Type} (f : β → γ) :
    ∀ {l : List (Nat × β)} {a : Nat} {x : γ},
      (l.map fun p => (p.1, f p.2)).lookup a = some x → ∃ y, (a, y) ∈ l ∧ x = f y
  | [], _, _, h => by simp at h
  | (b, y) :: l, a, x, h => by
    simp only [List.map_cons, List.lookup_cons] at h
    by_cases hab : a = b
    · subst hab
      simp only [beq_self_eq_true, Option.some.injEq] at h
      exact ⟨y, List.mem_cons_self .., h.symm⟩
    · have hb : (a == b) = false := by simpa using hab
      rw [hb] at h
      obtain ⟨y', hy', hx⟩ := lookup_map_mem f h
      exact ⟨y', List.mem_cons_of_mem _ hy', hx⟩

variable {Γr : SpecEnv}

/-- The core: under contracts that hold and terminate, a `callWPT` answer terminates, and so does
    a body whose cut points terminate. -/
theorem term_core (hVr : Valid P Γr) (hTr : ∀ sig S, Γr sig = some S → ContractTerm P sig S) :
    ∀ d, (∀ {α} (q : Res α) (Q : α → Prop), wpR (callWPT P Γr d) q Q → RTerm P q) ∧
      (∀ b (I : Cuts) (Post : Outcome → Prop),
        (∀ pc A, I.lookup pc = some A → ∀ fr σ, A fr σ → BTerm P b pc fr σ) →
        ∀ n pc fr σ, bodyWP P (callWPT P Γr d) b I Post n pc fr σ → BTerm P b pc fr σ) := by
  intro d
  induction d with
  | zero =>
    have h1 : ∀ {α} (q : Res α) (Q : α → Prop), wpR (callWPT P Γr 0) q Q → RTerm P q := by
      intro α q
      induction q with
      | ret a => intro _ _; exact .ret
      | call sig c args σ k ih =>
        intro Q h
        simp only [wpR] at h
        unfold callWPT at h
        rcases hΓ : Γr sig with _ | S <;> cases c <;> simp only [hΓ] at h
        · rename_i m
          obtain ⟨ht, hpre, hK⟩ := h
          exact .callM ((hTr sig S hΓ).1 m ht args σ hpre)
            (fun o ho => ih o Q (hK o ((hVr sig S hΓ).1 m ht args σ o hpre ho)))
        · rename_i c
          obtain ⟨hpc, hsub, hst, hconc, hpre, hK⟩ := h
          exact .callV ((hTr sig S hΓ).2 c hpc hsub hst hconc args σ hpre)
            (fun o ho => ih o Q (hK o ((hVr sig S hΓ).2 c hpc hsub hst args σ o hpre ho)))
      | choose k ih => intro Q h; exact .choose (fun n => ih n Q (h n))
    refine ⟨h1, ?_⟩
    intro b I Post hcut n
    induction n with
    | zero => intro _ _ _ h; exact h.elim
    | succ n ihn =>
      intro pc fr σ h
      simp only [bodyWP] at h
      refine .mk (h1 _ _ h) (fun r pc' fr' σ' hrx ha => ?_)
      have h2 := rexec_okV hVr hrx 0 _ (wpR_le (callWPT_le Γr 0) _ _ _ (fun _ x => x) h)
      simp only [ha] at h2
      split at h2
      · next A hA => exact hcut pc' A hA fr' σ' h2
      · exact ihn pc' fr' σ' h2
  | succ d ihd =>
    obtain ⟨ihR, ihB⟩ := ihd
    have h1 : ∀ {α} (q : Res α) (Q : α → Prop), wpR (callWPT P Γr (d + 1)) q Q → RTerm P q := by
      intro α q
      induction q with
      | ret a => intro _ _; exact .ret
      | call sig c args σ k ih =>
        intro Q h
        simp only [wpR] at h
        unfold callWPT at h
        rcases hΓ : Γr sig with _ | S
        · cases c with
          | method m =>
            simp only [hΓ] at h
            -- the outcomes of the inlined body satisfy the rest (partial correctness of inlining)
            have hK : ∀ o, MExec P m args σ o → wpR (callWPT P Γr (d + 1)) (k o) Q := by
              intro o ho
              refine minline_okV hVr ho d (fun o => wpR (callWPT P Γr (d + 1)) (k o) Q) ?_
              cases hb : m.decl.body with
              | none => simpa only [hb] using h
              | some b =>
                simp only [hb] at h ⊢
                exact bodyWP_le (callWPT_le Γr d) b [] _ _ (fun _ x => x) inlineFuel 0 _ σ h
            cases hb : m.decl.body with
            | none => exact .callM (.noBody hb) (fun o ho => ih o Q (hK o ho))
            | some b =>
              simp only [hb] at h
              exact .callM (.body hb (ihB b [] _ (by intro pc A hA; simp at hA) inlineFuel 0 _ σ h))
                (fun o ho => ih o Q (hK o ho))
          | virtual c =>
            simp only [hΓ] at h
            have hK : ∀ o, VExec P sig c args σ o → wpR (callWPT P Γr (d + 1)) (k o) Q := by
              intro o ho
              refine vinline_okV hVr ho d (fun o => wpR (callWPT P Γr (d + 1)) (k o) Q) ?_
              cases hsel : P.selectVirtual c sig.sub with
              | jimple m =>
                simp only [hsel] at h ⊢
                cases hb : m.decl.body with
                | none => simpa only [hb] using h
                | some b =>
                  simp only [hb] at h ⊢
                  exact bodyWP_le (callWPT_le Γr d) b [] _ _ (fun _ x => x) inlineFuel 0 _ σ h
              | native lc =>
                simp only [hsel] at h ⊢
                rcases args with _ | ⟨v, rest⟩
                · exact h.elim
                · cases v with
                  | ref a =>
                    simp only at h ⊢
                    cases hh : σ.heap a with
                    | none => simp only [hh] at h
                    | some ob =>
                      cases ob with
                      | plain c' fs =>
                        simp only [hh] at h ⊢
                        intro _
                        obtain ⟨-, h2⟩ := h
                        cases hp : Native.plainInst P sig lc a c fs rest σ with
                        | none => simpa only [hp] using h2
                        | some rq =>
                          simp only [hp] at h2 ⊢
                          exact wpR_le (callWPT_le Γr d) rq _ _ (fun _ x => x) h2
                      | _ => simp only [hh] at h
                  | _ => exact h.elim
              | none why =>
                simp only [hsel] at h ⊢
                exact fun _ => h.2
            refine .callV ?_ (fun o ho => ih o Q (hK o ho))
            cases hsel : P.selectVirtual c sig.sub with
            | jimple m =>
              simp only [hsel] at h
              cases hb : m.decl.body with
              | none => exact .jimple hsel (.noBody hb)
              | some b =>
                simp only [hb] at h
                exact .jimple hsel (.body hb (ihB b [] _ (by intro pc A hA; simp at hA) inlineFuel 0 _ σ h))
            | native lc =>
              simp only [hsel] at h
              rcases args with _ | ⟨v, rest⟩
              · exact h.elim
              · cases v with
                | ref a =>
                  simp only at h
                  cases hh : σ.heap a with
                  | none => simp only [hh] at h
                  | some ob =>
                    cases ob with
                    | plain c' fs =>
                      simp only [hh] at h
                      obtain ⟨hc, h2⟩ := h
                      subst hc
                      refine .native hsel hh (fun rq hrq => ?_)
                      simp only [hrq] at h2
                      exact (ihR rq _ h2)
                    | _ => simp only [hh] at h
                | _ => exact h.elim
            | none why =>
              simp only [hsel] at h
              exact .none hsel h.1
        · cases c with
          | method m =>
            simp only [hΓ] at h
            obtain ⟨ht, hpre, hK⟩ := h
            exact .callM ((hTr sig S hΓ).1 m ht args σ hpre)
              (fun o ho => ih o Q (hK o ((hVr sig S hΓ).1 m ht args σ o hpre ho)))
          | virtual c =>
            simp only [hΓ] at h
            obtain ⟨hpc, hsub, hst, hconc, hpre, hK⟩ := h
            exact .callV ((hTr sig S hΓ).2 c hpc hsub hst hconc args σ hpre)
              (fun o ho => ih o Q (hK o ((hVr sig S hΓ).2 c hpc hsub hst args σ o hpre ho)))
      | choose k ih => intro Q h; exact .choose (fun n => ih n Q (h n))
    refine ⟨h1, ?_⟩
    intro b I Post hcut n
    induction n with
    | zero => intro _ _ _ h; exact h.elim
    | succ n ihn =>
      intro pc fr σ h
      simp only [bodyWP] at h
      refine .mk (h1 _ _ h) (fun r pc' fr' σ' hrx ha => ?_)
      have h2 := rexec_okV hVr hrx (d + 1) _ (wpR_le (callWPT_le Γr (d + 1)) _ _ _ (fun _ x => x) h)
      simp only [ha] at h2
      split at h2
      · next A hA => exact hcut pc' A hA fr' σ' h2
      · exact ihn pc' fr' σ' h2

end TermSound

/-! ### From the VCs to termination -/

section TermLink
variable {P : Program} {Γ : SpecEnv} {rank : MethodSig → Nat}

/-- **One method**: if the contracts `Γ` hold, the callees of rank below `r` terminate, and the
    termination VC of `m` holds at rank `r`, every call of `m` on arguments satisfying the
    precondition terminates. -/
theorem TermVC.mterm {r d : Nat} {m : MethodRef} {S : Spec} {A : TermCuts} {fuel : Nat}
    (hV : Valid P Γ) (hT : ∀ sig S', (Γ.below rank r) sig = some S' → ContractTerm P sig S')
    (h : TermVC P Γ rank r d m S A fuel) : ∀ args σ0, S.pre args σ0 → MTerm P m args σ0 := by
  intro args σ0 hpre
  obtain ⟨b, hb, hvc⟩ := h
  obtain ⟨hentry, hcuts⟩ := hvc args σ0 hpre
  have core := (term_core (valid_below rank r hV) hT d).2 b
  -- every cut state terminates, by strong induction on its variant
  have hcut : ∀ v, ∀ p ∈ A, ∀ fr σ, p.2.1 args σ0 fr σ → p.2.2 args σ0 fr σ = v →
      BTerm P b p.1 fr σ := by
    intro v
    induction v using Nat.strongRecOn with
    | _ v ih =>
      intro p hp fr σ hinv hv
      refine core (A.dec args σ0 (p.2.2 args σ0 fr σ)) _ ?_ fuel p.1 fr σ (hcuts p hp fr σ hinv)
      intro pc X hX fr' σ' hx
      unfold TermCuts.dec at hX
      obtain ⟨y, hy, rfl⟩ := lookup_map_mem
        (fun (y : (List Value → State → Frame → State → Prop) × (List Value → State → Frame → State → Nat)) =>
          fun fr₁ σ₁ => y.1 args σ0 fr₁ σ₁ ∧ y.2 args σ0 fr₁ σ₁ < p.2.2 args σ0 fr σ) hX
      exact ih _ (hv ▸ hx.2) (pc, y) hy fr' σ' hx.1 rfl
  have hcutI : ∀ pc X, (A.inv args σ0).lookup pc = some X → ∀ fr σ, X fr σ → BTerm P b pc fr σ := by
    intro pc X hX fr σ hx
    unfold TermCuts.inv at hX
    obtain ⟨y, hy, rfl⟩ := lookup_map_mem
      (fun (y : (List Value → State → Frame → State → Prop) × (List Value → State → Frame → State → Nat)) =>
        y.1 args σ0) hX
    exact hcut _ (pc, y) hy fr σ hx rfl
  refine .body hb ?_
  simp only at hentry
  split at hentry
  · next X hX => exact hcutI 0 X hX _ _ hentry
  · exact core (A.inv args σ0) _ hcutI fuel 0 _ σ0 hentry

/-- A library method selected for a virtual call terminates when its termination VC holds. -/
theorem NativeTermVC.vterm {r d : Nat} {sig : MethodSig} {c lc : ClassName} {S : Spec}
    (hV : Valid P Γ) (hT : ∀ sig S', (Γ.below rank r) sig = some S' → ContractTerm P sig S')
    (hsel : P.selectVirtual c sig.sub = .native lc) (h : NativeTermVC P Γ rank r d sig c lc S) :
    ∀ args σ, S.pre args σ → VTerm P sig c args σ := by
  intro args σ hpre
  obtain ⟨a, rest, fs, rfl, hh, hr⟩ := h args σ hpre
  exact .native hsel hh (fun rq hrq => (term_core (valid_below rank r hV) hT d).1 rq _ (hr rq hrq))

/-- **Termination of a program fragment**: if the contracts `Γ` hold and every contract has its
    termination VC (`AllTermVC`, callees strictly lower in `rank`), every call answered by a
    contract of `Γ` terminates. -/
theorem AllTermVC.term {d : Nat} {Ann : TermAnnotations} (hV : Valid P Γ) (hT : AllTermVC P Γ rank d Ann) :
    ∀ sig S, Γ sig = some S → ContractTerm P sig S := by
  suffices h : ∀ r, ∀ sig S, Γ sig = some S → rank sig = r → ContractTerm P sig S from
    fun sig S hΓ => h _ sig S hΓ rfl
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro sig S hΓ hr
    have hbelow : ∀ sig' S', (Γ.below rank r) sig' = some S' → ContractTerm P sig' S' := by
      intro sig' S' h'
      unfold SpecEnv.below at h'
      split at h'
      · next hlt => exact ih _ hlt sig' S' h' rfl
      · cases h'
    obtain ⟨hm, hv⟩ := hT sig S hΓ
    refine ⟨fun m ht => ?_, fun c hpc hsub hst hconc => ?_⟩
    · exact TermVC.mterm hV hbelow (hr ▸ hm m ht)
    · have hc := hv c hpc hsub hst hconc
      cases hsel : P.selectVirtual c sig.sub with
      | jimple m =>
        simp only [hsel] at hc
        exact fun args σ hpre => .jimple hsel (TermVC.mterm hV hbelow (hr ▸ hc) args σ hpre)
      | native lc =>
        simp only [hsel] at hc
        exact NativeTermVC.vterm hV hbelow hsel (hr ▸ hc)
      | none why => exact fun args σ _ => .none hsel hconc

/-- **Total correctness**: a contract that holds (`Sat`) of a method that terminates (`MTerm`) has,
    for every argument list satisfying the precondition, an outcome, and every outcome satisfies the
    postcondition. -/
theorem total_of_sat_mterm {m : MethodRef} {S : Spec} (hs : Sat P m S)
    (ht : ∀ args σ, S.pre args σ → MTerm P m args σ) :
    ∀ args σ, S.pre args σ → (∃ o, MExec P m args σ o) ∧ ∀ o, MExec P m args σ o → S.post args σ o :=
  fun args σ hpre => ⟨(ht args σ hpre).run, fun o ho => hs args σ o hpre ho⟩

end TermLink

/-! ## Automation: `jterm` proves `TermVC` goals with the `jvc` loop -/

@[jsimp] theorem SpecEnv.below_def (Γ : SpecEnv) (rank : MethodSig → Nat) (r : Nat) (sig : MethodSig) :
    Γ.below rank r sig = if rank sig < r then Γ sig else none := rfl

attribute [jsimp] TermCuts.inv TermCuts.dec

@[jsimp] theorem callWPT_def (P : Program) (Γ : SpecEnv) (d : Nat) (sig : MethodSig) (callee : Callee)
    (args : List Value) (σ : State) (K : Outcome → Prop) :
    callWPT P Γ d sig callee args σ K =
      match Γ sig, callee with
      | some S, .method m => Targets P sig m ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
      | some S, .virtual c => P.isProgClass c = true ∧ P.isSubclass c sig.cls = some true ∧
          P.staticDecl sig = false ∧ P.concrete c = true ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
      | none, .method m =>
        match d with
        | 0 => False
        | d + 1 =>
          match m.decl.body with
          | some b => bodyWP P (callWPT P Γ d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
      | none, .virtual c =>
        match d with
        | 0 => False
        | d + 1 =>
          match P.selectVirtual c sig.sub with
          | .jimple m =>
            match m.decl.body with
            | some b => bodyWP P (callWPT P Γ d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
            | none => K (.wrong "abstract or native method")
          | .native lc =>
            match args with
            | .ref a :: rest =>
              match σ.heap a with
              | some (.plain c' fs) =>
                c' = c ∧
                match Native.plainInst P sig lc a c fs rest σ with
                | some r => wpR (callWPT P Γ d) r (fun ev => K ev.toOutcome)
                | none => K (.wrong "no model for library method")
              | _ => False
            | _ => False
          | .none why => P.concrete c = true ∧ K (.wrong why) := by
  rw [callWPT.eq_def]; rfl

open Lean Elab Tactic in
/-- `jterm`: prove `TermVC P Γ rank r d m S A fuel` — selects the body, unfolds the contract, the
    termination annotations, the environment and the rank, and runs `jvc`. -/
syntax (name := jtermTac) "jterm" (" [" ident,* "]")? : tactic

open Lean Elab Tactic in
@[tactic jtermTac] def evalJterm : Tactic := fun stx => do
  let extra : Array Ident := optIdents stx[1]
  let g ← getMainGoal
  let consts ← g.withContext do vcConstants (← g.getType)
  let tgt ← instantiateMVars (← g.getType)
  let args := tgt.getAppArgs
  let pick (i : Nat) (c : Name) : Bool :=
    match args[i]?.bind (·.getAppFn.constName?) with | some s => s == c | none => false
  let keep := consts.filter fun c => args.size == 9 && (pick 6 c || pick 7 c || pick 1 c || pick 2 c)
  let ids := keep.map mkIdent ++ extra
  if jimple.trace.get (← getOptions) then logInfo m!"jterm: unfolding {ids}"
  withJimpleHeartbeats do
  evalTactic (← `(tactic| refine ⟨_, rfl, ?_⟩))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    out := out ++ (← jvcGoal ids 400 g)
  setGoals out

/-! ## Linking termination results -/

section TermLinking
variable {P : Program}

/-- Termination annotations from loop invariants and one variant for all their cut points. -/
def Invariants.withVariant (A : Invariants) (v : List Value → State → Frame → State → Nat) : TermCuts :=
  A.map fun p => (p.1, p.2, v)

attribute [jsimp] Invariants.withVariant

/-- No contract below any rank. -/
theorem contractTerm_none (rank : MethodSig → Nat) (r : Nat) :
    ∀ sig S, SpecEnv.below (fun _ => none) rank r sig = some S → ContractTerm P sig S := by
  intro sig S h; simp [SpecEnv.below] at h

theorem below_some {Γ : SpecEnv} {rank : MethodSig → Nat} {r : Nat} {sig : MethodSig} {S : Spec}
    (h : (Γ.below rank r) sig = some S) : Γ sig = some S := by
  unfold SpecEnv.below at h; split at h; exact h; cases h

/-- The contracts of a table terminate when each of them does. -/
theorem Contracts.term_of_ok {T : Contracts} (h : ∀ p ∈ T, ContractTerm P p.1 p.2)
    (rank : MethodSig → Nat) (r : Nat) :
    ∀ sig S, (T.env.below rank r) sig = some S → ContractTerm P sig S := by
  intro sig S hΓ
  exact h (sig, S) (lookup_mem_dec (below_some hΓ))

/-- A virtual call selecting an application method terminates when the method does. -/
theorem vterm_of_jimple {sig : MethodSig} {c : ClassName} {m : MethodRef} {S : Spec}
    (hsel : P.selectVirtual c sig.sub = .jimple m) (hm : ∀ args σ, S.pre args σ → MTerm P m args σ) :
    ∀ args σ, S.pre args σ → VTerm P sig c args σ :=
  fun args σ hpre => .jimple hsel (hm args σ hpre)

/-- A virtual call on a concrete class whose selection fails terminates at once (`wrong`). -/
theorem vterm_of_none {sig : MethodSig} {c : ClassName} {why : String} {S : Spec}
    (hsel : P.selectVirtual c sig.sub = .none why) (hc : P.concrete c = true) :
    ∀ args σ, S.pre args σ → VTerm P sig c args σ :=
  fun _ _ _ => .none hsel hc

end TermLinking

open Lean Elab Tactic in
/-- `jcontract_term [h₁, …]`: prove `ContractTerm P sig S` for a concrete program from facts
    `hᵢ : ∀ args σ, S.pre args σ → MTerm P mᵢ args σ` about the implementations, as `jcontract_ok`
    does for `ContractOK`: every call target and every implementing application class is enumerated
    by evaluation (instance methods and constructors too). Abstract classes and the classes that are
    no subclasses drop out; a concrete class whose selection fails terminates at once; every other
    class must select the method of one of the given facts. -/
syntax (name := jcontractTermTac) "jcontract_term" (" [" term,* "]")? : tactic

open Lean Elab Tactic in
@[tactic jcontractTermTac] def evalJcontractTerm : Tactic := fun stx => do
  let facts : Array Term :=
    let s := stx[1]
    let s := if s.getNumArgs == 1 then s[0] else s
    if s.getNumArgs == 3 then s[1].getSepArgs.map (⟨·⟩) else #[]
  let useFact : TacticM Unit := do
    for f in facts do
      let s ← saveState
      try evalTactic (← `(tactic| exact $f)); return catch _ => s.restore
    throwError "jcontract_term: no given fact closes {← getMainTarget}"
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  let gs ← getGoals
  setGoals [gs[0]!]
  evalTactic (← `(tactic| intro m ht))
  evalTactic (← `(tactic| obtain ⟨hsel, hb⟩ := ht))
  evalTactic (← `(tactic| rcases hsel with h | h | ⟨hs, _⟩))
  for g in (← getGoals) do
    setGoals [g]
    evalTactic (← `(tactic| first
      | (have hn := congrArg MethodSig.name hs
         simp (config := { decide := true }) only [jground, clinitSig] at hn)
      | (simp (config := { decide := true }) only [jground, reduceCtorEq, Program.Target.jimple.injEq] at h
         try subst h
         try simp (config := { decide := true }) only [jground] at hb)))
    for g' in (← getGoals) do
      setGoals [g']
      useFact
  setGoals [gs[1]!]
  evalTactic (← `(tactic| intro c hpc hsub hst hconc))
  -- static methods: no virtual call
  let s ← saveState
  try
    evalTactic (← `(tactic| simp (config := { decide := true }) only [jground] at hst))
    if (← getGoals).isEmpty then return
    s.restore
  catch _ => s.restore
  -- instance methods (constructors included): the implementing application classes, enumerated
  evalTactic (← `(tactic| revert c))
  evalTactic (← `(tactic| apply forall_progClass_of_mem))
  evalTactic (← `(tactic| simp (config := { decide := true }) only [jground, List.forall_mem_cons,
    List.forall_mem_nil, List.not_mem_nil, false_implies, implies_true, and_true, true_implies]))
  evalTactic (← `(tactic| repeat' constructor))
  for g in (← getGoals) do
    setGoals [g]
    evalTactic (← `(tactic| first
      | (intro hf; exact False.elim hf)
      | (exact vterm_of_none rfl rfl)
      | skip))
    for g' in (← getGoals) do
      setGoals [g']
      let mut done := false
      let mut lastErr : MessageData := m!""
      for f in facts do
        let s ← saveState
        try
          -- the method is fixed by the fact, then its selection is checked by evaluation
          evalTactic (← `(tactic| exact vterm_of_jimple (by exact rfl) $f))
          done := true
          break
        catch e => lastErr := e.toMessageData; s.restore
      unless done do
        throwError "jcontract_term: no given fact implements {← getMainTarget}\n{lastErr}"

end Jimple
