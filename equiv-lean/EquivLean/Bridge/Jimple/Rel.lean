import EquivLean.Bridge.Jimple.Behaves

/-!
# Relational product of two Jimple methods (Java ≡ Java)

`Sim R t s` between two Java calls needs, for every terminating run of the target `t`, a
terminating run of the source `s`.  Partial correctness of `s` alone cannot supply one, so the
product executes the two bodies in lockstep between paired cut points and *builds* the source's
run segment by segment along the target's run:

* the target is executed universally, with JimpleLean's `bodyWP` (its calls answered by
  `callWP`, i.e. inlining);
* the source is executed existentially, with `bodyEWP` (`ewpR`: some resolution of the
  nondeterministic choices, callee runs that exist);
* `pairs : List (Nat × Nat × Coupling)` lists the lockstep points `(pc₁, pc₂, J)` (loop heads,
  and the entry `(0, 0, J₀)`).  From a pair `(pc₁, pc₂, J)` with `J fr₁ σ₁ fr₂ σ₂`, the target's
  symbolic execution must, at its next cut point `pc₁'`, find the source able to reach a
  `pc₂'` with `(pc₁', pc₂', J') ∈ pairs` and `J'` (the source's assertion is nested in the
  target's cut assertion), and at a final outcome `o₁` find the source able to finish with an
  outcome `o₂` related by `RelO R` (`ProdVC`);
* the source may also go wrong: then the source is unsafe and nothing is owed.

Soundness (`prod_sound`, `sim_of_prodVC`) is proved against `MExec`/`BExec` from JimpleLean's
own `bexec_ok`; the only new semantic facts are `ewpR_sound` and `bodyEWP_sound`
(existential execution builds `RExec`/`BExec` derivations) and the monotonicity of `bodyWP`.
Loop-free methods use the single pair `(0, 0, J₀)`.
-/

open Jimple

namespace EquivLean.Jimple

/-! ## Existential execution -/

/-- Some result of the request tree `r` satisfies `Q`: some choice for every `choose`, and an
existing run of every callee. -/
def ewpR (P : Program) {α : Type} : Res α → (α → Prop) → Prop
  | .ret a, Q => Q a
  | .call _ (.method m) args σ k, Q => ∃ o, MExec P m args σ o ∧ ewpR P (k o) Q
  | .call sig (.virtual c) args σ k, Q => ∃ o, VExec P sig c args σ o ∧ ewpR P (k o) Q
  | .choose k, Q => ∃ n, ewpR P (k n) Q

@[simp] theorem ewpR_ret (P : Program) {α : Type} (a : α) (Q : α → Prop) :
    ewpR P (.ret a) Q = Q a := rfl

theorem ewpR_sound {P : Program} {α : Type} :
    ∀ (r : Res α) (Q : α → Prop), ewpR P r Q → ∃ a, RExec P r a ∧ Q a
  | .ret a, _, h => ⟨a, .ret, h⟩
  | .call _ (.method _) _ _ k, Q, ⟨o, ho, h⟩ =>
    let ⟨a, ha, hq⟩ := ewpR_sound (k o) Q h
    ⟨a, .callM ho ha, hq⟩
  | .call _ (.virtual _) _ _ k, Q, ⟨o, ho, h⟩ =>
    let ⟨a, ha, hq⟩ := ewpR_sound (k o) Q h
    ⟨a, .callV ho ha, hq⟩
  | .choose k, Q, ⟨n, h⟩ =>
    let ⟨a, ha, hq⟩ := ewpR_sound (k n) Q h
    ⟨a, .choose n ha, hq⟩

/-- Existential symbolic execution of body `b` from `(pc, fr, σ)` for at most `n` statements:
some path ends in an outcome satisfying `Post`, or reaches a cut point whose assertion holds. -/
def bodyEWP (P : Program) (b : Body) (I : Cuts) (Post : Outcome → Prop) :
    Nat → Nat → Frame → State → Prop
  | 0, _, _, _ => False
  | n + 1, pc, fr, σ =>
    ewpR P (step P b pc fr σ) fun r =>
      match afterStep P b pc fr r with
      | .done o => Post o
      | .cont pc' fr' σ' =>
        match I.lookup pc' with
        | some A => A fr' σ'
        | none => bodyEWP P b I Post n pc' fr' σ'

/-- One unfolding of `bodyEWP` (for symbolic execution: `jbodyEWP`). -/
def bodyEWPStep (P : Program) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (n pc : Nat) (fr : Frame) (σ : State) : Prop :=
  ewpR P (step P b pc fr σ) fun r =>
    match afterStep P b pc fr r with
    | .done o => Post o
    | .cont pc' fr' σ' =>
      match I.lookup pc' with
      | some A => A fr' σ'
      | none => bodyEWP P b I Post n pc' fr' σ'

theorem bodyEWP_succ (P : Program) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (n pc : Nat) (fr : Frame) (σ : State) :
    bodyEWP P b I Post (n + 1) pc fr σ = bodyEWPStep P b I Post n pc fr σ := rfl

open Lean Meta in
/-- `jbodyEWP`: unfold `bodyEWP` at a literal program counter and fuel only (as JimpleLean's
`jbodyWP` does for `bodyWP`), so that `jvc [jbodyEWP, bodyEWPStep, …]` executes the source
statement by statement along each path. -/
dsimproc jbodyEWP (bodyEWP _ _ _ _ _ _ _ _) := fun e => do
  if e.hasLooseBVars then return .continue
  let_expr bodyEWP P b I Post n pc fr σ := e | return .continue
  let natOf (x : Lean.Expr) : Option Nat := x.nat? <|> x.rawNatLit?
  let some _ := natOf pc | return .continue
  let some nv := natOf n | return .continue
  if nv = 0 then return .done (mkConst ``False)
  return .visit (mkAppN (mkConst ``bodyEWPStep) #[P, b, I, Post, mkNatLit (nv - 1), pc, fr, σ])

/-- `(pc', fr', σ')` lies on a way from `(pc, fr, σ)`: every run from the former is (the end
of) a run from the latter. -/
def Prefix (P : Program) (b : Body) (pc : Nat) (fr : Frame) (σ : State)
    (pc' : Nat) (fr' : Frame) (σ' : State) : Prop :=
  ∀ o, BExec P b pc' fr' σ' o → BExec P b pc fr σ o

theorem Prefix.trans {P : Program} {b : Body} {pc pc' pc'' : Nat} {fr fr' fr'' : Frame}
    {σ σ' σ'' : State} (h₁ : Prefix P b pc fr σ pc' fr' σ')
    (h₂ : Prefix P b pc' fr' σ' pc'' fr'' σ'') : Prefix P b pc fr σ pc'' fr'' σ'' :=
  fun o ho => h₁ o (h₂ o ho)

/-- **Existential execution builds derivations**: a run from `(pc, fr, σ)` with an outcome
satisfying `Post`, or a cut point whose assertion holds on a way from `(pc, fr, σ)`. -/
theorem bodyEWP_sound {P : Program} {b : Body} {I : Cuts} {Post : Outcome → Prop} :
    ∀ n pc fr σ, bodyEWP P b I Post n pc fr σ →
      (∃ o, BExec P b pc fr σ o ∧ Post o) ∨
      (∃ pc' A fr' σ', I.lookup pc' = some A ∧ A fr' σ' ∧ Prefix P b pc fr σ pc' fr' σ')
  | 0, _, _, _, h => h.elim
  | n + 1, pc, fr, σ, h => by
    obtain ⟨r, hr, hq⟩ := ewpR_sound _ _ h
    try dsimp only at hq
    cases hc : afterStep P b pc fr r with
    | done o =>
      rw [hc] at hq
      exact .inl ⟨o, .done hr hc, hq⟩
    | cont pc' fr' σ' =>
      rw [hc] at hq
      try dsimp only at hq
      cases hl : I.lookup pc' with
      | some A =>
        rw [hl] at hq
        exact .inr ⟨pc', A, fr', σ', hl, hq, fun o ho => .cont hr hc ho⟩
      | none =>
        rw [hl] at hq
        rcases bodyEWP_sound n pc' fr' σ' hq with ⟨o, ho, hp⟩ | ⟨pc'', A, fr'', σ'', hl', hA, hpre⟩
        · exact .inl ⟨o, .cont hr hc ho, hp⟩
        · exact .inr ⟨pc'', A, fr'', σ'', hl', hA, fun o ho => .cont hr hc (hpre o ho)⟩

/-- Without cut points, existential execution is a run. -/
theorem bodyEWP_nil_sound {P : Program} {b : Body} {Post : Outcome → Prop} {n pc : Nat}
    {fr : Frame} {σ : State} (h : bodyEWP P b [] Post n pc fr σ) :
    ∃ o, BExec P b pc fr σ o ∧ Post o := by
  rcases bodyEWP_sound n pc fr σ h with h | ⟨_, _, _, _, hl, _⟩
  · exact h
  · simp at hl

/-! ## Monotonicity of `bodyWP` -/

/-- A call handler that is monotone in its continuation. -/
def HMono (H : Handler) : Prop :=
  ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K'

theorem wpR_mono {H : Handler} (hH : HMono H) {α : Type} :
    ∀ (r : Res α) (Q Q' : α → Prop), (∀ a, Q a → Q' a) → wpR H r Q → wpR H r Q'
  | .ret a, _, _, hq, h => hq a h
  | .call sig c args σ k, Q, Q', hq, h =>
    hH sig c args σ _ _ (fun o ho => wpR_mono hH (k o) Q Q' hq ho) h
  | .choose k, Q, Q', hq, h => fun n => wpR_mono hH (k n) Q Q' hq (h n)

/-- Two cut lists with the same cut points, the assertions of the first implying those of the
second. -/
def CutsLe (I I' : Cuts) : Prop :=
  ∀ pc, (I.lookup pc = none ∧ I'.lookup pc = none) ∨
    ∃ A A', I.lookup pc = some A ∧ I'.lookup pc = some A' ∧ ∀ fr σ, A fr σ → A' fr σ

theorem CutsLe.refl (I : Cuts) : CutsLe I I := fun pc => by
  cases h : I.lookup pc with
  | none => exact .inl ⟨rfl, rfl⟩
  | some A => exact .inr ⟨A, A, rfl, rfl, fun _ _ h => h⟩

theorem bodyWP_mono {P : Program} {H : Handler} {b : Body} (hH : HMono H) {I I' : Cuts}
    {Post Post' : Outcome → Prop} (hI : CutsLe I I') (hP : ∀ o, Post o → Post' o) :
    ∀ n pc fr σ, bodyWP P H b I Post n pc fr σ → bodyWP P H b I' Post' n pc fr σ
  | 0, _, _, _, h => h
  | n + 1, pc, fr, σ, h => by
    simp only [bodyWP] at h ⊢
    refine wpR_mono hH _ _ _ (fun r hr => ?_) h
    try dsimp only at hr ⊢
    cases hc : afterStep P b pc fr r with
    | done o => rw [hc] at hr; exact hP o hr
    | cont pc' fr' σ' =>
      rw [hc] at hr
      try dsimp only at hr ⊢
      rcases hI pc' with ⟨h1, h2⟩ | ⟨A, A', h1, h2, hA⟩
      · rw [h1] at hr; rw [h2]
        exact bodyWP_mono hH hI hP n pc' fr' σ' hr
      · rw [h1] at hr; rw [h2]
        exact hA fr' σ' hr

/-- Inlining calls (no contracts) is monotone. -/
theorem callWP_mono (P : Program) : ∀ d, HMono (callWP P (fun _ => none) d)
  | 0 => by
    intro sig c args σ K K' _ h
    cases c <;> simp [callWP_def] at h
  | d + 1 => by
    intro sig c args σ K K' hK h
    have ih := callWP_mono P d
    cases c with
    | method m =>
      rw [callWP_def] at h ⊢
      try dsimp only at h ⊢
      cases hb : m.decl.body with
      | some b =>
        rw [hb] at h
        exact bodyWP_mono ih (CutsLe.refl []) hK _ _ _ _ h
      | none => rw [hb] at h; exact hK _ h
    | virtual cl =>
      rw [callWP_def] at h ⊢
      try dsimp only at h ⊢
      cases hs : P.selectVirtual cl sig.sub with
      | jimple m =>
        rw [hs] at h
        try dsimp only at h ⊢
        cases hb : m.decl.body with
        | some b =>
          rw [hb] at h
          exact bodyWP_mono ih (CutsLe.refl []) hK _ _ _ _ h
        | none => rw [hb] at h; exact hK _ h
      | native lc =>
        rw [hs] at h
        try dsimp only at h ⊢
        split
        · next a rest =>
          split
          · next c' fs hheap =>
            simp only [hheap] at h
            intro hc'
            have h' := h hc'
            split
            · next r hr =>
              simp only [hr] at h'
              exact wpR_mono ih _ _ _ (fun ev hev => hK _ hev) h'
            · next hr =>
              simp only [hr] at h'
              exact hK _ h'
          · trivial
        · trivial
      | none why =>
        rw [hs] at h
        exact fun hc => hK _ (h hc)

/-! ## The product -/

/-- A coupling of two frames and states. -/
abbrev Coupling := Frame → State → Frame → State → Prop

/-- Relation of final outcomes: a target that goes wrong must be matched by a source that goes
wrong; a source that goes wrong owes nothing; otherwise `R` on the observable outcomes. -/
def RelO (R : Out → Out → Prop) : Outcome → Outcome → Prop
  | _, .wrong _ => True
  | .wrong _, _ => False
  | .normal v σ, .normal v' σ' => R (.normal v σ) (.normal v' σ')
  | .normal v σ, .exc e' σ' => R (.normal v σ) (.exc e' σ')
  | .exc e σ, .normal v' σ' => R (.exc e σ) (.normal v' σ')
  | .exc e σ, .exc e' σ' => R (.exc e σ) (.exc e' σ')

/-- `(pc₁, pc₂)` is a lockstep pair whose coupling holds. -/
def PairRel (pairs : List (Nat × Nat × Coupling)) (pc₁ pc₂ : Nat) (fr₁ : Frame) (σ₁ : State)
    (fr₂ : Frame) (σ₂ : State) : Prop :=
  ∃ J, (pc₁, pc₂, J) ∈ pairs ∧ J fr₁ σ₁ fr₂ σ₂

/-- The source's cut points, while the target sits at `pc₁` in `(fr₁, σ₁)`: reaching one, the
pair must be coupled. -/
def srcCuts (pairs : List (Nat × Nat × Coupling)) (pc₁ : Nat) (fr₁ : Frame) (σ₁ : State) : Cuts :=
  pairs.map fun p => (p.2.1, PairRel pairs pc₁ p.2.1 fr₁ σ₁)

/-- The source goes wrong. -/
def IsWrong : Outcome → Prop
  | .wrong _ => True
  | _ => False

/-- The target's assertion at its cut point `pc₁`, the source being at `(pc₂, fr₂, σ₂)`: the
source reaches a coupled cut point (or goes wrong).  A separate definition, so that symbolic
execution of the target carries it unexpanded (unfold it at the leaves). -/
@[irreducible] def tgtAssert (P₂ : Program) (b₂ : Body) (pairs : List (Nat × Nat × Coupling)) (fuel₂ : Nat)
    (pc₂ : Nat) (fr₂ : Frame) (σ₂ : State) (pc₁ : Nat) (fr₁ : Frame) (σ₁ : State) : Prop :=
  bodyEWP P₂ b₂ (srcCuts pairs pc₁ fr₁ σ₁) IsWrong fuel₂ pc₂ fr₂ σ₂

/-- The target's cut points, the source being at `(pc₂, fr₂, σ₂)`. -/
def tgtCuts (P₂ : Program) (b₂ : Body) (pairs : List (Nat × Nat × Coupling)) (fuel₂ : Nat)
    (pc₂ : Nat) (fr₂ : Frame) (σ₂ : State) : Cuts :=
  pairs.map fun p => (p.1, tgtAssert P₂ b₂ pairs fuel₂ pc₂ fr₂ σ₂ p.1)

/-- The target's postcondition, the source being at `(pc₂, fr₂, σ₂)`: the source finishes with
a related outcome. -/
@[irreducible] def tgtPost (P₂ : Program) (b₂ : Body) (R : Out → Out → Prop) (fuel₂ : Nat)
    (pc₂ : Nat) (fr₂ : Frame) (σ₂ : State) (o₁ : Outcome) : Prop :=
  bodyEWP P₂ b₂ [] (RelO R o₁) fuel₂ pc₂ fr₂ σ₂

/-- **Verification conditions of the product**: from every coupled pair, the target's
symbolic execution (inlining depth `d`, `fuel₁` statements) reaches cut points where the
source can follow (`fuel₂` statements), or ends where the source can end with a related
outcome. -/
def ProdVC (P₁ : Program) (b₁ : Body) (P₂ : Program) (b₂ : Body)
    (pairs : List (Nat × Nat × Coupling)) (R : Out → Out → Prop) (d fuel₁ fuel₂ : Nat) : Prop :=
  ∀ p ∈ pairs, ∀ fr₁ σ₁ fr₂ σ₂, p.2.2 fr₁ σ₁ fr₂ σ₂ →
    bodyWP P₁ (callWP P₁ (fun _ => none) d) b₁ (tgtCuts P₂ b₂ pairs fuel₂ p.2.1 fr₂ σ₂)
      (tgtPost P₂ b₂ R fuel₂ p.2.1 fr₂ σ₂) fuel₁ p.1 fr₁ σ₁

theorem lookup_map_some {α γ : Type} {l : List α} {k : α → Nat} {f : α → γ} {pc : Nat} {A : γ}
    (h : (l.map fun x => (k x, f x)).lookup pc = some A) : ∃ x ∈ l, k x = pc ∧ A = f x := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons, List.lookup] at h
    split at h
    · next hx =>
      exact ⟨x, List.mem_cons_self, (by simpa using hx : pc = k x).symm, (Option.some.inj h).symm⟩
    · obtain ⟨y, hy, h1, h2⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, h1, h2⟩

/-- Two cut lists built from the same list, with pointwise implications. -/
theorem cutsLe_map {α : Type} (l : List α) (k : α → Nat) (f g : α → Frame → State → Prop)
    (h : ∀ x ∈ l, ∀ fr σ, f x fr σ → g x fr σ) :
    CutsLe (l.map fun x => (k x, f x)) (l.map fun x => (k x, g x)) := by
  induction l with
  | nil => intro pc; exact .inl ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro pc
    simp only [List.map_cons, List.lookup]
    split
    · exact .inr ⟨f x, g x, rfl, rfl, h x List.mem_cons_self⟩
    · exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) pc

/-- **Soundness of the product**: from a coupled pair, every run of the target has a matching
run of the source (related outcomes, `RelO R`). -/
theorem prod_sound {P₁ P₂ : Program} {b₁ b₂ : Body} {pairs : List (Nat × Nat × Coupling)}
    {R : Out → Out → Prop} {d fuel₁ fuel₂ : Nat} (hvc : ProdVC P₁ b₁ P₂ b₂ pairs R d fuel₁ fuel₂)
    {pc₁ pc₂ : Nat} {J : Coupling} (hp : (pc₁, pc₂, J) ∈ pairs) {fr₁ fr₂ : Frame}
    {σ₁ σ₂ : State} (hJ : J fr₁ σ₁ fr₂ σ₂) {o₁ : Outcome} (hB : BExec P₁ b₁ pc₁ fr₁ σ₁ o₁) :
    ∃ o₂, BExec P₂ b₂ pc₂ fr₂ σ₂ o₂ ∧ RelO R o₁ o₂ := by
  -- a source that can go wrong from its start owes nothing
  by_cases hw : ∃ msg, BExec P₂ b₂ pc₂ fr₂ σ₂ (.wrong msg)
  · obtain ⟨msg, hm⟩ := hw
    exact ⟨_, hm, by cases o₁ <;> trivial⟩
  -- global cut assertions: a coupled source configuration on a way from the source's start
  let G : Nat × Nat × Coupling → Frame → State → Prop := fun p fr σ =>
    ∃ pc fr' σ', PairRel pairs p.1 pc fr σ fr' σ' ∧ Prefix P₂ b₂ pc₂ fr₂ σ₂ pc fr' σ'
  let Icut : Cuts := pairs.map fun p => (p.1, G p)
  let Post : Outcome → Prop := fun o => o = o₁ → ∃ o₂, BExec P₂ b₂ pc₂ fr₂ σ₂ o₂ ∧ RelO R o₁ o₂
  -- from a coupled source configuration on a way from the start, the product VC gives the
  -- target's `bodyWP` with the global assertions
  have step : ∀ c c₂ J', (c, c₂, J') ∈ pairs → ∀ fr σ fr' σ', J' fr σ fr' σ' →
      Prefix P₂ b₂ pc₂ fr₂ σ₂ c₂ fr' σ' →
      bodyWP P₁ (callWP P₁ (fun _ => none) d) b₁ Icut Post fuel₁ c fr σ := by
    intro c c₂ J' hmem fr σ fr' σ' hJ' hpre
    have h := hvc (c, c₂, J') hmem fr σ fr' σ' hJ'
    refine bodyWP_mono (callWP_mono P₁ d) ?_ ?_ fuel₁ c fr σ h
    · refine cutsLe_map pairs Prod.fst _ G (fun x _ fr₁' σ₁' hA => ?_)
      simp only [tgtAssert] at hA
      rcases bodyEWP_sound _ _ _ _ hA with ⟨o₂, ho₂, hwr⟩ | ⟨pc', A₂, fr₂', σ₂', hl₂, hA₂, hpre₂⟩
      · cases o₂ with
        | wrong msg => exact absurd ⟨msg, hpre _ ho₂⟩ hw
        | normal => exact hwr.elim
        | exc => exact hwr.elim
      · obtain ⟨z, _, hz1, hz2⟩ := lookup_map_some (k := fun p : Nat × Nat × Coupling => p.2.1)
          (f := fun p : Nat × Nat × Coupling => PairRel pairs x.1 p.2.1 fr₁' σ₁') hl₂
        subst hz2
        refine ⟨pc', fr₂', σ₂', ?_, hpre.trans hpre₂⟩
        rw [← hz1]
        exact hA₂
    · intro o ho heq
      subst heq
      simp only [tgtPost] at ho
      obtain ⟨o₂, ho₂, hr⟩ := bodyEWP_nil_sound ho
      exact ⟨o₂, hpre _ ho₂, hr⟩
  have hAll : AllVC P₁ (fun _ => none) d ({} : Annotations) := fun _ _ h => by cases h
  have hI : ∀ c A, Icut.lookup c = some A → ∀ fr σ, A fr σ →
      bodyWP P₁ (callWP P₁ (fun _ => none) d) b₁ Icut Post fuel₁ c fr σ := by
    intro c A hl fr σ hA
    obtain ⟨x, _, hx1, hx2⟩ := lookup_map_some (k := Prod.fst) (f := G) hl
    subst hx2
    obtain ⟨pc, fr', σ', ⟨J', hmem, hJ'⟩, hpre⟩ := hA
    rw [hx1] at hmem
    exact step c pc J' hmem fr σ fr' σ' hJ' hpre
  have hstart := step pc₁ pc₂ J hp fr₁ σ₁ fr₂ σ₂ hJ (fun _ h => h)
  exact bexec_ok hAll hB d Icut Post hI fuel₁ hstart rfl

/-! ## Methods -/

/-- **Java ≡ Java, one direction**: two methods whose product verification conditions hold from
coupled entry frames simulate each other (`t ⊑ s`).  Termination of the source is not
assumed: the source's run is built in lockstep with the target's. -/
theorem sim_of_prodVC {P₁ P₂ : Program} {m₁ m₂ : MethodRef} {b₁ b₂ : Body}
    (hb₁ : m₁.decl.body = some b₁) (hb₂ : m₂.decl.body = some b₂)
    {pairs : List (Nat × Nat × Coupling)} {R : Out → Out → Prop} {d fuel₁ fuel₂ : Nat}
    (hvc : ProdVC P₁ b₁ P₂ b₂ pairs R d fuel₁ fuel₂) {J₀ : Coupling} (h0 : (0, 0, J₀) ∈ pairs)
    {args₁ args₂ : List Value} {σ₁ σ₂ : State}
    (hJ₀ : J₀ (Frame.init m₁.decl.mods.isStatic args₁) σ₁ (Frame.init m₂.decl.mods.isStatic args₂) σ₂) :
    Sim R (Call.mk P₁ m₁ args₁ σ₁) (Call.mk P₂ m₂ args₂ σ₂) := by
  have key : ∀ o₁, MExec P₁ m₁ args₁ σ₁ o₁ → ∃ o₂, MExec P₂ m₂ args₂ σ₂ o₂ ∧ RelO R o₁ o₂ := by
    intro o₁ h
    cases h with
    | body hb hB =>
      rw [hb₁] at hb; cases hb
      obtain ⟨o₂, hB₂, hr⟩ := prod_sound hvc h0 hJ₀ hB
      exact ⟨o₂, .body hb₂ hB₂, hr⟩
    | noBody hb => rw [hb₁] at hb; cases hb
  intro hs
  refine ⟨fun msg hm => ?_, fun ot hot => ?_⟩
  · obtain ⟨o₂, ho₂, hr⟩ := key _ hm
    cases o₂ with
    | wrong msg' => exact hs msg' ho₂
    | normal => exact hr.elim
    | exc => exact hr.elim
  · obtain ⟨o₂, ho₂, hr⟩ := key _ hot
    cases o₂ with
    | wrong msg' => exact absurd ho₂ (hs msg')
    | normal v σ' => exact ⟨.normal v σ', ho₂, by cases ot <;> exact hr⟩
    | exc e σ' => exact ⟨.exc e σ', ho₂, by cases ot <;> exact hr⟩

end EquivLean.Jimple
