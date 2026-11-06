/-
  Jimple/Logic.lean

  Program logic for Jimple: method contracts, a verification-condition generator, and its
  soundness theorem with respect to the relational semantics.

  * A `Spec` is a contract: precondition on (arguments, entry state), postcondition on
    the outcome (normal return, exception, or `wrong`; postconditions built with
    `Spec.of` exclude `wrong`).
  * `bodyWP` symbolically executes a method body statement by statement, through the
    same `step` function that defines the semantics. Execution stops at *cut points*
    (loop heads) where an invariant must be established; each cut point's invariant
    gives one verification condition.
  * Calls are answered by `callWP`: with the callee's contract when there is one
    (modular verification, recursion and dynamic dispatch included), otherwise by
    inlining the callee's body (loop-free helpers need no contract).
  * `MethodVC` collects the verification conditions of one method; `AllVC` those of a
    whole program fragment. `AllVC.valid` (soundness) concludes that every contract holds
    for every terminating execution (partial correctness, no `wrong`).
-/
import Jimple.Interp

namespace Jimple

/-! ## Contracts -/

structure Spec where
  /-- precondition on the arguments (receiver first) and the entry state -/
  pre : List Value → State → Prop
  /-- postcondition on the outcome -/
  post : List Value → State → Outcome → Prop

/-- A contract from a normal-return and an exceptional postcondition; `wrong` outcomes
    are excluded. -/
def Spec.of (pre : List Value → State → Prop)
    (normal : List Value → State → Option Value → State → Prop)
    (exc : List Value → State → Addr → State → Prop := fun _ _ _ _ => False) : Spec where
  pre := pre
  post := fun args σ o =>
    match o with
    | .normal v σ' => normal args σ v σ'
    | .exc e σ' => exc args σ e σ'
    | .wrong _ => False

/-- `m` satisfies `S` (partial correctness). -/
def Sat (P : Program) (m : MethodRef) (S : Spec) : Prop :=
  ∀ args σ o, S.pre args σ → MExec P m args σ o → S.post args σ o

/-- Every implementation selected for a virtual call of `sig` on class `c` satisfies `S`. -/
def VSat (P : Program) (sig : MethodSig) (c : ClassName) (S : Spec) : Prop :=
  ∀ args σ o, S.pre args σ → VExec P sig c args σ o → S.post args σ o

/-- Methods that a `.method` call request for reference `sig` can carry: the static or
    special selection of `sig`, or the static initializer of its class. -/
def Targets (P : Program) (sig : MethodSig) (m : MethodRef) : Prop :=
  (P.selectStatic sig = .jimple m ∨ P.selectSpecial sig = .jimple m ∨
    (sig = clinitSig m.cls ∧ P.clinitOf m.cls = some m.decl)) ∧ m.decl.body.isSome

/-- Contract environment: the contract of each method reference that has one. -/
abbrev SpecEnv := MethodSig → Option Spec

/-- All contracts of `Γ` hold (for a method that is not static, in every application subclass
    as well). -/
def Valid (P : Program) (Γ : SpecEnv) : Prop :=
  ∀ sig S, Γ sig = some S →
    (∀ m, Targets P sig m → Sat P m S) ∧
    (∀ c, P.isProgClass c = true → P.isSubclass c sig.cls = some true →
      P.staticDecl sig = false → VSat P sig c S)

/-! ## Weakest preconditions -/

/-- How call requests are answered during symbolic execution. -/
abbrev Handler := MethodSig → Callee → List Value → State → (Outcome → Prop) → Prop

/-- All results of a request tree satisfy `Q`. -/
def wpR {α : Type} (H : Handler) : Res α → (α → Prop) → Prop
  | .ret a, Q => Q a
  | .call sig c args σ k, Q => H sig c args σ (fun o => wpR H (k o) Q)
  | .choose k, Q => ∀ n, wpR H (k n) Q

/-- Cut-point assertions of one body, already instantiated with the entry arguments and
    entry state. -/
abbrev Cuts := List (Nat × (Frame → State → Prop))

/-- Symbolic execution of `b` from `(pc, fr, σ)` for at most `n` statements: every path
    must end in an outcome satisfying `Post` or reach a cut point whose assertion holds. -/
def bodyWP (P : Program) (H : Handler) (b : Body) (I : Cuts) (Post : Outcome → Prop) :
    Nat → Nat → Frame → State → Prop
  | 0, _, _, _ => False
  | n + 1, pc, fr, σ =>
    wpR H (step P b pc fr σ) fun r =>
      match afterStep P b pc fr r with
      | .done o => Post o
      | .cont pc' fr' σ' =>
        match I.lookup pc' with
        | some A => A fr' σ'
        | none => bodyWP P H b I Post n pc' fr' σ'

/-- Statement budget for inlined (loop-free) callees. -/
def inlineFuel : Nat := 400

/-- Answering a call request: with the callee's contract if `Γ` has one, otherwise by
    inlining the selected method (up to depth `d`). -/
def callWP (P : Program) (Γ : SpecEnv) : Nat → Handler
  | d, sig, callee, args, σ, K =>
    match Γ sig, callee with
    | some S, .method m => Targets P sig m ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
    | some S, .virtual c => P.isProgClass c = true ∧ P.isSubclass c sig.cls = some true ∧
        P.staticDecl sig = false ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
    | none, .method m =>
      match d with
      | 0 => False
      | d + 1 =>
        match m.decl.body with
        | some b => bodyWP P (callWP P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
        | none => K (.wrong "abstract or native method")
    | none, .virtual c =>
      match d with
      | 0 => False
      | d + 1 =>
        match P.selectVirtual c sig.sub with
        | .jimple m =>
          match m.decl.body with
          | some b => bodyWP P (callWP P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
        | .native lc =>
          match args with
          | .ref a :: rest =>
            match σ.heap a with
            | some (.plain c' fs) =>
              c' = c →
              match Native.plainInst P sig lc a c fs rest σ with
              | some r => wpR (callWP P Γ d) r (fun ev => K ev.toOutcome)
              | none => K (.wrong "no model for library method")
            | _ => True
          | _ => True
        | .none why => P.concrete c = true → K (.wrong why)

/-! ## Verification conditions -/

/-- Loop invariants of a method, as functions of the entry arguments and entry state. -/
abbrev Invariants := List (Nat × (List Value → State → Frame → State → Prop))

def Invariants.inst (A : Invariants) (args : List Value) (σ0 : State) : Cuts :=
  A.map fun p => (p.1, p.2 args σ0)

/-- Verification conditions of method `m` against contract `S` with invariants `A`:
    the entry path and every cut point's paths, each explored for at most `fuel`
    statements, calls answered by `callWP P Γ d`. -/
def MethodVC (P : Program) (Γ : SpecEnv) (d : Nat) (m : MethodRef) (S : Spec)
    (A : Invariants) (fuel : Nat) : Prop :=
  ∃ b, m.decl.body = some b ∧
  ∀ args σ0, S.pre args σ0 →
    (let fr0 := Frame.init m.decl.mods.isStatic args
     match (A.inst args σ0).lookup 0 with
     | some a => a fr0 σ0
     | none => bodyWP P (callWP P Γ d) b (A.inst args σ0) (S.post args σ0) fuel 0 fr0 σ0) ∧
    ∀ p ∈ A.inst args σ0, ∀ fr σ, p.2 fr σ →
      bodyWP P (callWP P Γ d) b (A.inst args σ0) (S.post args σ0) fuel p.1 fr σ

/-- Verification conditions of a library implementation selected for a virtual call. -/
def NativeVC (P : Program) (Γ : SpecEnv) (d : Nat) (sig : MethodSig) (c lc : ClassName)
    (S : Spec) : Prop :=
  ∀ a rest σ fs, S.pre (.ref a :: rest) σ → σ.heap a = some (.plain c fs) →
    match Native.plainInst P sig lc a c fs rest σ with
    | some r => wpR (callWP P Γ d) r (fun ev => S.post (.ref a :: rest) σ ev.toOutcome)
    | none => S.post (.ref a :: rest) σ (.wrong "no model for library method")

/-- Annotations of a program fragment: invariants and exploration budget per method. -/
structure Annotations where
  inv : MethodRef → Invariants := fun _ => []
  fuel : MethodRef → Nat := fun _ => 1000

/-- Verification conditions of every implementation of every contract in `Γ`. -/
def AllVC (P : Program) (Γ : SpecEnv) (d : Nat) (Ann : Annotations) : Prop :=
  ∀ sig S, Γ sig = some S →
    (∀ m, Targets P sig m → MethodVC P Γ d m S (Ann.inv m) (Ann.fuel m)) ∧
    (∀ c, P.isProgClass c = true → P.isSubclass c sig.cls = some true →
      P.staticDecl sig = false →
      match P.selectVirtual c sig.sub with
      | .jimple m => MethodVC P Γ d m S (Ann.inv m) (Ann.fuel m)
      | .native lc => NativeVC P Γ d sig c lc S
      | .none _ => P.concrete c = false)

/-! ## Soundness -/

section Soundness
variable {P : Program} {Γ : SpecEnv} {D : Nat} {Ann : Annotations}

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · next hx =>
      cases h
      have : a = x := by simpa using hx
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem cuts_of_vc {H : Handler} {b : Body} {I : Cuts} {Post : Outcome → Prop} {fuel : Nat}
    (hcuts : ∀ p ∈ I, ∀ fr σ, p.2 fr σ → bodyWP P H b I Post fuel p.1 fr σ) :
    ∀ c A, I.lookup c = some A → ∀ fr σ, A fr σ → bodyWP P H b I Post fuel c fr σ :=
  fun c A hl fr σ hA => hcuts (c, A) (lookup_mem hl) fr σ hA

mutual
theorem mexec_ok_vc (hAll : AllVC P Γ D Ann) :
    ∀ {m args σ o}, MExec P m args σ o → ∀ {S : Spec}, MethodVC P Γ D m S (Ann.inv m) (Ann.fuel m) →
      S.pre args σ → S.post args σ o
  | _, _, _, _, .body (m := m) (args := args) (σ := σ) (b := b) hb hB, S, hvc, hpre => by
    obtain ⟨b', hb', hvc⟩ := hvc
    rw [hb] at hb'; cases hb'
    obtain ⟨hentry, hcuts⟩ := hvc args σ hpre
    have hI := cuts_of_vc (P := P) hcuts
    simp only at hentry
    split at hentry
    · next A hA => exact bexec_ok hAll hB D _ _ hI (Ann.fuel m) (hI 0 A hA _ _ hentry)
    · exact bexec_ok hAll hB D _ _ hI (Ann.fuel m) hentry
  | _, _, _, _, .noBody hb, S, hvc, hpre => by
    obtain ⟨b', hb', _⟩ := hvc
    rw [hb] at hb'; cases hb'

theorem vexec_ok (hAll : AllVC P Γ D Ann) :
    ∀ {sig c args σ o}, VExec P sig c args σ o →
      ∀ S, Γ sig = some S → P.isProgClass c = true → P.isSubclass c sig.cls = some true →
        P.staticDecl sig = false → S.pre args σ → S.post args σ o
  | _, _, _, _, _, .jimple (sig := sig) (c := c) hsel hm, S, hΓ, hpc, hsub, hst, hpre => by
    have h := (hAll sig S hΓ).2 c hpc hsub hst
    rw [hsel] at h
    exact mexec_ok_vc hAll hm h hpre
  | _, _, _, _, _, .native (sig := sig) (c := c) (a := a) (rest := rest) (σ := σ) (fs := fs) hsel hheap hpl hr,
      S, hΓ, hpc, hsub, hst, hpre => by
    have h := (hAll sig S hΓ).2 c hpc hsub hst
    rw [hsel] at h
    have h2 := h a rest σ fs hpre hheap
    rw [hpl] at h2
    exact rexec_ok hAll hr D _ h2
  | _, _, _, _, _, .noModel (sig := sig) (c := c) (a := a) (rest := rest) (σ := σ) (fs := fs) hsel hheap hpl,
      S, hΓ, hpc, hsub, hst, hpre => by
    have h := (hAll sig S hΓ).2 c hpc hsub hst
    rw [hsel] at h
    have h2 := h a rest σ fs hpre hheap
    rw [hpl] at h2
    exact h2
  | _, _, _, _, _, .none (sig := sig) (c := c) hsel hconc, S, hΓ, hpc, hsub, hst, hpre => by
    have h := (hAll sig S hΓ).2 c hpc hsub hst
    rw [hsel] at h
    simp only at h
    rw [h] at hconc; cases hconc

/-- Inlined (contract-free) calls of a selected method. -/
theorem minline_ok (hAll : AllVC P Γ D Ann) :
    ∀ {m args σ o}, MExec P m args σ o → ∀ (d : Nat) (K : Outcome → Prop),
      (match m.decl.body with
       | some b => bodyWP P (callWP P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
       | none => K (.wrong "abstract or native method")) → K o
  | _, _, _, _, .body hb hB, d, K, h => by
    simp only [hb] at h
    exact bexec_ok hAll hB d [] K (N := inlineFuel) (fun _ _ hl => by simp at hl) inlineFuel h
  | _, _, _, _, .noBody hb, d, K, h => by simpa only [hb] using h

/-- Inlined (contract-free) virtual calls. -/
theorem vinline_ok (hAll : AllVC P Γ D Ann) :
    ∀ {sig c args σ o}, VExec P sig c args σ o → ∀ (d : Nat) (K : Outcome → Prop),
      (match P.selectVirtual c sig.sub with
        | .jimple m =>
          match m.decl.body with
          | some b => bodyWP P (callWP P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
        | .native lc =>
          match args with
          | .ref a :: rest =>
            match σ.heap a with
            | some (.plain c' fs) =>
              c' = c →
              match Native.plainInst P sig lc a c fs rest σ with
              | some r => wpR (callWP P Γ d) r (fun ev => K ev.toOutcome)
              | none => K (.wrong "no model for library method")
            | _ => True
          | _ => True
        | .none why => P.concrete c = true → K (.wrong why)) → K o
  | _, _, _, _, _, .jimple hsel hm, d, K, h => by
    simp only [hsel] at h
    exact minline_ok hAll hm d K h
  | _, _, _, _, _, .native hsel hheap hpl hr, d, K, h => by
    simp only [hsel, hheap, hpl, forall_const] at h
    exact rexec_ok hAll hr d _ h
  | _, _, _, _, _, .noModel hsel hheap hpl, d, K, h => by
    simpa only [hsel, hheap, hpl, forall_const] using h
  | _, _, _, _, _, .none hsel hconc, d, K, h => by
    simp only [hsel] at h
    exact h hconc

theorem rexec_ok (hAll : AllVC P Γ D Ann) :
    ∀ {α} {r : Res α} {a : α}, RExec P r a → ∀ (d : Nat) (Q : α → Prop), wpR (callWP P Γ d) r Q → Q a
  | _, _, _, .ret, d, Q, h => by simpa [wpR] using h
  | _, _, _, .callM (sig := sig) (m := m) (args := args) (σ := σ) (o := o) (k := k) hm hk, d, Q, h => by
    simp only [wpR] at h
    apply rexec_ok hAll hk d Q
    unfold callWP at h
    rcases hΓ : Γ sig with _ | S
    · rw [hΓ] at h
      cases d with
      | zero => simp at h
      | succ d' => exact minline_ok hAll hm d' _ h
    · rw [hΓ] at h
      simp only at h
      obtain ⟨ht, hpre, hK⟩ := h
      have hS := (hAll sig S hΓ).1 m ht
      exact hK o (mexec_ok_vc hAll hm hS hpre)
  | _, _, _, .callV (sig := sig) (c := c) (args := args) (σ := σ) (o := o) (k := k) hv hk, d, Q, h => by
    simp only [wpR] at h
    apply rexec_ok hAll hk d Q
    unfold callWP at h
    rcases hΓ : Γ sig with _ | S
    · rw [hΓ] at h
      cases d with
      | zero => simp at h
      | succ d' => exact vinline_ok hAll hv d' _ h
    · rw [hΓ] at h
      simp only at h
      obtain ⟨hpc, hsub, hst, hpre, hK⟩ := h
      exact hK o (vexec_ok hAll hv S hΓ hpc hsub hst hpre)
  | _, _, _, .choose (k := k) n hk, d, Q, h => by
    simp only [wpR] at h
    exact rexec_ok hAll hk d Q (h n)

theorem bexec_ok (hAll : AllVC P Γ D Ann) :
    ∀ {b pc fr σ o}, BExec P b pc fr σ o →
      ∀ (d : Nat) (I : Cuts) (Post : Outcome → Prop) {N : Nat},
        (∀ c A, I.lookup c = some A → ∀ fr σ, A fr σ → bodyWP P (callWP P Γ d) b I Post N c fr σ) →
        ∀ n, bodyWP P (callWP P Γ d) b I Post n pc fr σ → Post o
  | _, _, _, _, _, .cont (b := b) (pc := pc) (fr := fr) (σ := σ) (r := r) (pc' := pc') (fr' := fr') (σ' := σ') hr hc hB,
      d, I, Post, N, hI, n, h => by
    cases n with
    | zero => simp [bodyWP] at h
    | succ n =>
      simp only [bodyWP] at h
      have h2 := rexec_ok hAll hr d _ h
      simp only [hc] at h2
      split at h2
      · next A hA => exact bexec_ok hAll hB d I Post hI N (hI pc' A hA fr' σ' h2)
      · exact bexec_ok hAll hB d I Post hI n h2
  | _, _, _, _, _, .done (r := r) hr hd, d, I, Post, N, hI, n, h => by
    cases n with
    | zero => simp [bodyWP] at h
    | succ n =>
      simp only [bodyWP] at h
      have h2 := rexec_ok hAll hr d _ h
      simpa [hd] using h2
end

theorem mexec_ok (hAll : AllVC P Γ D Ann) {m args σ o} (hm : MExec P m args σ o)
    {sig : MethodSig} {S : Spec} (hΓ : Γ sig = some S) (ht : Targets P sig m) (hpre : S.pre args σ) :
    S.post args σ o :=
  mexec_ok_vc hAll hm ((hAll sig S hΓ).1 m ht) hpre

/-- **Soundness**: if the verification conditions of all implementations hold, every
    contract of `Γ` holds. -/
theorem AllVC.valid (hAll : AllVC P Γ D Ann) : Valid P Γ := by
  intro sig S hΓ
  exact ⟨fun m ht args σ o hpre hm => mexec_ok hAll hm hΓ ht hpre,
         fun c hpc hsub hst args σ o hpre hv => vexec_ok hAll hv S hΓ hpc hsub hst hpre⟩

end Soundness

/-! ## Linking

  `MethodVC P Γ d m S A fuel` answers calls with the contracts of `Γ`. When those contracts are
  known to hold (`Valid P Γ`, from the callees' own proofs), the method satisfies its contract:
  each method is proved once, against its callees' contracts only, and the proofs are linked
  without re-checking any callee. (For recursive methods, whose contracts are assumed while
  being proved, use `AllVC.valid` on the strongly connected component instead.) -/

section Linking
variable {P : Program} {Γ : SpecEnv}

mutual
theorem minline_okV (hV : Valid P Γ) :
    ∀ {m args σ o}, MExec P m args σ o → ∀ (d : Nat) (K : Outcome → Prop),
      (match m.decl.body with
       | some b => bodyWP P (callWP P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
       | none => K (.wrong "abstract or native method")) → K o
  | _, _, _, _, .body hb hB, d, K, h => by
    simp only [hb] at h
    exact bexec_okV hV hB d [] K (N := inlineFuel) (fun _ _ hl => by simp at hl) inlineFuel h
  | _, _, _, _, .noBody hb, d, K, h => by simpa only [hb] using h

theorem vinline_okV (hV : Valid P Γ) :
    ∀ {sig c args σ o}, VExec P sig c args σ o → ∀ (d : Nat) (K : Outcome → Prop),
      (match P.selectVirtual c sig.sub with
        | .jimple m =>
          match m.decl.body with
          | some b => bodyWP P (callWP P Γ d) b [] K inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
        | .native lc =>
          match args with
          | .ref a :: rest =>
            match σ.heap a with
            | some (.plain c' fs) =>
              c' = c →
              match Native.plainInst P sig lc a c fs rest σ with
              | some r => wpR (callWP P Γ d) r (fun ev => K ev.toOutcome)
              | none => K (.wrong "no model for library method")
            | _ => True
          | _ => True
        | .none why => P.concrete c = true → K (.wrong why)) → K o
  | _, _, _, _, _, .jimple hsel hm, d, K, h => by
    simp only [hsel] at h
    exact minline_okV hV hm d K h
  | _, _, _, _, _, .native hsel hheap hpl hr, d, K, h => by
    simp only [hsel, hheap, hpl, forall_const] at h
    exact rexec_okV hV hr d _ h
  | _, _, _, _, _, .noModel hsel hheap hpl, d, K, h => by
    simpa only [hsel, hheap, hpl, forall_const] using h
  | _, _, _, _, _, .none hsel hconc, d, K, h => by
    simp only [hsel] at h
    exact h hconc

theorem rexec_okV (hV : Valid P Γ) :
    ∀ {α} {r : Res α} {a : α}, RExec P r a → ∀ (d : Nat) (Q : α → Prop), wpR (callWP P Γ d) r Q → Q a
  | _, _, _, .ret, d, Q, h => by simpa [wpR] using h
  | _, _, _, .callM (sig := sig) (m := m) (args := args) (σ := σ) (o := o) (k := k) hm hk, d, Q, h => by
    simp only [wpR] at h
    apply rexec_okV hV hk d Q
    unfold callWP at h
    rcases hΓ : Γ sig with _ | S
    · rw [hΓ] at h
      cases d with
      | zero => simp at h
      | succ d' => exact minline_okV hV hm d' _ h
    · rw [hΓ] at h
      simp only at h
      obtain ⟨ht, hpre, hK⟩ := h
      exact hK o ((hV sig S hΓ).1 m ht args σ o hpre hm)
  | _, _, _, .callV (sig := sig) (c := c) (args := args) (σ := σ) (o := o) (k := k) hv hk, d, Q, h => by
    simp only [wpR] at h
    apply rexec_okV hV hk d Q
    unfold callWP at h
    rcases hΓ : Γ sig with _ | S
    · rw [hΓ] at h
      cases d with
      | zero => simp at h
      | succ d' => exact vinline_okV hV hv d' _ h
    · rw [hΓ] at h
      simp only at h
      obtain ⟨hpc, hsub, hst, hpre, hK⟩ := h
      exact hK o ((hV sig S hΓ).2 c hpc hsub hst args σ o hpre hv)
  | _, _, _, .choose (k := k) n hk, d, Q, h => by
    simp only [wpR] at h
    exact rexec_okV hV hk d Q (h n)

theorem bexec_okV (hV : Valid P Γ) :
    ∀ {b pc fr σ o}, BExec P b pc fr σ o →
      ∀ (d : Nat) (I : Cuts) (Post : Outcome → Prop) {N : Nat},
        (∀ c A, I.lookup c = some A → ∀ fr σ, A fr σ → bodyWP P (callWP P Γ d) b I Post N c fr σ) →
        ∀ n, bodyWP P (callWP P Γ d) b I Post n pc fr σ → Post o
  | _, _, _, _, _, .cont (b := b) (pc := pc) (fr := fr) (σ := σ) (r := r) (pc' := pc') (fr' := fr') (σ' := σ') hr hc hB,
      d, I, Post, N, hI, n, h => by
    cases n with
    | zero => simp [bodyWP] at h
    | succ n =>
      simp only [bodyWP] at h
      have h2 := rexec_okV hV hr d _ h
      simp only [hc] at h2
      split at h2
      · next A hA => exact bexec_okV hV hB d I Post hI N (hI pc' A hA fr' σ' h2)
      · exact bexec_okV hV hB d I Post hI n h2
  | _, _, _, _, _, .done (r := r) hr hd, d, I, Post, N, hI, n, h => by
    cases n with
    | zero => simp [bodyWP] at h
    | succ n =>
      simp only [bodyWP] at h
      have h2 := rexec_okV hV hr d _ h
      simpa [hd] using h2
end

/-- **Linking**: a method verified against the contracts `Γ` of its callees satisfies its own
    contract when those contracts hold. -/
theorem MethodVC.sat_of_valid {d : Nat} {m : MethodRef} {S : Spec} {A : Invariants} {fuel : Nat}
    (hV : Valid P Γ) (h : MethodVC P Γ d m S A fuel) : Sat P m S := by
  intro args σ o hpre hm
  cases hm with
  | body hb hB =>
    obtain ⟨b', hb', hvc⟩ := h
    rw [hb] at hb'; cases hb'
    obtain ⟨hentry, hcuts⟩ := hvc args σ hpre
    have hI := cuts_of_vc (P := P) hcuts
    simp only at hentry
    split at hentry
    · next A hA => exact bexec_okV hV hB d _ _ hI fuel (hI 0 A hA _ _ hentry)
    · exact bexec_okV hV hB d _ _ hI fuel hentry
  | noBody hb =>
    obtain ⟨b', hb', _⟩ := h
    rw [hb] at hb'; cases hb'

end Linking

end Jimple

