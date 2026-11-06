import EquivLean.Bridge.Cir.Tactic

/-!
# tiny-regex-c → model, C side: partial correctness tools

The recursive matcher functions are specified by partial correctness (`pholds`: every `ok`
outcome satisfies the postcondition), so that a path on which the C has undefined behaviour
closes by itself.  The C runs in a hypothesis `h : x.holds (· = r)` (equiv-lean's `cir_hrun`);
here are the rules that the hypothesis side lacks:

* `holds_pspec_elim` / `holds_returns_elim`: a call with a partial or total contract, used
  forward (`cir_hrun_c` stops at every call so that a contract can be applied);
* `pholds_loop`: a loop by an invariant, without variant (a safe loop iterates finitely often:
  `LoopShape.Terminates`, proved once per loop construct by the bridge).
-/

namespace EquivLean.Cir

open CIR

section
variable {α : Type}

/-- A computation with a partial contract `P`, used forward. -/
theorem holds_pspec_elim {x : Res α} {K P : α → Prop} (h : x.holds K) (hp : pholds x P) :
    ∃ a, x = .ok a ∧ P a ∧ K a := by
  cases x with
  | ok a => exact ⟨a, rfl, hp a rfl, h⟩
  | ub _ => exact h.elim
  | div => exact h.elim

theorem holds_of_eq_ok {x : Res α} {a : α} (h : x = .ok a) : x.holds (· = a) := by rw [h]; rfl

/-- A computation with a total contract, used forward. -/
theorem holds_holds_elim {x : Res α} {K P : α → Prop} (h : x.holds K) (hp : x.holds P) :
    ∃ a, x = .ok a ∧ P a ∧ K a := by
  cases x with
  | ok a => exact ⟨a, rfl, hp, h⟩
  | ub _ => exact h.elim
  | div => exact h.elim

end

/-- A call with a `Returns` contract, used forward. -/
theorem holds_returns_elim {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {post : Option Val → Mem → Prop} {K : Exit × Mem → Prop}
    (h : (evalCall ctx sym args m).holds K) (hs : Returns ctx sym args m post) :
    ∃ v m', evalCall ctx sym args m = .ok (.ret v, m') ∧ post v m' ∧ K (.ret v, m') := by
  unfold Returns Calls at hs
  obtain ⟨⟨e, m'⟩, hx, hp, hk⟩ := holds_holds_elim h hs
  cases e with
  | ret v => exact ⟨v, m', hx, hp, hk⟩
  | _ => exact hp.elim

/-- Partial correctness of a loop by an invariant: every outcome of a run from a state in the
invariant satisfies `Post`, if every iteration from the invariant either leaves the loop with
an outcome in `Post` or continues in the invariant. -/
theorem pholds_loop {σ O OD : Type} {L : σ → Res O} {iter : σ → Res OD} {cls : OD → O ⊕ σ}
    (hL : LoopShape L iter cls) (ht : LoopShape.Terminates L iter cls) (Inv : σ → Prop)
    (Post : O → Prop)
    (hstep : ∀ s, Inv s → pholds (iter s) (fun r => match cls r with
      | .inl o => Post o
      | .inr s' => Inv s')) :
    ∀ s, Inv s → pholds (L s) Post := by
  intro s hs o ho
  have hacc := ht s ⟨o, ho⟩
  induction hacc generalizing o with
  | intro s _ ih =>
    obtain ⟨r, hr, hc⟩ := (hL.runs_iff s o).1 ho
    have hst := hstep s hs r hr
    dsimp only at hst
    rcases hc with hc | ⟨s', hc, ho'⟩
    · rw [hc] at hst; exact hst
    · rw [hc] at hst
      exact ih s' ⟨r, hr, hc⟩ hst o ho'

/-- Name the state at the head of a loop in a hypothesis. -/
theorem holds_while_name {ctx : Ctx} {c b : Region} {cl : Option (CleanupKind × Region)} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalWhile ctx c b cl σ₀).holds K) :
    ∃ s, s = σ₀ ∧ (evalWhile ctx c b cl s).holds K := ⟨σ₀, rfl, hs⟩

theorem holds_do_name {ctx : Ctx} {b c : Region} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalDo ctx b c σ₀).holds K) :
    ∃ s, s = σ₀ ∧ (evalDo ctx b c s).holds K := ⟨σ₀, rfl, hs⟩

/-- A `while` loop in a hypothesis, by an invariant (partial correctness, no variant). -/
theorem holds_while_inv {ctx : Ctx} {c b : Region} {cl : Option (CleanupKind × Region)} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalWhile ctx c b cl σ₀).holds K) (Inv : State → Prop)
    (Post : Step × State → Prop) (h0 : Inv σ₀)
    (hstep : ∀ σ, Inv σ → pholds (whileIter ctx c b cl σ) (fun r => match r with
      | .inl o => Post o
      | .inr σ' => Inv σ')) :
    ∃ a, Post a ∧ K a := by
  have hl := pholds_loop (loopShape_while ctx c b cl) (terminates_while ctx c b cl) Inv Post
    (fun σ hσ r hr => by have h := hstep σ hσ r hr; cases r <;> exact h) σ₀ h0
  obtain ⟨a, -, hp, hk⟩ := holds_pspec_elim hs hl
  exact ⟨a, hp, hk⟩

/-- A `do`-`while` loop in a hypothesis, by an invariant (partial correctness, no variant). -/
theorem holds_do_inv {ctx : Ctx} {b c : Region} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalDo ctx b c σ₀).holds K) (Inv : State → Prop)
    (Post : Step × State → Prop) (h0 : Inv σ₀)
    (hstep : ∀ σ, Inv σ → pholds (doIter ctx b c σ) (fun r => match r with
      | .inl o => Post o
      | .inr σ' => Inv σ')) :
    ∃ a, Post a ∧ K a := by
  have hl := pholds_loop (loopShape_do ctx b c) (terminates_do ctx b c) Inv Post
    (fun σ hσ r hr => by have h := hstep σ hσ r hr; cases r <;> exact h) σ₀ h0
  obtain ⟨a, -, hp, hk⟩ := holds_pspec_elim hs hl
  exact ⟨a, hp, hk⟩

open Lean Elab Tactic Meta in
/-- `cir_hrun h` that also stops at every call of a function, so that a contract can be applied
(`holds_pspec_elim`, `holds_returns_elim`).  Run `cir_hstep h` first to enter the function whose
call is the head of `h`. -/
elab "cir_hrun_c " h:ident : tactic => do
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
      if ← tryTac (hypExists h.getId) then work := (← getGoals) ++ work
      else done := done.push g
      continue
    if x.isAppOf ``CIR.evalFor || x.isAppOf ``CIR.evalWhile || x.isAppOf ``CIR.evalDo ||
        x.isAppOf ``CIR.evalCall then
      done := done.push g; continue
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do
        Lean.Core.withCurrHeartbeats (hypStepImpl h.getId)
        pure true)
      fun e => do
        s.restore
        if e.isRuntime then
          logWarning m!"cir_hrun_c: a step exceeded a resource limit: {e.toMessageData}"
        pure false
    if ok then work := (← getGoals) ++ work
    else done := done.push g
  setGoals (done.toList ++ work)

end EquivLean.Cir
