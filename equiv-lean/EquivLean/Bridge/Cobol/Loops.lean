import EquivLean.Core.Loop
import EquivLean.Bridge.Cobol.Behaves

/-!
# COBOL loops as `LoopShape`s

coblean runs `PERFORM … UNTIL` (out of line or inline, test before or after, and `VARYING`,
whose control variables are augmented by `step`) with
`Sem.loopUntil testAfter cond body step : Nat → State → Res`, and `PERFORM … TIMES` with
`Sem.loopTimes body : Nat → State → Res`.  For the generic loop rules of `Core/Loop.lean`:

* the loop state is `(fuel, State)` for `loopUntil` (one iteration consumes one unit of
  fuel; fuel `0` is `outOfFuel`, which is unsafe) and `(count, State)` for `loopTimes`;
* one iteration (`untilIter`, `timesIter`) either leaves the loop with a result (`.inl r`:
  the condition holds, the body ended with a non-`normal` signal, `EXIT PERFORM`, a fault),
  or continues from the next loop state (`.inr`);
* `IterExec` is the computation of one iteration (its `Behaves` instance: `none` = out of
  fuel is unsafe, a leaving result must be `Ok`), and the classification is the identity.

`untilShape` / `timesShape` are the `LoopShape`s, `untilTerminates` / `timesTerminates` their
`LoopShape.Terminates` (the fuel, resp. the count, decreases).  So a COBOL loop can be the
source of a lockstep product loop with `sim_loop_of_terminates` (no variant needed).
-/

open Cobol

namespace EquivLean.Cobol

/-- The outcome of one loop iteration: leave with a result, or continue from a new loop
state. -/
abbrev IterRes := Sem.Res ⊕ (Nat × State)

/-- One loop iteration, as a closed computation (`none`: out of fuel). -/
structure IterExec where
  res : Option IterRes

/-- A leaving result must be an observable outcome; continuing is always fine. -/
def IterOk : IterRes → Prop
  | .inl r => Ok r
  | .inr _ => True

instance instBehavesIterExec : Behaves IterExec IterRes where
  Runs c o := c.res = some o ∧ IterOk o
  Safe c := ∃ o, c.res = some o ∧ IterOk o

instance : Behaves.Total IterExec := ⟨fun _ h => h⟩
instance : Behaves.Det IterExec :=
  ⟨fun _ _ _ h₁ h₂ => Option.some.inj (h₁.1.symm.trans h₂.1)⟩

@[simp] theorem runs_iterExec_iff (r : Option IterRes) (o : IterRes) :
    Runs (IterExec.mk r) o ↔ r = some o ∧ IterOk o := Iff.rfl

@[simp] theorem safe_iterExec_iff (r : Option IterRes) :
    Safe (IterExec.mk r) ↔ ∃ o, r = some o ∧ IterOk o := Iff.rfl

@[simp] theorem iterOk_inl (r : Sem.Res) : IterOk (.inl r) ↔ Ok r := Iff.rfl
@[simp] theorem iterOk_inr (s : Nat × State) : IterOk (.inr s) ↔ True := Iff.rfl

@[simp] theorem wp_iterExec_some (o : IterRes) (Q : IterRes → Prop) :
    wp (IterExec.mk (some o)) Q ↔ IterOk o ∧ Q o := by
  constructor
  · intro h
    obtain ⟨_, ho, hok⟩ := h.1
    cases ho
    exact ⟨hok, h.2 _ ⟨rfl, hok⟩⟩
  · intro ⟨hok, hq⟩
    exact ⟨⟨o, rfl, hok⟩, fun o' ⟨ho, _⟩ => by cases ho; exact hq⟩

@[simp] theorem wp_iterExec_none (Q : IterRes → Prop) : wp (IterExec.mk none) Q ↔ False :=
  ⟨fun h => (by obtain ⟨_, ho, _⟩ := h.1; cases ho), False.elim⟩

/-- A simulation whose source is one COBOL loop iteration with result `o` is a weakest
precondition of the target (the iteration is deterministic). -/
theorem sim_iterExec_some_iff {T : Type _} {OT : Type _} [Behaves T OT]
    {R : OT → IterRes → Prop} {t : T} (o : IterRes) :
    Sim R t (IterExec.mk (some o)) ↔ (IterOk o → wp t (fun ot => R ot o)) := by
  have key : ∀ hok : IterOk o, Sim R t (IterExec.mk (some o)) ↔ wp t (fun ot => R ot o) :=
    fun hok => sim_iff_of_runs (show Safe (IterExec.mk (some o)) from ⟨o, rfl, hok⟩)
      (show Runs (IterExec.mk (some o)) o from ⟨rfl, hok⟩)
  constructor
  · intro h hok
    exact (key hok).1 h
  · intro h hs
    obtain ⟨o', ho', hok⟩ := hs
    cases ho'
    exact (key hok).2 (h hok) ⟨o, rfl, hok⟩

/-- A loop function that unfolds into one iteration (`F s = post (it s)`) has the
`LoopShape` of that iteration, with the identity classification. -/
theorem shape_of_unfold {F : Nat × State → Sem.Res} {it : Nat × State → Option IterRes}
    (hF : ∀ s, F s = match it s with
      | none => (.outOfFuel, s.2)
      | some (.inl r) => r
      | some (.inr s') => F s') :
    LoopShape (fun s => Exec.mk (F s)) (fun s => IterExec.mk (it s)) id := by
  constructor
  · intro s
    simp only [safe_exec_iff, safe_iterExec_iff, runs_iterExec_iff]
    rw [hF s]
    cases it s with
    | none => simp [Ok]
    | some o =>
      cases o with
      | inl r =>
        constructor
        · intro h; exact ⟨⟨.inl r, rfl, h⟩, fun r' s' ⟨he, _⟩ hc => by cases he; cases hc⟩
        · rintro ⟨⟨o, he, hok⟩, _⟩; cases he; exact hok
      | inr s' =>
        constructor
        · intro h
          exact ⟨⟨.inr s', rfl, trivial⟩, fun r' s'' ⟨he, _⟩ hc => by cases he; cases hc; exact h⟩
        · rintro ⟨_, hnext⟩; exact hnext (.inr s') s' ⟨rfl, trivial⟩ rfl
  · intro s o
    simp only [runs_exec_iff, runs_iterExec_iff]
    rw [hF s]
    cases it s with
    | none => simp [Ok]
    | some o' =>
      cases o' with
      | inl r =>
        constructor
        · rintro ⟨rfl, h⟩; exact ⟨.inl _, ⟨rfl, h⟩, .inl rfl⟩
        · rintro ⟨r', ⟨he, hok⟩, hc⟩
          cases he
          rcases hc with hc | ⟨s', hc, _⟩
          · cases hc; exact ⟨rfl, hok⟩
          · cases hc
      | inr s' =>
        constructor
        · intro h; exact ⟨.inr s', ⟨rfl, trivial⟩, .inr ⟨s', rfl, h⟩⟩
        · rintro ⟨r', ⟨he, _⟩, hc⟩
          cases he
          rcases hc with hc | ⟨s'', hc, h⟩
          · cases hc
          · cases hc; exact h

/-! ## `PERFORM … UNTIL` -/

section untilLoops
variable (ta : Bool) (cond : State → SemM Bool) (body step : State → Sem.Res)

/-- One iteration of `Sem.loopUntil ta cond body step` at a positive fuel, mirroring its
definition: test (before or after the body), run the body and the `VARYING` step; leave with a
result (`.inl`) or continue from a state (`.inr`). -/
def untilBody (st : State) : Sem.Res ⊕ State :=
  if ta then
    match body st with
    | (.normal, st1) | (.exitCycle, st1) =>
      match cond st1 with
      | .error f => .inl (.fault f, st1)
      | .ok true => .inl (.normal, st1)
      | .ok false =>
        match step st1 with
        | (.normal, st2) => .inr st2
        | r => .inl r
    | (.exitPerform, st1) => .inl (.normal, st1)
    | r => .inl r
  else
    match cond st with
    | .error f => .inl (.fault f, st)
    | .ok true => .inl (.normal, st)
    | .ok false =>
      match body st with
      | (.normal, st1) | (.exitCycle, st1) =>
        match step st1 with
        | (.normal, st2) => .inr st2
        | r => .inl r
      | (.exitPerform, st1) => .inl (.normal, st1)
      | r => .inl r

/-- Attach the remaining fuel to a continuing iteration. -/
def withFuel (n : Nat) : Sem.Res ⊕ State → IterRes
  | .inl r => .inl r
  | .inr st => .inr (n, st)

/-- One iteration on loop states `(fuel, state)`: out of fuel at `0`, otherwise `untilBody`
with one unit of fuel consumed. -/
def untilIter : Nat × State → Option IterRes
  | (0, _) => none
  | (n + 1, st) => some (withFuel n (untilBody ta cond body step st))

/-- The loop as a computation on loop states. -/
def untilLoop (s : Nat × State) : Exec := ⟨Sem.loopUntil ta cond body step s.1 s.2⟩

/-- The iteration as a computation on loop states. -/
def untilStep (s : Nat × State) : IterExec := ⟨untilIter ta cond body step s⟩

/-- `loopUntil` at a positive fuel is one iteration followed by the rest of the loop. -/
theorem loopUntil_succ_eq (n : Nat) (st : State) :
    Sem.loopUntil ta cond body step (n + 1) st =
      match untilBody ta cond body step st with
      | .inl r => r
      | .inr st2 => Sem.loopUntil ta cond body step n st2 := by
  cases ta
  · simp only [untilBody, Sem.loopUntil, Bool.false_eq_true, ↓reduceIte]
    cases hc : cond st with
    | error f => rfl
    | ok b =>
      cases b
      · dsimp only
        cases hb : body st with
        | mk sig st1 =>
          cases sig <;> dsimp only <;> (try rfl) <;>
            (cases hs : step st1 with | mk sig2 st2 => cases sig2 <;> rfl)
      · rfl
  · simp only [untilBody, Sem.loopUntil, ↓reduceIte]
    cases hb : body st with
    | mk sig st1 =>
      cases sig <;> dsimp only <;> (try rfl) <;>
        (cases hc : cond st1 with
          | error f => rfl
          | ok b =>
            cases b <;> dsimp only <;> (try rfl) <;>
              (cases hs : step st1 with | mk sig2 st2 => cases sig2 <;> rfl))

/-- `loopUntil` is its first iteration followed by the rest of the loop. -/
theorem loopUntil_eq_iter (n : Nat) (st : State) :
    Sem.loopUntil ta cond body step n st =
      match untilIter ta cond body step (n, st) with
      | none => (.outOfFuel, st)
      | some (.inl r) => r
      | some (.inr s) => Sem.loopUntil ta cond body step s.1 s.2 := by
  cases n with
  | zero =>
    -- `Sem.loopUntil` is defined by well-founded recursion: unfold it by its equation
    rw [Sem.loopUntil.eq_1]; rfl
  | succ n =>
    rw [loopUntil_succ_eq]
    simp only [untilIter]
    cases untilBody ta cond body step st <;> rfl

/-- Continuing iterations consume one unit of fuel. -/
theorem untilIter_inr_fuel {n : Nat} {st : State} {s : Nat × State}
    (h : untilIter ta cond body step (n, st) = some (.inr s)) : s.1 + 1 = n := by
  cases n with
  | zero => simp [untilIter] at h
  | succ n =>
    simp only [untilIter, Option.some.injEq] at h
    revert h
    cases untilBody ta cond body step st with
    | inl r => intro h; cases h
    | inr st2 => intro h; cases h; rfl

/-- **`PERFORM … UNTIL` is a loop**: `untilLoop` unfolds into `untilStep` and the identity
classification. -/
theorem untilShape : LoopShape (untilLoop ta cond body step) (untilStep ta cond body step) id :=
  shape_of_unfold (F := fun s => Sem.loopUntil ta cond body step s.1 s.2)
    (fun s => loopUntil_eq_iter ta cond body step s.1 s.2)

/-- **A `PERFORM … UNTIL` loop iterates finitely often**: the fuel decreases. -/
theorem untilTerminates :
    LoopShape.Terminates (untilLoop ta cond body step) (untilStep ta cond body step) id := by
  have key : ∀ n (st : State),
      Acc (LoopShape.Next (untilStep ta cond body step) id) (n, st) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro st
      refine Acc.intro _ fun s' ⟨r, ⟨hr, _⟩, hc⟩ => ?_
      simp only [id] at hc
      subst hc
      have h := untilIter_inr_fuel ta cond body step hr
      exact ih s'.1 (by omega) s'.2
  intro s _
  exact key s.1 s.2

end untilLoops

/-! ## `PERFORM … TIMES` -/

section timesLoops
variable (body : State → Sem.Res)

/-- One iteration of `Sem.loopTimes body` with iterations left: run the body; leave with a
result (`.inl`) or continue from a state (`.inr`). -/
def timesBody (st : State) : Sem.Res ⊕ State :=
  match body st with
  | (.normal, st1) | (.exitCycle, st1) => .inr st1
  | (.exitPerform, st1) => .inl (.normal, st1)
  | r => .inl r

/-- One iteration on loop states `(count, state)` (never out of fuel: the count is evaluated
once, before the loop). -/
def timesIter : Nat × State → Option IterRes
  | (0, st) => some (.inl (.normal, st))
  | (k + 1, st) => some (withFuel k (timesBody body st))

def timesLoop (s : Nat × State) : Exec := ⟨Sem.loopTimes body s.1 s.2⟩

def timesStep (s : Nat × State) : IterExec := ⟨timesIter body s⟩

theorem loopTimes_eq_iter (k : Nat) (st : State) :
    Sem.loopTimes body k st =
      match timesIter body (k, st) with
      | none => (.outOfFuel, st)
      | some (.inl r) => r
      | some (.inr s) => Sem.loopTimes body s.1 s.2 := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [timesIter, timesBody, Sem.loopTimes]
    cases hb : body st with
    | mk sig st1 => cases sig <;> rfl

theorem timesIter_inr_count {k : Nat} {st : State} {s : Nat × State}
    (h : timesIter body (k, st) = some (.inr s)) : s.1 + 1 = k := by
  cases k with
  | zero => simp [timesIter] at h
  | succ k =>
    simp only [timesIter, Option.some.injEq] at h
    revert h
    cases timesBody body st with
    | inl r => intro h; cases h
    | inr st2 => intro h; cases h; rfl

/-- **`PERFORM … TIMES` is a loop.** -/
theorem timesShape : LoopShape (timesLoop body) (timesStep body) id :=
  shape_of_unfold (F := fun s => Sem.loopTimes body s.1 s.2)
    (fun s => loopTimes_eq_iter body s.1 s.2)

/-- **A `PERFORM … TIMES` loop iterates finitely often**: the count decreases. -/
theorem timesTerminates : LoopShape.Terminates (timesLoop body) (timesStep body) id := by
  have key : ∀ k (st : State), Acc (LoopShape.Next (timesStep body) id) (k, st) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro st
      refine Acc.intro _ fun s' ⟨r, ⟨hr, _⟩, hc⟩ => ?_
      simp only [id] at hc
      subst hc
      have h := timesIter_inr_count body hr
      exact ih s'.1 (by omega) s'.2
  intro s _
  exact key s.1 s.2

end timesLoops

end EquivLean.Cobol
