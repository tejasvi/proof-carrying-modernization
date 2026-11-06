import EquivLean.Bridge.TS.Behaves

/-!
# StrictTS bridge: loops as `LoopShape`s

The interpreter runs `while`/`for` (`evalLoop`), `do … while` (`evalDo`) and
`for (const x of arr)` (`evalForOf`) by unfolding one iteration and recursing.  Here each
construct gets

* a *step* computation (`loopStep`, `doStep`, `forOfStep`) that runs one iteration and returns
  `.inl r` (leave the loop with the completion `r`) or `.inr s'` (continue from `s'`);
* the classification `stepCls` of the step's outcome (an exception or panic of the step also
  leaves the loop);
* `LoopShape` for the closed loop `fun ((s, w)) => JS.exec (loop s) w` (`loopShape`,
  `doShape`, `forOfShape`, and for the `Map`/`Set`/string iterations `forOfMapShape`,
  `forOfSetShape`, `forOfStrShape`), derived from the interpreter's unfolding equation `.eq_1`;
* `LoopShape.Terminates`, by fixpoint induction over the interpreter's least fixpoint
  (`Bridge/TS/Terminates.lean`).

The state of a loop includes the environment and the world.  The step functions are stated
for an arbitrary body evaluator (`…With`), so that the same definitions describe the real
interpreter and the approximants of its fixpoint.
-/

namespace EquivLean.TS
open StrictTS

/-! ## Option-valued loops -/

section
variable {α : Type}

theorem safe_option_iff (x : Option α) : Safe x ↔ x.isSome = true := Iff.rfl
theorem runs_option_iff (x : Option α) (o : α) : Runs x o ↔ x = some o := Iff.rfl

variable {σ O OD : Type}

/-- A loop on `Option` whose unfolding is a bind of one iteration has the `LoopShape`. -/
theorem loopShape_of_option {L : σ → Option O} {iter : σ → Option OD} {cls : OD → O ⊕ σ}
    (h : ∀ s, L s = (iter s).bind (fun r => Sum.elim some L (cls r))) :
    LoopShape L iter cls where
  safe_iff s := by
    simp only [safe_option_iff, runs_option_iff]
    rw [h s]
    rcases hi : iter s with _ | r
    · simp
    · rcases hc : cls r with o | s'
      · simp only [Option.bind_some, hc, Sum.elim_inl, Option.isSome_some, true_and, true_iff]
        rintro r' s'' ⟨⟩ hc'
        rw [hc] at hc'; cases hc'
      · simp only [Option.bind_some, hc, Sum.elim_inr, Option.isSome_some, true_and]
        constructor
        · rintro hs r' s'' ⟨⟩ hc'
          rw [hc] at hc'; cases hc'; exact hs
        · intro hall; exact hall r s' rfl hc
  runs_iff s o := by
    simp only [runs_option_iff]
    rw [h s]
    rcases hi : iter s with _ | r
    · simp
    · rcases hc : cls r with o' | s'
      · simp only [Option.bind_some, hc, Sum.elim_inl, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨r, rfl, .inl hc⟩
        · rintro ⟨r', h1, h' | ⟨s'', h', -⟩⟩
          · cases h1; rw [hc] at h'; cases h'; rfl
          · cases h1; rw [hc] at h'; cases h'
      · simp only [Option.bind_some, hc, Sum.elim_inr]
        constructor
        · intro ho; exact ⟨r, rfl, .inr ⟨s', hc, ho⟩⟩
        · rintro ⟨r', h1, h' | ⟨s'', h', ho⟩⟩
          · cases h1; rw [hc] at h'; cases h'
          · cases h1; rw [hc] at h'; cases h'; exact ho

end

/-! ## Loops in the `JS` monad -/

variable {TT : TypeTable}

/-- Classification of the outcome of one iteration: `.inl b` leaves the loop with the
completion `b`, `.inr s` continues from `s`; an exception or panic of the iteration leaves the
loop with that exception. -/
def stepCls {β σ : Type} : Out TT (β ⊕ σ) → Out TT β ⊕ (σ × World TT)
  | (.ok (.inl b), w) => .inl (.ok b, w)
  | (.ok (.inr s), w) => .inr (s, w)
  | (.error e, w) => .inl (.error e, w)

@[simp] theorem stepCls_inl {β σ : Type} (b : β) (w : World TT) :
    stepCls (σ := σ) (.ok (.inl b), w) = .inl (.ok b, w) := rfl
@[simp] theorem stepCls_inr {β σ : Type} (s : σ) (w : World TT) :
    stepCls (β := β) (.ok (.inr s), w) = .inr (s, w) := rfl
@[simp] theorem stepCls_error {β σ : Type} (e : Exc) (w : World TT) :
    stepCls (β := β) (σ := σ) (.error e, w) = .inl (.error e, w) := rfl

/-- A `JS` loop whose execution unfolds into one step and a recursive call. -/
theorem loopShape_js {β σ : Type} (L : σ → JS TT β) (step : σ → JS TT (β ⊕ σ))
    (h : ∀ s w, JS.exec (L s) w = (JS.exec (step s) w).bind
      (fun r => Sum.elim some (fun p => JS.exec (L p.1) p.2) (stepCls r))) :
    LoopShape (fun p : σ × World TT => JS.exec (L p.1) p.2) (fun p => JS.exec (step p.1) p.2)
      stepCls :=
  loopShape_of_option fun p => h p.1 p.2

/-! ## `while (c) body` and `for (; c; step) body` -/

section loop
variable {Γ : Ctx} {ρ : Ty}

/-- The body of `evalLoop`, with the evaluators of conditions and blocks and the recursive
call as parameters (a verbatim copy of `StrictTS.evalLoop`). -/
def loopBodyWith (E : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool))
    (B : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (L : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) :
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

/-- One iteration of `while`/`for`: `.inr env'` continues with the environment `env'`. -/
def loopStepWith (E : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool))
    (B : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ Env TT Γ) := do
  match ← JS.catchThrown (E c env) with
  | .error ex => pure (.inl (.exc ex, env))
  | .ok v =>
    if v.toBool then do
      let (cb, env1) ← B body env
      match cb with
      | .normal | .cont 0 => do
        let (cs, env2) ← B step env1
        match cs with
        | .normal => pure (.inr env2)
        | other => pure (.inl (other, env2))
      | .brk 0 => pure (.inl (.normal, env1))
      | .brk (n + 1) => pure (.inl (.brk n, env1))
      | .cont (n + 1) => pure (.inl (.cont n, env1))
      | other => pure (.inl (other, env1))
    else pure (.inl (.normal, env))

/-- One iteration of the real interpreter's `while`/`for`. -/
abbrev loopStep (I : Impl) (P : Program TT) (c : Expr TT Γ .bool) (body step : Block TT Γ ρ)
    (env : Env TT Γ) : JS TT ((Completion TT ρ × Env TT Γ) ⊕ Env TT Γ) :=
  loopStepWith (evalE I P) (evalB I P) c body step env

theorem exec_loopBodyWith (E : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool))
    (B : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (L : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) (env : Env TT Γ) (w : World TT) :
    JS.exec (loopBodyWith E B L c body step env) w =
      (JS.exec (loopStepWith E B c body step env) w).bind
        (fun r => Sum.elim some (fun p => JS.exec (L c body step p.1) p.2) (stepCls r)) := by
  simp only [loopBodyWith, loopStepWith, JS.exec_bind, JS.exec_catchThrown]
  rcases JS.exec (E c env) w with _ | ⟨(_ | _) | v, w₁⟩ <;> try rfl
  dsimp only
  cases v.toBool
  · rfl
  · simp only [ite_true, JS.exec_bind]
    rcases JS.exec (B body env) w₁ with _ | ⟨_ | ⟨cb, env1⟩, w₂⟩ <;> try rfl
    dsimp only
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex
    all_goals try rfl
    all_goals
      simp only [JS.exec_bind]
      rcases JS.exec (B step env1) w₂ with _ | ⟨_ | ⟨cs, env2⟩, w₃⟩ <;> try rfl
      dsimp only
      rcases cs with _ | (_ | n) | (_ | n) | v | p | ex <;> rfl

theorem evalLoop_eq_with (I : Impl) (P : Program TT) (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (env : Env TT Γ) :
    evalLoop I P c body step env =
      loopBodyWith (evalE I P) (evalB I P) (evalLoop I P) c body step env := by
  rw [evalLoop.eq_1]; rfl

/-- `while`/`for` loops have the `LoopShape` of their one-iteration step. -/
theorem loopShape (I : Impl) (P : Program TT) (c : Expr TT Γ .bool) (body step : Block TT Γ ρ) :
    LoopShape (fun p : Env TT Γ × World TT => JS.exec (evalLoop I P c body step p.1) p.2)
      (fun p => JS.exec (loopStep I P c body step p.1) p.2) stepCls :=
  loopShape_js (fun env => evalLoop I P c body step env) (fun env => loopStep I P c body step env)
    fun env w => by rw [evalLoop_eq_with, exec_loopBodyWith]

end loop

/-! ## `do body while (c)` -/

section dowhile
variable {Γ : Ctx} {ρ : Ty}

/-- The body of `evalDo` with its evaluators and recursive call as parameters. -/
def doBodyWith (E : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool))
    (B : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (L : Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  let (cb, env1) ← B body env
  match cb with
  | .normal | .cont 0 => do
    match ← JS.catchThrown (E c env1) with
    | .error ex => pure (.exc ex, env1)
    | .ok v => if v.toBool then L body c env1 else pure (.normal, env1)
  | .brk 0 => pure (.normal, env1)
  | .brk (n + 1) => pure (.brk n, env1)
  | .cont (n + 1) => pure (.cont n, env1)
  | other => pure (other, env1)

/-- One iteration of `do … while`. -/
def doStepWith (E : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool))
    (B : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ Env TT Γ) := do
  let (cb, env1) ← B body env
  match cb with
  | .normal | .cont 0 => do
    match ← JS.catchThrown (E c env1) with
    | .error ex => pure (.inl (.exc ex, env1))
    | .ok v => if v.toBool then pure (.inr env1) else pure (.inl (.normal, env1))
  | .brk 0 => pure (.inl (.normal, env1))
  | .brk (n + 1) => pure (.inl (.brk n, env1))
  | .cont (n + 1) => pure (.inl (.cont n, env1))
  | other => pure (.inl (other, env1))

abbrev doStep (I : Impl) (P : Program TT) (body : Block TT Γ ρ) (c : Expr TT Γ .bool)
    (env : Env TT Γ) : JS TT ((Completion TT ρ × Env TT Γ) ⊕ Env TT Γ) :=
  doStepWith (evalE I P) (evalB I P) body c env

theorem exec_doBodyWith (E : Expr TT Γ .bool → Env TT Γ → JS TT (Val TT .bool))
    (B : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (L : Block TT Γ ρ → Expr TT Γ .bool → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (body : Block TT Γ ρ) (c : Expr TT Γ .bool) (env : Env TT Γ) (w : World TT) :
    JS.exec (doBodyWith E B L body c env) w =
      (JS.exec (doStepWith E B body c env) w).bind
        (fun r => Sum.elim some (fun p => JS.exec (L body c p.1) p.2) (stepCls r)) := by
  simp only [doBodyWith, doStepWith, JS.exec_bind]
  rcases JS.exec (B body env) w with _ | ⟨_ | ⟨cb, env1⟩, w₁⟩ <;> try rfl
  dsimp only
  rcases cb with _ | (_ | n) | (_ | n) | v | p | ex
  all_goals try rfl
  all_goals
    simp only [JS.exec_bind, JS.exec_catchThrown]
    rcases JS.exec (E c env1) w₁ with _ | ⟨(_ | _) | v, w₂⟩ <;> try rfl
    dsimp only
    cases v.toBool <;> rfl

theorem evalDo_eq_with (I : Impl) (P : Program TT) (body : Block TT Γ ρ) (c : Expr TT Γ .bool)
    (env : Env TT Γ) :
    evalDo I P body c env = doBodyWith (evalE I P) (evalB I P) (evalDo I P) body c env := by
  rw [evalDo.eq_1]; rfl

theorem doShape (I : Impl) (P : Program TT) (body : Block TT Γ ρ) (c : Expr TT Γ .bool) :
    LoopShape (fun p : Env TT Γ × World TT => JS.exec (evalDo I P body c p.1) p.2)
      (fun p => JS.exec (doStep I P body c p.1) p.2) stepCls :=
  loopShape_js (fun env => evalDo I P body c env) (fun env => doStep I P body c env)
    fun env w => by rw [evalDo_eq_with, exec_doBodyWith]

end dowhile

/-! ## `for (const x of arr)` -/

section forof
variable {Γ : Ctx} {ρ t : Ty}

/-- The body of `evalForOf` with the block evaluator and the recursive call as parameters. -/
def forOfBodyWith
    (B : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ)))
    (L : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (a : Nat) (i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  let cell ← JS.readArr t a
  if h : i < cell.size then do
    let (cb, env1) ← B body (.cons cell[i] env)
    match cb with
    | .normal | .cont 0 => L a (i + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)
  else pure (.normal, env)

/-- One iteration of `for … of`: `.inr (i', env')` continues at index `i'`. -/
def forOfStepWith
    (B : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ)))
    (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (i : Nat) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ (Nat × Env TT Γ)) := do
  let cell ← JS.readArr t a
  if h : i < cell.size then do
    let (cb, env1) ← B body (.cons cell[i] env)
    match cb with
    | .normal | .cont 0 => pure (.inr (i + 1, env1.tail))
    | .brk 0 => pure (.inl (.normal, env1.tail))
    | .brk (n + 1) => pure (.inl (.brk n, env1.tail))
    | .cont (n + 1) => pure (.inl (.cont n, env1.tail))
    | other => pure (.inl (other, env1.tail))
  else pure (.inl (.normal, env))

abbrev forOfStep (I : Impl) (P : Program TT) (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ)
    (i : Nat) (env : Env TT Γ) : JS TT ((Completion TT ρ × Env TT Γ) ⊕ (Nat × Env TT Γ)) :=
  forOfStepWith (evalB I P) a body i env

theorem exec_forOfBodyWith
    (B : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ)))
    (L : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (a : Nat) (i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) :
    JS.exec (forOfBodyWith B L a i body env) w =
      (JS.exec (forOfStepWith B a body i env) w).bind
        (fun r => Sum.elim some (fun p => JS.exec (L a p.1.1 body p.1.2) p.2) (stepCls r)) := by
  simp only [forOfBodyWith, forOfStepWith, JS.exec_bind, JS.exec_readArr]
  rcases w.heap.get? (.arr t, a) with _ | cell <;> try rfl
  dsimp only
  by_cases hi : i < cell.size
  · simp only [hi, dite_true, JS.exec_bind]
    rcases JS.exec (B body (.cons cell[i] env)) w with _ | ⟨_ | ⟨cb, env1⟩, w₁⟩ <;> try rfl
    dsimp only
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> rfl
  · simp only [hi, dite_false]; rfl

theorem evalForOf_eq_with (I : Impl) (P : Program TT) (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOf I P a i body env = forOfBodyWith (evalB I P) (evalForOf I P) a i body env := by
  rw [evalForOf.eq_1]; rfl

theorem forOfShape (I : Impl) (P : Program TT) (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) :
    LoopShape (fun p : (Nat × Env TT Γ) × World TT => JS.exec (evalForOf I P a p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfStep I P a body p.1.1 p.1.2) p.2) stepCls :=
  loopShape_js (fun s => evalForOf I P a s.1 body s.2) (fun s => forOfStep I P a body s.1 s.2)
    fun s w => by rw [evalForOf_eq_with, exec_forOfBodyWith]

end forof

/-! ## `for (const [k, v] of map)`, `for (const x of set)`, `for (const ch of str)` -/

section forofmap
variable {Γ : Ctx} {ρ k v : Ty}

/-- The body of `evalForOfMap` with the block evaluator and the recursive call as parameters. -/
def forOfMapBodyWith
    (B : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ →
      Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ)))
    (L : Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    (a : Nat) (i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ)
    (env : Env TT Γ) : JS TT (Completion TT ρ × Env TT Γ) := do
  let m ← JS.readMap k v a
  match m.nextFrom i with
  | none => pure (.normal, env)
  | some (j, key, val) => do
    let (cb, env1) ← B body (.cons (.tup (.cons key (.cons val .nil))) env)
    match cb with
    | .normal | .cont 0 => L a (j + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)

/-- One iteration over a `Map`: `.inr (j', env')` continues at entry index `j'`. -/
def forOfMapStepWith
    (B : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ →
      Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ)))
    (a : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (i : Nat)
    (env : Env TT Γ) : JS TT ((Completion TT ρ × Env TT Γ) ⊕ (Nat × Env TT Γ)) := do
  let m ← JS.readMap k v a
  match m.nextFrom i with
  | none => pure (.inl (.normal, env))
  | some (j, key, val) => do
    let (cb, env1) ← B body (.cons (.tup (.cons key (.cons val .nil))) env)
    match cb with
    | .normal | .cont 0 => pure (.inr (j + 1, env1.tail))
    | .brk 0 => pure (.inl (.normal, env1.tail))
    | .brk (n + 1) => pure (.inl (.brk n, env1.tail))
    | .cont (n + 1) => pure (.inl (.cont n, env1.tail))
    | other => pure (.inl (other, env1.tail))

abbrev forOfMapStep (I : Impl) (P : Program TT) (a : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (i : Nat) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ (Nat × Env TT Γ)) :=
  forOfMapStepWith (evalB I P) a body i env

theorem exec_forOfMapBodyWith
    (B : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ →
      Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ)))
    (L : Nat → Nat → Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Env TT Γ →
      JS TT (Completion TT ρ × Env TT Γ))
    (a : Nat) (i : Nat) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ)
    (env : Env TT Γ) (w : World TT) :
    JS.exec (forOfMapBodyWith B L a i body env) w =
      (JS.exec (forOfMapStepWith B a body i env) w).bind
        (fun r => Sum.elim some (fun p => JS.exec (L a p.1.1 body p.1.2) p.2) (stepCls r)) := by
  simp only [forOfMapBodyWith, forOfMapStepWith, JS.exec_bind, JS.exec_readMap]
  rcases w.heap.get? (.map k v, a) with _ | m <;> try rfl
  dsimp only
  rcases m.nextFrom i with _ | ⟨j, key, val⟩
  · rfl
  · simp only [JS.exec_bind]
    rcases JS.exec (B body (.cons (.tup (.cons key (.cons val .nil))) env)) w with
      _ | ⟨_ | ⟨cb, env1⟩, w₁⟩ <;> try rfl
    dsimp only
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> rfl

theorem evalForOfMap_eq_with (I : Impl) (P : Program TT) (a i : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOfMap I P a i body env =
      forOfMapBodyWith (evalB I P) (evalForOfMap I P) a i body env := by
  rw [evalForOfMap.eq_1]; rfl

theorem forOfMapShape (I : Impl) (P : Program TT) (a : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) :
    LoopShape
      (fun p : (Nat × Env TT Γ) × World TT => JS.exec (evalForOfMap I P a p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfMapStep I P a body p.1.1 p.1.2) p.2) stepCls :=
  loopShape_js (fun s => evalForOfMap I P a s.1 body s.2) (fun s => forOfMapStep I P a body s.1 s.2)
    fun s w => by rw [evalForOfMap_eq_with, exec_forOfMapBodyWith]

end forofmap

section forofset
variable {Γ : Ctx} {ρ t : Ty}

/-- The body of `evalForOfSet` with the block evaluator and the recursive call as parameters. -/
def forOfSetBodyWith
    (B : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ)))
    (L : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (a : Nat) (i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  let m ← JS.readSet t a
  match m.nextFrom i with
  | none => pure (.normal, env)
  | some (j, x, _) => do
    let (cb, env1) ← B body (.cons x env)
    match cb with
    | .normal | .cont 0 => L a (j + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)

/-- One iteration over a `Set`. -/
def forOfSetStepWith
    (B : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ)))
    (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (i : Nat) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ (Nat × Env TT Γ)) := do
  let m ← JS.readSet t a
  match m.nextFrom i with
  | none => pure (.inl (.normal, env))
  | some (j, x, _) => do
    let (cb, env1) ← B body (.cons x env)
    match cb with
    | .normal | .cont 0 => pure (.inr (j + 1, env1.tail))
    | .brk 0 => pure (.inl (.normal, env1.tail))
    | .brk (n + 1) => pure (.inl (.brk n, env1.tail))
    | .cont (n + 1) => pure (.inl (.cont n, env1.tail))
    | other => pure (.inl (other, env1.tail))

abbrev forOfSetStep (I : Impl) (P : Program TT) (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ)
    (i : Nat) (env : Env TT Γ) : JS TT ((Completion TT ρ × Env TT Γ) ⊕ (Nat × Env TT Γ)) :=
  forOfSetStepWith (evalB I P) a body i env

theorem exec_forOfSetBodyWith
    (B : Block TT (⟨t, false⟩ :: Γ) ρ → Env TT (⟨t, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨t, false⟩ :: Γ)))
    (L : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (a : Nat) (i : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) :
    JS.exec (forOfSetBodyWith B L a i body env) w =
      (JS.exec (forOfSetStepWith B a body i env) w).bind
        (fun r => Sum.elim some (fun p => JS.exec (L a p.1.1 body p.1.2) p.2) (stepCls r)) := by
  simp only [forOfSetBodyWith, forOfSetStepWith, JS.exec_bind, JS.exec_readSet]
  rcases w.heap.get? (.set t, a) with _ | m <;> try rfl
  dsimp only
  rcases m.nextFrom i with _ | ⟨j, x, u⟩
  · rfl
  · simp only [JS.exec_bind]
    rcases JS.exec (B body (.cons x env)) w with _ | ⟨_ | ⟨cb, env1⟩, w₁⟩ <;> try rfl
    dsimp only
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> rfl

theorem evalForOfSet_eq_with (I : Impl) (P : Program TT) (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOfSet I P a i body env = forOfSetBodyWith (evalB I P) (evalForOfSet I P) a i body env := by
  rw [evalForOfSet.eq_1]; rfl

theorem forOfSetShape (I : Impl) (P : Program TT) (a : Nat) (body : Block TT (⟨t, false⟩ :: Γ) ρ) :
    LoopShape
      (fun p : (Nat × Env TT Γ) × World TT => JS.exec (evalForOfSet I P a p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfSetStep I P a body p.1.1 p.1.2) p.2) stepCls :=
  loopShape_js (fun s => evalForOfSet I P a s.1 body s.2) (fun s => forOfSetStep I P a body s.1 s.2)
    fun s w => by rw [evalForOfSet_eq_with, exec_forOfSetBodyWith]

end forofset

section forofstr
variable {Γ : Ctx} {ρ : Ty}

/-- The body of `evalForOfStr` (iteration over the remaining code points `cps`). -/
def forOfStrBodyWith
    (B : Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT (⟨.str, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.str, false⟩ :: Γ)))
    (L : List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (cps : List JSStr) (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) :=
  match cps with
  | [] => pure (.normal, env)
  | ch :: rest => do
    let (cb, env1) ← B body (.cons (.str ch) env)
    match cb with
    | .normal | .cont 0 => L rest body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)

/-- One iteration over the code points of a string: `.inr (rest, env')` continues. -/
def forOfStrStepWith
    (B : Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT (⟨.str, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.str, false⟩ :: Γ)))
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (cps : List JSStr) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ (List JSStr × Env TT Γ)) :=
  match cps with
  | [] => pure (.inl (.normal, env))
  | ch :: rest => do
    let (cb, env1) ← B body (.cons (.str ch) env)
    match cb with
    | .normal | .cont 0 => pure (.inr (rest, env1.tail))
    | .brk 0 => pure (.inl (.normal, env1.tail))
    | .brk (n + 1) => pure (.inl (.brk n, env1.tail))
    | .cont (n + 1) => pure (.inl (.cont n, env1.tail))
    | other => pure (.inl (other, env1.tail))

abbrev forOfStrStep (I : Impl) (P : Program TT) (body : Block TT (⟨.str, false⟩ :: Γ) ρ)
    (cps : List JSStr) (env : Env TT Γ) :
    JS TT ((Completion TT ρ × Env TT Γ) ⊕ (List JSStr × Env TT Γ)) :=
  forOfStrStepWith (evalB I P) body cps env

theorem exec_forOfStrBodyWith
    (B : Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT (⟨.str, false⟩ :: Γ) →
      JS TT (Completion TT ρ × Env TT (⟨.str, false⟩ :: Γ)))
    (L : List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ))
    (cps : List JSStr) (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT) :
    JS.exec (forOfStrBodyWith B L cps body env) w =
      (JS.exec (forOfStrStepWith B body cps env) w).bind
        (fun r => Sum.elim some (fun p => JS.exec (L p.1.1 body p.1.2) p.2) (stepCls r)) := by
  rcases cps with _ | ⟨ch, rest⟩
  · rfl
  · simp only [forOfStrBodyWith, forOfStrStepWith, JS.exec_bind]
    rcases JS.exec (B body (.cons (.str ch) env)) w with _ | ⟨_ | ⟨cb, env1⟩, w₁⟩ <;> try rfl
    dsimp only
    rcases cb with _ | (_ | n) | (_ | n) | v | p | ex <;> rfl

theorem evalForOfStr_eq_with (I : Impl) (P : Program TT) (cps : List JSStr)
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) :
    evalForOfStr I P cps body env = forOfStrBodyWith (evalB I P) (evalForOfStr I P) cps body env := by
  rw [evalForOfStr.eq_def]; rcases cps <;> rfl

theorem forOfStrShape (I : Impl) (P : Program TT) (body : Block TT (⟨.str, false⟩ :: Γ) ρ) :
    LoopShape
      (fun p : (List JSStr × Env TT Γ) × World TT => JS.exec (evalForOfStr I P p.1.1 body p.1.2) p.2)
      (fun p => JS.exec (forOfStrStep I P body p.1.1 p.1.2) p.2) stepCls :=
  loopShape_js (fun s => evalForOfStr I P s.1 body s.2) (fun s => forOfStrStep I P body s.1 s.2)
    fun s w => by rw [evalForOfStr_eq_with, exec_forOfStrBodyWith]

end forofstr

end EquivLean.TS
