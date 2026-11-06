/-
StrictTS proof layer: statements over the initialised module world.

Functions that read module-level variables (`const LIMIT = 10`, `const NAMES = new Set([…])`)
read heap cells that the module's initialisation creates: the variables' boxes at addresses
`0 … n-1` and the cells their initialisers allocate. A statement for every world would have to
cover worlds where these cells are missing or hold other values; the statement form here
restricts the world to one where the module has been initialised.

* `moduleInit I P`: the module's initialisation, as `runProgram` performs it before the event
  loop (and `Testing.initWorld` for random tests): allocate the module variables, run the module
  body.
* `World.ModuleInit I P w`: the initialisation, run from an initial world (nothing allocated,
  queued or printed; the host's oracles for external calls, `Math.random()` and `Date.now()`
  arbitrary: `World.initWith`), ends normally in a world `w0`, every cell of `w0` is unchanged in
  `w`, and `w` allocates after them. A function called by the host after start-up (an entry
  point, a handler) runs in such a world as long as no earlier call changed those cells. The
  oracles are quantified because a module body may call the host (`process.env`, a regular
  expression): with a fixed oracle that throws, its initialisation never ends normally and the
  hypothesis would be unsatisfiable. `ts_auto` turns the hypothesis into one heap fact per cell of
  `w0` (`w.heap.get? (k, a) = some c`), computing `w0` by symbolic execution of the module body;
  `World.exists_moduleInit` turns one concrete initialisation run into a world satisfying it
  (the satisfiability check of a module's statements).
* `runProgram_eq_moduleInit`: a whole run is the initialisation followed by the event loop in the
  world it leaves, which satisfies `World.ModuleInit` (`moduleInit_moduleInit`).
-/
import StrictTS.Proof.Exec

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- The module's initialisation: allocate the module variables (boxes at addresses
`0 … n-1`, uninitialised), then run the module body. -/
def moduleInit (I : Impl) (P : Program TT) : JS TT (Completion TT .undef × Env TT []) := do
  for t in P.globals do
    let _ ← JS.alloc (.box t) none
  evalB I P P.main .nil

/-- An initial world: nothing allocated, queued or printed, and the host's oracles (the answers
to external calls, `Math.random()`, `Date.now()`) given. -/
def World.initWith (ext : ExtOracle TT) (rand now : Nat → F64) : World TT :=
  { heap := ∅, next := 0, rand := rand, now := now, ext := ext }

/-- `World.init` is the initial world with the default oracles. -/
theorem World.init_eq_initWith : World.init TT = World.initWith (World.init TT).ext (World.init TT).rand
    (World.init TT).now := rfl

/-- **Statement form for code that reads module-level variables.** For some oracles of the host,
the module's initialisation, run from the initial world with these oracles, ends normally in a
world `w0`; every cell of `w0` holds the same content in `w`, and `w` allocates after them. -/
def World.ModuleInit (I : Impl) (P : Program TT) (w : World TT) : Prop :=
  ∃ (ext : ExtOracle TT) (rand now : Nat → F64) (w0 : World TT) (env : Env TT []),
    exec (moduleInit I P) (World.initWith ext rand now) = some (.ok (.normal, env), w0) ∧
    (∀ k : HKey, k.2 < w0.next → w.heap.get? k = w0.heap.get? k) ∧ w0.next ≤ w.next

/-- The world the initialisation leaves satisfies `World.ModuleInit`. -/
theorem moduleInit_moduleInit_with (I : Impl) (P : Program TT) (ext : ExtOracle TT) (rand now : Nat → F64)
    (w0 : World TT) (env : Env TT [])
    (h : exec (moduleInit I P) (World.initWith ext rand now) = some (.ok (.normal, env), w0)) :
    w0.ModuleInit I P :=
  ⟨ext, rand, now, w0, env, h, fun _ _ => rfl, Nat.le_refl _⟩

/-- The world the initialisation leaves from `World.init` satisfies `World.ModuleInit`. -/
theorem moduleInit_moduleInit (I : Impl) (P : Program TT) (w0 : World TT) (env : Env TT [])
    (h : exec (moduleInit I P) (World.init TT) = some (.ok (.normal, env), w0)) :
    w0.ModuleInit I P :=
  moduleInit_moduleInit_with I P _ _ _ w0 env h

/-- **Satisfiability**: one initialisation run that ends normally (for some oracles) gives a world
that satisfies `World.ModuleInit`, so statements assuming it are not vacuous. -/
theorem World.exists_moduleInit (I : Impl) (P : Program TT) {ext : ExtOracle TT} {rand now : Nat → F64}
    {w0 : World TT} {env : Env TT []}
    (h : exec (moduleInit I P) (World.initWith ext rand now) = some (.ok (.normal, env), w0)) :
    ∃ w : World TT, w.ModuleInit I P :=
  ⟨w0, moduleInit_moduleInit_with I P ext rand now w0 env h⟩

/-- A whole run: the module's initialisation, then (unless the module body throws) the event
loop, started in the world the initialisation leaves (which satisfies `World.ModuleInit`). -/
theorem runProgram_eq_moduleInit (I : Impl) (P : Program TT) (w : World TT) :
    exec (runProgram I P) w =
      match exec (moduleInit I P) w with
      | some (.ok (.exc e, _), w') => some (.error (.thrown e), w')
      | some (.ok (_, _), w') => exec (eventLoop I P) w'
      | some (.error e, w') => some (.error e, w')
      | none => none := by
  simp only [runProgram, moduleInit, exec_bind]
  rcases exec (forIn P.globals PUnit.unit fun t r => do
      let _ ← JS.alloc (.box t) none
      pure (ForInStep.yield PUnit.unit)) w with _ | ⟨_ | ⟨⟩, w1⟩
  · rfl
  · rfl
  · dsimp only
    rcases exec (evalB I P P.main Env.nil) w1 with _ | ⟨_ | ⟨c, env⟩, w2⟩
    · rfl
    · rfl
    · cases c <;> rfl

end StrictTS
