/-
Functions that read module-level constants (`consts.ts`), proved by `ts_auto` in the initialised
module world: `World.ModuleInit I program w` says that the module's initialisation (allocate the
module variables, run the module body) ends normally from the initial world and that `w` still
holds every cell it created. `ts_auto` runs the module body symbolically and turns the
hypothesis into one heap fact per cell (the boxes of `LIMIT`, `PREFIX`, `NAMES`, `WEIGHTS` and
the `Set` and array they hold), then proceeds as usual.
-/
import ModuleVars.ModVarsEx
import StrictTS.Proof.Auto

open StrictTS JS ModVarsEx

/-- A number constant in a ternary. -/
theorem clampToLimit_returns (I : Impl) (x : F64) (w : World TT) (hm : w.ModuleInit I program) :
    JS.Returns (callFun I program clampToLimitRef (.cons (.num x) .nil)) w := by
  ts_auto

/-- A string constant: the result is computed. -/
theorem userKey_eq (I : Impl) (s : JSStr) (w : World TT) (hm : w.ModuleInit I program) :
    exec (callFun I program userKeyRef (.cons (.str s) .nil)) w =
      some (.ok (.str (JSStr.ofString "user:" ++ s)), w) := by
  ts_auto

/-- A `Set` constant (its cell is allocated by the module body). -/
theorem isKnown_returns (I : Impl) (s : JSStr) (w : World TT) (hm : w.ModuleInit I program) :
    JS.Returns (callFun I program isKnownRef (.cons (.str s) .nil)) w := by
  ts_auto

/-- A loop that compares with a constant. -/
theorem countAboveLimit_returns (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hm : w.ModuleInit I program) (hw : w.heap.get? (.arr .num, a) = some xs) :
    JS.Returns (callFun I program countAboveLimitRef (.cons (.arr a) .nil)) w := by
  ts_auto

/-- A loop over an array constant. -/
theorem weightedSum_returns (I : Impl) (w : World TT) (hm : w.ModuleInit I program) :
    JS.Returns (callFun I program weightedSumRef .nil) w := by
  ts_auto

/-- A validation against a constant. -/
theorem checkedLimit_noPanic (I : Impl) (x : F64) (w : World TT) (hm : w.ModuleInit I program) :
    JS.NoPanic (callFun I program checkedLimitRef (.cons (.num x) .nil)) w := by
  ts_auto

/-- Without the initialised module world the statement fails: in a world where `LIMIT`'s box
holds nothing, reading it throws a `ReferenceError` (still no panic, but no value). -/
example (I : Impl) (x : F64) (w : World TT)
    (h : w.heap.get? (.box .num, 0) = some none) :
    ¬ JS.Returns (callFun I program clampToLimitRef (.cons (.num x) .nil)) w := by
  simp only [JS.Returns, clampToLimit_call, clampToLimitDef, ts_sym, g_LIMIT, h]
  simp

/-- The statements above are not vacuous: the module's initialisation ends normally (the body
makes no external call; any oracles), so a world satisfying `World.ModuleInit` exists. -/
theorem moduleInit_satisfiable (I : Impl) : ∃ w : World TT, w.ModuleInit I program := by
  have h : ∃ env w0, exec (moduleInit I program) (World.initWith (World.init TT).ext (fun _ => F64.zero)
      (fun _ => F64.zero)) = some (.ok (.normal, env), w0) :=
    ⟨_, _, by
      simp (disch := decide) only [moduleInit, World.initWith, ts_sym, List.forIn_cons, List.forIn_nil,
        program, mainBlock, g_LIMIT, g_PREFIX, g_NAMES, g_WEIGHTS]
      try rfl⟩
  obtain ⟨env, w0, h⟩ := h
  exact World.exists_moduleInit I program h
