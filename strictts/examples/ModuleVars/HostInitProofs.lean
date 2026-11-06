/-
A module whose initialisation calls the host (`hostinit.ts`: `"ﬁ".normalize("NFKC")`, an external
call answered by the world's oracle). `World.ModuleInit` quantifies over the host's oracles, so a
world satisfying it exists; with the default oracle of `World.init` (every external call throws)
the initialisation never ends normally, so a statement form that ran it from `World.init` would be
unsatisfiable for this module, and every theorem assuming it vacuous.
-/
import ModuleVars.HostInitEx
import StrictTS.Proof.Auto

open StrictTS JS HostInitEx

theorem program_main : program.main = mainBlock := rfl
theorem program_globals : program.globals = [.str] := rfl

/-- A host that normalizes every string to `"fi"` (and answers no other call). -/
def fiHost : ExtOracle TT := fun _ _ ret _ _ =>
  match ret with
  | .str => .ok (.val (.str (JSStr.ofString "fi")))
  | _ => .error ⟨JSStr.ofString "Error", JSStr.ofString "external call"⟩

/-- Satisfiability: with that host the initialisation ends normally, so statements about this
module that assume `World.ModuleInit` are not vacuous. -/
theorem moduleInit_satisfiable (I : Impl) : ∃ w : World TT, w.ModuleInit I program := by
  have h : ∃ env w0, exec (moduleInit I program) (World.initWith fiHost (fun _ => F64.zero)
      (fun _ => F64.zero)) = some (.ok (.normal, env), w0) :=
    ⟨_, _, by
      simp (disch := decide) only [moduleInit, World.initWith, ts_sym, List.forIn_cons, List.forIn_nil,
        program_main, program_globals, mainBlock, g_LIGATURE, ligatureLength_call, ligatureLengthDef,
        fiHost]
      try rfl⟩
  obtain ⟨env, w0, h⟩ := h
  exact World.exists_moduleInit I program h

/-- With the default oracle the initialisation does not end normally. -/
theorem moduleInit_default_not_normal (I : Impl) (env : Env TT []) (w0 : World TT) :
    exec (moduleInit I program) (World.init TT) ≠ some (.ok (.normal, env), w0) := by
  simp (disch := decide) only [moduleInit, World.init, ts_sym, List.forIn_cons, List.forIn_nil,
    program_main, program_globals, mainBlock, g_LIGATURE, ligatureLength_call, ligatureLengthDef]
  simp

/-- A function that reads the variable the host's answer initialised: `ts_auto` splits on the
answer in the initialisation (an error contradicts its normal end; the value fills the box). -/
theorem ligatureLength_returns (I : Impl) (w : World TT) (hm : w.ModuleInit I program) :
    JS.Returns (callFun I program ligatureLengthRef .nil) w := by
  ts_auto
