/-
Reporting for the uniform `JS.NoPanic` sweep of tools/public: `np_stuck` names the first stuck
construct of every goal that `ts_auto` leaves, without changing the goals.

The first stuck construct of a goal is the evaluation step that symbolic execution could not take:
an application of the interpreter (a loop, a builtin, a call, an external call's answer) or an
`if` whose condition is undecided, found outside binders (the continuations of `bind` and the
alternatives of a `match` are binders, so what is found is the current evaluation point), the
innermost first. A goal with no such construct is a residual side condition.

Output, one info message per goal: `NPSTUCK <kind> :: <the construct, pretty-printed, cut>`.
-/
import StrictTS.Proof.Auto

namespace StrictTS.PublicDiag
open Lean Elab Tactic Meta

/-- Interpreter functions and the kind of stuck construct they stand for. -/
def heads : Array (Name × String) := #[
  (``evalLoop, "while/for loop"), (``evalDo, "do-while loop"), (``evalForOf, "for-of over an array"),
  (``evalForOfMap, "for-of over a Map"), (``evalForOfSet, "for-of over a Set"),
  (``evalForOfStr, "for-of over a string"), (``evalBuiltin, "builtin"), (``callFun, "call"),
  (``applyFn, "call of a function value"), (``applyLam, "function body"), (``World.ext, "external call answer"),
  (``evalE, "expression"), (``evalS, "statement"), (``evalB, "block"), (``JS.read, "heap read")]

/-- A short one-line rendering of `e`. -/
def short (e : Lean.Expr) (n : Nat := 160) : MetaM String := do
  let cs := (toString (← ppExpr e)).toList.map fun c => if c == '\n' then ' ' else c
  -- collapse runs of spaces
  let cs := cs.foldl (fun (acc : List Char) c => if c == ' ' && acc.head? == some ' ' then acc else c :: acc) [] |>.reverse
  return if cs.length ≤ n then String.ofList cs else String.ofList (cs.take n) ++ " …"

/-- Stuck constructs of `e` outside binders, innermost first. -/
partial def collect (e : Lean.Expr) (acc : Array (String × Lean.Expr)) : MetaM (Array (String × Lean.Expr)) := do
  match e with
  | .mdata _ b => collect b acc
  | .proj _ _ b => collect b acc
  -- the binders of the statement itself (`∀ msg w', ¬ …`; also behind metadata)
  | .forallE _ ty b _ => do let acc ← collect ty acc; collect b acc
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``ite || fn.isConstOf ``dite then
      -- only the condition is evaluated; an undecided condition is the stuck construct
      let c := args[1]!
      let acc ← collect c acc
      if c.isConstOf ``True || c.isConstOf ``False || c.hasLooseBVars then return acc
      return acc.push ("undecided test", c)
    let mut acc := acc
    for a in args do
      acc ← collect a acc
    if let .const n _ := fn then
      if let some (_, kind) := heads.find? (·.1 == n) then
        if !e.hasLooseBVars then acc := acc.push (kind, e)
    return acc
  | _ => return acc

elab "np_stuck" : tactic => do
  for g in ← getGoals do
    g.withContext do
      let t ← instantiateMVars (← g.getType)
      -- `JS.NoPanic` goals are `∀ msg w', ¬ exec … = …`: open the binders (the run becomes a
      -- local hypothesis), then search the run, the rest of the goal and the hypotheses that the
      -- splits of `ts_auto` introduced (newest first)
      let found ← forallTelescope t fun xs body => do
        let mut found := #[]
        for x in xs do
          found ← collect (← instantiateMVars (← inferType x)) found
        found ← collect body found
        if found.isEmpty then
          for d in (← getLCtx).decls.toArray.reverse do
            if let some d := d then
              if !d.isImplementationDetail then
                found ← collect (← instantiateMVars d.type) found
        return found
      match found[0]? with
      | some (kind, e) => logInfo m!"NPSTUCK {kind} :: {← short e}"
      | none =>
        -- no interpreter step left: a side condition; show it with the newest hypothesis
        let last := (← getLCtx).decls.toArray.reverse.findSome? fun d =>
          d.bind fun d => if d.isImplementationDetail then none else some d.type
        let ctx ← match last with
          | some ty => do pure s!" | last hypothesis: {← short (← instantiateMVars ty) 120}"
          | none => pure ""
        logInfo m!"NPSTUCK residual condition :: {← short t 100}{ctx}"

/-- The modules that `import StrictTS` adds to the imports of `StrictTS.Proof.Auto` and of an emitted
module (`StrictTS.Frontend.Prelude`, `StrictTS.Proof.Extern`), as of e57150b. -/
def rootOnly : Array Name := #[`StrictTS.Proof.Obs, `StrictTS.Proof.Eval, `StrictTS.Proof.Bits,
  `StrictTS.Proof.DynNullish, `StrictTS.Proof.DynOpt, `StrictTS.Testing]

open Command in
/-- `np_used thm`: the modules of `rootOnly` whose constants the proof of `thm` mentions, through the
auxiliary constants of the current file (`simp` lemmas used by rewriting appear; definitional ones
may not). Output: `NPUSED <thm> :: <modules or none>`, an info message, never an error. -/
elab "np_used " id:ident : command => do
  try
    let n ← liftCoreM <| resolveGlobalConstNoOverload id
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[n]
    let mut mods : NameSet := {}
    while todo.size > 0 do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      match env.getModuleIdxFor? c with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        if rootOnly.contains m then mods := mods.insert m
      | none =>
        if let some ci := env.find? c then
          -- a theorem's proof is opaque to `value?` unless asked for
          if let some v := ci.value? (allowOpaque := true) then
            todo := v.foldConsts todo fun k acc => acc.push k
          todo := ci.type.foldConsts todo fun k acc => acc.push k
    let ms := mods.toList.map toString
    logInfo m!"NPUSED {n} :: {if ms.isEmpty then "none" else " ".intercalate ms}"
  catch e =>
    logInfo m!"NPUSED {id.getId} :: unavailable ({← e.toMessageData.toString})"

end StrictTS.PublicDiag
