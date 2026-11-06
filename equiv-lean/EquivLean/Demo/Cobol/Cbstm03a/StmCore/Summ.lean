/-
# `stm_summary`: derived summaries with `stm_auto`

`cobol_summary` (`Cobol.Logic.Derive`) computes a summary's right-hand side with `cobol_sym`
and the listed lemmas only.  `stm_summary name binders : lhs` computes it with `stm_auto`,
which also uses every fact among the binders (field reads of whole-record facts included, see
`cobol_auto`), and adds `theorem name : ∀ binders, lhs = rhs`.  An optional `with_pre (tac)` runs
`tac` first (say, to split a conjunction of facts into hypotheses).
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Tac

namespace Cobol.StmCore
open Lean Elab Command

syntax (docComment)? "stm_summary " ident Lean.Parser.Command.declSig
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? (" with_pre " "(" tacticSeq ")")? : command

elab_rules : command
  | `($[$doc?:docComment]? stm_summary $n:ident $sig:declSig $[using [$ls?,*]]? $[with_pre ($pre?)]?) => do
    let ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
      match ls? with
      | some ls => ls.getElems
      | none => #[]
    let (bs, lhs) ← match sig with
      | `(Lean.Parser.Command.declSig| $bs* : $lhs) => pure (bs, lhs)
      | _ => throwUnsupportedSyntax
    let name := (← getCurrNamespace) ++ n.getId
    liftTermElabM do
      Term.elabBinders (bs.map (·.raw)) fun xs => do
        let lhsE ← Term.elabTerm lhs none
        Term.synthesizeSyntheticMVarsNoPostponing
        let lhsE ← instantiateMVars lhsE
        let ty ← Meta.inferType lhsE
        let rhs ← Meta.mkFreshExprMVar ty
        let goal ← Meta.mkFreshExprMVar (← Meta.mkEq lhsE rhs)
        let tac ← match pre? with
          | some p => `(tactic| (($p); (stm_auto [$ls,*]) <;> rfl))
          | none => `(tactic| ((stm_auto [$ls,*]) <;> rfl))
        Term.runTactic goal.mvarId! tac .term
        let rhsV ← instantiateMVars rhs
        let pf ← instantiateMVars goal
        let stmt ← Meta.mkForallFVars xs (← Meta.mkEq lhsE rhsV)
        let pfL ← Meta.mkLambdaFVars xs pf
        let stmt ← Term.levelMVarToParam (← instantiateMVars stmt)
        let pfL ← Term.levelMVarToParam (← instantiateMVars pfL)
        if stmt.hasMVar || pfL.hasMVar then
          throwError "stm_summary: the derived statement or proof still has metavariables"
        let lps := (collectLevelParams (collectLevelParams {} stmt) pfL).params
        addDecl (.thmDecl { name, levelParams := lps.toList, type := stmt, value := pfL })
        if let some doc := doc? then
          addDocString name (mkNullNode #[]) doc
        logInfo m!"{name}: {lhsE} =\n{rhsV}"

end Cobol.StmCore
