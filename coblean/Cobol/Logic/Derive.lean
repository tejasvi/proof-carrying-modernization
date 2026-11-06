/-
# Derived summaries

`cobol_summary` states a summary without writing its right-hand side: the effect of the
paragraph is computed by symbolic execution and becomes the theorem's statement.

```
cobol_summary getAcct (P : Program) (hcfg : P.cfg = Cbact04c.cfg) … (i : Nat)
    (hi : Sem.findKey { off := 0, len := 11 } (m.read 150 11) accts = some i) … :
    Sem.execSentences P env rec fuel Cbact04c.«1100-GET-ACCT-DATA».body ⟨m, …⟩
  using [hcfg, hfiles, hm, hi, hrec]
```

adds `theorem getAcct : ∀ (P : Program) … , Sem.execSentences … = rhs`, where `rhs` is what
`cobol_sym [hcfg, hfiles, hm, hi, hrec]` turns the left-hand side into, and prints `rhs` (the
paragraph's effect on the state, in terms of the binders).  Registered with
`attribute [local cobol_eval high] getAcct`, it replaces the paragraph wherever it runs.

Binders that the left-hand side does not determine (here the record number `i`) are fine when
a hypothesis pins them down, as `hi` does: at a call site simp's discharger rewrites
`Sem.findKey … = some ?i` to `ai = ?i` with the call site's facts and assigns `?i := ai`.
-/
import Cobol.Logic.Summary

namespace Cobol
open Lean Elab Command

/-- `cobol_sym` as a conversion, for one side of an equation (same simp set and simprocs). -/
syntax "cobol_sym_conv" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : conv
macro_rules
  | `(conv| cobol_sym_conv) => `(conv| cobol_sym_conv [])
  | `(conv| cobol_sym_conv [$xs,*]) =>
    `(conv| simp (config := { decide := false, maxSteps := 10000000, maxDischargeDepth := 4 }) only
      [cobol_eval, ↓reduceIte, ↓reduceDIte, reduceCtorEq, matchIte, ↓stopAtLoop, ↓matchItePre,
       mergeCtorIte, projIte, normWrite, mergeMemIte,
       unrollLoopUntil,
       reduceFitNumRange, reduceDecodeEncodeRange, reduceIntCmpRange, reduceIntLtRange,
       reduceInt64ToIntOfInt,
       reduceDecodeNum, reduceIntCompare, reduceCp037Char, reduceCp037Byte, reduceCp037CharEq, reduceUInt8Eq,
       reduceUInt8Range, reduceUInt8ToNatRange, reduceNatCmpRange, reduceEncodeNumBEq,
       Nat.reduceSucc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
       Nat.reducePow, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq, Nat.reduceBNe, Nat.reduceEqDiff,
       Nat.reduceLeDiff, Nat.reduceSubDiff,
       Int.reduceNeg, Int.reduceAdd, Int.reduceMul, Int.reduceSub, Int.reduceDiv, Int.reduceMod,
       Int.reducePow, Int.reduceLT, Int.reduceLE, Int.reduceGT, Int.reduceGE, Int.reduceEq,
       Int.reduceNe, Int.reduceBEq, Int.reduceBNe, Int.reduceAbs, Int.reduceToNat,
       Int.reduceNatCast, Int.reduceOfNat,
       UInt8.reduceLT, UInt8.reduceLE, UInt8.reduceToNat, UInt8.reduceOfNat, $xs,*])

/-- `cobol_summary name binders : lhs using [lemmas]`: the theorem `name : ∀ binders,
lhs = rhs` with `rhs` computed from `lhs` by `cobol_sym [lemmas]` (see the module doc). -/
syntax (docComment)? "cobol_summary " ident Lean.Parser.Command.declSig
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? : command

elab_rules : command
  | `($[$doc?:docComment]? cobol_summary $n:ident $sig:declSig $[using [$ls?,*]]?) => do
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
        let tac ← `(tactic| ((conv => lhs; cobol_sym_conv [$ls,*]); try rfl))
        Term.runTactic goal.mvarId! tac .term
        let rhsV ← instantiateMVars rhs
        let pf ← instantiateMVars goal
        let stmt ← Meta.mkForallFVars xs (← Meta.mkEq lhsE rhsV)
        let pfL ← Meta.mkLambdaFVars xs pf
        -- universe metavariables left by elaboration become parameters of the theorem
        let stmt ← Term.levelMVarToParam (← instantiateMVars stmt)
        let pfL ← Term.levelMVarToParam (← instantiateMVars pfL)
        if stmt.hasMVar || pfL.hasMVar then
          throwError "cobol_summary: the derived statement or proof still has metavariables"
        let lps := (collectLevelParams (collectLevelParams {} stmt) pfL).params
        addDecl (.thmDecl { name, levelParams := lps.toList, type := stmt, value := pfL })
        if let some doc := doc? then
          addDocString name (mkNullNode #[]) doc
        logInfo m!"{name}: {lhsE} =\n{rhsV}"

end Cobol
