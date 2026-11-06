/-
# Equivalence proofs: COBOL program ≡ target-language rewrite

A typical statement: for every storage `m` whose input fields hold values `xᵢ`
(`hᵢ : decodeNum c fᵢ (m.read offᵢ lenᵢ) = some xᵢ`),

  `obsCOBOL (P.run c fuel (P.initState m)) = obsJava (method x₁ … xₙ)`.

`cobol_equiv [defs, facts]` proves such goals in two steps:

1. **symbolic execution** of both sides (`cobol_sym` with the `java_eval` / `rust_eval` sets,
   the observation functions, the transcribed method and the facts): the goal becomes an
   equation between two trees of `if`s whose conditions and leaves are scaled-integer terms
   over the inputs;
2. **`grind`** with the scaled-integer definitions (`divRound`, `fitNum`, …): congruence
   closure identifies equal subterms of the two sides — including nonlinear ones such as
   `bal * rate * days`, which linear arithmetic treats as atoms — linear integer arithmetic
   decides the conditions, and case splits enumerate the paths.

What `grind` does not find by itself is an arithmetic identity between *different* rounding
pipelines (e.g. COBOL's truncated intermediate quotient followed by a `ROUNDED` store, against
one `HALF_UP` division in Java).  State it as a lemma (usually closed by `cobol_arith`) and put
it in the context with `have`: congruence closure then uses it wherever the terms occur.

`cobol_ranges` adds the range of every input field (`decodeNum c f bs = some v` gives
`f.Holds c v`, evaluated: digits bound, sign, binary range) to the context.
-/
import Cobol.Logic.Eval
import Cobol.Target.Java
import Cobol.Target.Rust

namespace Cobol
open Lean Elab Tactic Meta

attribute [cobol_eval] false_implies true_implies Int.natAbs_natCast Int.natCast_nonneg

/-- For every hypothesis `h : decodeNum c f bs = some v`, add `h_range : f.Holds c v`,
evaluated to bounds on `v` (`cobol_ranges [defs]` also unfolds `defs`, e.g. named formats). -/
syntax "cobol_ranges" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cobol_ranges $[[$xs,*]]?) => withMainContext do
  let mut hyps : Array Hypothesis := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isAppOfArity ``decodeNum 3 && rhs.isAppOfArity ``Option.some 2 do continue
    let pf ← mkAppM ``decodeNum_holds #[lhs.getArg! 0, lhs.getArg! 1, ldecl.toExpr]
    let n := Name.mkSimple s!"{ldecl.userName.eraseMacroScopes}_range"
    hyps := hyps.push { userName := n, type := ← inferType pf, value := pf }
  if hyps.isEmpty then return
  let (_, g) ← (← getMainGoal).assertHypotheses hyps
  replaceMainGoal [g]
  let ids := hyps.map fun h => mkIdent h.userName
  let xs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := match xs with
    | some xs => xs.getElems
    | none => #[]
  evalTactic (← `(tactic| try cobol_sym [NumFmt.Holds, $xs,*] at $ids*))

/-- `grind` with the scaled-integer definitions: rounding, high-order truncation, fitting into
a receiving item, binary wrap-around.  Merged values are `if`-trees inside arithmetic, so the
case-split budget is larger than `grind`'s default. -/
macro "cobol_grind" : tactic =>
  `(tactic| grind (splits := 64) [divRound, divRoundZ, rescale, truncDigits, Sem.fitNum, Sem.fitDec, Sem.fitBin,
    Sem.inBinRange, Sem.wrapBin, binHalf, binMod, NumFmt.fullBinary, Config.binBytes])

/-- Prove `obsCOBOL (P.run …) = obsTarget (method …)`: symbolic execution of both sides with
the given definitions and facts, then `cobol_grind`. -/
syntax "cobol_equiv" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cobol_equiv) => `(tactic| cobol_equiv [])
  | `(tactic| cobol_equiv [$xs,*]) =>
    `(tactic| (try cobol_sym [java_eval, rust_eval, $xs,*]) <;> cobol_grind)

end Cobol
