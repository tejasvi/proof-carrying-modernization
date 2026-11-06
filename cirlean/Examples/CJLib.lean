import CIR

/-!
  Helpers for the cJSON string and buffer examples (`Examples/CJStrings.lean`,
  `Examples/CJScan.lean`, `Examples/CJParseString.lean`). Nothing here is
  specific to cJSON; each item stands for a step that `cir_vcg` does not do
  yet (see the list of automation gaps in the header of `CJStrings.lean`).
-/

open CIR

namespace Examples.CJ

/-- Weakening of a function's postcondition (a case lemma, proved over its own
precondition, is used for the whole specification). -/
theorem returns_mono {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {P Q : Option Val → Mem → Prop} (h : Returns ctx sym args m P)
    (hPQ : ∀ r m', P r m' → Q r m') : Returns ctx sym args m Q := by
  unfold Returns Calls at *
  apply Res.holds_mono h
  rintro ⟨e, m'⟩ he
  cases e with
  | ret v => exact hPQ v m' he
  | _ => exact he

/-- An unsigned conversion is in range. `cir_vcg` only knows the converse
(`wrap_u32_self`: a value already in range is unchanged), so an invariant such
as `h < 4294967296` for an unsigned variable that was assigned `h * 16 + d`
leaves `(wrap false 32 (...)).toNat < 4294967296`. -/
theorem wrap_u_range (w : Nat) (x : Int) : 0 ≤ wrap false w x ∧ wrap false w x < 2 ^ w := by
  unfold wrap
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hp : (0 : Int) < 2 ^ w := by exact_mod_cast Nat.two_pow_pos w
  exact ⟨Int.emod_nonneg _ (Int.ne_of_gt hp), Int.emod_lt_of_pos _ hp⟩

open Lean Meta Elab Tactic in
/-- `wrap_ranges` adds `0 ≤ wrap false w e ∧ wrap false w e < 2 ^ w` for every
unsigned conversion `wrap false w e` in the goal and the hypotheses. -/
elab "wrap_ranges" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let r ← IO.mkRef (#[] : Array Expr)
    let collect (e : Expr) : MetaM Unit :=
      e.forEachWhere (fun t => t.isAppOfArity ``CIR.wrap 3 && !t.hasLooseBVars &&
          (t.getArg! 0).isConstOf ``Bool.false)
        fun t => r.modify fun a => if a.contains t then a else a.push t
    collect (← instantiateMVars (← g.getType))
    for d in ← getLCtx do
      unless d.isImplementationDetail do collect (← instantiateMVars d.type)
    let mut g := g
    for t in ← r.get do
      let pf ← mkAppM ``wrap_u_range #[t.getArg! 1, t.getArg! 2]
      let (_, g') ← (← g.assert `cirW (← inferType pf) pf).intro1P
      g := g'
    replaceMainGoal [g]

end Examples.CJ
