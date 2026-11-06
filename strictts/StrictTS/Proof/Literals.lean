/-
StrictTS proof layer: literals and argument values in symbolic execution.

* `arrayIndexNumeral` (simproc, in `simp` and `ts_sym`): a constant index `xs[2]` reaches the
  interpreter as `Conv.arrayIndex? (2 : F64)`. `Conv.arrayIndex?_ofNat` is stated for
  `F64.ofNat n`, and simp cannot instantiate a lemma over `OfNat.ofNat n` with a variable `n`
  (numerals are literals in its index), so `simp only [ts_sym]` left such reads stuck.
* `ts_destruct`: case analysis of argument values (`Vals` lists, single-constructor values,
  records, tuples, optionals, enums), so that a statement over every argument list `vs` reaches the
  same form as one over explicit payloads. Record and tuple fields need their index
  (`(Fields.cons …).types`) reduced before `cases` can unify it, which `rcases` does not do.
* `ts_enum_cases`: the index of an enum value split into its values (for the narrowing of a
  string-literal union, which goes through `enumToStr` and string comparisons).
* `cell_cases_arr` / `_map` / `_set`, `ts_cell1`, `ts_cells`: case analysis of the heap cell an
  array, map or set argument refers to: present (with the cell's type, as the loop and callback
  summaries `ts_summarize` / `ts_callbacks` expect their hypothesis) or dangling.
-/
import StrictTS.Proof.Numbers

namespace StrictTS
open Lean Meta Simp

/-- `Conv.arrayIndex? (n : F64) = some n` for a numeral `n < 2^32 - 1` (an array index). -/
simproc [simp, ts_sym] arrayIndexNumeral (Conv.arrayIndex? _) := fun e => do
  let_expr Conv.arrayIndex? x := e | return .continue
  let_expr OfNat.ofNat _ lit _ := x | return .continue
  let some n := lit.rawNatLit? | return .continue
  unless n < 2 ^ 32 - 1 do return .continue
  let lem := mkApp (mkConst ``Conv.arrayIndex?_ofNat) (mkNatLit n)
  let .forallE _ hyp _ _ ← whnfR (← inferType lem) | return .continue
  let pf := mkApp lem (← mkDecideProof hyp)
  let rhs := mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) (mkNatLit n)
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-- The heap cell of an array argument is dangling or holds the array's elements. -/
theorem cell_cases_arr {TT : TypeTable} (w : World TT) (t : Ty) (a : Nat) :
    w.heap.get? (.arr t, a) = none ∨ ∃ c : Array (Val TT t), w.heap.get? (.arr t, a) = some c := by
  cases h : w.heap.get? (.arr t, a) with
  | none => exact .inl rfl
  | some c => exact .inr ⟨c, rfl⟩

/-- The heap cell of a `Map` argument is dangling or holds its entries. -/
theorem cell_cases_map {TT : TypeTable} (w : World TT) (k v : Ty) (a : Nat) :
    w.heap.get? (.map k v, a) = none ∨ ∃ c : JSMap (Val TT k) (Val TT v), w.heap.get? (.map k v, a) = some c := by
  cases h : w.heap.get? (.map k v, a) with
  | none => exact .inl rfl
  | some c => exact .inr ⟨c, rfl⟩

/-- The heap cell of a `Set` argument is dangling or holds its elements. -/
theorem cell_cases_set {TT : TypeTable} (w : World TT) (t : Ty) (a : Nat) :
    w.heap.get? (.set t, a) = none ∨ ∃ c : JSMap (Val TT t) Unit, w.heap.get? (.set t, a) = some c := by
  cases h : w.heap.get? (.set t, a) with
  | none => exact .inl rfl
  | some c => exact .inr ⟨c, rfl⟩

open Elab Tactic in
/-- `ts_destruct`: case analysis of every hypothesis `vs : Vals TT ts` (by its list of types) and
`v : Val TT t` with `t` a single-constructor type (number, string, bigint, boolean, undefined,
null, error, array, typed array, Map, Set, object, promise, box, enum) or a record or tuple (their
fields in turn), and of optionals and unions (a union value by its member) while there are fewer than
32 goals. -/
elab "ts_destruct" : tactic => do
  let destructible (t : Lean.Expr) (budget : Bool) : MetaM Bool := do
    let t ← whnfR t
    match t.getAppFn.constName? with
    | some n =>
      return n ∈ [``Ty.num, ``Ty.bigint, ``Ty.bool, ``Ty.str, ``Ty.undef, ``Ty.null, ``Ty.err, ``Ty.arr, ``Ty.tarr,
        ``Ty.map, ``Ty.set, ``Ty.obj, ``Ty.promise, ``Ty.box, ``Ty.enum, ``Ty.record, ``Ty.tup] ||
        (budget && (n == ``Ty.opt || n == ``Ty.union))
    | none => return false
  let rec loop : Nat → TacticM Unit
    | 0 => pure ()
    | fuel + 1 => do
      let gs ← getGoals
      let budget := gs.length < 32
      let mut progress := false
      let mut out : List MVarId := []
      for g in gs do
        let r ← g.withContext do
          for d in (← getLCtx) do
            if d.isImplementationDetail then continue
            let ty ← whnfR (← instantiateMVars d.type)
            let ok ← if ty.isAppOfArity ``StrictTS.Vals 2 then pure true
              else if ty.isAppOfArity ``StrictTS.Val 2 then destructible (ty.getArg! 1) budget
              -- the member of a union value (`Val.inj m x`): its cases fix the member type
              else if ty.isAppOfArity ``StrictTS.Mem 2 then pure budget
              else pure false
            if !ok then continue
            -- reduce the index (e.g. `(Fields.cons …).types`) so that `cases` can unify it
            let idx ← whnfR (ty.getArg! 1)
            let ty' := mkApp2 ty.getAppFn (ty.getArg! 0) idx
            let g' ← g.replaceLocalDeclDefEq d.fvarId ty'
            try
              let sub ← g'.cases d.fvarId
              return some (sub.toList.map (·.mvarId))
            catch _ => continue
          return none
        match r with
        | some sg => progress := true; out := out ++ sg
        | none => out := out ++ [g]
      setGoals out
      if progress then loop fuel
  loop 64

open Elab Tactic in
/-- `ts_enum_cases`: split every index `i : Fin n` of an enum value (`Val.enum i`, from
`ts_destruct`; `n` reduces to a literal of at most 16) into its `n` values, while there are at
most 64 goals; the values are then concrete, so that `enumToStr` and the comparisons of a
narrowed union evaluate. -/
elab "ts_enum_cases" : tactic => do
  let rec loop : Nat → TacticM Unit
    | 0 => pure ()
    | fuel + 1 => do
      let gs ← getGoals
      let mut progress := false
      let mut out : List MVarId := []
      for g in gs do
        let r ← g.withContext do
          for d in (← getLCtx) do
            if d.isImplementationDetail then continue
            let ty ← whnfR (← instantiateMVars d.type)
            unless ty.isAppOfArity ``Fin 1 do continue
            let some k := (← reduce (ty.getArg! 0)).rawNatLit? | continue
            unless 0 < k && k ≤ 16 && (gs.length + out.length) * k ≤ 64 do continue
            let g' ← g.rename d.fvarId `ts_enum_idx
            let pat := String.intercalate " | " (List.replicate k "_") ++ " | ts_enum_k"
            let .ok stx := Parser.runParserCategory (← getEnv) `tactic
                s!"rcases ts_enum_idx with ⟨{pat}, ts_enum_lt⟩" | continue
            let sub ← Tactic.run g' (evalTactic stx)
            -- the last case (`k + n < n`) is impossible
            let mut keep : List MVarId := []
            for s in sub do
              let closed ← try
                  let rest ← Tactic.run s (evalTactic (← `(tactic| (simp only [List.length_cons, List.length_nil] at $(mkIdent `ts_enum_lt):ident; omega))))
                  pure rest.isEmpty
                catch _ => pure false
              unless closed do keep := keep ++ [s]
            return some keep
          return none
        match r with
        | some sg => progress := true; out := out ++ sg
        | none => out := out ++ [g]
      setGoals out
      if progress then loop fuel
  loop 8

open Elab Tactic in
/-- `ts_cell1`: case analysis of the heap cell of one array, map or set argument of the goal
(`Val.arr a` with `a` a variable) that no hypothesis mentions yet: present
(`hcell : w.heap.get? (k, a) = some cell`, `cell` of the cell's type) or dangling (`= none`).
The world is the one of the first `JS.exec` in the goal. -/
elab "ts_cell1" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some ex := goal.find? (fun e => e.isAppOfArity ``JS.exec 4) | throwError "ts_cell1: no exec in the goal"
  let w := ex.getArg! 3
  -- (case lemma, its arguments TT and kind types, address)
  let collect (e : Lean.Expr) : Option (Name × Array Lean.Expr × Lean.Expr) :=
    if e.isAppOfArity ``Val.arr 3 && (e.getArg! 2).isFVar then some (``cell_cases_arr, #[e.getArg! 0, e.getArg! 1], e.getArg! 2)
    else if e.isAppOfArity ``Val.set 3 && (e.getArg! 2).isFVar then some (``cell_cases_set, #[e.getArg! 0, e.getArg! 1], e.getArg! 2)
    else if e.isAppOfArity ``Val.map 4 && (e.getArg! 3).isFVar then some (``cell_cases_map, #[e.getArg! 0, e.getArg! 1, e.getArg! 2], e.getArg! 3)
    else none
  let acc ← IO.mkRef (#[] : Array (Name × Array Lean.Expr × Lean.Expr))
  let _ ← Core.transform goal (pre := fun e => do
    if let some c := collect e then acc.modify (·.push c)
    return .continue)
  let lctx ← getLCtx
  for (lem, targs, a) in ← acc.get do
    let mut seen := false
    for d in lctx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if (t.find? fun e => e.isAppOf ``Std.ExtDHashMap.get? && e.containsFVar a.fvarId!).isSome then seen := true
    if seen then continue
    -- cell_cases_* {TT} w (kind types…) a
    let full := mkAppN (mkConst lem) (#[targs[0]!, w] ++ targs.extract 1 targs.size ++ #[a])
    let pS ← Term.exprToSyntax full
    evalTactic (← `(tactic| rcases $pS:term with hcell | ⟨cell, hcell⟩))
    return
  throwError "ts_cell1: no argument cell without a hypothesis"

/-- `ts_cells`: `ts_cell1` on every goal until every argument cell is split. -/
macro "ts_cells" : tactic => `(tactic| all_goals (repeat' ts_cell1))

section Tests
private def TT0 : TypeTable := ⟨fun _ => .undef, fun _ => .nil⟩

example : Conv.arrayIndex? (0 : F64) = some 0 := by simp only [arrayIndexNumeral]
example : Conv.arrayIndex? (7 : F64) = some 7 := by simp only [ts_sym]
example (x : Option Nat) (h : Conv.arrayIndex? (4294967294 : F64) = x) : x = some 4294967294 := by
  simp only [ts_sym] at h; exact h.symm

/-- Records, optionals, arrays and enums are taken apart: 4 goals with explicit payloads. -/
example (vs : Vals TT0 [(.record (.cons "a" (.opt .num) (.cons "b" .str .nil))), (.arr .num), (.opt .num),
    (.enum ["x", "y"])]) : True := by
  ts_destruct
  guard_target = True
  all_goals trivial

/-- Enum indices are split into their values (the impossible case is dropped). -/
example (vs : Vals TT0 [(.enum ["x", "y", "z"]), .num]) : True := by
  ts_destruct
  ts_enum_cases
  guard_target = True
  all_goals trivial

example (i : Fin ["x", "y", "z"].length) : i.val < 3 := by
  ts_enum_cases
  all_goals simp

example (I : Impl) (P : Program TT0) (f : FunRef (.cons (.arr .num) .nil) .num) (a : Nat) (w : World TT0) :
    JS.exec (callFun I P f (.cons (.arr a) .nil)) w = JS.exec (callFun I P f (.cons (.arr a) .nil)) w := by
  ts_cells
  all_goals rfl
end Tests

end StrictTS
