/-
StrictTS proof layer: `ts_auto`, the automatic proof attempt.

`ts_auto [lemmas]` runs the recipe that proves most refactorings and loop/callback contracts
without any invariant: unfold the calls of top-level functions in the goal (each function at
most once, so recursion cannot loop), execute symbolically (`ts_sym`), summarize every `for … of`
loop and every array callback (`ts_summarize`, `ts_callbacks`), and finish with `simp`.
An array, map or set argument whose cell no hypothesis fixes is split first (`ts_cells`): present
(the summaries need its contents) or dangling, where both sides panic at their first read of the
cell (`evalForOf_dangling`, `evalBuiltin_arrReduce_dangling`, …: `simp` lemmas of
`StrictTS.Proof.LibLemmas`, imported with `StrictTS`), so that statements for every world need no
`w.heap.get? … = some …` hypothesis.

A loop behind an undecided test (input validation `if (xs.length === 0) throw …` before the
loop) sits in the continuation of the `match` on the `if` statement's outcome, out of the
summaries' reach: `ts_auto` then splits on the innermost undecided test of the goal (`findTest`:
an `if`, an optional value or a Boolean that is not a constructor, an answer of the
external-call oracle), evaluates each case with its hypothesis and the heap hypotheses, closes the
cases that contradict the hypotheses (`omega` on the test's `Nat` facts, a precondition that gives
the test the other value), and goes on in each case. Straight-line code with such a test is
finished the same way when `split` (which takes the outermost, monadic `match`) does not close it.
For `JS.NoPanic` and `JS.NoFault` goals, a `while` or counted `for` loop that no summary handles
is replaced by its possible outcomes (`loopFallback`, `evalLoop_cases_exit`): it diverges, or it
ends in the same world with a completion a function body may end with, provided no iteration
panics or changes the world from an environment that satisfies the invariant: the loop's `const`
values, and the candidates about its other slots that one symbolic iteration keeps (Houdini-style:
slots the loop never assigns keep their values, a counter that the condition reads stays a safe
natural; `set_option trace.ts_auto.inv true` shows the candidates and the kept ones). An iteration
may end with an exception under `JS.NoPanic` and not under `JS.NoFault`, unless the program may
catch one (`try`, async code), where both are tried. A `for … of`
loop that no summary handles is replaced the same way when its iterations keep the world but for
the external-call counter (they may call the host). String arguments that a hypothesis bounds
(`v.toStr.length < 2 ^ 53`) are split into `.str s` first.
An answer of the oracle to a synchronous external call (a regex test, a string method) is split
into an error and a value of each form, or only the values under a hypothesis
`World.ExtReturns w f` (the library function never throws), of the forms that hypotheses
`World.ExtSpec` allow (ECMA-262's guarantees, e.g. element 0 of a match result is a string). A hypothesis
`w.ModuleInit I P` (the initialised module world, `StrictTS.Proof.Module`) is turned into one heap
fact per cell of the initialised world first, computed by symbolic execution of the module body.

Async goals (the microtask loop `drain`, the event loop, a whole run, promise cells) finish with
`ts_drain` instead, which runs every queued job; the given lemmas (e.g. the oracle's answers to
external calls) take part in that symbolic execution, and an answer of the oracle that they do
not fix is split on (an error, a value of each form, or the elements of a fresh array at array
types), so that statements about every oracle (`NoFault`) need no case analysis.

`set_option ts_auto.profile true` prints on stderr where a `ts_auto` call spends its heartbeats
and time, phase by phase, with the work of failed attempts that was thrown away.
-/
import StrictTS.Proof.Summarize
import StrictTS.Proof.Contract
import StrictTS.Proof.AsyncRace
import StrictTS.Proof.Literals
import StrictTS.Proof.F64Eval
import StrictTS.Proof.Extern
import StrictTS.Proof.Module
import StrictTS.Proof.LoopExit

namespace StrictTS
open Lean Elab Tactic Meta

/-- A query of the external-call oracle, `w.ext name args ret vs n`, as an application of
`World.ext` or of the structure's primitive projection (field 12): its arguments `vs` and `n`. -/
def oracleArgs? (q : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  let q := q.consumeMData
  if q.isAppOfArity ``World.ext 7 then some (q.getArg! 5, q.getArg! 6)
  else match q.getAppFn with
    | .proj ``World 12 _ => if q.getAppNumArgs == 5 then some (q.getArg! 3, q.getArg! 4) else none
    | _ => none

register_option ts_auto.profile : Bool := {
  defValue := false
  descr := "ts_auto: print the heartbeats and wall time of each phase on stderr (self: without the \
    phases that run inside it; total: of its outermost runs), every 10 s and at the end (one proof \
    at a time: with Elab.async=false)" }

/-- A phase of `ts_auto` (`ts_auto.profile`): heartbeats without the phases inside, heartbeats and
milliseconds of its outermost runs (a phase that runs inside itself counts once), runs. -/
structure TsProfEntry where
  name : String
  self : Nat := 0
  total : Nat := 0
  ms : Nat := 0
  runs : Nat := 0

/-- The profile of the current `ts_auto` call: its start (time, heartbeats), the time of the last
snapshot, the open phases (name, start time and heartbeats, heartbeats of the phases inside so
far) and the totals of the finished runs. -/
structure TsProfState where
  t0 : Nat := 0
  h0 : Nat := 0
  last : Nat := 0
  opens : Array (String × Nat × Nat × Nat) := #[]
  done : Array TsProfEntry := #[]
deriving Inhabited

initialize tsAutoProf : IO.Ref TsProfState ← IO.mkRef {}

/-- The profile so far on stderr, with the open phases (`ts_auto.profile`; heartbeats in the
units of `maxHeartbeats`, thousands). -/
def tsProfPrint (title : String) : IO Unit := do
  let st ← tsAutoProf.get
  let (now, hb) := (← IO.monoMsNow, ← IO.getNumHeartbeats)
  let (t, h) := (now - st.t0, hb - st.h0)
  let ps := st.done.qsort (fun a b => a.self > b.self)
  let attributed := ps.foldl (· + ·.self) 0
  let lines := ps.toList.map fun p =>
    s!"  {p.name}: self {p.self / 1000}, total {p.total / 1000} ({p.ms} ms), {p.runs} run(s)"
  let opens := st.opens.toList.map fun (n, ts, hs, _) =>
    s!"  open: {n}, {(hb - hs) / 1000} so far ({now - ts} ms)"
  IO.eprintln (s!"ts_auto profile ({title}): {t} ms, {h / 1000} heartbeats (maxHeartbeats units), \
    {(h - min h attributed) / 1000} outside the finished phases\n" ++ "\n".intercalate (lines ++ opens))

/-- Add the heartbeats and time since `t0`, `h0` to the entry `name` as work that was thrown away
(`ts_auto.profile`; its heartbeats also count in the phases that did it). -/
def tsProfNote (name : String) (t0 h0 : Nat) : TacticM Unit := do
  unless ts_auto.profile.get (← getOptions) do return
  let dt := (← IO.monoMsNow) - t0
  let dh := (← IO.getNumHeartbeats) - h0
  let upd (p : TsProfEntry) : TsProfEntry := { p with total := p.total + dh, ms := p.ms + dt, runs := p.runs + 1 }
  tsAutoProf.modify fun st =>
    { st with done := match st.done.findIdx? (·.name == name) with
      | some i => st.done.modify i upd
      | none => st.done.push (upd { name }) }

/-- Run `act` as the phase `name` of `ts_auto`, adding its heartbeats and time to the totals when
`ts_auto.profile` is set (also when it fails, is backtracked or runs out of heartbeats). -/
def tsProf {α : Type} (name : String) (act : TacticM α) : TacticM α := do
  unless ts_auto.profile.get (← getOptions) do return ← act
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  if t0 ≥ (← tsAutoProf.get).last + 10000 then
    tsAutoProf.modify ({ · with last := t0 })
    tsProfPrint "so far"
  let outer := !(← tsAutoProf.get).opens.any (·.1 == name)
  tsAutoProf.modify fun st => { st with opens := st.opens.push (name, t0, h0, 0) }
  let record : TacticM Unit := do
    let dt := (← IO.monoMsNow) - t0
    let dh := (← IO.getNumHeartbeats) - h0
    tsAutoProf.modify fun st =>
      let inner := st.opens.back?.map (·.2.2.2) |>.getD 0
      let os := st.opens.pop
      let os := if os.isEmpty then os else os.modify (os.size - 1) fun (n, ts, hs, i) => (n, ts, hs, i + dh)
      let upd (p : TsProfEntry) : TsProfEntry :=
        { p with self := p.self + (dh - min dh inner), total := p.total + (if outer then dh else 0),
                 ms := p.ms + (if outer then dt else 0), runs := p.runs + 1 }
      let done := match st.done.findIdx? (·.name == name) with
        | some i => st.done.modify i upd
        | none => st.done.push (upd { name })
      { st with opens := os, done }
  tryCatchRuntimeEx
    (do let r ← act; record; return r)
    (fun ex => do record; throw ex)

/-- The `X.f_call` lemma and `X.fDef` definition of the function whose reference is the constant
`X.fRef` (as emitted by the translator), if they exist. -/
def callLemmaOf (ref : Name) : MetaM (Option (Name × Name)) := do
  let s := ref.getString!
  unless s.endsWith "Ref" do return none
  let base := String.ofList (s.toList.take (s.length - 3))
  let pre := ref.getPrefix
  let lem := pre.str (base ++ "_call")
  let defn := pre.str (base ++ "Def")
  let env ← getEnv
  if env.contains lem && env.contains defn then return some (lem, defn) else return none

/-- Unfold one call of a top-level function in the goal whose name is not in `done`; returns its
reference name. -/
def unfoldOneCall (done : Array Name) : TacticM (Option Name) := withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  -- (a call under a binder, e.g. with the result of an earlier step as argument, cannot be
  -- rewritten: it is unfolded once a summary has computed that result)
  let some e := goal.find? fun e =>
      e.isAppOfArity ``callFun 7 && (e.getArg! 5).isConst && !done.contains (e.getArg! 5).constName! &&
        !e.hasLooseBVars
    | return none
  let ref := (e.getArg! 5).constName!
  let some (lem, defn) ← callLemmaOf ref | return none
  let lemI := mkIdent lem
  let defI := mkIdent defn
  try
    evalTactic (← `(tactic| rw [$lemI:ident]))
    evalTactic (← `(tactic| simp only [$defI:ident, ts_sym]))
  catch _ => return none
  return some ref

/-- Does the goal run async code: the microtask loop, the event loop, a whole run, or promise
cells? -/
def isAsyncGoal (e : Lean.Expr) : Bool :=
  (e.find? fun e => e.isConstOf ``drain || e.isConstOf ``eventLoop || e.isConstOf ``runOutput ||
    e.isConstOf ``runProgram || e.isConstOf ``HKind.promise).isSome

/-- An answer of the external-call oracle that the goal depends on (`w.ext name args ret vs n`,
not under a binder). -/
def findOracleQuery (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t => (oracleArgs? t).isSome && !t.hasLooseBVars

/-- The condition of an `if` of the goal that is not under a binder. -/
def findIteCond (e : Lean.Expr) : Option Lean.Expr :=
  (e.find? fun t => t.isAppOfArity ``ite 5 && !(t.getArg! 1).hasLooseBVars).map (·.getArg! 1)

/-- A Boolean variable of the goal (e.g. the payload of a `.bool b` answer of the oracle). -/
def findBoolFVar (e : Lean.Expr) : MetaM (Option FVarId) := do
  for fv in (Lean.collectFVars {} e).fvarIds do
    if (← whnfR (← fv.getType)).isConstOf ``Bool then return some fv
  return none

/-- Finish an async goal: run the code with `ts_drain`; if the outcome depends on an answer of
the external-call oracle that no lemma fixes, split on that answer (an error, a value of each
form, or the elements of a fresh array at array types) and continue in every case; a Boolean the
run branches on (the payload of a `.bool` answer), or else the condition of an `if` it is stuck on
(e.g. a comparison of a string answer), is split the same way. At most `depth` nested splits. -/
partial def finishAsync (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (depth : Nat) :
    TacticM Unit := do
  try evalTactic (← `(tactic| ts_drain [$lemmas,*])) catch _ => pure ()
  if (← getGoals).isEmpty || depth = 0 then return
  let target ← instantiateMVars (← getMainTarget)
  match findOracleQuery target with
  | some q =>
    let hI := mkIdent (Name.mkSimple s!"hext{depth}")
    let eI := mkIdent (Name.mkSimple s!"exte{depth}")
    let vI := mkIdent (Name.mkSimple s!"extv{depth}")
    let xI := mkIdent (Name.mkSimple s!"extx{depth}")
    let esI := mkIdent (Name.mkSimple s!"extes{depth}")
    let qs ← Term.exprToSyntax q
    evalTactic (← `(tactic| rcases $hI:ident : $qs:term with $eI:ident | $vI:ident))
    let lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| $hI:ident))
    let mut rest : List MVarId := []
    for g in ← getGoals do
      setGoals [g]
      -- the answer: a value `.val x` (or the elements of a fresh array, at array types), then
      -- each form of `x`
      try evalTactic (← `(tactic| rcases $vI:ident with $xI:ident | $esI:ident)) catch _ => pure ()
      try evalTactic (← `(tactic| cases $xI:ident)) catch _ => pure ()
      for g' in ← getGoals do
        setGoals [g']
        finishAsync lemmas (depth - 1)
        rest := rest ++ (← getGoals)
    setGoals rest
  | none =>
    -- a Boolean the run branches on (the payload of a `.bool` answer), else the condition of
    -- an `if` the run is stuck on (e.g. a comparison of a string answer)
    let mut lemmas := lemmas
    let goals ← match ← withMainContext (findBoolFVar target) with
      | some b => do
        let subgoals ← (← getMainGoal).cases b
        pure (subgoals.toList.map (·.mvarId))
      | none => do
        let some c := findIteCond target | return
        let hcI := mkIdent (Name.mkSimple s!"hcond{depth}")
        let cs ← Term.exprToSyntax c
        evalTactic (← `(tactic| by_cases $hcI:ident : $cs:term))
        lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| $hcI:ident))
        getGoals
    let mut rest : List MVarId := []
    for g in goals do
      setGoals [g]
      finishAsync lemmas (depth - 1)
      rest := rest ++ (← getGoals)
    setGoals rest

/-- Does a hypothesis say that a heap cell is missing (`w.heap.get? (k, a) = none`)? -/
def hasDanglingCell : TacticM Bool := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? then
      if lhs.isAppOf ``Std.ExtDHashMap.get? && rhs.isAppOf ``Option.none then return true
  return false

/-- The array methods with a callback that `ts_callbacks` rewrites. -/
def isCallbackBuiltin (b : Lean.Expr) : Bool :=
  [``Builtin.arrReduce, ``Builtin.arrMap, ``Builtin.arrForEach, ``Builtin.arrSort, ``Builtin.arrFilter,
    ``Builtin.arrSome, ``Builtin.arrEvery, ``Builtin.arrFind, ``Builtin.arrFindIndex, ``Builtin.arrFindLast,
    ``Builtin.arrFindLastIndex].any b.isAppOf

/-- The run of a loop that the summaries may handle (`for … of`, a `for` loop, a `while` loop:
counted ones whose body ends with the counter step), or of an array method with a callback. -/
def isSummarizableLoop (x : Lean.Expr) : Bool :=
  x.isAppOf ``evalForOf || x.isAppOf ``evalForOfStr || x.isAppOf ``evalForOfMap ||
    x.isAppOf ``evalForOfSet ||
    (x.isAppOf ``evalLoop && x.getAppNumArgs == 9) ||
    (x.isAppOf ``evalBuiltin && x.getAppNumArgs ≥ 6 && isCallbackBuiltin (x.getArg! 5).consumeMData)

/-- Such a loop is still in the goal (anywhere, also in the continuation of a `match` that is
stuck on a test). -/
def hasLoop (e : Lean.Expr) : Bool := (e.find? isSummarizableLoop).isSome

/-- Such a loop is run in the goal where the summaries find it (`JS.exec loop w`). -/
def hasExposedLoop (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``JS.exec 4 && isSummarizableLoop (x.getArg! 2).consumeMData).isSome

/-- A loop that the summaries or the partial-correctness fallback (`loopFallback`: `while` and
`for` loops) handle. -/
def isHandledLoop (x : Lean.Expr) : Bool := isSummarizableLoop x || x.isAppOfArity ``evalLoop 9

/-- Such a loop is in the goal where they do not find it (not run by a `JS.exec` of the goal: in
the continuation of a stuck `match`). -/
partial def hasHiddenLoop (e : Lean.Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``JS.exec 4 && isHandledLoop (e.getArg! 2).consumeMData then
    -- (a run at the world or environment of a stuck `match`'s case is hidden too)
    e.hasLooseBVars || hasHiddenLoop (e.getArg! 3)
  else if isHandledLoop e then true
  else match e with
    | .app f a => hasHiddenLoop f || hasHiddenLoop a
    | .lam _ t b _ | .forallE _ t b _ => hasHiddenLoop t || hasHiddenLoop b
    | .letE _ t v b _ => hasHiddenLoop t || hasHiddenLoop v || hasHiddenLoop b
    | .mdata _ b | .proj _ _ b => hasHiddenLoop b
    | _ => false

/-- Some loop (`while`, `do … while` included) is still in the goal. -/
def hasAnyLoop (e : Lean.Expr) : Bool :=
  hasLoop e || (e.find? fun x => x.isAppOf ``evalLoop || x.isAppOf ``evalDo).isSome

/-- An undecided test that a run is stuck on. -/
inductive AutoTest where
  /-- the condition of an `if` (e.g. the outcome of an `if` statement whose test the heap
  hypotheses do not decide) -/
  | cond (c : Lean.Expr)
  /-- an optional value or a Boolean that is not a constructor (a heap read, `m.get(k)`) -/
  | val (d : Lean.Expr)
  /-- an answer of the external-call oracle (`w.ext name args ret vs n`) -/
  | oracle (q : Lean.Expr)
  /-- the run of materializing a symbolic answer (`exec (materialize ev) w`, or of the elements
  of a fresh array), which always succeeds: named, not split (`exec_materialize_ok`) -/
  | mat (lem : Name) (x w : Lean.Expr)
  /-- an argument of optional or union type (`times?: number`): split into its forms -/
  | arg (fv : FVarId)
  /-- the goal is a test's implication (`c = true → …`): its premise is introduced -/
  | intro
  /-- the goal is a conjunction of such implications (the loop rule's obligation for the two
  outcomes of the condition): split into its parts -/
  | conj

/-- A test's outcome: `b = true` or `b = false` for a Boolean `b` that is not a constructor, an
equation or comparison of naturals or integers, or the negation of one. -/
partial def isTestFact (p : Lean.Expr) : MetaM Bool := do
  let p := p.consumeMData
  if let some q := p.not? then return ← isTestFact q
  if let some (ty, l, r) := p.eq? then
    if ty.isConstOf ``Bool then
      return (r.isConstOf ``Bool.true || r.isConstOf ``Bool.false) && !(← isConstructorApp' l)
    return ty.isConstOf ``Nat || ty.isConstOf ``Int
  if p.isAppOfArity ``LT.lt 4 || p.isAppOfArity ``LE.le 4 then
    return (p.getArg! 0).isConstOf ``Nat || (p.getArg! 0).isConstOf ``Int
  return false

/-- The premise of `e` when it is a test's implication `p → …` (`isTestFact p`; the loop rule's
obligation for one outcome of the condition: `c = true → …`, or `i < n → …` once evaluated). -/
def testPremise? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  -- (the rest may use the premise's proof: `∀ h : i < xs.size, … xs[i] …`)
  let .forallE _ p _ _ := e.consumeMData | return none
  if p.hasLooseBVars || (p.find? (·.isAppOf ``JS.exec)).isSome then return none
  return if ← isTestFact p then some p else none

/-- The innermost discriminant of a `match` in `e` that is an undecided test: an `if`, an
optional value or Boolean that is not a constructor, or an answer of the external-call oracle.
Matches under binders are searched too
(`JS.NoPanic` and `JS.Returns` quantify over the outcome), but the discriminant must not depend on
the bound variables, and the run of a computation (`JS.exec …`) is not a test. Outer
discriminants are stuck only because of an inner one, so the innermost is chosen. -/
def findTest (e : Lean.Expr) : MetaM (Option AutoTest) := do
  -- (the loop rule's obligation `(c = false → …) ∧ (c = true → …)`, once `c` is evaluated)
  let e' := e.consumeMData
  if (← testPremise? e').isSome then return some .intro
  if e'.isAppOfArity ``And 2 then
    if (← testPremise? (e'.getArg! 0)).isSome || (← testPremise? (e'.getArg! 1)).isSome then
      return some .conj
  let found ← IO.mkRef (#[] : Array (Lean.Expr × AutoTest))
  -- `forEachExpr` enters binders with fresh local variables: a discriminant that mentions one
  -- depends on a bound variable
  let lctx ← getLCtx
  -- `if`s of the goal itself (`exec (if c then A else B) w` is `if c then exec A w else …`)
  let ites ← IO.mkRef (#[] : Array Lean.Expr)
  Meta.forEachExpr e fun sub => do
    if sub.hasLooseBVars then return
    let sub' := sub.consumeMData
    if sub'.isAppOfArity ``ite 5 && !(sub'.getArg! 1).hasAnyFVar (!lctx.contains ·) then
      ites.modify (·.push sub')
    let some app ← matchMatcherApp? sub | return
    for d in app.discrs do
      -- (elaborated terms carry `save_info` annotations)
      let d := (← instantiateMVars d).consumeMData
      if d.hasLooseBVars || d.hasAnyFVar (!lctx.contains ·) then continue
      if d.isAppOfArity ``JS.exec 4 then
        let m := (d.getArg! 2).consumeMData
        if m.isAppOf ``JS.materialize && m.getAppNumArgs == 3 && !(← isConstructorApp' m.appArg!) then
          found.modify (·.push (d, .mat ``exec_materialize_ok m.appArg! (d.getArg! 3)))
        else if m.isAppOf ``JS.materializeList && m.getAppNumArgs == 3 && !(← isConstructorApp' m.appArg!) then
          found.modify (·.push (d, .mat ``exec_materializeList_ok m.appArg! (d.getArg! 3)))
        continue
      if d.isAppOfArity ``ite 5 || d.isAppOfArity ``dite 5 then
        found.modify (·.push (d, .cond (d.getArg! 1)))
      else if (oracleArgs? d).isSome then
        found.modify (·.push (d, .oracle d))
      else if ← isConstructorApp' d then continue
      -- (a value computed by a run is stuck on the run, not a test)
      else if (d.find? (·.isAppOf ``JS.exec)).isNone then
        let ty ← whnfR (← inferType d)
        if ty.isAppOfArity ``Option 1 || ty.isConstOf ``Bool then found.modify (·.push (d, .val d))
        else if d.isFVar && ty.isAppOfArity ``Val 2 then
          let t ← whnfR (ty.getArg! 1)
          if t.isAppOf ``Ty.opt || t.isAppOf ``Ty.union then found.modify (·.push (d, .arg d.fvarId!))
  let cands ← found.get
  -- an `if` of the goal whose branches hold tests is split first (its cases have fewer tests:
  -- `n % 2 === 0` before the read `xs[n / 2 - 1]` of one branch); the outermost such `if`
  let inBranch (it d : Lean.Expr) : Bool :=
    ((it.getArg! 3).find? (· == d)).isSome || ((it.getArg! 4).find? (· == d)).isSome
  let guarding := (← ites.get).filter fun it => cands.any fun (d, _) => inBranch it d
  let outer := guarding.filter fun it => !guarding.any fun it' => it' != it && inBranch it' it
  if let some it := outer[0]? then return some (.cond (it.getArg! 1))
  let inner := cands.filter fun (d, _) =>
    !cands.any fun (d', _) => d' != d && (d.find? (· == d')).isSome
  return (if inner.isEmpty then cands[0]? else inner[0]?).map (·.2)

/-- Facts about array sizes and other naturals in a test's outcome, as `Nat` facts for `omega`
(`xs.length === 0` is `xs.size = 0`, `xs.length < 2` is `xs.size < 2`). -/
macro "ts_test_nat" h:ident : tactic => `(tactic|
  simp (disch := first | omega | (simp only [StrictTS.JSStr.length_slice, StrictTS.JSStr.relIndex_natCast',
    StrictTS.JSStr.relIndex_ofNat_lit, Nat.min_self]; omega)) only [StrictTS.numEq_ofNat, StrictTS.lt_ofNat, StrictTS.le_ofNat, StrictTS.F64.gt,
    StrictTS.F64.ge, StrictTS.F64.lit_eq_ofNat, StrictTS.floor_div_ofNat, StrictTS.rem_ofNat,
    StrictTS.ofNat_sub_ofNat, StrictTS.sortBy_length, StrictTS.Conv.relIndex_fin_zero,
    StrictTS.Conv.arrayIndex?_ofNat, StrictTS.Conv.toIntegerOrInf_ofNat, StrictTS.JSStr.at?_natCast, StrictTS.JSStr.at?_ofNat_lit,
    StrictTS.isInteger_ofNat_safe, StrictTS.Val.toStr, StrictTS.JSStr.length_slice, StrictTS.JSStr.relIndex_natCast',
    StrictTS.JSStr.relIndex_ofNat_lit, List.length_take, List.length_drop, List.drop_zero, Nat.sub_zero,
    Array.length_toList, Array.size_map, List.length_map, Nat.min_self, reduceCtorEq, Option.some.injEq,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false'] at $h:ident)

/-- The differences of safe naturals that `ts_test_nat` left (`xs.length - 1` when `xs` may be
empty) as integers, and their comparisons (`i < xs.length - 1` is `(i : Int) < xs.size - 1`). -/
macro "ts_test_int" h:ident : tactic => `(tactic|
  simp (disch := omega) only [StrictTS.ofNat_sub_ofNat_int, StrictTS.lt_ofNat_ofInt, StrictTS.le_ofNat_ofInt,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at $h:ident)

/-- A hypothesis `World.ExtReturns w f` (the library function `f` never answers with an error)
that covers the oracle query `q`, applied to the query's arguments. -/
def extReturnsFor (q : Lean.Expr) : MetaM (Option Lean.Expr) := do
  -- q = @World.ext TT w name args ret vs n
  let some (vs, n) := oracleArgs? q | return none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``World.ExtReturns 3 do continue
    let pf := mkApp2 d.toExpr vs n
    let ok ← try
        let pty ← whnfR (← inferType pf)
        -- `∃ ev, w.answer f vs n = .ok ev`: compare the answer with the query
        match pty.getAppFnArgs with
        | (``Exists, #[_, body]) =>
          let .lam _ _ b _ := body | pure false
          let some (_, lhs, _) := b.eq? | pure false
          withNewMCtxDepth (isDefEq lhs q)
        | _ => pure false
      catch _ => pure false
    if ok then return some pf
  return none

/-- Split the main goal on the oracle's answer `q`: an error or a value (only a value under a
hypothesis `World.ExtReturns`), then on the forms of the value (a plain value of each
constructor, or the elements of a fresh array); `h` holds the answer. -/
def splitOracle (q : Lean.Expr) (h : Ident) : TacticM Unit := withMainContext do
  let qS ← Term.exprToSyntax q
  let ev := mkIdent (h.getId.appendAfter "_ev")
  let x := mkIdent (h.getId.appendAfter "_x")
  let es := mkIdent (h.getId.appendAfter "_es")
  match ← extReturnsFor q with
  | some pf =>
    let pfS ← Term.exprToSyntax pf
    evalTactic (← `(tactic| obtain ⟨$ev, $h⟩ : ∃ ev, $qS = .ok ev := $pfS))
  | none =>
    evalTactic (← `(tactic| rcases $h:ident : $qS:term with _ | $ev:ident))
  -- (hypotheses `World.ExtSpec`: the forms of a value that the host guarantees)
  let specs ← withMainContext do
    let mut out : Array Name := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← whnfR (← instantiateMVars d.type)).isAppOf ``World.ExtSpec then out := out.push d.userName
    return out
  let mut rest : List MVarId := []
  for g in ← getGoals do
    setGoals [g]
    for sp in specs do
      try evalTactic (← `(tactic| (obtain ⟨_, hev⟩ := $(mkIdent sp) _ _ (by simp) $ev:ident $h:ident; subst hev)))
      catch _ => pure ()
    -- the value: a plain value `.val x` (each form of `x`), or the elements of a fresh array
    try evalTactic (← `(tactic| rcases $ev:ident with $x:ident | $es:ident)) catch _ => pure ()
    for g' in ← getGoals do
      setGoals [g']
      try evalTactic (← `(tactic| cases $x:ident)) catch _ => pure ()
      rest := rest ++ (← getGoals)
  setGoals rest

/-- Index and length arithmetic on safe naturals in the goal (`xs[xs.length - 1]`, `i + 1 < n`),
with side conditions from the context by `omega` (e.g. `xs.size ≠ 0` from a test's outcome). -/
macro "ts_nat_arith" : tactic => `(tactic|
  simp (disch := first | omega | (simp only [StrictTS.JSStr.length_slice, StrictTS.JSStr.relIndex_natCast',
    StrictTS.JSStr.relIndex_ofNat_lit, Nat.min_self]; omega)) only [StrictTS.ofNat_sub_ofNat, StrictTS.ofNat_add_one, StrictTS.lt_ofNat,
    StrictTS.le_ofNat, StrictTS.numEq_ofNat, StrictTS.Conv.arrayIndex?_ofNat, StrictTS.F64.lit_eq_ofNat,
    StrictTS.Conv.toIntegerOrInf_ofNat, StrictTS.JSStr.at?_natCast, StrictTS.JSStr.at?_ofNat_lit,
    StrictTS.isInteger_ofNat_safe, StrictTS.Val.toStr, StrictTS.JSStr.length_slice, StrictTS.JSStr.relIndex_natCast',
    StrictTS.JSStr.relIndex_ofNat_lit, StrictTS.Conv.arrayIndex?_ofInt, StrictTS.floor_div_ofNat, StrictTS.rem_ofNat, StrictTS.sortBy_length, StrictTS.Conv.relIndex_fin_zero,
    List.length_take, List.length_drop, List.drop_zero, Nat.sub_zero, Array.length_toList, Array.size_map,
    List.length_map, Nat.min_self, decide_eq_true_eq, decide_eq_false_iff_not])

theorem bool_fact_ne {x b : Bool} (h : ¬ x = !b) : x = b := by cases x <;> cases b <;> simp_all
theorem bool_contra {x b : Bool} (h1 : x = b) (h2 : x = !b) : False := by cases b <;> simp_all

/-- `(e, b, proof of e = b)` when the hypothesis `pf : t` says that the Boolean `e` is `b`
(`e = b` or `¬ e = !b`). -/
def boolFact? (t pf : Lean.Expr) : Option (Lean.Expr × Bool × Lean.Expr) :=
  let lit (r : Lean.Expr) : Option Bool :=
    if r.isConstOf ``Bool.true then some true else if r.isConstOf ``Bool.false then some false else none
  match t.consumeMData.eq? with
  | some (_, l, r) => (lit r.consumeMData).map fun b => (l, b, pf)
  | none =>
    match t.consumeMData.not? >>= (·.consumeMData.eq?) with
    | some (_, l, r) => (lit r.consumeMData).map fun b =>
      (l, !b, mkApp3 (mkConst ``bool_fact_ne) l (toExpr !b) pf)
    | none => none

/-- Close the main goal if the hypothesis `h` (a test's outcome) contradicts another hypothesis
up to unfolding: a Boolean that the two give different values (`k.lt 0 = true` against a
precondition `hk : k.lt 0 = false`; `(xs.any fun a => (match a with | .num x => x).lt 0) = true`
against `(xs.any fun x => x.toNum.lt 0) = false`), or a proposition and its negation. -/
def closeByContradiction (h : Name) : TacticM Bool := withMainContext do
  let some hd := (← getLCtx).findFromUserName? h | return false
  let ht ← instantiateMVars hd.type
  let goal ← getMainGoal
  let close (pf : Lean.Expr) : TacticM Bool := do
    goal.assign (← mkFalseElim (← goal.getType) pf)
    replaceMainGoal []
    return true
  for d in ← getLCtx do
    if d.isImplementationDetail || d.fvarId == hd.fvarId then continue
    let dt ← instantiateMVars d.type
    match boolFact? ht hd.toExpr, boolFact? dt d.toExpr with
    | some (l, b, p), some (l', b', p') =>
      if b != b' && l.consumeMData.getAppFn == l'.consumeMData.getAppFn then
        if ← withNewMCtxDepth (isDefEq l l') then
          return ← close (mkApp4 (mkConst ``bool_contra) l (toExpr b) p p')
    | _, _ =>
      let same (p q : Lean.Expr) : MetaM Bool := do
        if p.consumeMData.getAppFn != q.consumeMData.getAppFn then return false
        withNewMCtxDepth (isDefEq p q)
      if let some q := dt.consumeMData.not? then
        if ← same q ht then return ← close (mkApp d.toExpr hd.toExpr)
      if let some q := ht.consumeMData.not? then
        if ← same q dt then return ← close (mkApp hd.toExpr d.toExpr)
  return false

/-- Split the main goal on the test `t` (the hypothesis `h` holds the case) and evaluate each
case with it and the heap hypotheses. A case that contradicts the hypotheses (the statement's
precondition) is closed: by `omega` on the test's `Nat` facts (`xs.length === 0` against
`xs.size ≠ 0`), by a hypothesis that gives the test the other value (`k < 0` against
`hk : k.lt 0 = false`), or by `simp` (`Number.isNaN(t)` against `t ≠ .nan`). -/
def splitOnTest (t : AutoTest) (h : Ident) (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM Unit := do
  withMainContext do
    match t with
    | .cond c => evalTactic (← `(tactic| by_cases $h:ident : $(← Term.exprToSyntax c)))
    | .val d => evalTactic (← `(tactic| rcases $h:ident : $(← Term.exprToSyntax d) with _ | _))
    | .oracle q => splitOracle q h
    | .mat lem x w =>
      -- (the world after it: the same but for the heap and the next address)
      let v := mkIdent (h.getId.appendAfter "_v")
      let hh := mkIdent (h.getId.appendAfter "_heap")
      let nn := mkIdent (h.getId.appendAfter "_next")
      evalTactic (← `(tactic| obtain ⟨$v, $hh, $nn, $h⟩ := $(mkIdent lem) $(← Term.exprToSyntax x)
        $(← Term.exprToSyntax w)))
    | .arg fv =>
      let gs ← (← getMainGoal).cases fv
      replaceMainGoal (gs.toList.map (·.mvarId))
    | .intro => evalTactic (← `(tactic| intro $h:ident))
    | .conj => evalTactic (← `(tactic| constructor))
  let hn := mkIdent (h.getId.appendAfter "_nat")
  let mut rest : List MVarId := []
  for g in ← getGoals do
    setGoals [g]
    -- (a split argument has no case hypothesis)
    let hasH ← withMainContext do return ((← getLCtx).findFromUserName? h.getId).isSome
    let hS ← `(Lean.Parser.Tactic.simpLemma| $h:ident)
    let ls := lemmas ++ (← heapHyps) ++ (if hasH then #[hS] else #[])
    tsProf "split: case simp" <| try evalTactic (← `(tactic| simp only [ts_sym, ↓reduceIte, ite_true, ite_false,
      not_false_eq_true, ne_eq, reduceCtorEq, $ls,*])) catch _ => pure ()
    unless (← getGoals).isEmpty do
      let nat ← `(tactic| first | (ts_test_nat $hn; try ts_test_int $hn) | ts_test_int $hn)
      tsProf "split: test Nat facts" <|
        try evalTactic (← `(tactic| (have $hn:ident := $h:ident; $nat))) catch _ => pure ()
    -- the earlier tests' facts again, with this one (`xs[n / 2 - 1]` is an index once `n` is even)
    unless (← getGoals).isEmpty do
      let older ← withMainContext do
        return (← getLCtx).foldl (init := #[]) fun acc d =>
          let n := d.userName.eraseMacroScopes.toString
          if n.startsWith "htest" && n.endsWith "_nat" && d.userName != hn.getId then acc.push d.userName
          else acc
      for o in older do
        unless (← getGoals).isEmpty do
          tsProf "split: older Nat facts" do
            try evalTactic (← `(tactic| ts_test_nat $(mkIdent o):ident)) catch _ => pure ()
            try evalTactic (← `(tactic| ts_test_int $(mkIdent o):ident)) catch _ => pure ()
    unless (← getGoals).isEmpty do
      tsProf "split: omega" <| try evalTactic (← `(tactic| (exfalso; omega))) catch _ => pure ()
    unless (← getGoals).isEmpty do
      try discard <| closeByContradiction h.getId catch _ => pure ()
    unless (← getGoals).isEmpty do
      try evalTactic (← `(tactic| (simp only [*, StrictTS.isNaN_eq_true_iff, reduceCtorEq, Bool.false_eq_true,
        Bool.true_eq_false, not_true_eq_false, not_false_eq_true] at $h:ident; done))) catch _ => pure ()
    -- index arithmetic that the case decides (`xs[xs.length - 1]` once `xs.size ≠ 0`)
    unless (← getGoals).isEmpty do
      tsProf "split: nat arith" <| try evalTactic (← `(tactic| ts_nat_arith)) catch _ => pure ()
    rest := rest ++ (← getGoals)
  setGoals rest

/-- Summarize loops and callbacks on the main goal until none is left; whether one was. -/
def summarizeAll (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (unfolded : IO.Ref (Array Name)) :
    TacticM Bool := do
  let mut any := false
  let summ ← if lemmas.isEmpty then `(tactic| ts_summarize) else `(tactic| ts_summarize [$lemmas,*])
  let cbs ← if lemmas.isEmpty then `(tactic| ts_callbacks) else `(tactic| ts_callbacks [$lemmas,*])
  -- (`ts_auto.profile`: the time of failed attempts)
  let attempt (name : String) (tac : TSyntax `tactic) : TacticM Bool := do
    let (t0, h0) := (← IO.monoMsNow, ← IO.getNumHeartbeats)
    try tsProf name (evalTactic tac); pure true
    catch _ => tsProfNote s!"(discarded) {name}, failed" t0 h0; pure false
  -- (`ts_summarize` fails without a loop in the goal, after computing the facts that tell the
  -- cells apart: not tried then)
  let hasLoop : TacticM Bool := withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    let loops := #[``evalForOf, ``evalLoop, ``evalForOfStr, ``evalForOfMap, ``evalForOfSet]
    return (goal.find? fun e => e.isAppOfArity ``JS.exec 4 && loops.any (e.getArg! 2).isAppOf).isSome
  for _ in [0:16] do
    if (← getGoals).isEmpty then return any
    let progress ← (hasLoop <&&> attempt "2 ts_summarize" summ) <||> attempt "2 ts_callbacks" cbs
    -- a call that a summary exposed (its argument is the summarized value, once evaluated into
    -- the code after it): unfold it once
    let progress ← if progress then pure true else tsProf "2 simp, unfold a call" do
      let saved ← saveState
      let ls := lemmas ++ (← heapHyps)
      try evalTactic (← `(tactic| simp only [ts_sym, $ls,*])) catch _ => pure ()
      if (← getGoals).isEmpty then return true
      match ← unfoldOneCall (← unfolded.get) with
      | some r => unfolded.modify (·.push r); pure true
      | none => saved.restore; pure false
    unless progress do break
    any := true
  return any

/-- Split every environment variable of the main goal into its slots (`Env.cons v rest`, for a
context that is a list literal). -/
def splitEnvs : TacticM Unit := do
  for _ in [0:64] do
    let some fv ← withMainContext do
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let ty ← whnfR (← instantiateMVars d.type)
          if ty.isAppOfArity ``Env 2 then
            -- (contexts are often `[s, …] ++ Γ`)
            let ctx ← whnf (ty.getArg! 1)
            if ctx.isAppOf ``List.cons || ctx.isAppOf ``List.nil then return some d.fvarId
        return none
      | return
    let gs ← (← getMainGoal).cases fv
    replaceMainGoal (gs.toList.map (·.mvarId))

/-- The keys `(k, a)` of the cells written by a chain of `insert`s (outermost first). -/
partial def insertedKeys (h : Lean.Expr) : Array Lean.Expr :=
  let h := h.consumeMData
  if h.isAppOf ``Std.ExtDHashMap.insert && h.getAppNumArgs ≥ 3 then
    let n := h.getAppNumArgs
    #[h.getArg! (n - 2)] ++ insertedKeys (h.getArg! (n - 3))
  else #[]

/-- Split the conjunctions among the hypotheses of the main goal into their parts. -/
def splitAnds : TacticM Unit := do
  for _ in [0:64] do
    let some fv ← withMainContext do
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if (← whnfR (← instantiateMVars d.type)).isAppOfArity ``And 2 then return some d.fvarId
        return none
      | return
    let gs ← (← getMainGoal).cases fv
    replaceMainGoal (gs.toList.map (·.mvarId))

/-- The elements of the list `l` (after `whnf`), if it is a list literal. -/
partial def listElems (l : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let l ← whnf l
  if l.isAppOfArity ``List.cons 3 then
    return (← listElems l.appArg!).map (#[l.appFn!.appArg!] ++ ·)
  if l.isAppOfArity ``List.nil 1 then return some #[]
  return none

/-- The values of the environment `e` (after `whnfR`), if it is a chain of `Env.cons`. -/
partial def envElems (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let e ← whnfR e
  if e.isAppOfArity ``Env.cons 5 then
    return (← envElems e.appArg!).map (#[e.appFn!.appArg!] ++ ·)
  if e.isAppOfArity ``Env.nil 1 then return some #[]
  return none

/-- The position of the variable `v` (`Var.here.there…` or `MVar.here.there…`) in its context. -/
partial def varIndex (v : Lean.Expr) : Option Nat :=
  let v := v.consumeMData
  if v.isAppOf ``Var.here || v.isAppOf ``MVar.here then some 0
  else if v.isAppOf ``Var.there || v.isAppOf ``MVar.there then (varIndex v.appArg!).map (· + 1)
  else none

/-- The subterms of `e` that satisfy `p` (no binders are entered: IR terms have none). -/
partial def collectSubterms (p : Lean.Expr → Bool) (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  let acc := if p e then acc.push e else acc
  match e with
  | .app f a => collectSubterms p a (collectSubterms p f acc)
  | .mdata _ b => collectSubterms p b acc
  | _ => acc

/-- The positions in a loop's context of `n` slots of the variables that the subterms `subs` refer
to: each subterm has its context as argument 1 and its variable as argument `i` (the context there
is the loop's, extended by the declarations around the subterm). -/
def loopSlotsOf (n i : Nat) (subs : Array Lean.Expr) : MetaM (Array Nat) := do
  let mut out := #[]
  for a in subs do
    let some Δ ← listElems (a.getArg! 1) | continue
    let some k := varIndex (a.getArg! i) | continue
    let d := Δ.size - n
    if d ≤ k && !out.contains (k - d) then out := out.push (k - d)
  return out

/-- The candidate about one slot of a loop (`Env.slotsOk`): the mode, and for a down counter
(mode `3`) its start `a - c` (naturals; `c = 0` for a start `a`), whose integer value bounds it. -/
structure SlotCand where
  mode : Nat
  start : Option (Lean.Expr × Lean.Expr) := none
  deriving Inhabited

instance : ToString SlotCand := ⟨fun c => toString c.mode⟩

/-- Candidate modes for the slots of the loop `evalLoop I P c body step env` (`Env.slotsOk`):
`1` (kept) for a mutable slot that no assignment in the body or the step writes; `2` (a safe
natural) for a written `number` slot that starts at a natural-number literal and that the
condition reads (a counter); `3` (an integer between `-1` and its start) for such a slot that
starts at `a` or `a - c` with naturals `a`, `c` (a counter running down from `xs.length - 1`);
`0` otherwise. -/
def loopCandidates (loop : Lean.Expr) : MetaM (List SlotCand) := do
  let some slots ← listElems (loop.getArg! 3) | return []
  let some inits ← envElems (loop.getArg! 8) | return []
  let n := slots.size
  let isAssign (e : Lean.Expr) := e.isAppOfArity ``Stmt.assign 6
  let written ← loopSlotsOf n 4
    (collectSubterms isAssign (loop.getArg! 6) ++ collectSubterms isAssign (loop.getArg! 7))
  let read ← loopSlotsOf n 3 (collectSubterms (·.isAppOfArity ``Expr.var 4) (loop.getArg! 5))
  let mut ms := #[]
  for (s, p) in slots.zipIdx do
    let s ← whnf s
    unless s.isAppOfArity ``Slot.mk 2 do
      ms := ms.push {mode := 0}
      continue
    let mutable := (← whnf (s.getArg! 1)).isConstOf ``Bool.true
    let num := (← whnf (s.getArg! 0)).isConstOf ``Ty.num
    -- (`.num (F64.ofNat k)` or `.num k` with a literal `k < 2 ^ 53`)
    let natLit (x : Lean.Expr) : Option Nat :=
      if x.isAppOfArity ``F64.ofNat 1 then x.appArg!.nat? <|> x.appArg!.rawNatLit?
      else if x.isAppOfArity ``OfNat.ofNat 3 then (x.getArg! 1).rawNatLit? <|> (x.getArg! 1).nat?
      else none
    let natInit := match inits[p]? with
      | some v =>
        let v := v.consumeMData
        v.isAppOfArity ``Val.num 2 &&
          (match natLit v.appArg!.consumeMData with | some k => k < 2 ^ 53 | none => false)
      | none => false
    -- (`.num (F64.ofNat a - F64.ofNat c)` or `.num (F64.ofNat a)`)
    let downStart : Option (Lean.Expr × Lean.Expr) := match inits[p]? with
      | some v =>
        let v := v.consumeMData
        if !v.isAppOfArity ``Val.num 2 then none else
        let x := v.appArg!.consumeMData
        let nat? (y : Lean.Expr) : Option Lean.Expr :=
          let y := y.consumeMData
          if y.isAppOfArity ``F64.ofNat 1 then some y.appArg!
          else if y.isAppOfArity ``OfNat.ofNat 3 then some (mkNatLit ((y.getArg! 1).rawNatLit?.getD 0))
          else none
        if x.isAppOfArity ``HSub.hSub 6 then
          match nat? (x.getArg! 4), nat? (x.getArg! 5) with
          | some a, some c => some (a, c)
          | _, _ => none
        else (nat? x).map (·, mkNatLit 0)
      | none => none
    ms := ms.push <| if !mutable then {mode := 0} else if !written.contains p then {mode := 1}
      else if num && natInit && read.contains p then {mode := 2}
      else if num && read.contains p && downStart.isSome then {mode := 3, start := downStart}
      else {mode := 0}
  return ms.toList

/-- Open the candidate facts among the hypotheses of the main goal: `KeptAt p v v₀` becomes
`v = v₀` (substituted), `NatAt p v` gives `v = .num (F64.ofNat k)` (substituted) and
`k < 2 ^ 53`. -/
def openSlotFacts : TacticM Unit := do
  let h := mkIdent `hslot
  for _ in [0:64] do
    -- (kind: 0 kept, 1 a safe natural, 2 an integer between -1 and a bound)
    let some (fv, kind, v) ← withMainContext do
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let t := (← instantiateMVars d.type).consumeMData
          if t.isAppOfArity ``KeptAt 5 then return some (d.fvarId, 0, t.getArg! 3)
          if t.isAppOfArity ``NatAt 4 then return some (d.fvarId, 1, (t.getArg! 3).consumeMData)
          if t.isAppOfArity ``IntLeAt 5 then return some (d.fvarId, 2, (t.getArg! 3).consumeMData)
        return none
      | return
    if kind != 0 && v.isFVar then
      -- (a `number` slot's value is `.num x`)
      let gs ← (← getMainGoal).cases v.fvarId!
      replaceMainGoal (gs.toList.map (·.mvarId))
      continue
    replaceMainGoal [← (← getMainGoal).rename fv `hslot]
    if kind == 0 then
      evalTactic (← `(tactic| rw [StrictTS.keptAt_iff] at $h:ident))
    else if kind == 1 then
      evalTactic (← `(tactic| (rw [StrictTS.natAt_num_iff] at $h:ident; obtain ⟨_, $h:ident, _⟩ := $h:ident)))
    else
      evalTactic (← `(tactic| rw [StrictTS.intLeAt_num_iff] at $h:ident))
      evalTactic (← `(tactic| obtain ⟨_, $h:ident, _, _, _⟩ := $h:ident))
    -- (the equation stays when neither side is a variable)
    try evalTactic (← `(tactic| subst $h:ident)) catch _ =>
      replaceMainGoal [← (← getMainGoal).rename (← withMainContext do
        return ((← getLCtx).findFromUserName? `hslot).get!.fvarId) `hslot_eq]

/-- The slot that the goal `g` names, if it is a candidate fact (`KeptAt p …`, `NatAt p …`). -/
def slotFact? (g : MVarId) : MetaM (Option Nat) := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.isAppOfArity ``KeptAt 5 || t.isAppOfArity ``NatAt 4 || t.isAppOfArity ``IntLeAt 5 then
    return ← (evalNat (t.getArg! 1)).run
  return none

/-- Whether the goal `g` mentions a candidate fact (a case whose obligation may fail only on a
candidate: `finishTsAuto` goes on with the other cases, so that all failing candidates show). -/
def mentionsSlotFact (g : MVarId) : MetaM Bool := do
  return ((← instantiateMVars (← g.getType)).find? fun e =>
    e.isConstOf ``KeptAt || e.isConstOf ``NatAt || e.isConstOf ``IntLeAt).isSome

/-- Close the candidate fact of the main goal: a kept value that is the same, or a safe natural
that is a literal, sum or difference of safe naturals within the bound (`omega` on the context's
facts, e.g. `i < s.length` from the condition and `s.length < 2 ^ 53`). -/
def closeSlotFact : TacticM Unit := do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  if t.isAppOfArity ``KeptAt 5 then
    evalTactic (← `(tactic| (rw [StrictTS.keptAt_iff]; first | rfl | (simp_all; done))))
    return
  if t.isAppOfArity ``IntLeAt 5 then
    let v := (t.getArg! 3).consumeMData
    let x := if v.isAppOfArity ``Val.num 2 then v.appArg!.consumeMData else v
    if x.isAppOfArity ``F64.ofInt 1 then
      evalTactic (← `(tactic| exact StrictTS.intLeAt_ofInt _ (by omega) (by omega) (by omega)))
    else if x.isAppOfArity ``HSub.hSub 6 && (x.getArg! 4).consumeMData.isAppOfArity ``F64.ofInt 1 then
      evalTactic (← `(tactic| exact StrictTS.intLeAt_ofInt_sub_ofNat _ (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)))
    else if x.isAppOfArity ``HSub.hSub 6 then
      evalTactic (← `(tactic| exact StrictTS.intLeAt_ofNat_sub_ofNat _ (by omega) (by omega) (by omega)
        (by omega) (by omega)))
    else if x.isAppOfArity ``F64.ofNat 1 then
      evalTactic (← `(tactic| exact StrictTS.intLeAt_ofNat _ (by omega) (by omega)))
    else throwError "ts_auto: not a counter's value"
    return
  unless t.isAppOfArity ``NatAt 4 do throwError "ts_auto: not a candidate fact"
  let v := (t.getArg! 3).consumeMData
  let x := if v.isAppOfArity ``Val.num 2 then v.appArg!.consumeMData else v
  if x.isAppOfArity ``F64.ofNat 1 then
    evalTactic (← `(tactic| exact StrictTS.natAt_ofNat _ (by omega)))
  else if x.isAppOfArity ``HAdd.hAdd 6 then
    evalTactic (← `(tactic| exact StrictTS.natAt_add_ofNat _ (by omega)))
  else if x.isAppOfArity ``HSub.hSub 6 then
    evalTactic (← `(tactic| exact StrictTS.natAt_sub_ofNat _ (by omega) (by omega)))
  else throwError "ts_auto: not a safe natural"

/-- The step of `loopFallback`, without backtracking (`e` = the loop's run `JS.exec (evalLoop …) W`;
`finish` closes one iteration's obligation; `modes` = the candidates about the loop's slots, as
in `Env.slotsOk`). The slots of the candidates that an iteration does not keep (empty: the
loop is done, and the goals are its exits); an error when an iteration may panic or change the
world. -/
def loopFallbackCore (e : Lean.Expr) (finish : TacticM Unit) (throws : Bool) (cell : Option Lean.Expr)
    (modes : List SlotCand) (writes : IO.Ref Bool) : TacticM (Array Nat) := do
  let loop := (e.getArg! 2).consumeMData
  let stx (x : Lean.Expr) : TacticM Term := withMainContext (Term.exprToSyntax x)
  let I ← stx (loop.getArg! 1)
  let P ← stx (loop.getArg! 2)
  let c ← stx (loop.getArg! 5)
  let body ← stx (loop.getArg! 6)
  let step ← stx (loop.getArg! 7)
  let env ← stx (loop.getArg! 8)
  let W ← stx (e.getArg! 3)
  let ms ← `([$(← modes.toArray.mapM fun m => do
      let k := Syntax.mkNumLit (toString m.mode)
      match m.start with
      | some (a, c) => `(($k, (($(← stx a) : Nat) : Int) - (($(← stx c) : Nat) : Int)))
      | none => `(($k, (0 : Int)))),*])
  let hl := mkIdent `hloop
  -- (a named hole is one metavariable per declaration: a fresh name for each loop)
  let hsName ← mkFreshUserName `hstep
  let hsI := mkIdent hsName
  -- `while (true)` ends only by `return` or `throw`
  let cnd := (loop.getArg! 5).consumeMData
  let litTrue := cnd.isAppOf ``Expr.lit && cnd.appArg!.consumeMData.isAppOf ``Lit.bool &&
    cnd.appArg!.consumeMData.appArg!.isConstOf ``Bool.true
  let normalOk := !litTrue
  let nS ← if normalOk then `(Bool.true) else `(Bool.false)
  let eS ← if throws then `(Bool.true) else `(Bool.false)
  -- the state: the world unchanged, or (`cell = some K`) unchanged but for the content of `K`
  let hiName ← mkFreshUserName `hinit
  let hiI := mkIdent hiName
  -- (the `const` slots keep their values: references the body reads stay valid; the candidates
  -- hold)
  match cell with
  | none =>
    evalTactic (← `(tactic| have $hl := StrictTS.evalLoop_cases_exit $I $P $c $body $step
      (fun e w' => StrictTS.Env.slotsOk 0 $ms e $env ∧ w' = $W)
      (fun cmp e w' => StrictTS.Env.slotsOk 0 $ms e $env ∧ (cmp.isNormal = true → w' = $W) ∧
        cmp.exitOk $nS $eS = true) ?$hsI $env $W ?$hiI))
  | some K =>
    let KS ← stx K
    evalTactic (← `(tactic| have $hl := StrictTS.evalLoop_cases_exit $I $P $c $body $step
      (fun e w' => StrictTS.Env.slotsOk 0 $ms e $env ∧
        ∃ c, w' = { $W with heap := Std.ExtDHashMap.insert (World.heap $W) $KS c })
      (fun cmp e w' => StrictTS.Env.slotsOk 0 $ms e $env ∧
        (cmp.isNormal = true → ∃ c, w' = { $W with heap := Std.ExtDHashMap.insert (World.heap $W) $KS c }) ∧
        cmp.exitOk $nS $eS = true) ?$hsI $env $W ?$hiI))
  let gls ← getGoals
  let some hs ← gls.findM? (fun g => return (← g.getTag) == hsName) | throwError "ts_auto: no step goal"
  let hi? ← gls.findM? (fun g => return (← g.getTag) == hiName)
  if let some hi := hi? then
    -- the start: the same `const` values, the candidates (kept values; counters at literals), and
    -- the cell exists (`W` is `W` with the cell rewritten with its own content)
    setGoals [hi]
    if cell.isSome then
      evalTactic (← `(tactic| refine ⟨?_, ⟨_, StrictTS.World.eq_insert_getD _ _ (StrictTS.HKind.dflt _)
          (by simp (disch := first | decide | omega) [ts_sym, *])⟩⟩))
    else
      evalTactic (← `(tactic| refine ⟨?_, rfl⟩))
    -- (a down counter's start: by arithmetic)
    evalTactic (← `(tactic| simp [StrictTS.Env.slotsOk_cons, StrictTS.natAt_ofNat]))
    for g in ← getGoals do
      setGoals [g]
      closeSlotFact
  let main := gls.filter (fun g => g != hs && some g != hi?)
  -- the run: divergence (closed for a partial-correctness goal; checked first, it is cheap) or
  -- an exit in the same world
  setGoals main
  let cmp := mkIdent `cmp
  let env' := mkIdent `env'
  let hfx := mkIdent `hexit
  let hw := mkIdent `hw'
  -- (a quoted `rfl` pattern would be hygienic, so `subst`)
  let hk := mkIdent `hconst
  evalTactic (← `(tactic| rcases $hl:ident with $hl:ident | ⟨$cmp:ident, $env':ident, _, $hl:ident, $hk:ident, $hw:ident, $hfx:ident⟩))
  let gls ← getGoals
  setGoals [gls.head!]
  evalTactic (← `(tactic| (simp only [$hl:ident]; simp; done)))
  setGoals gls.tail!
  evalTactic (← `(tactic| rw [$hl:ident]))
  evalTactic (← `(tactic| rcases $cmp:ident with _ | _ | _ | _ | _ | _ <;> simp only [Completion.exitOk_normal,
    Completion.exitOk_ret, Completion.exitOk_exc, Completion.exitOk_brk, Completion.exitOk_cont,
    Completion.exitOk_retP, Bool.false_eq_true] at $hfx:ident))
  -- the environment after the loop: its `const` slots as before, the candidates; the world: the
  -- state's after a normal exit (after `return`/`throw` the function leaves, in any world)
  let mut exits : List MVarId := []
  for g in ← getGoals do
    setGoals [g]
    try evalTactic (← `(tactic| simp only [Completion.isNormal_normal, Completion.isNormal_ret,
      Completion.isNormal_exc, Completion.isNormal_brk, Completion.isNormal_cont, Completion.isNormal_retP,
      Bool.false_eq_true, false_implies, forall_const, true_implies] at $hw:ident)) catch _ => pure ()
    if cell.isSome then
      try evalTactic (← `(tactic| (obtain ⟨_, $hw:ident⟩ := $hw:ident; subst $hw:ident))) catch _ => pure ()
    else
      try evalTactic (← `(tactic| subst $hw:ident)) catch _ => pure ()
    splitEnvs
    try
      evalTactic (← `(tactic| simp [StrictTS.Env.slotsOk_cons] at $hk:ident))
      splitAnds
      evalTactic (← `(tactic| subst_vars))
    catch _ => pure ()
    try openSlotFacts catch _ => pure ()
    exits := exits ++ (← getGoals)
  -- one iteration from every environment: no panic, the world unchanged (but for the cell), the
  -- candidates kept
  setGoals [hs]
  let hcI := mkIdent `hconsts
  let hwI := mkIdent `hworld
  if cell.isSome then
    evalTactic (← `(tactic| (intro env w' ⟨$hcI:ident, _, $hwI:ident⟩; subst $hwI:ident)))
  else
    evalTactic (← `(tactic| (intro env w' ⟨$hcI:ident, $hwI:ident⟩; subst $hwI:ident)))
  splitEnvs
  -- (the `const` slots: their values at the loop; the candidates: kept values, counters
  -- `F64.ofNat k` with `k < 2 ^ 53`)
  try
    evalTactic (← `(tactic| simp [StrictTS.Env.slotsOk_cons] at $hcI:ident))
    splitAnds
    evalTactic (← `(tactic| subst_vars))
  catch _ => pure ()
  try openSlotFacts catch _ => pure ()
  evalTactic (← `(tactic| all_goals ts_destruct))
  let mut failing : Array Nat := #[]
  for g in ← getGoals do
    setGoals [g]
    finish
    -- (the written cell's new content is the witness: `∃ c, h.insert K c' = h.insert K c`)
    unless (← getGoals).isEmpty do
      try evalTactic (← `(tactic| all_goals (repeat' first | exact ⟨_, rfl⟩ | (simp_all; done) | intro _ |
        apply And.intro)))
      catch _ => pure ()
    -- what is left: candidate facts, closed by arithmetic or failing
    for g' in ← getGoals do
      let some p ← slotFact? g' | do
        trace[ts_auto.inv] "an iteration's obligation stays open:{indentD (MessageData.ofGoal g')}"
        -- (a world that a write changed: `writes`)
        let t ← instantiateMVars (← g'.getType)
        if (t.find? (·.isAppOf ``Std.ExtDHashMap.insert)).isSome || (t.isAppOfArity ``Eq 3 &&
            ((t.getArg! 0).isAppOf ``World || (t.getArg! 0).isAppOf ``Std.ExtDHashMap)) then
          writes.set true
        throwError "ts_auto: an iteration may panic or change the world"
      setGoals [g']
      try closeSlotFact catch _ => unless failing.contains p do failing := failing.push p
  setGoals exits
  return failing

/-- The fallback for a `for (const x of arr)` loop that no summary handles (`e` = its run
`JS.exec (evalForOf I P a i body env) W`; `evalForOf_cases_exit`): the state keeps the `const`
slots and the world but for the external-call counter (an iteration may call the host); an
iteration may leave by `return`, `break` or an exception (e.g. thrown by the host), never by a
panic. -/
def forOfFallbackCore (e : Lean.Expr) (finish : TacticM Unit) : TacticM Unit := do
  let loop := (e.getArg! 2).consumeMData
  let stx (x : Lean.Expr) : TacticM Term := withMainContext (Term.exprToSyntax x)
  let I ← stx (loop.getArg! 1)
  let P ← stx (loop.getArg! 2)
  let a ← stx (loop.getArg! 6)
  let i ← stx (loop.getArg! 7)
  let body ← stx (loop.getArg! 8)
  let env ← stx (loop.getArg! 9)
  let W ← stx (e.getArg! 3)
  let hl := mkIdent `hloop
  let hsName ← mkFreshUserName `hstep
  let hiName ← mkFreshUserName `hinit
  let (hsI, hiI) := (mkIdent hsName, mkIdent hiName)
  evalTactic (← `(tactic| have $hl := StrictTS.evalForOf_cases_exit $I $P $a $body
    (fun _ e w' => StrictTS.Env.slotsOk 0 [] e $env ∧ ∃ k, w' = { $W with extIdx := k })
    (fun r w' => match r with
      | .ok (cmp, e) => StrictTS.Env.slotsOk 0 [] e $env ∧
          (cmp.isNormal = true → ∃ k, w' = { $W with extIdx := k }) ∧ cmp.exitOk true true = true
      | .error (.thrown _) => True
      | .error (.panic _) => False) ?$hsI $i $env $W ?$hiI))
  let gls ← getGoals
  let some hs ← gls.findM? (fun g => return (← g.getTag) == hsName) | throwError "ts_auto: no step goal"
  let hi? ← gls.findM? (fun g => return (← g.getTag) == hiName)
  if let some hi := hi? then
    setGoals [hi]
    evalTactic (← `(tactic| exact ⟨by simp, _, rfl⟩))
  let main := gls.filter (fun g => g != hs && some g != hi?)
  setGoals main
  let (r, w', hx) := (mkIdent `r, mkIdent `w', mkIdent `hexit)
  evalTactic (← `(tactic| rcases $hl:ident with $hl:ident | ⟨$r:ident, $w':ident, $hl:ident, $hx:ident⟩))
  let gls ← getGoals
  setGoals [gls.head!]
  evalTactic (← `(tactic| (simp only [$hl:ident]; simp; done)))
  setGoals gls.tail!
  evalTactic (← `(tactic| rw [$hl:ident]))
  -- the outcomes: an exception (the run goes on with it), a panic (excluded), a completion
  let (ex, cmp, env', hw, hk, hfx) := (mkIdent `ex, mkIdent `cmp, mkIdent `env', mkIdent `hw', mkIdent `hconst,
    mkIdent `hok)
  evalTactic (← `(tactic| rcases $r:ident with $ex:ident | ⟨$cmp:ident, $env':ident⟩))
  let mut exits : List MVarId := []
  for g in ← getGoals do
    setGoals [g]
    try evalTactic (← `(tactic| rcases $ex:ident with _ | _ <;> simp only at $hx:ident)) catch _ => pure ()
    try
      evalTactic (← `(tactic| obtain ⟨$hk:ident, $hw:ident, $hfx:ident⟩ := $hx:ident))
      evalTactic (← `(tactic| rcases $cmp:ident with _ | _ | _ | _ | _ | _ <;> simp only [Completion.exitOk_normal,
        Completion.exitOk_ret, Completion.exitOk_exc, Completion.exitOk_brk, Completion.exitOk_cont,
        Completion.exitOk_retP, Bool.false_eq_true, Completion.isNormal_normal, Completion.isNormal_ret,
        Completion.isNormal_exc, Completion.isNormal_brk, Completion.isNormal_cont, Completion.isNormal_retP,
        false_implies, true_implies] at $hfx:ident $hw:ident))
    catch _ => pure ()
    for g' in ← getGoals do
      setGoals [g']
      try evalTactic (← `(tactic| (obtain ⟨_, $hw:ident⟩ := $hw:ident; subst $hw:ident))) catch _ => pure ()
      splitEnvs
      try
        evalTactic (← `(tactic| simp [StrictTS.Env.slotsOk_cons] at $hk:ident))
        splitAnds
        evalTactic (← `(tactic| subst_vars))
      catch _ => pure ()
      exits := exits ++ (← getGoals)
  -- one iteration from every state: no panic, the state again (or an exit)
  setGoals [hs]
  let (hcI, hwI) := (mkIdent `hconsts, mkIdent `hworld)
  evalTactic (← `(tactic| (intro _ env w' ⟨$hcI:ident, _, $hwI:ident⟩; subst $hwI:ident)))
  splitEnvs
  try
    evalTactic (← `(tactic| simp [StrictTS.Env.slotsOk_cons] at $hcI:ident))
    splitAnds
    evalTactic (← `(tactic| subst_vars))
  catch _ => pure ()
  evalTactic (← `(tactic| all_goals ts_destruct))
  for g in ← getGoals do
    setGoals [g]
    finish
    unless (← getGoals).isEmpty do
      try evalTactic (← `(tactic| all_goals (repeat' first | exact ⟨_, rfl⟩ | (simp_all; done) | intro _ |
        apply And.intro)))
      catch _ => pure ()
    for g' in ← getGoals do
      trace[ts_auto.inv] "a for … of iteration's obligation stays open:{indentD (MessageData.ofGoal g')}"
    unless (← getGoals).isEmpty do throwError "ts_auto: a for … of iteration may panic or change the world"
  setGoals exits

/-- Register the trace class `ts_auto.inv`: the loop-invariant candidates of `loopFallback`, the
ones it drops and the ones it keeps. -/
initialize registerTraceClass `ts_auto.inv

/-- Whether a thrown exception may leave the code that `ts_auto` works on (an internal option,
set per call, as proofs may run in parallel): `0` not known, also when the program may catch one;
`1` it may (`JS.NoPanic`, where an exception is no panic, or an iteration of a loop of
`loopFallback` that may throw); `2` it may not (`JS.NoFault`, where it is a fault, or an iteration
that may not throw). -/
def excOpt : Name := `ts_auto.internal.exc

/-- The number of `loopFallback` attempts under way (an internal option, for `ts_auto.profile`). -/
def fallbackDepthOpt : Name := `ts_auto.internal.fallbackDepth

/-- Whether the code of the program `P` (a constant) may catch an exception: a `try` statement, an
async function or a promise callback (an exception rejects a promise) in the definitions outside
the library that `P`'s value reaches. -/
def programMayCatch (P : Lean.Expr) : MetaM Bool := do
  let some n := P.getAppFn.constName? | return true
  let env ← getEnv
  let lib (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some i => [`StrictTS, `Init, `Lean, `Std].contains (env.allImportedModuleNames[i.toNat]!).getRoot
    | none => false
  let catching := [``Stmt.try, ``Stmt.tryFin, ``Lam.async, ``Block.await, ``Stmt.retP, ``Builtin.promNew,
    ``Builtin.promThen, ``Builtin.promThenP, ``Builtin.promCatch, ``Builtin.promFinally,
    ``Builtin.queueMicrotask, ``Builtin.setTimeout]
  let mut seen : NameSet := {}
  let mut todo := [n]
  for _ in [0:100000] do
    let c :: rest := todo | return false
    todo := rest
    if seen.contains c then continue
    seen := seen.insert c
    let some v := (env.find? c).bind (·.value?) | continue
    for d in v.getUsedConstants do
      if catching.contains d then return true
      unless seen.contains d || lib d do todo := d :: todo
  return true

/-- For a partial-correctness goal (`JS.NoPanic`, `JS.NoFault`: the divergence case closes by
`simp`) with a `while`/`for` loop that no summary handles (`JS.exec (evalLoop …) W` in the goal):
if no iteration panics or changes the world, from every environment that satisfies the
invariant (`finish` proves one iteration's obligation), the loop diverges or ends in `W` with a
completion a function body may end with (`evalLoop_cases_exit`: `.ret v`, `.normal` unless the
loop is `while (true)`, and `.exc e` if an iteration may throw);
the goal continues with each such completion and an environment that satisfies the invariant.
The invariant: the `const` slots keep their values, and the candidates about the other slots
(`loopCandidates`: kept values, counters that stay safe naturals) that survive, Houdini-style:
the candidates that an iteration does not keep are dropped and the iteration is checked again
(`set_option trace.ts_auto.inv true` shows them). `splits` (the number of test splits so far)
is restored after a failed attempt. Whether it applied. -/
def loopFallback (finish : TacticM Unit) (splits : IO.Ref Nat) : TacticM Bool := do
  let some e ← withMainContext do
      return (← instantiateMVars (← getMainTarget)).find? fun e =>
        e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).consumeMData.isAppOfArity ``evalLoop 9 && !e.hasLooseBVars
    | -- (a `for … of` loop: the world but for the external-call counter)
      let some e ← withMainContext do
          return (← instantiateMVars (← getMainTarget)).find? fun e =>
            e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).consumeMData.isAppOfArity ``evalForOf 10 &&
              !e.hasLooseBVars
        | return false
      let saved ← saveState
      let s0 ← splits.get
      try
        withoutRecover <| forOfFallbackCore e finish
        return true
      catch ex =>
        saved.restore
        splits.set s0
        trace[ts_auto.inv] "for … of fallback: {ex.toMessageData}"
        return false
  -- the cells the loop may write: the last one allocated before it (a `Set` or array it fills),
  -- then the argument cells
  let cells ← withMainContext do
    let W ← whnfR (e.getArg! 3)
    let mut ks : Array Lean.Expr := #[]
    if W.isAppOf ``World.mk then
      if let some k := (insertedKeys (← whnfR (W.getArg! 1)))[0]? then ks := ks.push k
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some (_, lhs, _) := (← instantiateMVars d.type).eq? then
        if lhs.isAppOf ``Std.ExtDHashMap.get? && lhs.getAppNumArgs ≥ 1 then
          let k := lhs.appArg!
          unless ks.contains k do ks := ks.push k
    return ks
  let cands ← withMainContext do loopCandidates (e.getArg! 2).consumeMData
  trace[ts_auto.inv] "loop slots: candidates {cands} (1 kept, 2 a safe natural)"
  -- (exceptions: an iteration may throw where an exception may leave the code under proof, in
  -- `JS.NoPanic` or in an iteration of an enclosing loop that may throw (a check without them
  -- fails wherever this one does); not where none may, in `JS.NoFault` (the exit by an exception
  -- could not finish); first without, then with them where the program may catch one. First
  -- with the world unchanged, then with one cell written)
  let exc := (← getOptions).get excOpt (0 : Nat)
  let variants := if exc == 0 then [false, true] else [exc == 1]
  let depth := (← getOptions).get fallbackDepthOpt (0 : Nat)
  -- (an attempt with a cell written starts from more worlds and has the same obligations but
  -- for the world: only after an attempt with the world unchanged left a changed world open)
  let writes ← IO.mkRef false
  for cell in #[none] ++ (cells.toList.take 2).toArray.map some do
   if cell.isSome && !(← writes.get) then break
   for throws in variants do
    let mut modes := cands
    for _ in [0:4] do
      let saved ← saveState
      let s0 ← splits.get
      let (t0, h0) := (← IO.monoMsNow, ← IO.getNumHeartbeats)
      -- (`ts_auto.profile`: failed attempts, apart from those inside an iteration of an enclosing
      -- attempt)
      let wasted := s!"(discarded{if depth == 0 then "" else ", nested"}) 2c attempt, \
        throws {throws}, {if cell.isSome then "a cell written" else "world kept"}"
      try
        -- (without error recovery: a failing nested proof, `exact … (by omega)`, is an error,
        -- not a `sorry`)
        let failing ← withOptions (fun o => (o.set fallbackDepthOpt (depth + 1)).set excOpt
            (if exc == 0 then 0 else if throws then 1 else 2)) <|
          withoutRecover <| loopFallbackCore e finish throws cell modes writes
        if failing.isEmpty then
          trace[ts_auto.inv] "loop slots: candidates {cands}, kept {modes}"
          return true
        saved.restore
        splits.set s0
        tsProfNote wasted t0 h0
        trace[ts_auto.inv] "loop slots: candidates {modes}, not kept at {failing}"
        let modes' := modes.mapIdx fun p m => if failing.contains p then {mode := 0} else m
        if modes'.map (·.mode) == modes.map (·.mode) then break
        modes := modes'
      catch _ =>
        saved.restore
        splits.set s0
        tsProfNote wasted t0 h0
        break
  return false

/-- At most this many nested case splits on tests before a loop (`finishTsAuto`), and this many
in one `ts_auto` call. -/
def maxTestSplits : Nat × Nat := (6, 16)

/-- Steps 2 and 3 of `ts_auto` on the main goal (`depth` = the number of enclosing test splits,
`splits` = the number of splits so far; `outer` = not in a case of a final-step split, where
`split` and `simp_all` already failed). -/
partial def finishTsAuto (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (splits : IO.Ref Nat)
    (unfolded : IO.Ref (Array Name)) (depth : Nat := 0) (outer : Bool := true) : TacticM Unit := do
  -- 2. summarize loops and callbacks until none is left
  let _ ← tsProf "2 summarize" <| summarizeAll lemmas unfolded
  if (← getGoals).isEmpty then return
  -- 2b. a loop left behind a test (input validation before the loop: the loop sits in the
  -- continuation of a `match` on the outcome of the `if` statement, out of the summaries' reach):
  -- evaluate what the heap hypotheses decide, split on the innermost undecided test, and go on
  -- in each case
  let canSplit := do return depth < maxTestSplits.1 && (← splits.get) < maxTestSplits.2
  -- go on in each case of a split; once a case stays open the attempt has failed, and the
  -- remaining cases are left as they are
  let goOn (outer : Bool) (next : Nat := depth + 1) (failFast := true) : TacticM Unit := do
    let mut rest : List MVarId := []
    for g in ← getGoals do
      -- (a case left with a loop invariant's candidate fact only: go on, all failing candidates
      -- should show)
      unless !failFast || (← rest.allM (fun g => mentionsSlotFact g)) do
        rest := rest ++ [g]
        continue
      setGoals [g]
      finishTsAuto lemmas splits unfolded next outer
      rest := rest ++ (← getGoals)
    setGoals rest
  -- (a loop where the summaries find it and fail stays: splits would not change it)
  if (← canSplit) && hasHiddenLoop (← instantiateMVars (← getMainTarget)) then
    let saved ← saveState
    let ls := lemmas ++ (← heapHyps)
    try evalTactic (← `(tactic| simp only [ts_sym, $ls,*])) catch _ => pure ()
    if (← getGoals).isEmpty then return
    -- the heap hypotheses alone may have exposed the loop
    if hasExposedLoop (← instantiateMVars (← getMainTarget)) then
      if ← summarizeAll lemmas unfolded then
        finishTsAuto lemmas splits unfolded (depth + 1)
        return
    let found ← if hasHiddenLoop (← instantiateMVars (← getMainTarget)) then
        withMainContext do findTest (← instantiateMVars (← getMainTarget))
      else pure none
    match found with
    | some t =>
      -- (a test whose cases both go on to the loop, `if (n % 2 === 0) n = n / 2`, is split too;
      -- the number of splits is bounded and a failing case stops the search)
      splits.modify (· + 1)
      splitOnTest t (mkIdent (Name.mkSimple s!"htest{depth}")) lemmas
      goOn outer
      return
    | none =>
      -- (the heap facts exposed a `while`/`for` loop that no summary handles: the fallback below
      -- works on that state)
      let exposed := ((← instantiateMVars (← getMainTarget)).find? fun e => e.isAppOfArity ``JS.exec 4 &&
        (e.getArg! 2).consumeMData.isAppOfArity ``evalLoop 9 && !e.hasLooseBVars).isSome
      unless exposed do saved.restore
  -- 2c. a `while`/counted `for` loop that no summary handles, in a partial-correctness goal: the
  -- loop diverges or exits without changing the world when no iteration panics or does
  -- (an iteration starts at depth 1: its tests are its own; the total number of splits bounds
  -- the search)
  if (← canSplit) && (← tsProf "2c loop fallback (incl. iterations)" <|
      loopFallback (finishTsAuto lemmas splits unfolded 1 false) splits) then
    splits.modify (· + 1)
    goOn outer
    return
  -- 3. finish: async code runs its microtask queue (and event loop) to the end
  if (← getGoals).isEmpty then return
  if isAsyncGoal (← instantiateMVars (← getMainTarget)) then
    finishAsync lemmas 16
  else
    -- (reads after a summarized loop: the heap hypotheses evaluate them)
    let ls := lemmas ++ (← heapHyps)
    tsProf "3 final simp" <| try evalTactic (← `(tactic| simp [ts_sym, $ls,*])) catch _ => pure ()
    if (← getGoals).isEmpty then return
    let simped ← saveState
    let (t0, h0) := (← IO.monoMsNow, ← IO.getNumHeartbeats)
    -- straight-line code with a symbolic test left: split on it and finish each case
    if outer then
      for _ in [0:8] do
        if (← getGoals).isEmpty then return
        try tsProf "3 split <;> simp_all" <|
          evalTactic (← `(tactic| all_goals (split <;> simp_all [ts_sym, $lemmas,*])))
        catch _ => break
    if (← getGoals).isEmpty then return
    -- `split` takes the outermost `match` (the monadic sequencing, whose cases lose the test):
    -- split on the innermost undecided test instead and finish each case
    -- (not with a loop left that no summary handles: splits would not remove it)
    let unsplit ← saveState
    simped.restore
    let found ← if (← splits.get) < maxTestSplits.2 && !hasAnyLoop (← instantiateMVars (← getMainTarget)) then
        tsProf "3 findTest" <| withMainContext do findTest (← instantiateMVars (← getMainTarget))
      else pure none
    if found.isSome then tsProfNote "(discarded) 3 split <;> simp_all, a test found" t0 h0
    match found with
    | some t@.intro | some t@.conj =>
      -- (introducing a test's premise, or splitting a conjunction of such implications, is no
      -- case split: the cases go on at the same depth)
      let n ← splits.get
      splits.modify (· + 1)
      splitOnTest t (mkIdent (Name.mkSimple s!"htest{depth}c{n}")) lemmas
      -- (the parts of a conjunction are separate obligations: each is tried, as one goal before;
      -- what stays open goes to the caller, e.g. the cell witness of `loopFallback`)
      goOn false depth (failFast := false)
    | some t =>
      if depth < maxTestSplits.1 then
        splits.modify (· + 1)
        splitOnTest t (mkIdent (Name.mkSimple s!"htest{depth}")) lemmas
        goOn false
      else if outer then unsplit.restore
      else try evalTactic (← `(tactic| (simp_all [ts_sym, $lemmas,*]; done))) catch _ => pure ()
    | none =>
      if outer then unsplit.restore
      else try evalTactic (← `(tactic| (simp_all [ts_sym, $lemmas,*]; done))) catch _ => pure ()

/-- The global references (`«g_x» : GRef t := ⟨i, "x"⟩`) that the module body of the program
`P` (a constant `X.program`, with `X.mainBlock`) mentions, as simp lemmas that unfold them. -/
def moduleGRefs (P : Lean.Expr) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let some n := P.constName? | return #[]
  let env ← getEnv
  let some ci := env.find? (n.getPrefix.str "mainBlock") | return #[]
  let some v := ci.value? | return #[]
  let mut out := #[]
  for c in v.getUsedConstants do
    if let some cc := env.find? c then
      if cc.type.isAppOf ``GRef then
        out := out.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident))
  return out

/-- A hypothesis `w.ModuleInit I P` becomes facts about the cells of the initialised world: the
module body is run symbolically from the initial world (the program and its `mainBlock`
unfolded, with the call lemmas of the functions it calls), and each cell `(k, a)` it leaves gives
`w.heap.get? (k, a) = some c`; the bound `n ≤ w.next` on fresh addresses stays. The hypothesis is
left as it is when the module body does not evaluate to one world. -/
def moduleFactsOf (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (fv : FVarId) (i : Nat) :
    TacticM Unit := do
  let (P, hS) ← withMainContext do
    let ty ← instantiateMVars (← fv.getType)
    return (ty.getArg! 2, ← Term.exprToSyntax (mkFVar fv))
  let mut defs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  let nm (s : String) := mkIdent (Name.mkSimple s!"hmod{i}_{s}")
  if let some n := P.constName? then
    -- (the program's globals and main block, not the program itself: the module body's calls
    -- `callFun I P f` keep matching their call lemmas)
    let proj (f : Name) : TacticM (Option Term) := withMainContext do
      let some e ← unfoldDefinition? (← mkAppM f #[P]) | return none
      let e ← whnfCore e
      if e.isAppOf f then return none
      return some (← Term.exprToSyntax e)
    for (f, h) in [(``Program.globals, nm "globals"), (``Program.main, nm "main")] do
      if let some v ← proj f then
        let PS ← withMainContext <| Term.exprToSyntax P
        let lhs ← `($(mkIdent f) $PS)
        try
          evalTactic (← `(tactic| have $h : $lhs = $v := rfl))
          defs := defs.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
        catch _ => defs := defs.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
    let mb := n.getPrefix.str "mainBlock"
    if (← getEnv).contains mb then
      defs := defs.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent mb):ident))
  -- (the module's global references, unfolded: the keys of their boxes compare, `g_phi.idx = 1`)
  defs := defs ++ (← moduleGRefs P)
  let (w0, env0, hrun, hcells, hnext) := (nm "w0", nm "env", nm "run", nm "cells", nm "next")
  let (ext, rnd, now) := (nm "ext", nm "rand", nm "now")
  evalTactic (← `(tactic| obtain ⟨$ext, $rnd, $now, $w0, $env0, $hrun, $hcells, $hnext⟩ := $hS))
  -- (`decide`: the boxes of globals of one type differ by their literal addresses, and string
  -- literals compare (`"&" == "__proto__"` in a dictionary literal); a module body that builds
  -- large literals needs many steps)
  tsProf "0 module body simp" <|
    evalTactic (← `(tactic| simp (config := { maxSteps := 4000000, decide := true }) (disch := decide) only
      [StrictTS.moduleInit, World.initWith, ts_sym, List.forIn_cons, List.forIn_nil, $defs,*, $lemmas,*]
      at $hrun:ident))
  -- functions called by the module body (each once), and the host's answers to its external
  -- calls (`ext name args ret vs n`): an error ends the initialisation abnormally, which
  -- contradicts the hypothesis; the value goes on (calls run at a world or with arguments that a
  -- pending answer decides wait for it)
  let extFv ← withMainContext do return ((← getLCtx).findFromUserName? ext.getId).map (·.fvarId)
  let mut done : Array Name := #[]
  for _ in [0:24] do
    let hrunTy ← withMainContext do
      let some d := (← getLCtx).findFromUserName? hrun.getId | return none
      return some (← instantiateMVars d.type)
    let some t := hrunTy | break
    let call? ← withMainContext do
      let some e := t.find? fun e => e.isAppOfArity ``callFun 7 && (e.getArg! 5).isConst &&
          !e.hasLooseBVars && !done.contains (e.getArg! 5).constName! | return none
      let ref := (e.getArg! 5).constName!
      return (← callLemmaOf ref).map fun (l, d) => (ref, l, d)
    if let some (ref, lem, defn) := call? then
      done := done.push ref
      evalTactic (← `(tactic| rw [$(mkIdent lem):ident] at $hrun:ident))
      evalTactic (← `(tactic| simp (disch := decide) only [$(mkIdent defn):ident, ts_sym, $defs,*,
        $lemmas,*] at $hrun:ident))
      continue
    let some q := t.find? fun e => e.getAppNumArgs == 5 && e.getAppFn.isFVar &&
        some e.getAppFn.fvarId! == extFv && !e.hasLooseBVars
      | break
    let qS ← withMainContext <| Term.exprToSyntax q
    let (hq, ev, er) := (nm "ans", nm "ev", nm "err")
    evalTactic (← `(tactic| rcases $hq:ident : $qS with $er:ident | $ev:ident))
    let mut rest : List MVarId := []
    for g in ← getGoals do
      setGoals [g]
      -- (the value case: the answer's forms at the call's type)
      try evalTactic (← `(tactic| cases $ev:ident)) catch _ => pure ()
      for g' in ← getGoals do
        setGoals [g']
        try evalTactic (← `(tactic| simp (disch := decide) only [$hq:ident, ts_sym, reduceCtorEq,
          Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, false_and, and_false, $defs,*, $lemmas,*]
          at $hrun:ident)) catch _ => pure ()
        rest := rest ++ (← getGoals)
    setGoals rest
    -- (facts for one initialisation only)
    unless rest.length == 1 do throwError "ts_auto: the module body's external answers have several forms"
  -- `some (.ok (.normal, env), W) = some (.ok (.normal, env0), w0)`: `w0` is `W`; an
  -- initialisation that ends otherwise (`.exc e`, a thrown error) contradicts the hypothesis,
  -- which closes the goal
  evalTactic (← `(tactic| simp only [Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, true_and,
    and_true, reduceCtorEq, false_and, and_false, Option.some_ne_none] at $hrun:ident))
  if (← getGoals).isEmpty then return
  -- (a quoted `rfl` pattern would be hygienic, so `subst`)
  let hW := nm "W"
  evalTactic (← `(tactic| obtain ⟨-, $hW:ident⟩ := $hrun:ident))
  evalTactic (← `(tactic| subst $hW:ident))
  -- one fact per cell of `W`: `∀ k, k.2 < W.next → w.heap.get? k = W.heap.get? k`
  let keys ← withMainContext do
    let some d := (← getLCtx).findFromUserName? hcells.getId | return #[]
    let t ← instantiateMVars d.type
    let .forallE _ _ body _ := t | return #[]
    let .forallE _ _ eqn _ := body | return #[]
    let some (_, _, rhs) := eqn.eq? | return #[]
    let some heap := (rhs.getAppArgs.toList.find? fun a => a.isAppOf ``World.heap) | return #[]
    return insertedKeys (← whnfR heap)
  let mut seen : Array Lean.Expr := #[]
  for (K, j) in keys.zipIdx do
    if seen.contains K then continue
    seen := seen.push K
    let KS ← withMainContext <| Term.exprToSyntax K
    let hk := mkIdent (Name.mkSimple s!"hmod{i}_cell{j}")
    try
      evalTactic (← `(tactic| have $hk:ident := $hcells:ident $KS (by first | decide | simp)))
      evalTactic (← `(tactic| simp (disch := decide) only [ts_sym, Nat.zero_add, Nat.reduceAdd] at $hk:ident))
      -- keep the facts that evaluate to a content (a key that the cell's later write shadows
      -- under another name of the same address stays unevaluated)
      let ok ← withMainContext do
        let some d := (← getLCtx).findFromUserName? hk.getId | return false
        let some (_, _, rhs) := (← instantiateMVars d.type).eq? | return false
        return rhs.isAppOf ``Option.some || rhs.isAppOf ``Option.none
      unless ok do evalTactic (← `(tactic| clear $hk:ident))
    catch _ => pure ()
  evalTactic (← `(tactic| clear $hcells:ident))
  try evalTactic (← `(tactic| simp only [Nat.zero_add, Nat.reduceAdd] at $hnext:ident)) catch _ => pure ()

/-- `moduleFactsOf` for every hypothesis `w.ModuleInit I P`; the unfolding lemmas of the
program's global references (`moduleGRefs`), which the rest of `ts_auto` uses too, so that the
box reads of the code meet the facts' keys. -/
def moduleFacts (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let hyps ← withMainContext do
    return (← getLCtx).foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail && d.type.isAppOfArity ``World.ModuleInit 4 then acc.push (d.fvarId, d.type)
      else acc
  let mut grefs := #[]
  for ((fv, ty), i) in hyps.zipIdx do
    let P := (← instantiateMVars ty).consumeMData.getArg! 2
    grefs := grefs ++ (← moduleGRefs P)
    -- (an initialisation that cannot end normally closes the goal)
    if (← getGoals).isEmpty then break
    let saved ← saveState
    try moduleFactsOf lemmas fv i catch _ => saved.restore
  return grefs

/-- The string arguments that a hypothesis bounds (`hl : v.toStr.length < 2 ^ 53`, ECMA-262
§6.1.4): their case `v = .str s`, so that the semantics' `v.toStr` and the bound meet at `s`. -/
def destructBoundedStrs : TacticM Unit := do
  let mut any := false
  for _ in [0:16] do
    let some fv ← withMainContext do
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let ty ← instantiateMVars d.type
          if let some e := ty.find? fun e => e.isAppOfArity ``Val.toStr 2 && e.appArg!.isFVar then
            return some e.appArg!.fvarId!
        return none
      | break
    let gs ← (← getMainGoal).cases fv
    replaceMainGoal (gs.toList.map (·.mvarId))
    any := true
  if any then
    try evalTactic (← `(tactic| simp only [StrictTS.Val.toStr] at *)) catch _ => pure ()

/-- The recipe of `ts_auto` with the extra simp lemmas `lemmas` (`runTsAuto`). -/
def runTsAutoCore (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  -- 0. contract statements are definitions: expose the runs; a world in which the module has
  -- been initialised: facts about the module's cells (and its global references unfolded)
  try evalTactic (← `(tactic| simp only [JS.Returns, JS.NoFault, JS.NoPanic])) catch _ => pure ()
  let lemmas := lemmas ++ (← tsProf "0 module facts" <| moduleFacts lemmas)
  if (← getGoals).isEmpty then return
  -- (the host's regular-expression guarantees: one `World.ExtSpec` per external function)
  for _ in [0:4] do
    let some fv ← withMainContext do
        return (← getLCtx).findDecl? fun d =>
          if !d.isImplementationDetail && d.type.isAppOfArity ``World.RegExpSpec 2 then some d.fvarId else none
      | break
    let h ← withMainContext do Term.exprToSyntax (mkFVar fv)
    evalTactic (← `(tactic| obtain ⟨$(mkIdent `hspec_matchAll), $(mkIdent `hspec_elem0)⟩ := $h))
    try replaceMainGoal [← (← getMainGoal).clear fv] catch _ => pure ()
  destructBoundedStrs
  -- 1. unfold the calls of the functions under proof (and of callees exposed by them)
  let mut done : Array Name := #[]
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    match ← tsProf "1 unfold calls" <| unfoldOneCall done with
    | some r => done := done.push r
    | none => break
  if (← getGoals).isEmpty then return
  -- 1b. split the argument cells that no hypothesis fixes: present or dangling
  tsProf "1b ts_cells" <| try evalTactic (← `(tactic| ts_cells)) catch _ => pure ()
  let splits ← IO.mkRef 0
  let unfolded ← IO.mkRef done
  let mut rest : List MVarId := []
  for g in ← getGoals do
    setGoals [g]
    if ← hasDanglingCell then
      -- a missing cell: both sides panic at their first read of it (no summaries: they would
      -- leave unprovable `w.heap.get? … = some …` goals)
      let ls := lemmas ++ (← heapHyps)
      evalTactic (← `(tactic| simp [ts_sym, $ls,*]))
    else
      finishTsAuto lemmas splits unfolded
    rest := rest ++ (← getGoals)
  setGoals rest

/-- The recipe of `ts_auto` with the extra simp lemmas `lemmas`, knowing whether an exception may
leave the code under proof (`excOpt`). -/
def runTsAuto (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  let exc ← withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    let k := if t.isAppOf ``JS.NoPanic then 1 else if t.isAppOf ``JS.NoFault then 2 else 0
    let some c := t.find? (·.isAppOfArity ``callFun 7) | return 0
    if k == 0 || (← programMayCatch (c.getArg! 2)) then return 0
    return k
  withOptions (·.set excOpt exc) (runTsAutoCore lemmas)

/-- `ts_auto [lemmas]`: the automatic proof attempt (see the module comment). -/
syntax (name := tsAuto) "ts_auto" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- `runTsAuto`, printing the phase totals on stderr when `ts_auto.profile` is set (every 10 s,
for a run that a time limit kills, and at the end, also after the heartbeat limit). -/
def runTsAutoProfiled (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  unless ts_auto.profile.get (← getOptions) do return ← runTsAuto lemmas
  let t0 ← IO.monoMsNow
  tsAutoProf.set { t0, h0 := ← IO.getNumHeartbeats, last := t0 }
  tryCatchRuntimeEx
    (do runTsAuto lemmas; tsProfPrint "end")
    (fun ex => do tsProfPrint "failed"; throw ex)

elab_rules : tactic
  | `(tactic| ts_auto) => runTsAutoProfiled #[]
  | `(tactic| ts_auto [$hs,*]) => runTsAutoProfiled hs.getElems

end StrictTS
