/-
  Jimple/Report.lean

  Failures in Java terms. `traceMethod` runs a method like `runMethod` and records every
  executed statement (method, statement index, Java line from `Body.lines`); `report` renders
  the outcome and the path as Java source positions, e.g.

      Item.price() throws java.lang.NullPointerException at line 9
      path: Item.price() lines 9

  The trace is for reading only: the outcome it reports is the interpreter's (`runR_sound`
  covers `runMethod`, which takes the same steps).
-/
import Jimple.Generic

namespace Jimple

/-- One executed statement: call depth, method, statement index and Java line (0 = unknown). -/
structure TraceEvt where
  depth : Nat
  cls : ClassName
  meth : String
  pc : Nat
  line : Nat
  deriving Inhabited, Repr

abbrev TraceM := StateM (Array TraceEvt)

mutual
/-- `runM` recording the executed statements. -/
partial def traceM (P : Program) (d : Nat) : Nat → MethodRef → List Value → State → TraceM (Option Outcome)
  | 0, _, _, _ => pure none
  | n + 1, m, args, σ =>
    match m.decl.body with
    | some b => traceB P d m n b 0 (Frame.init m.decl.mods.isStatic args) σ
    | none => pure (some (.wrong "abstract or native method"))

partial def traceV (P : Program) (d : Nat) : Nat → MethodSig → ClassName → List Value → State →
    TraceM (Option Outcome)
  | 0, _, _, _, _ => pure none
  | n + 1, sig, c, args, σ =>
    match P.selectVirtual c sig.sub with
    | .jimple m => traceM P d n m args σ
    | .native lc =>
      match args with
      | .ref a :: rest =>
        match σ.heap a with
        | some (.plain c' fs) =>
          if c' = c then
            match Native.plainInst P sig lc a c fs rest σ with
            | some r => do return (← traceR P d n r).map EvOut.toOutcome
            | none => pure (some (.wrong "no model for library method"))
          else pure none
        | _ => pure none
      | _ => pure none
    | .none why => pure (if P.concrete c then some (.wrong why) else none)

partial def traceR (P : Program) (d : Nat) {α : Type} [Inhabited α] : Nat → Res α → TraceM (Option α)
  | 0, _ => pure none
  | _ + 1, .ret a => pure (some a)
  | n + 1, .call _ (.method m) args σ k => do
    match ← traceM P (d + 1) n m args σ with
    | some o => traceR P d n (k o)
    | none => pure none
  | n + 1, .call sig (.virtual c) args σ k => do
    match ← traceV P (d + 1) n sig c args σ with
    | some o => traceR P d n (k o)
    | none => pure none
  | n + 1, .choose k => traceR P d n (k 0)

partial def traceB (P : Program) (d : Nat) (m : MethodRef) : Nat → Body → Nat → Frame → State →
    TraceM (Option Outcome)
  | 0, _, _, _, _ => pure none
  | n + 1, b, pc, fr, σ => do
    modify (·.push { depth := d, cls := m.cls, meth := m.decl.name, pc, line := b.lines.getD pc 0 })
    match ← traceR P d n (step P b pc fr σ) with
    | some r =>
      match afterStep P b pc fr r with
      | .cont pc' fr' σ' => traceB P d m n b pc' fr' σ'
      | .done o => pure (some o)
    | none => pure none
end

instance : Inhabited StepOut := ⟨.wrong ""⟩
instance : Inhabited EvOut := ⟨.wrong ""⟩
instance : Inhabited InitOut := ⟨.wrong ""⟩

/-- Run `m` on `args` from `σ` like `runMethod`, recording the executed statements. -/
def traceMethod (P : Program) (m : MethodRef) (args : List Value) (σ : State)
    (fuel : Nat := 100000000) : Option Outcome × Array TraceEvt :=
  let prog : Res Outcome := (ensureInit P m.cls σ).bind fun r =>
    match r with
    | .ok σ => .call m.sig (.method m) args σ fun o => .ret o
    | .thr e σ => .ret (.exc e σ)
    | .wrong msg => .ret (.wrong msg)
  (traceR P 0 fuel prog).run #[]

/-- A value as Java would show it in a message (objects by their class, decimals and strings by
    their contents). -/
def showValue (σ : State) : Value → String
  | .int x => toString x.toInt
  | .long x => toString x.toInt ++ "L"
  | .float _ => "<float>"
  | .double _ => "<double>"
  | .null => "null"
  | .retAddr l => s!"<return address {l}>"
  | .ref a => match σ.heap a with
    | some (.dec d) => d.toPlainString
    | some (.str s) => (repr (JStr.toLean s)).pretty
    | some (.bigInt i) => toString i
    | some (.boxed c v) => s!"{c}({match v with | .int x => toString x.toInt | .long x => toString x.toInt | _ => "?"})"
    | some o => match o.ty with
      | .cls c => s!"{c}@{a}"
      | _ => s!"array@{a}"
    | none => s!"<dangling {a}>"

/-- `Class.method()` for messages. -/
def methodName (m : MethodRef) : String := s!"{m.cls}.{m.decl.name}()"

/-- The Java lines of the statements executed at depth `d`, consecutive repetitions merged. -/
def linesAt (tr : Array TraceEvt) (d : Nat) : List Nat :=
  (tr.toList.filter (·.depth == d)).foldl (fun acc e =>
    if e.line == 0 || acc.head? == some e.line then acc else e.line :: acc) [] |>.reverse

/-- The outcome and the path of a run of `m`, in Java terms. -/
def report (P : Program) (m : MethodRef) (args : List Value) (σ : State)
    (fuel : Nat := 100000000) : String :=
  let (o, tr) := traceMethod P m args σ fuel
  -- the statement of `m` (depth 1: called from the class-initialization wrapper) executed last
  let top := tr.toList.filter (·.depth == 1)
  let pos := match top.getLast? with
    | some e => if e.line != 0 then s!" at line {e.line}" else s!" at statement {e.pc}"
    | none => ""
  let outcome := match o with
    | some (.normal (some v) σ') => s!"returns {showValue σ' v}"
    | some (.normal none _) => "returns"
    | some (.exc e σ') =>
      let cls := match σ'.heap e with
        | some o => match o.ty with | .cls c => c | _ => "?"
        | none => "?"
      s!"throws {cls}{pos}"
    | some (.wrong msg) => s!"goes wrong ({msg}){pos}"
    | none => "runs out of fuel"
  let path := (linesAt tr 1).map toString
  s!"{methodName m} {outcome}\npath: {methodName m} lines {String.intercalate " → " path}"

end Jimple
