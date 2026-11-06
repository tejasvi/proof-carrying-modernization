/-
StrictTS frontend prelude: notation used by the Lean code that the TypeScript translator
(`frontend/`) generates, and a driver that runs a translated program.

All notations are macros that expand to the plain IR constructors (`Var.there`, `Args.cons`,
`Tys.cons`, …), so a generated term is literally an IR term: proofs never have to unfold a
prelude definition to see the IR.
-/
import StrictTS.Core.Sem

namespace StrictTS.Frontend
open StrictTS

/-- `tys[a, b, c]` is the `Tys` list `.cons a (.cons b (.cons c .nil))`. -/
syntax "tys[" term,* "]" : term
macro_rules
  | `(tys[]) => `(StrictTS.Tys.nil)
  | `(tys[$t]) => `(StrictTS.Tys.cons $t StrictTS.Tys.nil)
  | `(tys[$t, $ts,*]) => `(StrictTS.Tys.cons $t tys[$ts,*])

/-- One field of a record or class: `"name" : type`. -/
declare_syntax_cat fldItem
syntax str " : " term : fldItem

/-- `flds["x" : .num, "y" : .str]` is the `Fields` list `.cons "x" .num (.cons "y" .str .nil)`. -/
syntax "flds[" fldItem,* "]" : term
macro_rules
  | `(flds[]) => `(StrictTS.Fields.nil)
  | `(flds[$n:str : $t]) => `(StrictTS.Fields.cons $n $t StrictTS.Fields.nil)
  | `(flds[$n:str : $t, $fs,*]) => `(StrictTS.Fields.cons $n $t flds[$fs,*])

/-- `args[a, b]` is the argument list `Args.cons a (Args.cons b Args.nil)`. -/
syntax "args[" term,* "]" : term
macro_rules
  | `(args[]) => `(StrictTS.Args.nil)
  | `(args[$t]) => `(StrictTS.Args.cons $t StrictTS.Args.nil)
  | `(args[$t, $ts,*]) => `(StrictTS.Args.cons $t args[$ts,*])

/-- `alts[a, b]`: branches of an expression-level union case analysis. -/
syntax "alts[" term,* "]" : term
macro_rules
  | `(alts[]) => `(StrictTS.Alts.nil)
  | `(alts[$t]) => `(StrictTS.Alts.cons $t StrictTS.Alts.nil)
  | `(alts[$t, $ts,*]) => `(StrictTS.Alts.cons $t alts[$ts,*])

/-- `altsS[a, b]`: branches of a statement-level union case analysis. -/
syntax "altsS[" term,* "]" : term
macro_rules
  | `(altsS[]) => `(StrictTS.AltsS.nil)
  | `(altsS[$t]) => `(StrictTS.AltsS.cons $t StrictTS.AltsS.nil)
  | `(altsS[$t, $ts,*]) => `(StrictTS.AltsS.cons $t altsS[$ts,*])

/-- `caps[x, y]`: the captured variables of a closure. -/
syntax "caps[" term,* "]" : term
macro_rules
  | `(caps[]) => `(StrictTS.Caps.nil)
  | `(caps[$t]) => `(StrictTS.Caps.cons $t StrictTS.Caps.nil)
  | `(caps[$t, $ts,*]) => `(StrictTS.Caps.cons $t caps[$ts,*])

/-- `var! n`: the expression reading the variable with de Bruijn index `n`. -/
syntax "var! " num : term
/-- `vr! n`: the typed variable (`Var`) with de Bruijn index `n`. -/
syntax "vr! " num : term
/-- `mvar! n`: the assignable variable with de Bruijn index `n`. -/
syntax "mvar! " num : term
/-- `cvar! n`: the capturable variable with de Bruijn index `n`. -/
syntax "cvar! " num : term
/-- `mem! n`: position `n` of a member/field list. -/
syntax "mem! " num : term

macro_rules
  | `(vr! $n) => do
    let mut v ← `(StrictTS.Var.here)
    for _ in [0:n.getNat] do v ← `(StrictTS.Var.there $v)
    return v
  | `(var! $n) => `(StrictTS.Expr.var (vr! $n))
  | `(mvar! $n) => do
    let mut v ← `(StrictTS.MVar.here)
    for _ in [0:n.getNat] do v ← `(StrictTS.MVar.there $v)
    return v
  | `(cvar! $n) => do
    let mut v ← `(StrictTS.CVar.here)
    for _ in [0:n.getNat] do v ← `(StrictTS.CVar.there $v)
    return v
  | `(mem! $n) => do
    let mut v ← `(StrictTS.Mem.here)
    for _ in [0:n.getNat] do v ← `(StrictTS.Mem.there $v)
    return v

/-- `js! "text"`: a string literal as a JavaScript string (UTF-16 code units). -/
syntax "js! " str : term
macro_rules
  | `(js! $s) => `(StrictTS.JSStr.ofString $s)

/-! ### Running translated programs -/

/-- Console output and final status of a run, in the format of the differential tester:
the printed lines, then `[ok]`, `[uncaught Name: message]`, `[PANIC message]` or
`[DIVERGED]`. -/
def showRun : Option (Except Exc Unit × List JSStr) → String
  | none => "[DIVERGED]"
  | some (r, out) =>
    let status := match r with
      | .ok _ => "[ok]"
      | .error (.thrown e) => s!"[uncaught {e.name}: {e.message}]"
      | .error (.panic m) => s!"[PANIC {m}]"
    String.intercalate "\n" (out.map toString ++ [status])

/-- Print the run of a translated program between markers (used by `tests/difftest`). -/
def runMain {TT : TypeTable} (P : Program TT) (label : String := "") (I : Impl := Impl.host) : IO Unit := do
  IO.println s!"=====STRICTTS-BEGIN {label}====="
  IO.println (showRun (runOutput I P))
  IO.println s!"=====STRICTTS-END {label}====="

/-! ### Programs with external calls: replaying a Node run

For a corpus program marked `@extern`, `tests/difftest` records every external call of the Node
run (name, arguments, outcome) and every `Date.now()` value. The Lean run answers its external
calls and `Date.now()` from that record (the world's call-indexed oracles); a call whose name or
primitive arguments differ from the recorded one throws `TraceMismatch`, and calls left over
are reported after the run. -/

/-- A recorded value: primitives, external objects (by identity), records (by field name),
arrays (by element, for results); `other` is a value that is not compared (arguments that are
arrays or functions). -/
inductive Rec where
  | undef | null
  | bool (b : Bool) | num (x : F64) | str (s : JSStr)
  | handle (id : Nat)
  | fields (kvs : List (String × Rec))
  | list (xs : List Rec)
  | other
  deriving Inhabited, BEq

def Rec.enumIdx (s : JSStr) : List String → Nat → Option Nat
  | [], _ => none
  | c :: cs, i => if JSStr.ofString c == s then some i else Rec.enumIdx s cs (i + 1)

mutual
/-- The value of type `t` that a recorded value stands for (`none` if it does not fit). -/
partial def Rec.toVal {TT : TypeTable} : (t : Ty) → Rec → Option (Val TT t)
  | .undef, .undef => some .undef
  | .null, .null => some .null
  | .bool, .bool b => some (.bool b)
  | .num, .num x => some (.num x)
  | .str, .str s => some (.str s)
  | .ext _, .handle i => some (.ext i)
  | .enum cs, .str s => (Rec.enumIdx s cs 0).bind fun i => if h : i < cs.length then some (.enum ⟨i, h⟩) else none
  | .opt _, .undef => some .none
  | .opt t, r => (Rec.toVal t r).map .some
  | .union ts, r => (Rec.toInj ts.toList r).map fun ⟨_, m, v⟩ => .inj m v
  | .record fs, .fields kvs => (Rec.toFields fs kvs).map .record
  | _, _ => none

partial def Rec.toInj {TT : TypeTable} : (ts : List Ty) → Rec → Option ((t : Ty) × Mem t ts × Val TT t)
  | [], _ => none
  | t :: ts, r => match Rec.toVal (TT := TT) t r with
    | some v => some ⟨t, .here, v⟩
    | none => (Rec.toInj ts r).map fun ⟨u, m, v⟩ => ⟨u, .there m, v⟩

partial def Rec.toFields {TT : TypeTable} : (fs : Fields) → List (String × Rec) → Option (Vals TT fs.types)
  | .nil, _ => some .nil
  | .cons n t fs, kvs => do
    let v ← Rec.toVal t ((kvs.lookup n).getD .undef)
    let vs ← Rec.toFields fs kvs
    pure (.cons v vs)
end

mutual
/-- The oracle answer a recorded result stands for: arrays are allocated by the semantics
(`EVal.arr`), everything else is a value; at type `unknown`, JSON-like values with their
runtime types (arrays of `unknown`, objects as dictionaries of `unknown`). -/
partial def Rec.toEVal {TT : TypeTable} : (t : Ty) → Rec → Option (EVal TT t)
  | .arr t, .list xs => (xs.mapM (Rec.toEVal t)).map fun es => .arr (es.foldr .cons .nil)
  | .dict t, .fields kvs => (kvs.mapM fun (kv : String × Rec) => Rec.toEVal (TT := TT) t kv.2).map fun (es : List (EVal TT t)) =>
      .dict (kvs.map fun kv => JSStr.ofString kv.1) (es.foldr .cons .nil)
  | .dyn, r => Rec.dynEVal r
  | t, r => (Rec.toVal t r).map .val
partial def Rec.dynEVal {TT : TypeTable} : Rec → Option (EVal TT .dyn)
  | .undef => some (.val (.dyn .undef .undef))
  | .null => some (.val (.dyn .null .null))
  | .bool b => some (.val (.dyn .bool (.bool b)))
  | .num x => some (.val (.dyn .num (.num x)))
  | .str s => some (.val (.dyn .str (.str s)))
  | .list xs => (xs.mapM Rec.dynEVal).map fun es => .dyn (.arr .dyn) (.arr (es.foldr .cons .nil))
  | .fields kvs => (kvs.mapM fun (kv : String × Rec) => Rec.dynEVal (TT := TT) kv.2).map fun (es : List (EVal TT .dyn)) =>
      .dyn (.dict .dyn) (.dict (kvs.map fun kv => JSStr.ofString kv.1) (es.foldr .cons .nil))
  | _ => none
end

/-- A value as a recorded value (`other` for heap values, records, functions). -/
partial def Rec.ofVal {TT : TypeTable} : (t : Ty) → Val TT t → Rec
  | .undef, _ => .undef
  | .null, _ => .null
  | .bool, v => .bool v.toBool
  | .num, v => .num v.toNum
  | .str, v => .str v.toStr
  | .ext _, v => .handle v.extId
  | .enum cs, .enum i => .str (JSStr.ofString (cs.get i))
  | .opt _, .none => .undef
  | .opt t, .some x => Rec.ofVal t x
  | .union _, .inj (t := u) _ x => Rec.ofVal u x
  | .dyn, .dyn u x => Rec.ofVal u x
  | _, _ => .other

partial def Rec.ofVals {TT : TypeTable} : {ts : List Ty} → Vals TT ts → List Rec
  | _, .nil => []
  | t :: _, .cons v vs => Rec.ofVal t v :: Rec.ofVals vs

def Rec.agree : Rec → Rec → Bool
  | .other, _ | _, .other => true
  | a, b => a == b

/-- One recorded external call: name, arguments, and the value returned or the error thrown. -/
structure RecCall where
  name : String
  args : List Rec
  out : Except (String × String) Rec

/-- The external-call oracle that replays recorded calls in order. -/
def traceOracle {TT : TypeTable} (calls : Array RecCall) : ExtOracle TT := fun name _ ret vs n =>
  let mismatch (msg : String) : Except ErrVal (EVal TT ret) :=
    .error ⟨JSStr.ofString "TraceMismatch", JSStr.ofString s!"external call {n} ({name}): {msg}"⟩
  match calls[n]? with
  | none => mismatch "not made by the Node run"
  | some c =>
    let got := Rec.ofVals vs
    if c.name != name then mismatch s!"the Node run called {c.name}"
    else if c.args.length != got.length || !((c.args.zip got).all fun (a, b) => Rec.agree a b) then
      mismatch "the arguments differ from the Node run"
    else match c.out with
      | .error (nm, msg) => .error ⟨JSStr.ofString nm, JSStr.ofString msg⟩
      | .ok r => match r.toEVal ret with
        | some v => .ok v
        | none => mismatch "the Node result does not fit the type"

/-- `runMain` for a program with external calls, answered from a Node run's record. -/
def runMainTrace {TT : TypeTable} (P : Program TT) (label : String) (calls : Array RecCall) (nows : Array F64)
    (I : Impl := Impl.host) : IO Unit := do
  let w0 : World TT := { heap := ∅, next := 0, ext := traceOracle calls, now := fun i => nows.getD i F64.zero }
  let r := (runProgram I P).run.run w0
  IO.println s!"=====STRICTTS-BEGIN {label}====="
  IO.println (showRun (r.map fun (o, w) => (o, w.out)))
  match r with
  | some (_, w) =>
    if w.extIdx < calls.size then IO.println s!"[TRACE: {w.extIdx} of the {calls.size} external calls of the Node run made]"
    if w.nowIdx < nows.size then IO.println s!"[TRACE: {w.nowIdx} of the {nows.size} Date.now() calls of the Node run made]"
  | none => pure ()
  IO.println s!"=====STRICTTS-END {label}====="

end StrictTS.Frontend
