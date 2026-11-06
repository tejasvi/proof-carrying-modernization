/-
# Control flow: paragraphs, `PERFORM ... THRU`, `GO TO`

## `PERFORM` semantics (IBM return slots)

IBM Enterprise COBOL implements an out-of-line `PERFORM p THRU q` (statement `s`) as:
save the return slot of the end of `q` in `s`'s save area, set that slot to "return to
`s`", jump to `p`.  When control reaches the end of any paragraph `k` whose slot is set to
`s`, it jumps back to the statement after `s`, which restores the slot from its save area.
Falling off the end of a paragraph with no slot set continues with the next paragraph.

This file models exactly that, with a structured interpreter:

* re-executing a `PERFORM` statement while it is still active (recursion, e.g. `GO TO` back
  into the paragraph that performed the range) is undefined in the standard and
  implementation-specific (static save areas and counters on IBM, dynamic frames in other
  compilers): the model reports it as unsupported.  Nested `PERFORM`s sharing an exit point
  are modelled (IBM saves and restores the slot);
* `State.slots` / `State.saves` are the slots and save areas; slots are keyed by exit point
  (end of paragraph `k`, then end of the section closed by `k`, see `ExitPt`);
* reaching an exit point whose slot holds `s` produces the signal `ret s`, which
  propagates outward through active `PERFORM`s until the innermost activation of `s`
  catches it (activations it passes through are abandoned and their slots stay set, as on
  IBM).  If no activation of `s` is active, IBM would resume an abandoned `PERFORM`; the
  model does not follow that and reports `Fault.unsupported` (`Program.run`).

So `GO TO` out of a performed range, `PERFORM` ranges sharing an exit paragraph, and the
classic "`GO TO` the outer range's exit" idiom are all modelled exactly.

## Fuel

`runFrom P env fuel k st` runs paragraphs from `k`.  Fuel is a depth bound: it decreases
at every paragraph transition, `PERFORM` entry and loop iteration.  `outOfFuel` is never a
real outcome: theorems are stated for a sufficient fuel (a numeral, or `n + c` with
`n ≥` the number of loop iterations, as in `Examples/RecSum.lean`), and a theorem that
concludes a real signal (`.stop .goback`) shows that the fuel was sufficient.
-/
import Cobol.Sem.Arith
import Cobol.Sem.File
import Cobol.Sem.Inspect
import Cobol.Sem.Unstring
import Cobol.Sem.StringInto

namespace Cobol
namespace Sem

/-- Result of executing statements. -/
abbrev Res := Signal × State

/-- Set (`some v`) or clear (`none`) key `k` of an association list. -/
def setAssoc {κ : Type} [BEq κ] (l : List (κ × Nat)) (k : κ) : Option Nat → List (κ × Nat)
  | none => l.filter (fun p => p.1 != k)
  | some v => (k, v) :: l.filter (fun p => p.1 != k)

/-- Condition of a loop, as a function of the state (a named function rather than a lambda,
so that symbolic execution does not evaluate it on a symbolic state). -/
def condFn (P : Program) (c : Cond) (st : State) : SemM Bool := evalCond P.cfg st c

/-- No `VARYING` step. -/
def noStep (st : State) : Res := (.normal, st)

/-- One out-of-line `PERFORM` of the range starting at paragraph `first` and returning at
exit point `exit`, by `PERFORM` statement `id`.  `rec` runs paragraphs from a given index
(one fuel level down). -/
def performOnce (rec : Nat → State → Res) (id first : Nat) (exit : ExitPt) (st : State) : Res :=
  if st.active.contains id then (.fault (.unsupported "recursive PERFORM"), st) else
  let st1 := { st with slots := setAssoc st.slots exit (some id),
                       saves := setAssoc st.saves id (st.slots.lookup exit),
                       active := id :: st.active }
  match rec first st1 with
  | (.ret s, st2) =>
    if s = id then
      (.normal, { st2 with slots := setAssoc st2.slots exit (st2.saves.lookup id),
                           active := st.active })
    else (.ret s, { st2 with active := st.active })
  | (sig, st2) => (sig, { st2 with active := st.active })

/-- `PERFORM ... UNTIL` (and `VARYING`) loop.  `step` augments the control variables.

Defined by well-founded recursion on the fuel (not structurally), so that the kernel never
unfolds it: symbolic execution keeps loops whose fuel is `n + k` folded and handles them with
`loopUntil_succ` / `loopUntil_list`; a structural definition let the kernel's definitional
checks run `k` iterations of the body (seconds per iteration for a large loop body). -/
def loopUntil (testAfter : Bool) (cond : State → SemM Bool) (body step : State → Res) :
    Nat → State → Res
  | 0, st => (.outOfFuel, st)
  | n + 1, st =>
    if testAfter then
      match body st with
      | (.normal, st1) | (.exitCycle, st1) =>
        match cond st1 with
        | .error f => (.fault f, st1)
        | .ok true => (.normal, st1)
        | .ok false =>
          match step st1 with
          | (.normal, st2) => loopUntil testAfter cond body step n st2
          | r => r
      | (.exitPerform, st1) => (.normal, st1)
      | r => r
    else
      match cond st with
      | .error f => (.fault f, st)
      | .ok true => (.normal, st)
      | .ok false =>
        match body st with
        | (.normal, st1) | (.exitCycle, st1) =>
          match step st1 with
          | (.normal, st2) => loopUntil testAfter cond body step n st2
          | r => r
        | (.exitPerform, st1) => (.normal, st1)
        | r => r
termination_by n => n

/-- Serial `SEARCH` (`Stmt.search`): `over` ends the search with `atEnd`; otherwise the `WHEN`
conditions are tried (`whens k`: the body of the first true one, or `k` when none is true),
and `k` bumps the index and repeats.  Well-founded on the fuel, like `loopUntil`. -/
def searchLoop (over : State → SemM Bool) (whens : (State → Res) → State → Res)
    (atEnd bump : State → Res) : Nat → State → Res
  | 0, st => (.outOfFuel, st)
  | n + 1, st =>
    match over st with
    | .error f => (.fault f, st)
    | .ok b =>
      if b then atEnd st
      else
        whens (fun st1 =>
          match bump st1 with
          | (.normal, st2) => searchLoop over whens atEnd bump n st2
          | r => r) st
termination_by n => n

/-- The state with index `i` on occurrence `k`. -/
def withIdx (st : State) (i : Nat) (k : Int) : State :=
  { st with idx := (i, k) :: st.idx.filter (fun p => p.1 != i) }

/-- A `SEARCH ALL` key of the element the index is on: a number, or bytes (alphanumeric). -/
def keyVal (c : Config) (st : State) (r : DataRef) : SemM (Int ⊕ List UInt8) :=
  match resolve c st r with
  | .error f => .error f
  | .ok d =>
    match d.kind with
    | .num _ => (Sum.inl ·) <$> evalExpr c st (.ref r)
    | _ => .ok (.inr (readBytes st d))

/-- Elements `k` and `k + 1` are in `KEY` order: the first differing key decides. -/
def keysInOrder : List (Bool × (Int ⊕ List UInt8) × (Int ⊕ List UInt8)) → Bool
  | [] => true
  | (asc, a, b) :: rest =>
    let o := match a, b with
      | .inl x, .inl y => compare x y
      | .inr x, .inr y => cmpBytes x y
      | _, _ => .eq
    match o with
    | .eq => keysInOrder rest
    | .lt => asc
    | .gt => !asc

/-- `SEARCH ALL`: the occurrence satisfying `cond` (`none`: no element does). -/
def searchAllPick (c : Config) (st : State) (i n : Nat) (keys : List (Bool × DataRef))
    (cond : Cond) : SemM (Option Nat) := do
  let vals ← (List.range n).mapM fun (k : Nat) =>
    keys.mapM fun (_, r) => keyVal c (withIdx st i ((k + 1 : Nat) : Int)) r
  let sorted := ((List.range (n - 1)).map fun k =>
    keysInOrder (keys.zip ((vals.getD k []).zip (vals.getD (k + 1) []))
      |>.map fun ((asc, _), (a, b)) => (asc, a, b))).all id
  if !sorted then throw (.unsupported "SEARCH ALL on a table out of KEY order")
  let hits ← (List.range n).filterMapM fun (k : Nat) => do
    let b ← evalCond c (withIdx st i ((k + 1 : Nat) : Int)) cond
    pure (if b then some (k + 1) else none)
  match hits with
  | [] => pure none
  | [k] => pure (some k)
  | _ => throw (.unsupported "SEARCH ALL: several elements satisfy the WHEN condition")

/-- `PERFORM ... n TIMES` (`n` evaluated once). -/
def loopTimes (body : State → Res) : Nat → State → Res
  | 0, st => (.normal, st)
  | k + 1, st =>
    match body st with
    | (.normal, st1) | (.exitCycle, st1) => loopTimes body k st1
    | (.exitPerform, st1) => (.normal, st1)
    | r => r

/-- The integer value of a `TIMES` / index / `DEPENDING ON` expression. -/
def evalInt (c : Config) (st : State) (e : Expr) : SemM Int :=
  match evalExpr c st e with
  | .error f => .error f
  | .ok v => .ok (rescale .truncation v e.scale 0)

/-- Bytes shown by `DISPLAY` for an operand. -/
def displayBytes (c : Config) (st : State) : Operand → SemM (List UInt8)
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      match d.kind with
      | .num f =>
        if f.usage == .display then .ok (readBytes st d)
        else
          match numOf c st d with
          | .error e => .error e
          | .ok (v, _) =>
            .ok (encZoned c { f with usage := .display, signSep := false, signLead := false } v)
      | _ => .ok (readBytes st d)
  | .num v s n =>
    -- the digits as written: a literal's decimal point is an assumed one, "not taking up a
    -- character position" (IBM, numeric literals); IBM gives no form for a sign
    if v < 0 then .error (.unsupported "DISPLAY of a signed numeric literal")
    else .ok (digitChars c (max (if n = 0 then numDigits v.natAbs else n) (max s.toNat 1)) v.natAbs)
  | .alnum bs => .ok bs
  | .fig f => .ok (figBytes c f)
  | .afn f a => afnArg c st (.afn f a)
  | .chr a cs => fnBytes c st (.chr a cs)
  | .amax mx a b pos => fnBytes c st (.amax mx a b pos)

/-- Resolve a list of references. -/
def resolveAll (c : Config) (st : State) : List DataRef → SemM (List FieldDesc)
  | [] => .ok []
  | r :: rs =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      match resolveAll c st rs with
      | .error e => .error e
      | .ok ds => .ok (d :: ds)

/-- `DISPLAY` bytes of a list of operands. -/
def displayAll (c : Config) (st : State) : List Operand → SemM (List (List UInt8))
  | [] => .ok []
  | o :: os =>
    match displayBytes c st o with
    | .error e => .error e
    | .ok b =>
      match displayAll c st os with
      | .error e => .error e
      | .ok bs => .ok (b :: bs)

/-- `CALL`: pass the argument bytes to the environment and store what it returns. -/
def callProg (c : Config) (env : Env) (st : State) (prog : String) (args : List DataRef) :
    SemM State :=
  match resolveAll c st args with
  | .error e => .error e
  | .ok ds =>
    match env.call prog (ds.map (readBytes st)) with
    | none => .error (.unsupported s!"CALL {prog}")
    | some outs =>
      if outs.length = ds.length ∧ (outs.zip ds).all (fun (o, d) => o.length == d.len) then
        let st' := (outs.zip ds).foldl (fun st (o, d) => writeBytes st d o) st
        .ok { st' with out := .call prog :: st'.out }
      else .error (.unsupported s!"CALL {prog}: bad result")

/-- `ACCEPT` from the system input device into a receiving area of `len` bytes, `rs` being the
records not yet read, `acc` the data read so far and `k` the number of records read so far.  IBM
(ACCEPT format 1): "The system input device is read until the receiving area is filled or EOF is
encountered. If the length of the receiving area is not an even multiple of the system input
device record length, the final record will be truncated as required. If EOF is encountered after
data has been moved and before the receiving area has been filled, the receiving area is padded
with spaces … If EOF is encountered before any data has been moved to the receiving area, padding
will not take place and the contents of the receiving area are unchanged. Each input record is
concatenated with the previous input record."  Result: the number of records read, and the new
contents of the area (`none`: unchanged, no byte was read). -/
def sysinRead (c : Config) (len : Nat) : List (List UInt8) → List UInt8 → Nat → Nat × Option (List UInt8)
  | [], acc, k =>
    if len ≤ acc.length then (k, some (acc.take len))
    else (k, if acc.isEmpty then none else some (padRight c acc len))
  | r :: rest, acc, k =>
    if len ≤ acc.length then (k, some (acc.take len)) else sysinRead c len rest (acc ++ r) (k + 1)

/-- `INSPECT … TALLYING`: add each count to its counter, as `ADD count TO counter`. -/
def inspTally (c : Config) (st : State) : List (DataRef × Nat) → SemM State
  | [] => .ok st
  | (r, n) :: rest =>
    match arith c st (.addTo (.lit n)) [{ ref := r }] false with
    | .error f => .error f
    | .ok (st1, _) => inspTally c st1 rest

/-- Run a data operation: normal completion with the new state, or a fault. -/
def lift (st : State) : SemM State → Res
  | .ok st' => (.normal, st')
  | .error f => (.fault f, st)

/-- End of an I/O statement without conditional phrases (`OPEN`, `CLOSE`). -/
def ioFinish (code : Nat) (nx : IoNext) (st : State) : Res :=
  match nx with
  | .abend => (.fault (.io code), st)
  | _ => (.normal, st)

/-- The `USE` declarative for an I/O error on file `d` open in `mode` (for `OPEN`, the mode of
the statement): one naming the file, else one naming that open mode (IBM: "A USE AFTER
EXCEPTION/ERROR declarative statement specifying the name of a file takes precedence over a
declarative statement specifying the open mode of the file"). -/
def useProc? (P : Program) (d : FileDecl) (mode : Option OpenMode) : Option UseProc :=
  match P.useProcs.find? (fun u => u.files.contains d.id) with
  | some u => some u
  | none => P.useProcs.find? (fun u => u.mode.isSome && u.mode == mode)

/-- An I/O statement ended with a status (`1x` to `4x`) that no `AT END` / `INVALID KEY` phrase
handles: run the applicable `USE` declarative as an out-of-line `PERFORM` of its section, then
continue with the next statement (IBM: control returns "to the next executable statement
following the input/output statement whose execution caused the exception").  Without one,
`dflt`: continue when the file has a `FILE STATUS` item, else abend. -/
def ioErr (P : Program) (rec : Nat → State → Res) (d : FileDecl) (mode : Option OpenMode)
    (st : State) (dflt : Res) : Res :=
  match useProc? P d mode with
  | none => dflt
  | some u => performOnce rec u.id u.first u.exit st

/-- End of `OPEN` / `CLOSE`, with the `USE` declarative of an error. -/
def ioFinishU (P : Program) (rec : Nat → State → Res) (d : FileDecl) (mode : Option OpenMode)
    (code : Nat) (nx : IoNext) (st : State) : Res :=
  match nx with
  | .abend => ioErr P rec d mode st (.fault (.io code), st)
  | .cont => ioErr P rec d mode st (.normal, st)
  | _ => (.normal, st)

mutual

/-- Execute one statement.  `rec` runs paragraphs from an index (used by out-of-line
`PERFORM`); `fuel` bounds loop iterations. -/
def execStmt (P : Program) (env : Env) (rec : Nat → State → Res) (fuel : Nat) :
    Stmt → State → Res
  | .move src dsts, st => lift st (move P.cfg st src dsts)
  | .arith op rcv trap onSize notOnSize, st =>
    match arith P.cfg st op rcv trap with
    | .error f => (.fault f, st)
    | .ok (st1, err) =>
      if err then (if trap then execStmts P env rec fuel onSize st1 else (.normal, st1))
      else execStmts P env rec fuel notOnSize st1
  | .divRem a b q rm trap onSize notOnSize, st =>
    match Sem.divRem P.cfg st a b q rm trap with
    | .error f => (.fault f, st)
    | .ok (st1, err) =>
      if err then (if trap then execStmts P env rec fuel onSize st1 else (.normal, st1))
      else execStmts P env rec fuel notOnSize st1
  | .ite c t e, st =>
    match evalCond P.cfg st c with
    | .error f => (.fault f, st)
    | .ok b => if b then execStmts P env rec fuel t st else execStmts P env rec fuel e st
  | .perform id first exit, st => performOnce rec id first exit st
  | .performTimes id n first exit, st =>
    match evalInt P.cfg st n with
    | .error f => (.fault f, st)
    | .ok k => loopTimes (performOnce rec id first exit) k.toNat st
  | .performUntil id ta c first exit, st =>
    loopUntil ta (condFn P c) (performOnce rec id first exit) noStep fuel st
  | .performVarying id ta init c step first exit, st =>
    match execStmts P env rec fuel init st with
    | (.normal, st1) =>
      loopUntil ta (condFn P c) (performOnce rec id first exit) (execStmts P env rec fuel step)
        fuel st1
    | r => r
  | .block body, st => execStmts P env rec fuel body st
  | .inlineTimes n body, st =>
    match evalInt P.cfg st n with
    | .error f => (.fault f, st)
    | .ok k => loopTimes (execStmts P env rec fuel body) k.toNat st
  | .inlineUntil ta c body, st =>
    loopUntil ta (condFn P c) (execStmts P env rec fuel body) noStep fuel st
  | .inlineVarying ta init c step body, st =>
    match execStmts P env rec fuel init st with
    | (.normal, st1) =>
      loopUntil ta (condFn P c) (execStmts P env rec fuel body) (execStmts P env rec fuel step)
        fuel st1
    | r => r
  | .goTo p, st => (.goto p, st)
  | .goToDep e targets, st =>
    match evalInt P.cfg st e with
    | .error f => (.fault f, st)
    | .ok k =>
      if 1 ≤ k ∧ k ≤ targets.length then (.goto (targets.getD (k.toNat - 1) 0), st)
      else (.normal, st)
  | .exitPerform, st => (.exitPerform, st)
  | .exitCycle, st => (.exitCycle, st)
  | .exitPara, st => (.exitPara, st)
  | .exitSection, st => (.exitSection, st)
  | .nextSentence, st => (.nextSentence, st)
  | .cont, st => (.normal, st)
  | .stop k, st => if k == .exitProgram && P.isMain then (.normal, st) else (.stop k, st)
  | .setIdx i e, st =>
    match evalInt P.cfg st e with
    | .error f => (.fault f, st)
    | .ok v => (.normal, { st with idx := (i, v) :: st.idx.filter (fun p => p.1 != i) })
  | .setIdxBy i e down, st =>
    match idxVal st i, evalInt P.cfg st e with
    | .ok cur, .ok v =>
      let nv := if down then cur - v else cur + v
      (.normal, { st with idx := (i, nv) :: st.idx.filter (fun p => p.1 != i) })
    | .error f, _ => (.fault f, st)
    | _, .error f => (.fault f, st)
  | .display ops, st =>
    match displayAll P.cfg st ops with
    | .error f => (.fault f, st)
    | .ok bss => (.normal, { st with out := .display bss.flatten :: st.out })
  | .call prog args, st => lift st (callProg P.cfg env st prog args)
  | .read file recd into atEnd notAtEnd, st =>
    match resolve P.cfg st recd with
    | .error f => (.fault f, st)
    | .ok d =>
      match (st.inp.lookup file).getD [] with
      | [] => execStmts P env rec fuel atEnd st
      | r :: rs =>
        if r.length = d.len then
          let st1 := { writeBytes st d r with
            inp := (file, rs) :: st.inp.filter (fun p => p.1 != file) }
          let st2 := match into with
            | none => Except.ok st1
            | some i => move P.cfg st1 (.ref recd) [i]
          match st2 with
          | .error f => (.fault f, st1)
          | .ok st2 => execStmts P env rec fuel notAtEnd st2
        else (.fault (.unsupported "record length differs from the record area"), st)
  | .write file recd, st =>
    match resolve P.cfg st recd with
    | .error f => (.fault f, st)
    | .ok d => (.normal, { st with out := .write file (readBytes st d) :: st.out })
  | .unsupported what, st => (.fault (.unsupported what), st)
  | .fopen file mode, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "OPEN of an undeclared file"), st)
    | some d =>
      let (code, st1) := fileOpen env d mode st
      -- the open mode a declarative is selected by: the file's, when it is already open (41),
      -- else the mode it is being opened in
      ioFinishU P rec d (some ((fileSt st d.id).mode.getD mode)) code (ioNext d code false false)
        (setStatus P.cfg d code st1)
  | .fclose file, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "CLOSE of an undeclared file"), st)
    | some d =>
      let (code, st1) := fileClose d st
      ioFinishU P rec d (fileSt st d.id).mode code (ioNext d code false false)
        (setStatus P.cfg d code st1)
  | .fread file key into trap exc noExc, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "READ of an undeclared file"), st)
    | some d =>
      match fileRead d key st with
      | .error f => (.fault f, st)
      | .ok (code, st1) =>
        let st1 := if code < 10 then setRecLen P.cfg d st1 else st1
        let st2 := setStatus P.cfg d code st1
        let nx := ioNext d code trap (if key.isNone then atEndCond code else invalidKeyCond code)
        match nx, into with
        | .ok, some i =>
          match move P.cfg st2 (.ref { desc := recordIn d st2 }) [i] with
          | .error f => (.fault f, st2)
          | .ok st3 => execStmts P env rec fuel noExc st3
        | .ok, none => execStmts P env rec fuel noExc st2
        | .exc, _ => execStmts P env rec fuel exc st2
        | .cont, _ => ioErr P rec d (fileSt st d.id).mode st2 (.normal, st2)
        | .abend, _ => ioErr P rec d (fileSt st d.id).mode st2 (.fault (.io code), st2)
  | .fwrite file recd trap exc noExc, st =>
    match fileDecl P file, resolve P.cfg st recd with
    | none, _ => (.fault (.unsupported "WRITE to an undeclared file"), st)
    | _, .error f => (.fault f, st)
    | some d, .ok rd =>
      match recordOut P.cfg d rd st >>= fun bs => fileWrite d bs st with
      | .error f => (.fault f, st)
      | .ok (code, st1) =>
        match ioNext d code trap (d.org == .indexed && invalidKeyCond code) with
        | .ok => execStmts P env rec fuel noExc (setStatus P.cfg d code st1)
        | .exc => execStmts P env rec fuel exc (setStatus P.cfg d code st1)
        | .cont => ioErr P rec d (fileSt st d.id).mode (setStatus P.cfg d code st1)
            (.normal, setStatus P.cfg d code st1)
        | .abend => ioErr P rec d (fileSt st d.id).mode (setStatus P.cfg d code st1)
            (.fault (.io code), setStatus P.cfg d code st1)
  | .frewrite file recd trap exc noExc, st =>
    match fileDecl P file, resolve P.cfg st recd with
    | none, _ => (.fault (.unsupported "REWRITE of an undeclared file"), st)
    | _, .error f => (.fault f, st)
    | some d, .ok rd =>
      match recordOut P.cfg d rd st >>= fun bs => fileRewrite d bs st with
      | .error f => (.fault f, st)
      | .ok (code, st1) =>
        match ioNext d code trap (d.org == .indexed && invalidKeyCond code) with
        | .ok => execStmts P env rec fuel noExc (setStatus P.cfg d code st1)
        | .exc => execStmts P env rec fuel exc (setStatus P.cfg d code st1)
        | .cont => ioErr P rec d (fileSt st d.id).mode (setStatus P.cfg d code st1)
            (.normal, setStatus P.cfg d code st1)
        | .abend => ioErr P rec d (fileSt st d.id).mode (setStatus P.cfg d code st1)
            (.fault (.io code), setStatus P.cfg d code st1)
  | .fdelete file trap exc noExc, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "DELETE of an undeclared file"), st)
    | some d =>
      match fileDelete d st with
      | .error f => (.fault f, st)
      | .ok (code, st1) =>
        match ioNext d code trap (invalidKeyCond code) with
        | .ok => execStmts P env rec fuel noExc (setStatus P.cfg d code st1)
        | .exc => execStmts P env rec fuel exc (setStatus P.cfg d code st1)
        | .cont => ioErr P rec d (fileSt st d.id).mode (setStatus P.cfg d code st1)
            (.normal, setStatus P.cfg d code st1)
        | .abend => ioErr P rec d (fileSt st d.id).mode (setStatus P.cfg d code st1)
            (.fault (.io code), setStatus P.cfg d code st1)
  | .inspect target tally repl, st =>
    match resolve P.cfg st target with
    | .error f => (.fault f, st)
    | .ok td =>
      -- a signed numeric `DISPLAY` item is inspected without its sign (`inspView`)
      match inspView P.cfg td.kind (readBytes st td) with
      | .error f => (.fault f, st)
      | .ok (vw, s) =>
        match inspPhs P.cfg st s tally, inspPhs P.cfg st s repl with
        | .error f, _ => (.fault f, st)
        | _, .error f => (.fault f, st)
        | .ok tp, .ok rp =>
          let (tq, _) := inspScan s tp (s.length + 1) 0 (inspInit tp) s
          let (_, out) := inspScan s rp (s.length + 1) 0 (inspInit rp) s
          let st1 : SemM State :=
            if repl.isEmpty then .ok st else (inspUnview P.cfg vw out).map (writeBytes st td)
          match st1 with
          | .error f => (.fault f, st)
          | .ok st1 =>
            -- the counters are incremented by their phrases' occurrences (an `ADD`)
            lift st (inspTally P.cfg st1 ((tally.zip tq).filterMap fun (ph, q) =>
              ph.counter.map fun c => (c, q.count)))
  | .convert target src dst before after, st =>
    match resolve P.cfg st target with
    | .error f => (.fault f, st)
    | .ok td =>
      match inspView P.cfg td.kind (readBytes st td) with
      | .error f => (.fault f, st)
      | .ok (vw, s) =>
        match (do
            let sb ← inspBytes P.cfg st 1 src
            let db ← inspBytes P.cfg st sb.length dst
            let bb ← match before with
              | some o => some <$> inspBytes P.cfg st 1 o
              | none => pure none
            let ab ← match after with
              | some o => some <$> inspBytes P.cfg st 1 o
              | none => pure none
            pure (sb, db, bb, ab) : SemM _) with
        | .error f => (.fault f, st)
        | .ok (sb, db, bb, ab) =>
          if sb.length ≠ db.length then
            (.fault (.unsupported "INSPECT CONVERTING operands of different lengths"), st)
          else
            match inspRegion s bb ab with
            | none =>
              (.fault (.unsupported "INSPECT: BEFORE delimiter located before the AFTER delimiter"), st)
            | some (lo, hi) =>
              match inspUnview P.cfg vw (inspConvert s sb db lo hi) with
              | .error f => (.fault f, st)
              | .ok out => (.normal, writeBytes st td out)
  | .search over conds bodies bump atEnd, st =>
    searchLoop (condFn P over) (execWhens P env rec fuel conds bodies)
      (execStmts P env rec fuel atEnd) (execStmts P env rec fuel bump) fuel st
  | .fstart file op key trap exc noExc, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "START of an undeclared file"), st)
    | some d =>
      let (code, st1) := fileStart d op key st
      let st2 := setStatus P.cfg d code st1
      match ioNext d code trap (invalidKeyCond code) with
      | .ok => execStmts P env rec fuel noExc st2
      | .exc => execStmts P env rec fuel exc st2
      | .cont => ioErr P rec d (fileSt st d.id).mode st2 (.normal, st2)
      | .abend => ioErr P rec d (fileSt st d.id).mode st2 (.fault (.io code), st2)
  | .searchAll i n keys c body atEnd, st =>
    match searchAllPick P.cfg st i n keys c with
    | .error f => (.fault f, st)
    | .ok none => execStmts P env rec fuel atEnd st
    | .ok (some k) => execStmts P env rec fuel body (withIdx st i (k : Int))
  | .unstring src delims into ptr tally trap ovf notOvf, st =>
    match unstring P.cfg st src delims into ptr tally with
    | .error f => (.fault f, st)
    | .ok (st1, overflow) =>
      if overflow then (if trap then execStmts P env rec fuel ovf st1 else (.normal, st1))
      else execStmts P env rec fuel notOvf st1
  | .stringInto srcs into ptr trap ovf notOvf, st =>
    match stringInto P.cfg st srcs into ptr with
    | .error f => (.fault f, st)
    | .ok (st1, overflow) =>
      if overflow then (if trap then execStmts P env rec fuel ovf st1 else (.normal, st1))
      else execStmts P env rec fuel notOvf st1
  | .setAddress dst ptr, st =>
    match resolve P.cfg st ptr, resolve P.cfg st dst with
    | .ok pd, .ok dd =>
      match pd.kind with
      | .num f =>
        match decodeNum P.cfg f (readBytes st pd) with
        | some p => (.normal, writeBytes st dd ((List.range dd.len).map fun i => env.addrSpace (p.toNat + i)))
        | none => (.fault .invalidData, st)
      | _ => (.fault (.unsupported "SET ADDRESS OF: the pointer is not numeric"), st)
    | .error f, _ => (.fault f, st)
    | _, .error f => (.fault f, st)
  | .callLocal para binds, st =>
    match copyBytes P.cfg st binds with
    | .error f => (.fault f, st)
    | .ok st1 =>
      -- the called program runs with its own PERFORM state; the caller's is restored after
      match rec para { st1 with slots := [], saves := [], active := [] } with
      | (.stop .goback, st2) | (.stop .exitProgram, st2) | (.stop .endOfProgram, st2) =>
        if st2.slots.isEmpty && st2.active.isEmpty then
          match copyBytes P.cfg { st2 with slots := st1.slots, saves := st1.saves, active := st1.active }
              (binds.map fun (a, b) => (b, a)) with
          | .error f => (.fault f, st2)
          | .ok st3 => (.normal, st3)
        else (.fault (.unsupported "CALL: the called program returned inside a PERFORM"), st2)
      | r => r
  | .clock dst start len, st =>
    let bs := ((env.clock st.clockN).drop (start - 1)).take len
    lift st (move P.cfg { st with clockN := st.clockN + 1 } (.alnum bs) [dst])
  | .abend code, st =>
    match evalInt P.cfg st code with
    | .error f => (.fault f, st)
    | .ok k => (.fault (.abend k), st)
  | .accept dst, st =>
    match resolve P.cfg st dst with
    | .error f => (.fault f, st)
    | .ok d =>
      match env.sysin with
      | none => (.fault (.unsupported "ACCEPT: no system input device"), st)
      | some rs =>
        -- the records read so far: `pos` of the file entry `0` (`State.files`)
        let n := (fileSt st 0).pos
        -- the bytes go in unchanged (IBM: "There is no editing or error checking of the incoming data")
        match sysinRead P.cfg d.len (rs.drop n) [] 0 with
        | (k, none) => (.normal, setFile st 0 { fileSt st 0 with pos := n + k })
        | (k, some bs) => (.normal, setFile (writeBytes st d bs) 0 { fileSt st 0 with pos := n + k })
  | .fcloseOpt file opt, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "CLOSE of an undeclared file"), st)
    | some d =>
      match fileCloseOpt env d opt st with
      | .error f => (.fault f, st)
      | .ok (code, st1) =>
        ioFinishU P rec d (fileSt st d.id).mode code (ioNext d code false false)
          (setStatus P.cfg d code st1)
  | .fopenRev file, st =>
    match fileDecl P file with
    | none => (.fault (.unsupported "OPEN of an undeclared file"), st)
    | some d =>
      match fileOpenRev env d st with
      | .error f => (.fault f, st)
      | .ok (code, st1) =>
        -- the open mode a declarative is selected by: as for `OPEN INPUT`
        ioFinishU P rec d (some ((fileSt st d.id).mode.getD .input)) code (ioNext d code false false)
          (setStatus P.cfg d code st1)

/-- Execute a statement list (stops at the first non-`normal` signal). -/
def execStmts (P : Program) (env : Env) (rec : Nat → State → Res) (fuel : Nat) :
    List Stmt → State → Res
  | [], st => (.normal, st)
  | s :: rest, st =>
    match execStmt P env rec fuel s st with
    | (.normal, st') => execStmts P env rec fuel rest st'
    | r => r


/-- The `WHEN` phrases of a `SEARCH`: the statement of the first true condition, or `k` when
none is true. -/
def execWhens (P : Program) (env : Env) (rec : Nat → State → Res) (fuel : Nat) :
    List Cond → List Stmt → (State → Res) → State → Res
  | c :: cs, b :: bs, k, st =>
    match evalCond P.cfg st c with
    | .error f => (.fault f, st)
    | .ok v => if v then execStmt P env rec fuel b st else execWhens P env rec fuel cs bs k st
  | _, _, k, st => k st
end

/-- Execute the sentences of a paragraph (`NEXT SENTENCE` continues with the next one). -/
def execSentences (P : Program) (env : Env) (rec : Nat → State → Res) (fuel : Nat) :
    List (List Stmt) → State → Res
  | [], st => (.normal, st)
  | s :: ss, st =>
    match execStmts P env rec fuel s st with
    | (.normal, st1) | (.nextSentence, st1) => execSentences P env rec fuel ss st1
    | r => r

/-- End of paragraph `k` reached: return to the `PERFORM` whose slot is set at the end of the
paragraph, else at the end of the section it closes, or fall through to the next paragraph. -/
def endOfPara (rec : Nat → State → Res) (slots : List (ExitPt × Nat)) (k : Nat) (st : State) :
    Res :=
  match slots.lookup (.para k) with
  | some s => (.ret s, st)
  | none =>
    match slots.lookup (.sect k) with
    | some s => (.ret s, st)
    | none => rec (k + 1) st

/-- Run paragraphs starting at paragraph `k`. -/
def runFrom (P : Program) (env : Env) : Nat → Nat → State → Res
  | 0, _, st => (.outOfFuel, st)
  | n + 1, k, st =>
    match P.paras[k]? with
    | none => (.stop .endOfProgram, st)
    | some para =>
      match execSentences P env (runFrom P env n) n para.body st with
      | (.normal, st1) | (.exitPara, st1) => endOfPara (runFrom P env n) st1.slots k st1
      | (.exitSection, st1) => endOfPara (runFrom P env n) st1.slots (P.sectionEnd k) st1
      | (.goto l, st1) => runFrom P env n l st1
      | (.exitPerform, st1) | (.exitCycle, st1) | (.nextSentence, st1) =>
        (.fault (.unsupported "EXIT PERFORM outside an inline PERFORM"), st1)
      | r => r

end Sem

/-- Initial storage: `m0` (arbitrary contents) overwritten by the `VALUE` clauses. -/
def Program.initMem (P : Program) (m0 : Mem) : Mem :=
  P.inits.foldl (fun m (o, bs) => m.write o bs) m0

/-- Initial state for storage `m0` and input files `inp`. -/
def Program.initState (P : Program) (m0 : Mem) (inp : List (Nat × List (List UInt8)) := []) :
    State :=
  { mem := P.initMem m0, inp := inp }

/-- Run a program from its first paragraph.  A `ret` reaching the top level means control
reached a paragraph end whose return slot belongs to an abandoned `PERFORM`; IBM would
resume that `PERFORM`, which the model does not follow. -/
def Program.run (P : Program) (env : Env) (fuel : Nat) (st : State) : Sem.Res :=
  match Sem.runFrom P env fuel 0 st with
  | (.ret _, st') => (.fault (.unsupported "return into an abandoned PERFORM"), st')
  | r => r

end Cobol
