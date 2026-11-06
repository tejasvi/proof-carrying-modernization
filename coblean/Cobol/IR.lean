/-
# Normalized COBOL IR

The IR is what an extractor produces from a resolved COBOL AST (copybooks expanded, names
qualified and resolved, `CORRESPONDING` expanded, implicit conversions explicit), after the
Lean-side resolver (`Cobol.Resolve`) has filled in data descriptors from the layout.

Design choices:

* **Data**: every reference carries the resolved `FieldDesc` of the item (offset, length,
  category), so the semantics never looks anything up.  Records stay hierarchical in the
  data division (`Cobol.Layout.Item`); a reference to a group is just the group's byte range.
* **Arithmetic**: expressions are exact over scaled integers.  The only places where digits
  are dropped are explicit: `Expr.div` / `Expr.rescale` carry the intermediate scale and
  rounding mode chosen by the dialect profile; `Expr.ir30` truncates an intermediate result
  that can need more than 30 digits to the decimal places IBM carries; `Expr.powInt` truncates
  a power by an integer exponent (and, for a negative one, 1 divided by it) to `dmax` places;
  `Expr.pow0`, a power by the literal 0, evaluates its base and keeps none of its digits (the
  value is 1; a zero base can be the statement's size error); and stores into receivers round
  by the receiver's `ROUNDED MODE` (`.truncation` when no `ROUNDED`).
* **Control**: paragraphs and sections are kept.  `PERFORM p THRU q` is a primitive with
  IBM's return-slot semantics (see `Cobol.Sem.Exec`), `GO TO`, `GO TO ... DEPENDING`,
  `EXIT PARAGRAPH/SECTION/PERFORM [CYCLE]` and `NEXT SENTENCE` are primitives.  Nothing is
  lowered to a CFG or to runtime-library calls.
-/
import Cobol.Codec
import Cobol.Mem

namespace Cobol

/-- Operand of a subscript or reference modifier: literal, integer data item `± k`, or
index name `± k` (relative subscripting). -/
inductive SubExpr where
  | lit (n : Int)
  | ref (d : FieldDesc) (k : Int := 0)
  | idx (i : Nat) (k : Int := 0)
  deriving DecidableEq, Repr, Inhabited

/-- One subscript: occurrence number (1-based), byte stride of the table, `OCCURS` count. -/
structure Subscript where
  e : SubExpr
  stride : Nat
  max : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Reference modification `(start : length)`; the result is alphanumeric. -/
structure RefMod where
  start : SubExpr
  len : Option SubExpr := none
  deriving DecidableEq, Repr, Inhabited

/-- A data reference.  `desc` describes the first occurrence of the item. -/
structure DataRef where
  /-- Data item id in the data division (traceability; checked by `Program.wf`). -/
  item : Nat := 0
  desc : FieldDesc
  subs : List Subscript := []
  refmod : Option RefMod := none
  deriving DecidableEq, Repr, Inhabited

/-- Figurative constants. -/
inductive Figurative where
  | zero | space | high | low | quote
  /-- `ALL literal`. -/
  | all (bs : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- Alphanumeric intrinsic functions of one alphanumeric argument; the value has the
argument's length. -/
inductive AlnumFn where
  /-- `FUNCTION UPPER-CASE`: the letters `a`-`z` become `A`-`Z`. -/
  | upperCase
  /-- `FUNCTION LOWER-CASE`: the letters `A`-`Z` become `a`-`z`. -/
  | lowerCase
  /-- `FUNCTION REVERSE`: the characters in reverse order. -/
  | reverse
  deriving DecidableEq, Repr, Inhabited

/-- Source operand of `MOVE` and of nonnumeric comparisons. -/
inductive Operand where
  | ref (r : DataRef)
  /-- Numeric literal `v * 10^(-scale)`; `digits` = number of digits as written (used when a
  numeric literal is moved to an alphanumeric item; `0` = minimal). -/
  | num (v : Int) (scale : Int := 0) (digits : Nat := 0)
  /-- Alphanumeric literal, already encoded in the platform character set. -/
  | alnum (bs : List UInt8)
  | fig (f : Figurative)
  /-- An alphanumeric intrinsic function of an alphanumeric item, literal or function. -/
  | afn (f : AlnumFn) (arg : Operand)
  /-- `FUNCTION CHAR (arg)`, `arg` an integer item or literal: the character at that ordinal
  position of the program collating sequence, `chars[arg - 1]` (`chars`: the character of each
  position, the first one given there by the `ALPHABET` clause). -/
  | chr (arg : Operand) (chars : List UInt8)
  /-- `FUNCTION MAX (a, b)` (`max = true`) or `MIN` of alphanumeric arguments, compared by the
  collating positions `pos` (`pos[b]` for byte `b`): `a` unless `b` is greater (less), so a
  left fold over the arguments returns the leftmost greatest (least) one. -/
  | amax (max : Bool) (a b : Operand) (pos : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Integer date functions; integer dates count the days from 1601-01-01 (day 1). -/
inductive DateFn where
  /-- `FUNCTION INTEGER-OF-DATE (YYYYMMDD)`. -/
  | integerOfDate
  /-- `FUNCTION DATE-OF-INTEGER (n)`: `YYYYMMDD`. -/
  | dateOfInteger
  /-- `FUNCTION INTEGER-OF-DAY (YYYYDDD)`. -/
  | integerOfDay
  /-- `FUNCTION DAY-OF-INTEGER (n)`: `YYYYDDD`. -/
  | dayOfInteger
  deriving DecidableEq, Repr, Inhabited

/-- Arithmetic expressions over scaled integers.  Every node has a static scale
(`Expr.scale`); evaluation is exact except where a node says otherwise. -/
inductive Expr where
  | lit (v : Int) (scale : Int := 0)
  | ref (r : DataRef)
  /-- Value of an index name (occurrence number). -/
  | idx (i : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  /-- Quotient computed to `scale` decimal places, rounded by `mode` (the dialect's
  intermediate-precision rule makes this explicit). -/
  | div (a b : Expr) (scale : Int) (mode : RoundingMode := .truncation)
  /-- Explicit intermediate rounding / truncation to `scale`. -/
  | rescale (a : Expr) (scale : Int) (mode : RoundingMode := .truncation)
  /-- `FUNCTION ABS`. -/
  | abs (a : Expr)
  /-- `FUNCTION MIN` / `MAX` of two arguments. -/
  | min (a b : Expr)
  | max (a b : Expr)
  /-- `FUNCTION INTEGER` (floor). -/
  | integer (a : Expr)
  /-- `FUNCTION INTEGER-PART` (truncation). -/
  | integerPart (a : Expr)
  /-- `FUNCTION MOD` (integer arguments, result has the sign of the divisor). -/
  | mod (a b : Expr)
  /-- `FUNCTION REM`: `a - b * INTEGER-PART(a / b)`. -/
  | rem (a b : Expr)
  /-- `FUNCTION FACTORIAL` (an integer argument from 0 to 28). -/
  | factorial (a : Expr)
  /-- An integer date function of an integer argument. -/
  | dateFn (f : DateFn) (a : Expr)
  /-- `FUNCTION ORD (a)`: the ordinal position (from 1) of the one character of `a` in the
  collating sequence, `pos[b] + 1`. -/
  | ord (a : Operand) (pos : List Nat)
  /-- `FUNCTION ORD-MAX` (`max = true`) / `ORD-MIN` of alphanumeric arguments: the position
  (from 1) of the leftmost greatest (least) argument, compared by the collating positions `pos`. -/
  | ordA (max : Bool) (args : List Operand) (pos : List Nat)
  /-- `a ** e` for an exponent `e` that is an integral data item or expression, or a literal for
  which IBM's exponentiation table takes the same action (from 30 digits on), in fixed point with
  `s` (IBM's `dmax`) decimal places: the power `a ^ |n|` truncated to `s` places and, for a negative
  `n`, `1` divided by it, truncated to `s` places (`Sem.powIntVal`). -/
  | powInt (a e : Expr) (s : Int)
  /-- An intermediate result IBM carries with `s` decimal and `ip` integer places because it can
  need more than 30 digits (`ARITH(COMPAT)`): `a` truncated to `s` places (`s ≥ 0`); when an integer
  digit cut there is not 0, IBM writes message IGZ0036W and goes on, which is not modelled
  (`Sem.ir30Val`). -/
  | ir30 (a : Expr) (s : Int) (ip : Nat)
  /-- An intermediate result that can need more than 30 digits where IBM's text leaves the places
  carried open (`why` names the open point): `unsupported` when evaluated. -/
  | ir30open (a : Expr) (why : String)
  /-- `a ** 0` for the literal exponent 0: `a` is evaluated, the value is 1 (scale 0).  IBM: "If the
  value of an expression to be raised to a power is zero, the exponent must have a value greater
  than zero. Otherwise, the size error condition exists" (Language Reference, "Arithmetic
  expressions"); zero raised to zero power: "The SIZE ERROR imperative is executed" when a SIZE
  ERROR clause is present, otherwise "The value returned is 1, and a message is issued" ("SIZE
  ERROR phrases").  With `trap` (the statement has `ON SIZE ERROR`) a zero `a` is the statement's
  size error, signalled as a division by zero is (`Fault.divByZero`, which `Sem.catchDiv` turns
  into it); otherwise the value is 1 (the message is not modelled), except with `notOnly` (the
  statement has `NOT ON SIZE ERROR` and no `ON SIZE ERROR`): there a zero `a` is a size error
  condition that skips that phrase while the value 1 is stored (without `ON SIZE ERROR` the
  resultant identifier is computed; `NOT ON SIZE ERROR` runs only when no size error condition
  exists), which the model does not represent: `unsupported`. -/
  | pow0 (a : Expr) (trap : Bool) (notOnly : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Relational operators. -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- Class conditions. -/
inductive ClassTest where
  | numeric | alphabetic | alphabeticLower | alphabeticUpper
  deriving DecidableEq, Repr, Inhabited

/-- Conditions.  Sign conditions are numeric comparisons with `0`; level-88 condition
names are expanded into comparisons by the resolver. -/
inductive Cond where
  | const (b : Bool)
  /-- Numeric (algebraic) comparison. -/
  | numCmp (op : CmpOp) (a b : Expr)
  /-- Nonnumeric comparison: byte strings, the shorter padded with spaces, compared in the
  native collating sequence. -/
  | alnumCmp (op : CmpOp) (a b : Operand)
  | cls (t : ClassTest) (r : DataRef)
  | not (c : Cond)
  | and (a b : Cond)
  | or (a b : Cond)
  /-- Nonnumeric comparison in a program collating sequence (`PROGRAM COLLATING SEQUENCE` naming
  an `ALPHABET` given by literals): as `alnumCmp`, the characters compared by their positions
  `pos[b]` (characters given with `ALSO` share one). -/
  | alnumCmpSeq (op : CmpOp) (a b : Operand) (pos : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A receiving item of an arithmetic statement and its rounding (`.truncation` = no
`ROUNDED` phrase, `.nearestAwayFromZero` = plain `ROUNDED`). -/
structure Receiver where
  ref : DataRef
  mode : RoundingMode := .truncation
  deriving DecidableEq, Repr, Inhabited

/-- How the new value of each receiver is formed.  Operands are evaluated once, before any
receiver is stored; all combinations are exact and rounded only into the receiver. -/
inductive ArithOp where
  /-- `r := e` (`COMPUTE`, and `ADD`/`SUBTRACT`/`MULTIPLY` ... `GIVING`). -/
  | giving (e : Expr)
  /-- `ADD ... TO r`: `r := r + e`. -/
  | addTo (e : Expr)
  /-- `SUBTRACT ... FROM r`: `r := r - e`. -/
  | subFrom (e : Expr)
  /-- `MULTIPLY e BY r`: `r := r * e`. -/
  | mulBy (e : Expr)
  /-- `DIVIDE e INTO r`: `r := r / e` (exact quotient, rounded into `r`). -/
  | divInto (e : Expr)
  /-- `DIVIDE a BY b GIVING r` / `DIVIDE b INTO a GIVING r`: `r := a / b`. -/
  | divGiving (a b : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- How the run unit ends. -/
inductive StopKind where
  | run | goback | exitProgram
  /-- Control fell off the end of the procedure division (implicit `GOBACK`). -/
  | endOfProgram
  deriving DecidableEq, Repr, Inhabited

/-- Exit point of a `PERFORM` range.  The end of a paragraph and the end of the section it
closes are distinct exit points, checked in this order (IBM / OS/VS behaviour): a pending
`PERFORM ... THRU p` returns at the end of paragraph `p` before a pending `PERFORM s` of the
section `s` ending there. -/
inductive ExitPt where
  /-- End of paragraph `k` (`PERFORM ... THRU paragraph`). -/
  | para (k : Nat)
  /-- End of the section whose last paragraph is `k` (`PERFORM section`, `... THRU section`). -/
  | sect (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Boolean equality of exit points (structural, so that symbolic execution evaluates it). -/
def ExitPt.beq : ExitPt → ExitPt → Bool
  | .para a, .para b => a == b
  | .sect a, .sect b => a == b
  | _, _ => false

instance : BEq ExitPt := ⟨ExitPt.beq⟩

instance : LawfulBEq ExitPt where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, ExitPt.beq]
  rfl {a} := by cases a <;> simp [BEq.beq, ExitPt.beq]

/-! ## Files

A file is declared by `SELECT` + `FD`.  Its contents are a list of records: in file order
for a sequential file, in ascending order of the record key for an indexed (VSAM KSDS) file.
The initial contents come from the environment (`State.inp`); `OPEN`, `READ`, `WRITE`,
`REWRITE`, `DELETE` and `CLOSE` follow IBM Enterprise COBOL, including the `FILE STATUS`
codes and the `AT END` / `INVALID KEY` conditions (`Cobol.Sem.File`). -/

/-- `OPEN` mode. -/
inductive OpenMode where
  | input | output | io | extend
  deriving DecidableEq, Repr, Inhabited

/-- The phrase of a `CLOSE` statement with one (`Stmt.fcloseOpt`; IBM format 1 for sequential files,
format 2 (`LOCK` only) for indexed files): `REEL` and `UNIT` are interchangeable, `WITH` and `FOR`
optional. -/
inductive CloseOpt where
  /-- `REEL` / `UNIT`. -/
  | reel
  /-- `REEL` / `UNIT` `WITH NO REWIND`. -/
  | reelNoRewind
  /-- `REEL` / `UNIT` `FOR REMOVAL`. -/
  | reelRemoval
  /-- `WITH NO REWIND`. -/
  | noRewind
  /-- `WITH LOCK`. -/
  | lock
  deriving DecidableEq, Repr, Inhabited

/-- A `USE AFTER STANDARD EXCEPTION/ERROR PROCEDURE` declarative: the section it heads
(paragraphs `first` to the exit point `exit`, run as an out-of-line `PERFORM` by statement
number `id`) and the files it applies to: the files named (`files`) or every file open in
`mode`.  IBM: a declarative naming the file takes precedence over one naming its open mode. -/
structure UseProc where
  files : List Nat := []
  mode : Option OpenMode := none
  id : Nat
  first : Nat
  exit : ExitPt
  deriving Repr, Inhabited

inductive FileOrg where
  | sequential | indexed
  deriving DecidableEq, Repr, Inhabited

inductive AccessMode where
  | sequential | random | dynamic
  deriving DecidableEq, Repr, Inhabited

/-- A record key: position and length in the record; duplicates allowed. -/
structure KeyDecl where
  off : Nat
  len : Nat
  dups : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A file of the program. -/
structure FileDecl where
  id : Nat
  org : FileOrg := .sequential
  access : AccessMode := .sequential
  /-- The record area (shared by the records of the `FD`). -/
  area : FieldDesc
  /-- `RECORD KEY` (indexed files). -/
  key : Option KeyDecl := none
  /-- `ALTERNATE RECORD KEY`s. -/
  alt : List KeyDecl := []
  /-- `FILE STATUS` item (two bytes). -/
  status : Option FieldDesc := none
  /-- `RECORD VARYING FROM min TO max`: the record lengths a variable-length file allows
  (`none`: fixed length, the record area's). -/
  varying : Option (Nat × Nat) := none
  /-- `DEPENDING ON` item of a variable-length file: the length of the record a `WRITE` writes,
  set by `READ` to the length of the record read. -/
  dependsOn : Option FieldDesc := none
  /-- `SELECT OPTIONAL`: the file may be absent when the run starts (`Env.absent`). -/
  optional : Bool := false
  /-- The key of reference can be an alternate key (the program `START`s the file by one, or
  reads it by one in dynamic access) or an alternate key allows duplicates: the semantics tracks
  the key of reference and the order in which duplicates were placed (`Sem.fileReadK` and the
  other `K` functions).  Set by the resolver; `false`: the key of reference is always the record
  key. -/
  keyRef : Bool := false
  /-- Some `CLOSE … WITH LOCK` of the program names the file: `OPEN` checks the lock
  (`FileSt.locked`, `Sem.fileOpenL`).  Set by the resolver; `false`: the file is never locked. -/
  lockable : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Kind of an `INSPECT` phrase: `CHARACTERS`, `ALL`, `LEADING`, `FIRST`. -/
inductive InspKind where
  | chars | all | leading | first
  deriving DecidableEq, Repr, Inhabited

/-- One phrase of `INSPECT … TALLYING` / `REPLACING`: `CHARACTERS` (`pat = none`) or
`ALL / LEADING / FIRST pat`, the replacement (`REPLACING`), the region delimiters
`BEFORE INITIAL` / `AFTER INITIAL`, and the counter (`TALLYING`). -/
structure InspPhrase where
  kind : InspKind
  pat : Option Operand := none
  rep : Option Operand := none
  before : Option Operand := none
  after : Option Operand := none
  counter : Option DataRef := none
  deriving DecidableEq, Repr, Inhabited

/-- One receiver of `UNSTRING`: `INTO rcv [DELIMITER IN delim] [COUNT IN count]`. -/
structure UnstrInto where
  rcv : DataRef
  delim : Option DataRef := none
  count : Option DataRef := none
  deriving DecidableEq, Repr, Inhabited

/-- Statements.  Paragraph and `PERFORM` statement ids are indices assigned by the
resolver: paragraphs are numbered in source order, `PERFORM` statements uniquely. -/
inductive Stmt where
  /-- `MOVE src TO d1 d2 ...`. -/
  | move (src : Operand) (dsts : List DataRef)
  /-- Arithmetic statement.  `trap` = an `ON SIZE ERROR` phrase is present (size errors
  leave the receiver unchanged and run `onSize`); `notOnSize` runs when no size error
  occurred. -/
  | arith (op : ArithOp) (rcv : List Receiver) (trap : Bool) (onSize notOnSize : List Stmt)
  /-- `DIVIDE a BY b GIVING q REMAINDER r`. -/
  | divRem (a b : Expr) (q r : Receiver) (trap : Bool) (onSize notOnSize : List Stmt)
  | ite (c : Cond) (t e : List Stmt)
  /-- `PERFORM first THRU ...` (out-of-line, once), returning at exit point `exit`.  `id`
  identifies the statement. -/
  | perform (id first : Nat) (exit : ExitPt)
  | performTimes (id : Nat) (n : Expr) (first : Nat) (exit : ExitPt)
  | performUntil (id : Nat) (testAfter : Bool) (c : Cond) (first : Nat) (exit : ExitPt)
  /-- `PERFORM ... VARYING`: `init` sets the control variable(s), `step` augments them. -/
  | performVarying (id : Nat) (testAfter : Bool) (init : List Stmt) (c : Cond)
      (step : List Stmt) (first : Nat) (exit : ExitPt)
  /-- Inline `PERFORM ... END-PERFORM` without a loop phrase (also used for grouping). -/
  | block (body : List Stmt)
  | inlineTimes (n : Expr) (body : List Stmt)
  | inlineUntil (testAfter : Bool) (c : Cond) (body : List Stmt)
  | inlineVarying (testAfter : Bool) (init : List Stmt) (c : Cond) (step body : List Stmt)
  | goTo (p : Nat)
  /-- `GO TO p1 p2 ... DEPENDING ON e` (no jump if `e` is out of range). -/
  | goToDep (e : Expr) (targets : List Nat)
  | exitPerform | exitCycle | exitPara | exitSection | nextSentence
  /-- `CONTINUE` / `EXIT` (no-op). -/
  | cont
  | stop (k : StopKind)
  /-- `SET idx TO e`. -/
  | setIdx (i : Nat) (e : Expr)
  /-- `SET idx UP BY e` (`down = false`) / `DOWN BY e`. -/
  | setIdxBy (i : Nat) (e : Expr) (down : Bool)
  | display (ops : List Operand)
  /-- `CALL prog USING BY REFERENCE args`; the callee is an oracle of the environment. -/
  | call (prog : String) (args : List DataRef)
  /-- `READ file [INTO into] AT END ... NOT AT END ...`; `rec` is the file's record area. -/
  | read (file : Nat) (rec : DataRef) (into : Option DataRef) (atEnd notAtEnd : List Stmt)
  /-- `WRITE rec` to `file`. -/
  | write (file : Nat) (rec : DataRef)
  /-- A statement outside the modelled fragment, kept by the extractor so that execution
  faults exactly where it would run. -/
  | unsupported (what : String)
  /-- `OPEN mode file` / `CLOSE file` (declared files). -/
  | fopen (file : Nat) (mode : OpenMode)
  | fclose (file : Nat)
  /-- `READ file [INTO into]`: `key = none` reads the next record (sequential access),
  `key = some k` the record whose key `k` (`0` = record key, `j + 1` = alternate key `j`)
  equals that field of the record area.  `trap`: an `AT END` / `INVALID KEY` phrase is
  present (statements `exc`); `noExc`: `NOT AT END` / `NOT INVALID KEY`. -/
  | fread (file : Nat) (key : Option Nat) (into : Option DataRef) (trap : Bool)
      (exc noExc : List Stmt)
  /-- `WRITE rec` / `REWRITE rec` (`rec` = a record of the file), `DELETE file`. -/
  | fwrite (file : Nat) (rec : DataRef) (trap : Bool) (exc noExc : List Stmt)
  | frewrite (file : Nat) (rec : DataRef) (trap : Bool) (exc noExc : List Stmt)
  | fdelete (file : Nat) (trap : Bool) (exc noExc : List Stmt)
  /-- `START file KEY op key` (indexed files, `op` = `eq` / `gt` / `ge`): position for
  sequential reading at the first record whose record key (or its leading part `key`)
  satisfies the relation with the value in the record area. -/
  | fstart (file : Nat) (op : CmpOp) (key : KeyDecl) (trap : Bool) (exc noExc : List Stmt)
  /-- Move characters `start ..< start + len` (1-based) of the next clock reading
  (`FUNCTION CURRENT-DATE` format, from the environment) to `dst`: `FUNCTION CURRENT-DATE`,
  `ACCEPT ... FROM DATE / TIME`. -/
  | clock (dst : DataRef) (start len : Nat)
  /-- Abnormal termination with a user abend code (`CALL 'CEE3ABD' USING code`). -/
  | abend (code : Expr)
  /-- `INSPECT target TALLYING … REPLACING …`: the tallying phrases, then the replacing
  phrases (IBM: as two successive `INSPECT` statements). -/
  | inspect (target : DataRef) (tally replace : List InspPhrase)
  /-- `INSPECT target CONVERTING src TO dst [BEFORE | AFTER INITIAL …]`. -/
  | convert (target : DataRef) (src dst : Operand) (before after : Option Operand)
  /-- Serial `SEARCH`: while `over` (the index is past the table) is false, the first true
  `conds[k]` runs `bodies[k]` and ends the search; if none is true, `bump` (the index and the
  `VARYING` item up by one) and test again; once `over` holds, `atEnd` runs. -/
  | search (over : Cond) (conds : List Cond) (bodies : List Stmt) (bump atEnd : List Stmt)
  /-- `SEARCH ALL` of a table of `n` occurrences with index `idx` and `KEY`s (ascending?, the key
  subscripted by the index): the element satisfying `c` runs `body` with the index on it; none
  runs `atEnd`.  A table out of `KEY` order (IBM: unpredictable) and several elements
  satisfying `c` (IBM: any of them) are unsupported. -/
  | searchAll (idx n : Nat) (keys : List (Bool × DataRef)) (c : Cond) (body atEnd : List Stmt)
  /-- `UNSTRING src [DELIMITED BY [ALL] d OR …] INTO … [WITH POINTER ptr] [TALLYING IN tally]
  [ON OVERFLOW onOvf] [NOT ON OVERFLOW notOnOvf]`; `delims`: (`ALL`, delimiter); `trap`: an
  `ON OVERFLOW` phrase is present. -/
  | unstring (src : DataRef) (delims : List (Bool × Operand)) (into : List UnstrInto)
      (ptr tally : Option DataRef) (trap : Bool) (onOvf notOnOvf : List Stmt)
  /-- `STRING src … DELIMITED BY d … INTO into [WITH POINTER ptr] [ON OVERFLOW …]` with a
  source delimited by a value or a `POINTER` (all-`SIZE` `STRING`s are lowered to `MOVE`s):
  `srcs`: (source, delimiter; `none` = `SIZE`); `trap`: an `ON OVERFLOW` phrase is present. -/
  | stringInto (srcs : List (Operand × Option Operand)) (into : DataRef) (ptr : Option DataRef)
      (trap : Bool) (onOvf notOnOvf : List Stmt)
  /-- `SET ADDRESS OF dst TO ptr`: `dst` (a LINKAGE item) becomes the storage at the address in
  `ptr`, taken from the environment's address space; it is copied (the programs only read
  such storage). -/
  | setAddress (dst ptr : DataRef)
  /-- `CALL` of a program linked into this one (`tools/cobolfe/link.py`): its `USING` items get
  the arguments' bytes (`binds`: argument, parameter), its paragraphs run from `para` until
  `GOBACK`, `EXIT PROGRAM` or their end, and the parameters' bytes go back to the arguments. -/
  | callLocal (para : Nat) (binds : List (DataRef × DataRef))
  /-- `ACCEPT dst` from the system input device (`SYSIN`, `SYSIPT`, or no `FROM`): the next
  records of the input stream (`Env.sysin`) fill `dst` (IBM format 1; `Sem.sysinRead`). -/
  | accept (dst : DataRef)
  /-- `CLOSE file` with a phrase (`Sem.fileCloseOpt`). -/
  | fcloseOpt (file : Nat) (opt : CloseOpt)
  /-- `OPEN INPUT file REVERSED` (`Sem.fileOpenRev`). -/
  | fopenRev (file : Nat)
  deriving Repr, Inhabited

/-- A paragraph: a list of sentences (a sentence ends at a separator period; only
`NEXT SENTENCE` can observe sentence boundaries). -/
structure Paragraph where
  name : String := ""
  body : List (List Stmt)
  deriving Repr, Inhabited

/-- A normalized program. -/
structure Program where
  name : String := ""
  cfg : Config := {}
  paras : Array Paragraph
  /-- `secEnd[k]` = index of the last paragraph of the section containing paragraph `k`
  (default `k`: no sections). -/
  secEnd : Array Nat := #[]
  /-- Size of the storage in bytes. -/
  memSize : Nat
  /-- Initial bytes from `VALUE` clauses: `(offset, bytes)`, applied in order. -/
  inits : List (Nat × List UInt8) := []
  /-- Main program (`EXIT PROGRAM` is a no-op) or subprogram. -/
  isMain : Bool := true
  /-- Declared files. -/
  files : List FileDecl := []
  /-- `USE AFTER EXCEPTION/ERROR` declaratives (none: an unhandled I/O error continues when the
  file has a `FILE STATUS` item and abends otherwise, as before declaratives were modelled). -/
  useProcs : List UseProc := []
  deriving Repr, Inhabited

/-- Last paragraph of the section containing paragraph `k`. -/
def Program.sectionEnd (P : Program) (k : Nat) : Nat := P.secEnd.getD k k

/-- Observable events, in execution order. -/
inductive Event where
  | display (bs : List UInt8)
  | write (file : Nat) (bs : List UInt8)
  | call (prog : String)
  /-- `REWRITE` of a record / `DELETE` of the record with this key value. -/
  | rewrite (file : Nat) (bs : List UInt8)
  | delete (file : Nat) (key : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- The place of a record in an alternate key's order: its value of that key, its placement stamp
(`none`: in the file before the run; see `FileSt.stamps`) and its record key.  The order is by
value, then placement (records without a stamp first), then record key (`Sem.altLt`). -/
structure AltPos where
  val : List UInt8
  stamp : Option Nat
  key : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Run-time state of a declared file. -/
structure FileSt where
  /-- `none`: closed. -/
  mode : Option OpenMode := none
  /-- Contents (file order / record-key order). -/
  recs : List (List UInt8) := []
  /-- Sequential access: index of the next record to read. -/
  pos : Nat := 0
  /-- A sequential `READ` has reached the end of the file. -/
  eof : Bool := false
  /-- Record of the last successful `READ` (for a sequential-access `REWRITE` / `DELETE`). -/
  cur : Option Nat := none
  /-- `ACCESS DYNAMIC` indexed files: the file position indicator, as the record key it holds
  and whether the record with that key is itself read next (`true`: set by `OPEN` to the first
  record and by `START` to the record found) or only a higher key is (`false`: set by a `READ`
  to the record read).  It decides whether a record that a `WRITE` inserts at the reading
  position is read next (`none`: an empty file at `OPEN`, so it is).  Unused otherwise. -/
  bound : Option (List UInt8 × Bool) := none
  /-- An `OPTIONAL` file absent when the run started (`Env.absent`) has been created by an `OPEN`
  (`OUTPUT`, `I-O` or `EXTEND`). -/
  created : Bool := false
  /-- Files with `FileDecl.keyRef` only: the key of reference (`0` = record key, `j + 1` =
  alternate key `j`), set by `START` and, in dynamic access, by a keyed `READ`; `OPEN` sets `0`. -/
  kor : Nat := 0
  /-- Files with `FileDecl.keyRef` only, while `kor = j + 1`: the file position indicator, as the
  place of a record in alternate key `j`'s order (`AltPos`) and whether that record is itself
  read next (`true`: set by `START`) or only the records after it are (`false`: set by `READ`). -/
  abound : Option (AltPos × Bool) := none
  /-- Files with `FileDecl.keyRef` only: `((j, k), n)` = the record with record key `k` took its
  value of alternate key `j` (one `WITH DUPLICATES`) with the `n`-th `WRITE` / `REWRITE` that
  stamped (records in the file before the run have no stamp). -/
  stamps : List ((Nat × List UInt8) × Nat) := []
  /-- The next stamp. -/
  nstamp : Nat := 0
  /-- Files with `FileDecl.lockable` only: closed `WITH LOCK`, so no `OPEN` of the file succeeds in
  this run unit (status 38). -/
  locked : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Machine state.

* `slots`: IBM `PERFORM` return slots, exit point `↦` id of the `PERFORM` statement whose
  range ends there (absent = fall through).
* `saves`: save areas of `PERFORM` statements (`id ↦` slot value saved at entry;
  absent = no return pending). -/
structure State where
  mem : Mem
  idx : List (Nat × Int) := []
  slots : List (ExitPt × Nat) := []
  saves : List (Nat × Nat) := []
  /-- `PERFORM` statements currently executing (innermost first).  Re-entering one of them
  is recursion, which IBM implements with static save areas and counters (undefined in the
  standard): the model reports it as unsupported. -/
  active : List Nat := []
  /-- Events, newest first. -/
  out : List Event := []
  /-- Input records per file: the remaining records of an undeclared input file, the
  initial contents of a declared file. -/
  inp : List (Nat × List (List UInt8)) := []
  /-- Declared files touched so far (others: closed, contents from `inp`); under the id `0`, which
  no declared file has, the system input device once read (`Stmt.accept`; `pos`: the number of
  its records read). -/
  files : List (Nat × FileSt) := []
  /-- Number of clock readings so far. -/
  clockN : Nat := 0
  deriving Inhabited

/-- Why execution left the modelled fragment. -/
inductive Fault where
  /-- A numeric item does not hold a valid encoding (IBM: S0C7 or unpredictable). -/
  | invalidData
  /-- Subscript or reference modification out of range (undefined without `SSRANGE`). -/
  | range
  /-- Overlapping sending and receiving items (undefined). -/
  | overlap
  /-- Size error without `ON SIZE ERROR` where the result is undefined
  (`TRUNC(OPT)` binary, or `Config.sizeErrorTruncates = false`). -/
  | sizeUndefined
  /-- Division by zero without `ON SIZE ERROR` (IBM: abend S0CB / S0C9). -/
  | divByZero
  /-- A construct outside the modelled fragment. -/
  | unsupported (what : String)
  /-- An unsuccessful I/O statement (file status `status`) that the program does not handle:
  no applicable `AT END` / `INVALID KEY` phrase and no `FILE STATUS` item (IBM abends). -/
  | io (status : Nat)
  /-- `CALL 'CEE3ABD'`: abnormal termination with a user abend code (`-1`: none given). -/
  | abend (code : Int)
  deriving DecidableEq, Repr, Inhabited

/-- Completion signal of executing statements. -/
inductive Signal where
  | normal
  | goto (p : Nat)
  | exitPerform | exitCycle | exitPara | exitSection | nextSentence
  /-- End of a `PERFORM` range reached; return to `PERFORM` statement `s`. -/
  | ret (s : Nat)
  | stop (k : StopKind)
  | fault (f : Fault)
  | outOfFuel
  deriving DecidableEq, Repr, Inhabited

/-- Environment: behaviour of called programs.  `call prog args` returns the new contents
of the `BY REFERENCE` arguments (same lengths) or `none` (callee failed). -/
structure Env where
  call : String → List (List UInt8) → Option (List (List UInt8)) := fun _ _ => none
  /-- Outcome of `OPEN` of file `f` in a mode: `none` = success, `some status` = failure
  (e.g. `35`: file not found); the file stays closed. -/
  openError : Nat → OpenMode → Option Nat := fun _ _ => none
  /-- `OPTIONAL` files that are not present when the run starts (`true`): an `OPEN` of such a
  file gives status 05 (`Sem.fileOpen`).  No effect on other files (a failing `OPEN` of one
  comes from `openError`). -/
  absent : Nat → Bool := fun _ => false
  /-- The `n`-th clock reading, in `FUNCTION CURRENT-DATE` format (21 characters
  `YYYYMMDDhhmmsshh±hhmm`, in the program's character set). -/
  clock : Nat → List UInt8 := fun _ => []
  /-- The byte at each address of the address space outside the program's storage, for
  `SET ADDRESS OF` (operating-system control blocks). -/
  addrSpace : Nat → UInt8 := fun _ => 0
  /-- The records of the system input device (`SYSIN`), in order, in the program's character set,
  each of its own length (fixed-length format: all of one length, 80 for the usual in-stream
  data); `none`: the run has no system input device, and an `ACCEPT` from it fails (IBM: "If
  this ddname is not defined and your program is not running in the z/OS UNIX environment, the
  ACCEPT statement fails"). -/
  sysin : Option (List (List UInt8)) := none
  deriving Inhabited

end Cobol
