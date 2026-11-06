/-
# Surface IR: the extraction contract

This is what an extractor emits (as JSON, see `Cobol.Frontend.Load`) from a resolved COBOL
AST plus expanded copybooks.  Compared with the core IR (`Cobol.IR`):

* data references name items by id; the extractor does **not** compute offsets, lengths,
  strides or encodings (the Lean resolver does, from the data division);
* paragraphs / sections are referred to by name;
* literals are source strings (encoded in the program's character set by the resolver);
* a division's intermediate scale may be omitted (the resolver applies the dialect rule);
* level-88 condition names are referred to by id (expanded by the resolver).

Everything a COBOL parser front end already knows after name resolution, nothing more.
-/
import Cobol.Layout

namespace Cobol.Surface

/-- Subscript operand: literal, integer item `± k`, index name `± k`. -/
inductive Sub where
  | lit (n : Int)
  | item (id : Nat) (k : Int := 0)
  | idx (id : Nat) (k : Int := 0)
  deriving Repr, Inhabited

/-- Data reference: item id, subscripts (outermost first), reference modification. -/
structure Ref where
  item : Nat
  subs : List Sub := []
  refStart : Option Sub := none
  refLen : Option Sub := none
  /-- A group containing an `OCCURS DEPENDING ON` table, referenced while the table's object holds
  `v` (`some v`): the group with `v` occurrences of the table (`none`: the declared length, which
  has the maximum number). -/
  odo : Option Nat := none
  deriving Repr, Inhabited

/-- Literals and figurative constants. -/
inductive Lit where
  /-- Numeric literal `v * 10^(-scale)`, `digits` as written. -/
  | num (v : Int) (scale : Int := 0) (digits : Nat := 0)
  /-- Alphanumeric literal (source text). -/
  | str (s : String)
  /-- Hexadecimal literal `X'...'`. -/
  | hex (h : String)
  /-- `ZERO`, `SPACE`, `HIGH-VALUE`, `LOW-VALUE`, `QUOTE`. -/
  | fig (name : String)
  /-- `ALL 'literal'`. -/
  | all (s : String)
  deriving Repr, Inhabited

inductive Operand where
  | ref (r : Ref)
  | lit (l : Lit)
  /-- Alphanumeric intrinsic function (`UPPER-CASE`, `LOWER-CASE`, `REVERSE`) of its argument. -/
  | fn (name : String) (args : List Operand)
  deriving Repr, Inhabited

inductive Expr where
  | lit (v : Int) (scale : Int := 0)
  | ref (r : Ref)
  | idx (id : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  /-- Division; `scale = none`: intermediate scale from the dialect rule. -/
  | div (a b : Expr) (scale : Option Int := none)
  /-- `a ** n` for a literal integer `n ≥ 0`. -/
  | pow (a : Expr) (n : Nat)
  | fn (name : String) (args : List Expr)
  /-- An integer function of alphanumeric arguments (`ORD`, `ORD-MAX`, `ORD-MIN`). -/
  | afn (name : String) (args : List Operand)
  /-- `a ** e` for an exponent `e` that is an integral data item or expression, not a literal
  (lowered to `Cobol.Expr.powInt` with the statement's `dmax`). -/
  | powE (a e : Expr)
  deriving Repr, Inhabited

inductive Cond where
  | const (b : Bool)
  /-- Relation condition `a op b` (`op` ∈ `=` `<>` `<` `<=` `>` `>=`).  The resolver picks
  numeric or nonnumeric comparison from the operands' categories. -/
  | rel (op : String) (a b : Operand)
  /-- Relation with an arithmetic-expression operand (always numeric). -/
  | relExpr (op : String) (a b : Expr)
  /-- Class condition (`NUMERIC`, `ALPHABETIC`, `ALPHABETIC-LOWER`, `ALPHABETIC-UPPER`). -/
  | cls (test : String) (r : Ref)
  /-- Sign condition (`POSITIVE`, `NEGATIVE`, `ZERO`). -/
  | sign (test : String) (e : Expr)
  /-- Level-88 condition name, with the subscripts of its parent. -/
  | cond88 (id : Nat) (subs : List Sub := [])
  | not (c : Cond)
  | and (a b : Cond)
  | or (a b : Cond)
  /-- The object of the `OCCURS DEPENDING ON` table `id` (item id) is within the table's range of
  occurrences: true, or a `range` fault (IBM: undefined when it is outside). -/
  | odoCheck (id : Nat)
  /-- An `EVALUATE` subject compared with an object, one of them an arithmetic expression with a
  division or a power with a variable exponent: as `relExpr`, but with no relational operator
  written, so each operand is evaluated on its own (its own `dmax`, IBM). -/
  | relOwn (op : String) (a b : Expr)
  deriving Repr, Inhabited

/-- Receiving item of an arithmetic statement; `rounded` = `ROUNDED [MODE ...]`
(`"NEAREST-AWAY-FROM-ZERO"` for plain `ROUNDED`). -/
structure Receiver where
  ref : Ref
  rounded : Option String := none
  deriving Repr, Inhabited

/-- Loop phrase of a `PERFORM`. -/
inductive Loop where
  | once
  | times (n : Expr)
  | until (testAfter : Bool) (c : Cond)
  /-- `VARYING v FROM f BY b UNTIL c` of a data item `v`. -/
  | varying (testAfter : Bool) (var : Ref) (fromE byE : Expr) (c : Cond)
  /-- `VARYING i FROM f BY b UNTIL c` of an index name `i`: set and augmented as by `SET i TO f`
  and `SET i UP BY b` (IBM). -/
  | varyingIdx (testAfter : Bool) (idx : Nat) (fromE byE : Expr) (c : Cond)
  deriving Repr, Inhabited

/-- A `KEY` of a table searched by `SEARCH ALL`: ascending?, the key subscripted by the index. -/
structure SearchKey where
  asc : Bool
  key : Ref
  deriving Repr, Inhabited

/-- A delimiter of `UNSTRING`: `[ALL] op`. -/
structure UnstrDelim where
  all : Bool := false
  op : Operand
  deriving Repr, Inhabited

/-- A receiver of `UNSTRING` (`Cobol.UnstrInto`). -/
structure UnstrInto where
  rcv : Ref
  delim : Option Ref := none
  count : Option Ref := none
  deriving Repr, Inhabited

/-- One `INSPECT` phrase (`Cobol.InspPhrase`); `kind`: `"chars"`, `"all"`, `"leading"` or
`"first"`. -/
structure InspPhrase where
  kind : String
  pat : Option Operand := none
  rep : Option Operand := none
  before : Option Operand := none
  after : Option Operand := none
  counter : Option Ref := none
  deriving Repr, Inhabited

/-- The sources of a `STRING` sharing one `DELIMITED BY` phrase (`none` = `SIZE`). -/
structure StrGroup where
  srcs : List Operand
  delim : Option Operand := none
  deriving Repr, Inhabited

inductive Stmt where
  | move (src : Operand) (dsts : List Ref)
  /-- `COMPUTE r... = e`. -/
  | compute (rcv : List Receiver) (e : Expr) (onSize : Option (List Stmt)) (notOnSize : List Stmt)
  /-- `ADD a... TO r...` / `ADD a... GIVING r...` (`giving = true`). -/
  | add (ops : List Expr) (rcv : List Receiver) (giving : Bool) (onSize : Option (List Stmt))
      (notOnSize : List Stmt)
  /-- `SUBTRACT a... FROM m` / `... FROM r...`: with `giving = some m`, `r := m - Σa`. -/
  | subtract (ops : List Expr) (rcv : List Receiver) (giving : Option Expr)
      (onSize : Option (List Stmt)) (notOnSize : List Stmt)
  /-- `MULTIPLY a BY r...` / `MULTIPLY a BY b GIVING r...`. -/
  | multiply (a : Expr) (rcv : List Receiver) (giving : Option Expr)
      (onSize : Option (List Stmt)) (notOnSize : List Stmt)
  /-- `DIVIDE a INTO r...` (`giving = none`) / `DIVIDE ... GIVING r...` (`dividend/divisor`). -/
  | divide (dividend divisor : Expr) (rcv : List Receiver) (giving : Bool)
      (remainder : Option Ref) (onSize : Option (List Stmt)) (notOnSize : List Stmt)
  | ite (c : Cond) (t e : List Stmt)
  /-- `EVALUATE` already lowered to `WHEN` arms: first true condition wins. -/
  | evaluate (arms : List (Cond × List Stmt)) (other : List Stmt)
  /-- Out-of-line `PERFORM first [THRU last]` (paragraph or section names). -/
  | perform (first : String) (last : Option String) (loop : Loop)
  /-- Inline `PERFORM ... END-PERFORM`. -/
  | performInline (body : List Stmt) (loop : Loop)
  | goTo (target : String)
  | goToDep (targets : List String) (e : Expr)
  | exitPerform | exitCycle | exitPara | exitSection | nextSentence | cont
  | stopRun | goback | exitProgram
  | setIdx (id : Nat) (e : Expr)
  | setIdxBy (id : Nat) (e : Expr) (down : Bool)
  /-- `SET condition-name TO TRUE`. -/
  | setTrue (id : Nat) (subs : List Sub := [])
  | display (ops : List Operand)
  | initialize (dsts : List Ref)
  | call (prog : String) (args : List Ref)
  | read (file : Nat) (rec : Ref) (into : Option Ref) (atEnd notAtEnd : List Stmt)
  | write (file : Nat) (rec : Ref)
  /-- A statement the extractor cannot express (execution faults there). -/
  | unsupported (what : String)
  /-- `OPEN` (`mode`: `"INPUT"`, `"OUTPUT"`, `"I-O"`, `"EXTEND"`) / `CLOSE` of a declared file. -/
  | fopen (file : Nat) (mode : String)
  | fclose (file : Nat)
  /-- `READ file [INTO into]`; `key`: the key of reference (item id) of a keyed `READ`,
  `none` for the next record.  `trap`: `AT END` / `INVALID KEY` phrase present. -/
  | fread (file : Nat) (key : Option Nat) (into : Option Ref) (trap : Bool) (exc noExc : List Stmt)
  /-- `WRITE rec` / `REWRITE rec` (`FROM` already lowered to a `MOVE`), `DELETE file`. -/
  | fwrite (file : Nat) (rec : Ref) (trap : Bool) (exc noExc : List Stmt)
  | frewrite (file : Nat) (rec : Ref) (trap : Bool) (exc noExc : List Stmt)
  | fdelete (file : Nat) (trap : Bool) (exc noExc : List Stmt)
  /-- `START file [KEY op key]` (`op`: `"="`, `">"`, `">="`; no `KEY`: the record key, `=`). -/
  | fstart (file : Nat) (op : String) (key : Option Nat) (trap : Bool) (exc noExc : List Stmt)
  /-- Characters `start ..< start + len` of the clock reading (`FUNCTION CURRENT-DATE`
  format) moved to `dst`. -/
  | clock (dst : Ref) (start len : Nat)
  /-- `CALL 'CEE3ABD' USING code ...`. -/
  | abend (code : Expr)
  /-- `INSPECT target TALLYING … REPLACING …`. -/
  | inspect (target : Ref) (tally replace : List InspPhrase)
  /-- `INSPECT target CONVERTING src TO dst [BEFORE | AFTER INITIAL …]`. -/
  | convert (target : Ref) (src dst : Operand) (before after : Option Operand)
  /-- Serial `SEARCH` of a table with index `idx` and `occurs` occurrences, `VARYING` another
  index (`varIdx`) or an integer item (`varRef`), the `AT END` statements, and the `WHEN`
  conditions with their statements. -/
  | search (idx occurs : Nat) (varIdx : Option Nat) (varRef : Option Ref) (atEnd : List Stmt)
      (conds : List Cond) (bodies : List (List Stmt))
  /-- `SEARCH ALL` of a table with index `idx`, `occurs` occurrences and `keys`. -/
  | searchAll (idx occurs : Nat) (keys : List SearchKey) (atEnd : List Stmt) (c : Cond)
      (body : List Stmt)
  /-- `UNSTRING src DELIMITED BY … INTO … WITH POINTER … TALLYING IN … ON OVERFLOW …`. -/
  | unstring (src : Ref) (delims : List UnstrDelim) (into : List UnstrInto) (ptr tally : Option Ref)
      (onOvf : Option (List Stmt)) (notOnOvf : List Stmt)
  /-- `STRING …` with a source delimited by a value or with a `POINTER`. -/
  | stringInto (groups : List StrGroup) (into : Ref) (ptr : Option Ref)
      (onOvf : Option (List Stmt)) (notOnOvf : List Stmt)
  /-- `SET ADDRESS OF dst TO ptr`. -/
  | setAddress (dst ptr : Ref)
  /-- `CALL` of a linked program: its first paragraph and the (argument, parameter) pairs. -/
  | callLocal (para : String) (binds : List (Ref × Ref))
  /-- `CALL` of a program that is not in the run unit (`tools/cobolfe/unit.py`, `link.py`): named by
  the literal `prog` with an `ON EXCEPTION` (`onExc`) or `NOT ON EXCEPTION` phrase, or by the value
  of `target` (`CALL identifier`, no program of the run unit has that name).  Whether such a program
  is available is not modelled: the resolver makes it `unsupported`. -/
  | callDyn (prog : Option String) (target : Option Ref) (args : List Ref)
      (onExc : Option (List Stmt)) (notOnExc : List Stmt)
  /-- `CANCEL` of a program (named by `prog`, or by the value of `target`) that the extractor and
  `link.py` did not find among the programs linked into the program that cancels it: the resolver
  makes it `unsupported`. -/
  | cancel (prog : Option String) (target : Option Ref)
  /-- `ACCEPT dst` from the system input device (`Cobol.Stmt.accept`). -/
  | accept (dst : Ref)
  /-- `CLOSE file` with a phrase (`opt`: `"REEL"`, `"REEL-NO-REWIND"`, `"REEL-REMOVAL"`, `"NO-REWIND"`,
  `"LOCK"`; `UNIT` is written as `REEL`), `Cobol.Stmt.fcloseOpt`. -/
  | fcloseOpt (file : Nat) (opt : String)
  /-- `OPEN INPUT file REVERSED` (`Cobol.Stmt.fopenRev`). -/
  | fopenRev (file : Nat)
  deriving Repr, Inhabited

/-- A file (`SELECT` + `FD`), by item ids. -/
structure FileDecl where
  id : Nat
  /-- `"sequential"` or `"indexed"`. -/
  org : String := "sequential"
  /-- `"sequential"`, `"random"` or `"dynamic"`. -/
  access : String := "sequential"
  /-- The record area: the first record description of the `FD`. -/
  record : Nat
  /-- `RECORD KEY` item. -/
  key : Option Nat := none
  /-- `ALTERNATE RECORD KEY` items, with `WITH DUPLICATES`. -/
  alt : List (Nat × Bool) := []
  /-- `FILE STATUS` item. -/
  status : Option Nat := none
  /-- `RECORD VARYING [FROM minLen] [TO maxLen]` / `RECORD CONTAINS minLen TO maxLen`
  (variable-length records). -/
  minLen : Option Nat := none
  maxLen : Option Nat := none
  /-- `DEPENDING ON` item of a variable-length file. -/
  dependsOn : Option Nat := none
  /-- `SELECT OPTIONAL` (`some true`; the JSON key is left out for other files). -/
  optional : Option Bool := none
  deriving Repr, Inhabited

structure Paragraph where
  name : String
  sect : Option String := none
  sentences : List (List Stmt)
  deriving Repr, Inhabited

/-- A `USE AFTER STANDARD EXCEPTION/ERROR PROCEDURE` declarative: the section it heads and the
files it applies to (file ids, or an open mode `INPUT` / `OUTPUT` / `I-O` / `EXTEND`). -/
structure UseDecl where
  sect : String
  files : List Nat := []
  mode : Option String := none
  deriving Repr, Inhabited

/-- One phrase of the literal list of an `ALPHABET` clause: `lit [THROUGH thru]` or `lit ALSO
also…`. A literal is an alphanumeric literal (each character its own position; one character
with `THROUGH` or `ALSO`), a numeric literal (the character at that ordinal position of the
native character set) or a figurative constant (`HIGH-VALUE` and `LOW-VALUE` of the native set). -/
structure AlphaPhrase where
  lit : Lit
  thru : Option Lit := none
  also : List Lit := []
  deriving Repr, Inhabited

/-- An `OCCURS integer-1 TO integer-2 DEPENDING ON` table: the table item (its `OCCURS` count in
the data division is `integer-2`), `integer-1` and the object (an integer item). -/
structure OdoDecl where
  subject : Nat
  min : Nat
  obj : Nat
  deriving Repr, Inhabited

/-- Dialect options of the resolver (not part of the run-time semantics). -/
structure Dialect where
  /-- Extra decimal place carried by division intermediates when a receiver is `ROUNDED`. -/
  divExtraForRounded : Bool := true
  deriving Repr, Inhabited

structure Program where
  name : String := ""
  config : Config := {}
  dialect : Dialect := {}
  data : List Item
  paras : List Paragraph
  isMain : Bool := true
  files : List FileDecl := []
  /-- `USE` declaratives (their sections are among `paras`). -/
  use : List UseDecl := []
  /-- `PROGRAM COLLATING SEQUENCE` naming an `ALPHABET` given by literals: its phrases (absent:
  the native collating sequence, also when the alphabet is `NATIVE` or the native code set). -/
  collating : Option (List AlphaPhrase) := none
  /-- `OCCURS DEPENDING ON` tables (the JSON key is left out for programs without one). -/
  odo : Option (List OdoDecl) := none
  deriving Repr, Inhabited

end Cobol.Surface
