/-
  Jimple/Parser.lean

  A parser for Soot's textual Jimple (one `.jimple` file = one class), producing the AST of
  `Jimple/Syntax.lean`. It follows the SableCC grammar `jimple.scc` (soot-oss/soot, develop
  branch) and the output of Soot's printer:
  * keyword-like names are single-quoted (`'int'`, `'void'`, `'from'`); primitive types are
    recognized quoted or unquoted (the unnamed signature of `dynamicinvoke` prints them
    unquoted), and dotted names may have quoted segments (`java.lang.'annotation'.Retention`);
  * `true`/`false` are the int constants 1/0, `#Infinity`, `#-Infinity`, `#NaN` (with an
    optional `F` for float) the special floating-point constants, and decimal literals are
    rounded correctly to binary64 / binary32 (`JFloat.decimalToDouble`, `decimalToFloat`);
  * string literals use `\"`, `\\`, `\n`, ..., `\uXXXX` (one UTF-16 code unit each); a
    literal that is not well-formed UTF-16 becomes `Const.strUnits`.

  Locals are numbered in declaration order. A label denotes the index of the statement that
  follows it (`stmts.size` if none does), and branch targets and catch clauses are resolved
  to those indices. Comments and annotations are skipped.

  Entry point: `Jimple.Parser.parseClass : String → Except String ClassDecl`; errors carry
  the line number.
-/
import Jimple.Numeric
import Std.Data.HashMap

namespace Jimple.Parser

/-! ## Tokens -/

/-- Tokens. Keywords are not separate tokens but unquoted `word`s, so a quoted name such as
    `'from'` or `'int'` is never taken for a keyword. -/
inductive Tok where
  /-- unquoted identifier (one segment): names, keywords, `<init>`, `<clinit>` -/
  | word (s : String)
  /-- quoted name `'...'`, quotes removed -/
  | quoted (s : String)
  /-- dotted name such as `java.lang.Object` or `a.'b'.C`, quotes removed -/
  | dotted (s : String)
  /-- unsigned integer literal; `nonDec` for hex/octal; optional suffix `L`, `B`, `S`, `C` -/
  | int (v : Nat) (nonDec : Bool) (suffix : Option Char)
  /-- unsigned decimal floating-point literal `m * 10^e`; `isFloat` for an `F` suffix -/
  | float (m : Nat) (e : Int) (isFloat : Bool)
  /-- `#Infinity` (`inf = some false`), `#-Infinity` (`some true`), `#NaN` (`none`) -/
  | special (inf : Option Bool) (isFloat : Bool)
  /-- string literal, as UTF-16 code units -/
  | str (units : Array Nat)
  | sym (s : String)
  | atThis
  | atParam (n : Nat)
  | atCaught
  /-- `@` starting an annotation -/
  | annot
  | eof
  deriving Inhabited

structure PTok where
  tok : Tok
  line : Nat
  /-- the line of a line number tag comment (`/*12*/`) that follows the token, `0` if none -/
  tag : Nat := 0
  deriving Inhabited

namespace Tok

def isSym (t : Tok) (s : String) : Bool := match t with | .sym s' => s' == s | _ => false
def isWord (t : Tok) (s : String) : Bool := match t with | .word s' => s' == s | _ => false
def isEof (t : Tok) : Bool := match t with | .eof => true | _ => false

def describe : Tok → String
  | .word s => s!"'{s}'"
  | .quoted s => s!"quoted name '{s}'"
  | .dotted s => s!"name '{s}'"
  | .int v _ _ => s!"integer constant {v}"
  | .float .. | .special .. => "floating-point constant"
  | .str _ => "string constant"
  | .sym s => s!"'{s}'"
  | .atThis => "'@this:'"
  | .atParam n => s!"'@parameter{n}:'"
  | .atCaught => "'@caughtexception'"
  | .annot => "'@'"
  | .eof => "end of file"

end Tok

/-! ## UTF-16 -/

def pushUtf16 (u : Array Nat) (c : Char) : Array Nat :=
  let n := c.toNat
  if n < 0x10000 then u.push n
  else
    let m := n - 0x10000
    (u.push (0xD800 + m / 0x400)).push (0xDC00 + m % 0x400)

/-- Decode UTF-16 code units. The flag is `true` iff every surrogate is part of a valid pair;
    unpaired surrogates are replaced by U+FFFD. -/
def decodeUtf16 (u : Array Nat) : String × Bool := Id.run do
  let mut s := ""
  let mut ok := true
  let mut i := 0
  while i < u.size do
    let c := u[i]!
    if 0xD800 ≤ c && c < 0xDC00 then
      let d := u.getD (i + 1) 0
      if 0xDC00 ≤ d && d < 0xE000 then
        s := s.push (Char.ofNat (0x10000 + (c - 0xD800) * 0x400 + (d - 0xDC00)))
        i := i + 2
      else
        s := s.push (Char.ofNat 0xFFFD)
        ok := false
        i := i + 1
    else if 0xDC00 ≤ c && c < 0xE000 then
      s := s.push (Char.ofNat 0xFFFD)
      ok := false
      i := i + 1
    else
      s := s.push (Char.ofNat c)
      i := i + 1
  return (s, ok)

/-- The string denoted by UTF-16 code units, if they are well-formed. -/
def utf16ToString? (u : Array Nat) : Option String :=
  let (s, ok) := decodeUtf16 u
  if ok then some s else none

/-! ## Lexer -/

section Lexer

private def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$' || c.toNat ≥ 128
private def isIdChar (c : Char) : Bool := isIdStart c || c.isDigit || c == '-' || c == '#'
private def isHex (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
private def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

private def charAt? (cs : Array Char) (i : Nat) : Option Char := cs[i]?

private def matchesAt (cs : Array Char) (i : Nat) (s : String) : Bool := Id.run do
  let mut k := i
  for c in s.toList do
    if charAt? cs k != some c then return false
    k := k + 1
  return true

private def skipWhile (cs : Array Char) (i : Nat) (p : Char → Bool) : Nat := Id.run do
  let mut k := i
  while k < cs.size && p cs[k]! do
    k := k + 1
  return k

private def digitsVal (cs : Array Char) (a b base : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [a:b] do
    v := v * base + hexVal cs[k]!
  return v

/-- The escape sequence starting at `cs[i] = '\\'`: its UTF-16 code unit and the next index. -/
private def lexEscape (cs : Array Char) (i line : Nat) : Except String (Nat × Nat) := do
  let err := s!"line {line}: invalid escape sequence"
  match charAt? cs (i + 1) with
  | some 'n' => return (10, i + 2)
  | some 't' => return (9, i + 2)
  | some 'r' => return (13, i + 2)
  | some 'b' => return (8, i + 2)
  | some 'f' => return (12, i + 2)
  | some 'u' =>
    let mut v := 0
    for k in [0:4] do
      match charAt? cs (i + 2 + k) with
      | some h => if isHex h then v := v * 16 + hexVal h else throw err
      | none => throw err
    return (v, i + 6)
  | some c =>
    if c == '\\' || c == '"' || c == '\'' || c == '.' || c == '#' || c == ' ' then
      return (c.toNat, i + 2)
    else throw err
  | none => throw err

/-- Unescape the contents of a quoted name; invalid escapes are kept literally (as Soot's
    own parser does). -/
private def unescapeLenient (raw : Array Char) : String := Id.run do
  let mut units : Array Nat := #[]
  let mut j := 0
  while j < raw.size do
    let c := raw[j]!
    if c == '\\' then
      match lexEscape raw j 0 with
      | .ok (u, j') =>
        units := units.push u
        j := j'
      | .error _ =>
        units := units.push c.toNat
        j := j + 1
    else
      units := pushUtf16 units c
      j := j + 1
  return (decodeUtf16 units).1

/-- One segment of a name starting at `i`: a quoted segment `'...'` or an identifier run
    (with escapes). Returns the text, whether it was quoted, and the next index. -/
private def lexSegment (cs : Array Char) (i line : Nat) : Except String (String × Bool × Nat) := do
  if charAt? cs i == some '\'' then
    let mut j := i + 1
    let mut raw : Array Char := #[]
    repeat
      match charAt? cs j with
      | some '\'' => break
      | some c =>
        if c == '\n' || c == '\r' then throw s!"line {line}: unterminated quoted name"
        raw := raw.push c
        j := j + 1
      | none => throw s!"line {line}: unterminated quoted name"
    if raw.isEmpty then throw s!"line {line}: empty quoted name"
    return (unescapeLenient raw, true, j + 1)
  else
    let mut j := i
    let mut units : Array Nat := #[]
    repeat
      match charAt? cs j with
      | some '\\' =>
        let (u, j') ← lexEscape cs j line
        units := units.push u
        j := j'
      | some c =>
        if isIdChar c then
          units := pushUtf16 units c
          j := j + 1
        else break
      | none => break
    return ((decodeUtf16 units).1, false, j)

private def isSegStart (c : Char) : Bool := isIdStart c || c.isDigit || c == '\\' || c == '\''

/-- A (possibly dotted) name starting at `i`. -/
private def lexName (cs : Array Char) (i line : Nat) : Except String (Tok × Nat) := do
  let (s0, q0, j0) ← lexSegment cs i line
  let mut segs := #[s0]
  let mut j := j0
  repeat
    match charAt? cs j, charAt? cs (j + 1) with
    | some '.', some c =>
      if isSegStart c then
        let (s, _, j') ← lexSegment cs (j + 1) line
        segs := segs.push s
        j := j'
      else break
    | _, _ => break
  if segs.size == 1 then
    return (if q0 then .quoted s0 else .word s0, j)
  else
    return (.dotted (".".intercalate segs.toList), j)

private def expStart (cs : Array Char) (j : Nat) : Bool :=
  match charAt? cs j, charAt? cs (j + 1), charAt? cs (j + 2) with
  | some e, some c, c2 =>
    (e == 'e' || e == 'E') &&
      (c.isDigit || ((c == '+' || c == '-') && (c2.map Char.isDigit).getD false))
  | _, _, _ => false

/-- A numeric literal starting at the digit `cs[i]` (the sign is a separate token). -/
private def lexNumber (cs : Array Char) (i line : Nat) : Except String (Tok × Nat) := do
  let bad := s!"line {line}: malformed number"
  let endsWell (j : Nat) : Bool :=
    match charAt? cs j with
    | some c => !(isIdStart c || c.isDigit)
    | none => true
  let intSuffix (j : Nat) : Option Char × Nat :=
    match charAt? cs j with
    | some c => if c == 'L' || c == 'l' || c == 'B' || c == 'S' || c == 'C' then (some c, j + 1)
                else (none, j)
    | none => (none, j)
  if cs[i]! == '0' && (charAt? cs (i + 1) == some 'x' || charAt? cs (i + 1) == some 'X') then
    let e := skipWhile cs (i + 2) isHex
    if e == i + 2 then throw bad
    let (sfx, j) := intSuffix e
    if !endsWell j then throw bad
    return (.int (digitsVal cs (i + 2) e 16) true sfx, j)
  let e1 := skipWhile cs i Char.isDigit
  let frac := charAt? cs e1 == some '.' && ((charAt? cs (e1 + 1)).map Char.isDigit).getD false
  if frac || expStart cs e1 then
    let (fa, fb) := if frac then (e1 + 1, skipWhile cs (e1 + 1) Char.isDigit) else (e1, e1)
    let mut j := fb
    let mut exp : Int := 0
    if expStart cs j then
      let neg := charAt? cs (j + 1) == some '-'
      let a := if charAt? cs (j + 1) == some '-' || charAt? cs (j + 1) == some '+' then j + 2
               else j + 1
      let b := skipWhile cs a Char.isDigit
      let ev : Int := digitsVal cs a b 10
      exp := if neg then -ev else ev
      j := b
    let m := digitsVal cs i e1 10 * 10 ^ (fb - fa) + digitsVal cs fa fb 10
    let isF := charAt? cs j == some 'f' || charAt? cs j == some 'F'
    if isF || charAt? cs j == some 'd' || charAt? cs j == some 'D' then j := j + 1
    if !endsWell j then throw bad
    return (.float m (exp - ((fb - fa : Nat) : Int)) isF, j)
  let octal := cs[i]! == '0' && e1 > i + 1 && (cs.extract (i + 1) e1).all (· ≤ '7')
  let v := if octal then digitsVal cs (i + 1) e1 8 else digitsVal cs i e1 10
  let (sfx, j) := intSuffix e1
  if !endsWell j then throw bad
  return (.int v octal sfx, j)

/-- `#Infinity`, `#-Infinity`, `#NaN`, each with an optional `F`. -/
private def lexSpecial (cs : Array Char) (i line : Nat) : Except String (Tok × Nat) := do
  let (inf, j) ←
    if matchesAt cs (i + 1) "Infinity" then pure (some false, i + 9)
    else if matchesAt cs (i + 1) "-Infinity" then pure (some true, i + 10)
    else if matchesAt cs (i + 1) "NaN" then pure (none, i + 4)
    else throw s!"line {line}: invalid '#' constant"
  let isF := charAt? cs j == some 'f' || charAt? cs j == some 'F'
  return (.special inf isF, if isF then j + 1 else j)

/-- A string literal starting at `cs[i] = '"'`; returns the token, next index and line. -/
private def lexString (cs : Array Char) (i line : Nat) : Except String (Tok × Nat × Nat) := do
  let mut j := i + 1
  let mut ln := line
  let mut units : Array Nat := #[]
  repeat
    match charAt? cs j with
    | none => throw s!"line {line}: unterminated string constant"
    | some '"' => break
    | some '\\' =>
      let (u, j') ← lexEscape cs j ln
      units := units.push u
      j := j'
    | some c =>
      if c == '\n' then ln := ln + 1
      units := pushUtf16 units c
      j := j + 1
  return (.str units, j + 1, ln)

/-- `@this:`, `@parameterN:`, `@caughtexception`, or `@` starting an annotation. The colon
    after `@this` and `@parameterN` is optional. -/
private def lexAt (cs : Array Char) (i : Nat) : Tok × Nat :=
  let endsAt (j : Nat) : Bool := !((charAt? cs j).map isIdChar).getD false
  let colon (j : Nat) : Nat := if charAt? cs j == some ':' then j + 1 else j
  if matchesAt cs (i + 1) "this" && endsAt (i + 5) then (.atThis, colon (i + 5))
  else if matchesAt cs (i + 1) "parameter" then
    let b := skipWhile cs (i + 10) Char.isDigit
    if b > i + 10 && endsAt b then (.atParam (digitsVal cs (i + 10) b 10), colon b)
    else (.annot, i + 1)
  else if matchesAt cs (i + 1) "caughtexception" && endsAt (i + 16) then (.atCaught, i + 16)
  else (.annot, i + 1)

private def symbols2 : List String := [":=", "==", "!=", ">>", ">=", "<<", "<="]
private def symbols1 : List Char :=
  [',', '{', '}', ';', '[', ']', '(', ')', ':', '.', '=', '&', '|', '^', '%', '>', '<', '+', '-',
   '*', '/']

/-- Split Jimple source text into tokens (the last one is `eof`). -/
def tokenize (src : String) : Except String (Array PTok) := do
  let cs := src.toList.toArray
  let mut i := 0
  let mut line := 1
  let mut out : Array PTok := #[]
  while i < cs.size do
    let c := cs[i]!
    if c == '\n' then
      line := line + 1
      i := i + 1
    else if c == ' ' || c == '\t' || c == '\r' || c == '\x0c' || c.toNat == 0xFEFF then
      i := i + 1
    else if c == '/' && charAt? cs (i + 1) == some '/' then
      i := skipWhile cs i (· != '\n')
    else if c == '/' && charAt? cs (i + 1) == some '*' then
      let start := line
      let mut k := i + 2
      while k < cs.size && !(cs[k]! == '*' && charAt? cs (k + 1) == some '/') do
        if cs[k]! == '\n' then line := line + 1
        k := k + 1
      if k ≥ cs.size then throw s!"line {start}: unterminated comment"
      -- a line number tag `/*12*/` belongs to the token before it (the first tag counts)
      if k > i + 2 && skipWhile cs (i + 2) Char.isDigit == k then
        match out.back? with
        | some p => if p.tag == 0 then out := out.pop.push { p with tag := digitsVal cs (i + 2) k 10 }
        | none => pure ()
      i := k + 2
    else if isIdStart c || c == '\\' || c == '\'' then
      let (t, j) ← lexName cs i line
      out := out.push ⟨t, line, 0⟩
      i := j
    else if c.isDigit then
      let (t, j) ← lexNumber cs i line
      out := out.push ⟨t, line, 0⟩
      i := j
    else if c == '"' then
      let (t, j, ln) ← lexString cs i line
      out := out.push ⟨t, line, 0⟩
      i := j
      line := ln
    else if c == '#' then
      let (t, j) ← lexSpecial cs i line
      out := out.push ⟨t, line, 0⟩
      i := j
    else if c == '@' then
      let (t, j) := lexAt cs i
      out := out.push ⟨t, line, 0⟩
      i := j
    else if matchesAt cs i "<init>" then
      out := out.push ⟨.word "<init>", line, 0⟩
      i := i + 6
    else if matchesAt cs i "<clinit>" then
      out := out.push ⟨.word "<clinit>", line, 0⟩
      i := i + 8
    else if matchesAt cs i ">>>" then
      out := out.push ⟨.sym ">>>", line, 0⟩
      i := i + 3
    else
      match symbols2.find? (matchesAt cs i ·) with
      | some s =>
        out := out.push ⟨.sym s, line, 0⟩
        i := i + 2
      | none =>
        if symbols1.contains c then
          out := out.push ⟨.sym (String.singleton c), line, 0⟩
          i := i + 1
        else throw s!"line {line}: unexpected character '{c}'"
  return out.push ⟨.eof, line, 0⟩

end Lexer

/-! ## Printing types (for method handle descriptions and generated names) -/

def primName : PrimType → String
  | .boolean => "boolean" | .byte => "byte" | .char => "char" | .short => "short"
  | .int => "int" | .long => "long" | .float => "float" | .double => "double"

/-- A Jimple type as text, without quotes: `int`, `java.lang.String[]`, ... -/
def typeStr : JType → String
  | .prim p => primName p
  | .cls c => c
  | .array t => typeStr t ++ "[]"
  | .null => "null_type"
  | .unknown => "unknown"
  | .void => "void"

/-- Parameter types separated by commas (no spaces). -/
def paramsStr (ps : List JType) : String := ",".intercalate (ps.map typeStr)

/-! ## Parser -/

abbrev P := ReaderT (Array PTok) (StateT Nat (Except String))

def curTok : P PTok := do
  let ts ← read
  return ts.getD (← get) (ts.back?.getD ⟨.eof, 0, 0⟩)

def peekN (k : Nat) : P Tok := do
  let ts ← read
  return (ts.getD ((← get) + k) (ts.back?.getD ⟨.eof, 0, 0⟩)).tok

def peek : P Tok := peekN 0

def advance : P Unit := modify (· + 1)

/-- The token before the current one. -/
def prevTok : P PTok := do
  let ts ← read
  return ts.getD ((← get) - 1) default

def failAt (line : Nat) (msg : String) : P α := throw s!"line {line}: {msg}"

def fail (msg : String) : P α := do failAt (← curTok).line msg

def expected (what : String) : P α := do
  let t ← curTok
  failAt t.line s!"expected {what}, found {t.tok.describe}"

def expectSym (s : String) : P Unit := do
  if (← peek).isSym s then advance else expected s!"'{s}'"

def expectKw (k : String) : P Unit := do
  if (← peek).isWord k then advance else expected s!"'{k}'"

def acceptSym (s : String) : P Bool := do
  if (← peek).isSym s then
    advance
    return true
  else return false

/-- Reserved words: never names unless quoted. These are the keyword tokens of `jimple.scc`
    that Soot 4.7.1 quotes when it prints them as names (`Jimple.jimpleKeywordList()`);
    `dynamicinvoke` is not in that list, so it is not reserved here either. -/
def keywords : List String :=
  ["abstract", "final", "native", "public", "protected", "private", "static", "synchronized",
   "transient", "volatile", "strictfp", "enum", "annotation", "class", "interface", "void",
   "boolean", "byte", "short", "char", "int", "long", "float", "double", "null_type", "unknown",
   "extends", "implements", "breakpoint", "case", "catch", "cmp", "cmpg", "cmpl", "default",
   "entermonitor", "exitmonitor", "goto", "if", "instanceof", "interfaceinvoke", "lengthof",
   "lookupswitch", "neg", "new", "newarray", "newmultiarray", "nop", "ret", "return",
   "specialinvoke", "staticinvoke", "tableswitch", "throw", "throws", "virtualinvoke", "null",
   "from", "to", "with", "cls", "true", "false"]

def isKeyword (s : String) : Bool := keywords.contains s

def modifierWords : List String :=
  ["abstract", "final", "native", "public", "protected", "private", "static", "synchronized",
   "transient", "volatile", "strictfp", "enum", "annotation"]

def primOf? : String → Option PrimType
  | "boolean" => some .boolean | "byte" => some .byte | "char" => some .char
  | "short" => some .short | "int" => some .int | "long" => some .long
  | "float" => some .float | "double" => some .double | _ => none

/-- A token usable as a local, label, field or method name. -/
def isNameTok : Tok → Bool
  | .word s => !isKeyword s
  | .quoted _ => true
  | _ => false

/-- The type named by a token (array brackets not included). -/
def baseType? : Tok → Option JType
  | .word s =>
    match primOf? s with
    | some p => some (.prim p)
    | none =>
      if s == "void" then some .void
      else if s == "null_type" then some .null
      else if s == "unknown" then some .unknown
      else if isKeyword s || s == "<init>" || s == "<clinit>" then none
      else some (.cls s)
  | .quoted s =>
    match primOf? s with
    | some p => some (.prim p)
    | none => some (if s == "void" then .void else .cls s)
  | .dotted s => some (.cls s)
  | _ => none

def parseType : P JType := do
  let some t := baseType? (← peek) | expected "a type"
  advance
  let mut t := t
  repeat
    if (← peek).isSym "[" && (← peekN 1).isSym "]" then
      advance
      advance
      t := .array t
    else break
  return t

def parseClassName : P ClassName := do
  match ← peek with
  | .word s =>
    if isKeyword s || s == "<init>" || s == "<clinit>" then expected "a class name"
    else
      advance
      return s
  | .quoted s | .dotted s =>
    advance
    return s
  | _ => expected "a class name"

def parseClassNameList : P (List ClassName) := do
  let mut cs : Array ClassName := #[]
  repeat
    cs := cs.push (← parseClassName)
    if !(← acceptSym ",") then break
  return cs.toList

/-- A local, label, field or method name (`<init>` and `<clinit>` included). -/
def parseName : P String := do
  match ← peek with
  | .word s =>
    if isKeyword s then expected "a name"
    else
      advance
      return s
  | .quoted s =>
    advance
    return s
  | _ => expected "a name"

/-- Skip a balanced `(...)` group (annotation parameters). -/
def skipBalanced : P Unit := do
  let start ← curTok
  let mut depth : Nat := 0
  repeat
    let t ← curTok
    advance
    match t.tok with
    | .sym "(" | .sym "{" => depth := depth + 1
    | .sym ")" | .sym "}" =>
      depth := depth - 1
      if depth == 0 then break
    | .eof => failAt start.line "unterminated annotation"
    | _ => pure ()

/-- Skip annotations: `@Name`, optionally followed by `(...)`. -/
def skipAnnotations : P Unit := do
  repeat
    match ← peek with
    | .annot =>
      advance
      match ← peek with
      | .word _ | .quoted _ | .dotted _ => advance
      | _ => pure ()
      if (← peek).isSym "(" then skipBalanced
    | _ => break

/-- `( T1, T2, ... )` (parameter annotations are skipped). -/
def parseParamTypes : P (List JType) := do
  expectSym "("
  if (← acceptSym ")") then return []
  let mut ps : Array JType := #[]
  repeat
    skipAnnotations
    ps := ps.push (← parseType)
    if !(← acceptSym ",") then break
  expectSym ")"
  return ps.toList

/-- `<C: T name` (shared by method and field signatures). -/
def parseSigHead : P (ClassName × JType × String) := do
  expectSym "<"
  let c ← parseClassName
  expectSym ":"
  let t ← parseType
  let n ← parseName
  return (c, t, n)

/-- `<C: T name` where the name may be a keyword: Soot prints the names in method handle
    constants without quoting keywords (`methodhandle: "REF_GET_FIELD" <C: T from>`). -/
def parseSigHeadAny : P (ClassName × JType × String) := do
  expectSym "<"
  let c ← parseClassName
  expectSym ":"
  let t ← parseType
  let n ← match ← peek with
    | .word s => do advance; pure s
    | _ => parseName
  return (c, t, n)

def parseMethodSig : P MethodSig := do
  let (c, t, n) ← parseSigHead
  let ps ← parseParamTypes
  expectSym ">"
  return { cls := c, ret := t, name := n, params := ps }

def parseFieldSig : P FieldSig := do
  let (c, t, n) ← parseSigHead
  expectSym ">"
  return { cls := c, ty := t, name := n }

/-! ### Constants and immediates -/

/-- `x` reduced to the signed range of `w` bits (two's complement). -/
def wrapInt (w : Nat) (x : Int) : Int :=
  let m := x % ((2 ^ w : Nat) : Int)
  if m ≥ ((2 ^ (w - 1) : Nat) : Int) then m - ((2 ^ w : Nat) : Int) else m

/-- Value of an integer literal of width `w` (`neg` for a leading `-`). Decimal literals
    must have magnitude at most `2^(w-1)` (`2^(w-1)` itself denotes the minimum, as in
    Soot's parser); hex/octal literals are bit patterns of at most `w` bits. -/
def intLitValue (neg : Bool) (v : Nat) (nonDec : Bool) (w : Nat) : P Int := do
  if nonDec then
    if v ≥ 2 ^ w then fail "integer constant out of range"
    let s := wrapInt w v
    return if neg then wrapInt w (-s) else s
  else
    if v > 2 ^ (w - 1) then fail "integer constant out of range"
    return wrapInt w (if neg then -(v : Int) else v)

def isLongSuffix (sfx : Option Char) : Bool := sfx == some 'L' || sfx == some 'l'

def intConst (neg : Bool) (v : Nat) (nonDec : Bool) (sfx : Option Char) : P Const := do
  if isLongSuffix sfx then return .long (← intLitValue neg v nonDec 64)
  else return .int (← intLitValue neg v nonDec 32)

def floatConst (neg : Bool) (m : Nat) (e : Int) (isF : Bool) : Const :=
  if isF then .float (JFloat.decimalToFloat neg m e) else .double (JFloat.decimalToDouble neg m e)

def specialConst (neg : Bool) (inf : Option Bool) (isF : Bool) : Const :=
  match inf, isF with
  | some n, true => .float (if n != neg then JFloat.negInf32 else JFloat.posInf32)
  | some n, false => .double (if n != neg then JFloat.negInf64 else JFloat.posInf64)
  | none, true => .float JFloat.nan32
  | none, false => .double JFloat.nan64

def strConst (u : Array Nat) : Const :=
  match utf16ToString? u with
  | some s => .str s
  | none => .strUnits u.toList

/-- A string literal that must be well-formed (class constants, names). -/
def parseStrLit (what : String) : P String := do
  match ← peek with
  | .str u =>
    match utf16ToString? u with
    | some s =>
      advance
      return s
    | none => fail s!"{what} is not well-formed UTF-16"
  | _ => expected what

/-- Parse a constant if the next tokens start one. -/
def parseConst? : P (Option Const) := do
  match ← peek with
  | .sym "-" =>
    advance
    match ← peek with
    | .int v nd sfx =>
      let c ← intConst true v nd sfx
      advance
      return some c
    | .float m e f =>
      advance
      return some (floatConst true m e f)
    | .special inf f =>
      advance
      return some (specialConst true inf f)
    | _ => expected "a number after '-'"
  | .int v nd sfx =>
    let c ← intConst false v nd sfx
    advance
    return some c
  | .float m e f =>
    advance
    return some (floatConst false m e f)
  | .special inf f =>
    advance
    return some (specialConst false inf f)
  | .str u =>
    advance
    return some (strConst u)
  | .word "true" =>
    advance
    return some (.int 1)
  | .word "false" =>
    advance
    return some (.int 0)
  | .word "null" =>
    advance
    return some .null
  | .word "class" =>
    advance
    return some (.clazz (← parseStrLit "a class descriptor string"))
  | .word "methodhandle" =>
    if !(← peekN 1).isSym ":" then return none
    advance
    advance
    let kind ← parseStrLit "a method handle kind string"
    let (c, t, n) ← parseSigHeadAny
    if (← peek).isSym "(" then
      let ps ← parseParamTypes
      expectSym ">"
      return some (.methodHandle s!"{kind} <{c}: {typeStr t} {n}({paramsStr ps})>")
    else
      expectSym ">"
      return some (.methodHandle s!"{kind} <{c}: {typeStr t} {n}>")
  | .word "methodtype" =>
    if !(← peekN 1).isSym ":" then return none
    advance
    advance
    let t ← parseType
    let n ← parseName
    let ps ← parseParamTypes
    return some (.methodHandle s!"methodtype: {typeStr t} {n}({paramsStr ps})")
  | _ => return none

abbrev LocalEnv := Std.HashMap String LocalIdx

def parseLocal (env : LocalEnv) : P LocalIdx := do
  let t ← curTok
  let n ← parseName
  match env.get? n with
  | some x => return x
  | none => failAt t.line s!"undeclared local '{n}'"

def parseImm (env : LocalEnv) : P Imm := do
  match ← parseConst? with
  | some c => return .const c
  | none =>
    if isNameTok (← peek) then return .loc (← parseLocal env)
    else expected "a local or a constant"

def parseArgs (env : LocalEnv) : P (List Imm) := do
  expectSym "("
  if (← acceptSym ")") then return []
  let mut args : Array Imm := #[]
  repeat
    args := args.push (← parseImm env)
    if !(← acceptSym ",") then break
  expectSym ")"
  return args.toList

/-! ### Expressions -/

def binOp? : Tok → Option BinOp
  | .sym "+" => some .add | .sym "-" => some .sub | .sym "*" => some .mul
  | .sym "/" => some .div | .sym "%" => some .rem
  | .sym "&" => some .and | .sym "|" => some .or | .sym "^" => some .xor
  | .sym "<<" => some .shl | .sym ">>" => some .shr | .sym ">>>" => some .ushr
  | .word "cmp" => some .cmp | .word "cmpl" => some .cmpl | .word "cmpg" => some .cmpg
  | .sym "==" => some .eq | .sym "!=" => some .ne
  | .sym "<" => some .lt | .sym "<=" => some .le
  | .sym ">" => some .gt | .sym ">=" => some .ge
  | _ => none

def isCmpOp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def invKind? : Tok → Option InvKind
  | .word "virtualinvoke" => some .virtual
  | .word "specialinvoke" => some .special
  | .word "interfaceinvoke" => some .interface
  | _ => none

def isInvokeStart (t : Tok) : Bool :=
  (invKind? t).isSome || t.isWord "staticinvoke" || t.isWord "dynamicinvoke"

def parseInvoke (env : LocalEnv) : P Invoke := do
  let t ← peek
  if let some k := invKind? t then
    advance
    let base ← parseLocal env
    expectSym "."
    let m ← parseMethodSig
    let args ← parseArgs env
    return .inst k base m args
  else if t.isWord "staticinvoke" then
    advance
    let m ← parseMethodSig
    let args ← parseArgs env
    return .static m args
  else if t.isWord "dynamicinvoke" then
    advance
    let name ← parseStrLit "the name of the dynamicinvoke (a string constant)"
    expectSym "<"
    let ret ← parseType
    let ps ← parseParamTypes
    expectSym ">"
    let args ← parseArgs env
    let bsm ← parseMethodSig
    let bsmArgs ← parseArgs env
    return .dynamic name ret ps args bsm bsmArgs
  else expected "an invoke expression"

/-- Right-hand side of an assignment. -/
def parseExpr (env : LocalEnv) : P Expr := do
  let t ← peek
  match t with
  | .word "new" =>
    advance
    let ct ← curTok
    match ← parseType with
    | .cls c => return .new c
    | _ => failAt ct.line "'new' needs a class type"
  | .word "newarray" =>
    advance
    expectSym "("
    let elem ← parseType
    expectSym ")"
    expectSym "["
    let n ← parseImm env
    expectSym "]"
    return .newArray elem n
  | .word "newmultiarray" =>
    advance
    expectSym "("
    let base ← parseType
    expectSym ")"
    let mut sizes : Array Imm := #[]
    let mut dims := 0
    repeat
      if !(← acceptSym "[") then break
      if !(← acceptSym "]") then
        if dims > sizes.size then fail "newmultiarray: a sized dimension after an unsized one"
        sizes := sizes.push (← parseImm env)
        expectSym "]"
      dims := dims + 1
    if dims == 0 then expected "'['"
    return .newMultiArray base sizes.toList dims
  | .word "neg" =>
    advance
    let a ← parseImm env
    return .unop .neg a
  | .word "lengthof" =>
    advance
    let a ← parseImm env
    return .unop .lengthof a
  | .sym "(" =>
    advance
    let ty ← parseType
    expectSym ")"
    let a ← parseImm env
    return .cast ty a
  | .sym "<" =>
    let f ← parseFieldSig
    return .ref (.staticField f)
  | _ =>
    if isInvokeStart t then
      let i ← parseInvoke env
      return .invoke i
    let t1 ← peekN 1
    if isNameTok t && t1.isSym "." then
      let b ← parseLocal env
      advance
      let f ← parseFieldSig
      return .ref (.instField b f)
    if isNameTok t && t1.isSym "[" then
      let b ← parseLocal env
      advance
      let i ← parseImm env
      expectSym "]"
      return .ref (.arrayElem b i)
    let a ← parseImm env
    let t2 ← peek
    if t2.isWord "instanceof" then
      advance
      let ty ← parseType
      return .instOf a ty
    match binOp? t2 with
    | some op =>
      advance
      let b ← parseImm env
      return .binop op a b
    | none => return .imm a

/-! ### Statements -/

/-- A label reference, with its line for error messages. -/
structure LRef where
  name : String
  line : Nat

/-- A statement whose branch targets are still label names. -/
inductive RStmt where
  | done (s : Stmt)
  | goto (l : LRef)
  | ifGoto (op : BinOp) (a b : Imm) (l : LRef)
  | tableSwitch (key : Imm) (low : Int) (targets : List LRef) (dflt : LRef)
  | lookupSwitch (key : Imm) (cases : List (Int × LRef)) (dflt : LRef)

def parseLabelRef : P LRef := do
  let t ← curTok
  let n ← parseName
  return ⟨n, t.line⟩

/-- `goto L;` -/
def parseGoto : P LRef := do
  expectKw "goto"
  let l ← parseLabelRef
  expectSym ";"
  return l

/-- `(key) { case c: goto L; ... default: goto D; };` (after the keyword). -/
def parseSwitch (env : LocalEnv) (isTable : Bool) : P RStmt := do
  let st ← curTok
  expectSym "("
  let key ← parseImm env
  expectSym ")"
  expectSym "{"
  let mut cases : Array (Int × LRef) := #[]
  let mut dflt : Option LRef := none
  repeat
    let t ← curTok
    match t.tok with
    | .word "case" =>
      advance
      let neg ← acceptSym "-"
      let v ← match ← peek with
        | .int v nd sfx => intLitValue neg v nd (if isLongSuffix sfx then 64 else 32)
        | _ => expected "an integer case value"
      advance
      expectSym ":"
      let l ← parseGoto
      if cases.any (·.1 == v) then failAt t.line s!"duplicate case {v}"
      cases := cases.push (v, l)
    | .word "default" =>
      advance
      expectSym ":"
      let l ← parseGoto
      if dflt.isSome then failAt t.line "duplicate default case"
      dflt := some l
    | .sym "}" =>
      advance
      break
    | _ => expected "'case', 'default' or '}'"
  discard <| acceptSym ";"
  let some d := dflt | failAt st.line "switch without a default case"
  if isTable then
    let low := (cases[0]?.map (·.1)).getD 0
    let mut next := low
    for (v, _) in cases do
      if v != next then failAt st.line "tableswitch cases must be consecutive and ascending"
      next := next + 1
    return .tableSwitch key low (cases.toList.map (·.2)) d
  else
    return .lookupSwitch key cases.toList d

/-- One statement (labels and catch clauses are handled by `parseBody`). `locTys` are the
    declared types of the locals (used by identity statements written without a type). -/
def parseStmt (env : LocalEnv) (locTys : Array JType) : P RStmt := do
  let t ← peek
  match t with
  | .word "nop" =>
    advance
    expectSym ";"
    return .done .nop
  | .word "breakpoint" =>
    advance
    expectSym ";"
    return .done .breakpoint
  | .word "entermonitor" =>
    advance
    let a ← parseImm env
    expectSym ";"
    return .done (.enterMonitor a)
  | .word "exitmonitor" =>
    advance
    let a ← parseImm env
    expectSym ";"
    return .done (.exitMonitor a)
  | .word "goto" =>
    let l ← parseGoto
    return .goto l
  | .word "if" =>
    advance
    let a ← parseImm env
    let opTok ← curTok
    let some op := binOp? opTok.tok | expected "a comparison operator"
    if !isCmpOp op then failAt opTok.line "the condition of 'if' must be a comparison"
    advance
    let b ← parseImm env
    let l ← parseGoto
    return .ifGoto op a b l
  | .word "tableswitch" =>
    advance
    parseSwitch env true
  | .word "lookupswitch" =>
    advance
    parseSwitch env false
  | .word "ret" =>
    advance
    let x ← parseLocal env
    expectSym ";"
    return .done (.ret x)
  | .word "return" =>
    advance
    if (← acceptSym ";") then return .done .returnVoid
    let a ← parseImm env
    expectSym ";"
    return .done (.returnVal a)
  | .word "throw" =>
    advance
    let a ← parseImm env
    expectSym ";"
    return .done (.throw a)
  | .sym "<" =>
    let f ← parseFieldSig
    expectSym "="
    let e ← parseExpr env
    expectSym ";"
    return .done (.assign (.ref (.staticField f)) e)
  | _ =>
    if isInvokeStart t then
      let i ← parseInvoke env
      expectSym ";"
      return .done (.invoke i)
    if !isNameTok t then expected "a statement"
    let x ← parseLocal env
    let t1 ← peek
    if t1.isSym ":=" then
      advance
      let idt ← curTok
      advance
      let optType : P JType := do
        if (← peek).isSym ";" then return locTys.getD x .unknown else parseType
      let r ← match idt.tok with
        | .atThis => IdRef.this <$> optType
        | .atParam n => IdRef.param n <$> optType
        | .atCaught => do
          if !(← peek).isSym ";" then discard parseType
          pure IdRef.caught
        | tok =>
          let msg := s!"expected '@this:', '@parameterN:' or '@caughtexception', found {tok.describe}"
          failAt idt.line msg
      expectSym ";"
      return .done (.identity x r)
    let lhs ← if t1.isSym "=" then pure (LValue.loc x)
      else if t1.isSym "." then do
        advance
        pure (LValue.ref (.instField x (← parseFieldSig)))
      else if t1.isSym "[" then do
        advance
        let i ← parseImm env
        expectSym "]"
        pure (LValue.ref (.arrayElem x i))
      else expected "':=', '=', '.' or '['"
    expectSym "="
    let e ← parseExpr env
    expectSym ";"
    return .done (.assign lhs e)

/-- `catch C from L1 to L2 with L3;` -/
def parseCatch : P (ClassName × LRef × LRef × LRef) := do
  expectKw "catch"
  let c ← parseClassName
  expectKw "from"
  let a ← parseLabelRef
  expectKw "to"
  let b ← parseLabelRef
  expectKw "with"
  let h ← parseLabelRef
  expectSym ";"
  return (c, a, b, h)

/-- Does a local declaration `T x, y;` / `T[] x;` start here? -/
def looksLikeDecl : P Bool := do
  let t0 ← peek
  let t1 ← peekN 1
  let t2 ← peekN 2
  let typeStart := match t0 with
    | .word s => !isKeyword s || (primOf? s).isSome || s == "unknown" || s == "null_type"
    | .quoted _ | .dotted _ => true
    | _ => false
  return typeStart && ((t1.isSym "[" && t2.isSym "]") || isNameTok t1)

def resolveStmt (resolve : LRef → P Label) : RStmt → P Stmt
  | .done s => pure s
  | .goto l => return .goto (← resolve l)
  | .ifGoto op a b l => return .ifGoto op a b (← resolve l)
  | .tableSwitch k low ls d => return .tableSwitch k low (← ls.mapM resolve) (← resolve d)
  | .lookupSwitch k cs d =>
    return .lookupSwitch k (← cs.mapM fun (v, l) => return (v, ← resolve l)) (← resolve d)

/-- `{ declarations statements catch-clauses }` -/
def parseBody : P Body := do
  expectSym "{"
  let mut env : LocalEnv := {}
  let mut locals : Array (String × JType) := #[]
  repeat
    if !(← looksLikeDecl) then break
    let ty ← parseType
    repeat
      let t ← curTok
      let n ← parseName
      if env.contains n then failAt t.line s!"local '{n}' declared twice"
      env := env.insert n locals.size
      locals := locals.push (n, ty)
      if !(← acceptSym ",") then break
    expectSym ";"
  let locTys := locals.map (·.2)
  let mut stmts : Array RStmt := #[]
  let mut labels : Std.HashMap String Label := {}
  let mut catches : Array (ClassName × LRef × LRef × LRef) := #[]
  let mut lines : Array Nat := #[]
  repeat
    let t ← curTok
    if t.tok.isSym "}" then
      advance
      break
    if t.tok.isWord "catch" then
      catches := catches.push (← parseCatch)
      continue
    if !catches.isEmpty then failAt t.line "statement after a catch clause"
    if isNameTok t.tok && (← peekN 1).isSym ":" then
      let n ← parseName
      advance
      if labels.contains n then failAt t.line s!"label '{n}' defined twice"
      labels := labels.insert n stmts.size
      continue
    stmts := stmts.push (← parseStmt env locTys)
    lines := lines.push (← prevTok).tag
  let resolve (l : LRef) : P Label :=
    match labels.get? l.name with
    | some i => pure i
    | none => failAt l.line s!"undefined label '{l.name}'"
  let mut out : Array Stmt := Array.mkEmpty stmts.size
  for s in stmts do
    out := out.push (← resolveStmt resolve s)
  let mut traps : Array Trap := #[]
  for (c, a, b, h) in catches do
    traps := traps.push { exc := c, first := (← resolve a), last := (← resolve b),
                          handler := (← resolve h) }
  return { locals := locals.toList, stmts := out, traps := traps.toList,
           lines := if lines.any (· != 0) then lines else #[] }

/-! ### Classes -/

def parseModifiers : P (List String) := do
  let mut ms : Array String := #[]
  repeat
    match ← peek with
    | .word s =>
      if modifierWords.contains s then
        advance
        ms := ms.push s
      else break
    | _ => break
  return ms.toList

/-- A field `mods T name;` or a method `mods T name(params) throws ... (; | body)`. -/
def parseMember : P (Sum FieldDecl MethodDecl) := do
  skipAnnotations
  let mods ← parseModifiers
  let has := fun (m : String) => mods.contains m
  let ty ← parseType
  let name ← parseName
  if (← acceptSym ";") then
    return .inl { name := name, ty := ty, isStatic := has "static", isFinal := has "final" }
  if !(← peek).isSym "(" then expected "';' or '('"
  let params ← parseParamTypes
  let mut throws : List ClassName := []
  if (← peek).isWord "throws" then
    advance
    throws ← parseClassNameList
  let body ← if (← acceptSym ";") then pure none else some <$> parseBody
  let mm : MethodMods :=
    { isPublic := has "public", isPrivate := has "private", isProtected := has "protected",
      isStatic := has "static", isFinal := has "final", isAbstract := has "abstract",
      isNative := has "native", isSynchronized := has "synchronized" }
  return .inr { name := name, params := params, ret := ty, mods := mm, throws := throws,
                body := body }

def parseFile : P ClassDecl := do
  skipAnnotations
  let mods ← parseModifiers
  let isIface ← match ← peek with
    | .word "class" => do advance; pure false
    | .word "interface" => do advance; pure true
    | _ => expected "'class' or 'interface'"
  let name ← parseClassName
  let mut sup : Option ClassName := none
  if (← peek).isWord "extends" then
    advance
    sup := some (← parseClassName)
  let mut ifaces : List ClassName := []
  if (← peek).isWord "implements" then
    advance
    ifaces ← parseClassNameList
  expectSym "{"
  let mut fields : Array FieldDecl := #[]
  let mut methods : Array MethodDecl := #[]
  repeat
    if (← acceptSym "}") then break
    match ← parseMember with
    | .inl f => fields := fields.push f
    | .inr m => methods := methods.push m
  if !(← peek).isEof then expected "end of file"
  return { name := name, isInterface := isIface, isAbstract := isIface || mods.contains "abstract",
           isEnum := mods.contains "enum", super := sup, interfaces := ifaces,
           fields := fields.toList, methods := methods.toList }

/-- Parse the text of one `.jimple` file. -/
def parseClass (src : String) : Except String ClassDecl := do
  let toks ← tokenize src
  let (c, _) ← (parseFile.run toks).run 0
  return c

end Jimple.Parser
