/-
  Lexer for the textual (pretty) form of ClangIR / MLIR.

  Produces a flat token array with line numbers. Line numbers matter to the
  parser: the MLIR printer puts one operation per line, so "the rest of the
  current line" is a reliable way to skip trailing attribute dictionaries and
  `loc(...)` annotations, and to skip operations the AST does not model.
-/

namespace CIR.Frontend

inductive TokKind where
  /-- `%name` (text without `%`) -/
  | percent
  /-- `@name` or `@"quoted"` (text without `@`, quotes and escapes kept) -/
  | at
  /-- `^bb1` (text without `^`) -/
  | caret
  /-- `!name`, e.g. `!s32i`, `!cir.ptr` (text without `!`) -/
  | bang
  /-- `#name`, e.g. `#cir.int`, `#loc3`, `#true` (text without `#`) -/
  | hash
  /-- bare identifier / keyword, e.g. `cir.load`, `align`, `x` -/
  | ident
  /-- integer literal (decimal, optionally negative, or `0x...`) -/
  | int
  /-- floating point literal -/
  | float
  /-- string literal: raw text between the quotes, escapes not decoded -/
  | str
  /-- punctuation: `( ) { } [ ] < > , : = -> ... * ? +` -/
  | punct
  | eof
  deriving Repr, DecidableEq, Inhabited

structure Token where
  kind : TokKind
  text : String
  line : Nat
  deriving Repr, Inhabited

namespace Lex

@[inline] def u (c : Char) : UInt8 := c.toNat.toUInt8

@[inline] def isDigit (c : UInt8) : Bool := c ≥ u '0' && c ≤ u '9'
@[inline] def isHex (c : UInt8) : Bool :=
  isDigit c || (c ≥ u 'a' && c ≤ u 'f') || (c ≥ u 'A' && c ≤ u 'F')
@[inline] def isAlpha (c : UInt8) : Bool :=
  (c ≥ u 'a' && c ≤ u 'z') || (c ≥ u 'A' && c ≤ u 'Z')
/-- Characters allowed after the first one in names (`%x`, `@x`, `!x`, `#x`,
identifiers). -/
@[inline] def isNameChar (c : UInt8) : Bool :=
  isAlpha c || isDigit c || c == u '_' || c == u '$' || c == u '.'

/-- Bytes `[i, j)` as a string (assumed ASCII/UTF-8). -/
def slice (b : ByteArray) (i j : Nat) : String :=
  let sub := b.extract i j
  match String.fromUTF8? sub with
  | some s => s
  | none => String.ofList (sub.toList.map fun x => Char.ofNat x.toNat)

end Lex

open Lex in
/-- Tokenize CIR text. Comments (`// ...`) are dropped. -/
partial def lex (src : String) : Except String (Array Token) := do
  let b := src.toUTF8
  let n := b.size
  let rec go (i : Nat) (line : Nat) (acc : Array Token) : Except String (Array Token) := do
    if i ≥ n then
      return acc.push { kind := .eof, text := "", line := line }
    let c := b.get! i
    -- whitespace
    if c == u '\n' then go (i+1) (line+1) acc
    else if c == u ' ' || c == u '\t' || c == u '\r' then go (i+1) line acc
    -- comment
    else if c == u '/' && i+1 < n && b.get! (i+1) == u '/' then
      let rec skipLine (j : Nat) : Nat :=
        if j ≥ n then j else if b.get! j == u '\n' then j else skipLine (j+1)
      go (skipLine i) line acc
    -- string literal
    else if c == u '"' then
      let rec scanStr (j : Nat) : Except String Nat :=
        if j ≥ n then .error s!"line {line}: unterminated string"
        else
          let d := b.get! j
          if d == u '\\' then scanStr (j+2)
          else if d == u '"' then .ok j
          else scanStr (j+1)
      let j ← scanStr (i+1)
      go (j+1) line (acc.push { kind := .str, text := slice b (i+1) j, line := line })
    -- sigils
    else if c == u '%' || c == u '@' || c == u '^' || c == u '!' || c == u '#' then
      let kind : TokKind :=
        if c == u '%' then .percent else if c == u '@' then .at
        else if c == u '^' then .caret else if c == u '!' then .bang else .hash
      if c == u '@' && i+1 < n && b.get! (i+1) == u '"' then
        -- @"quoted symbol"
        let rec scanQuoted (j : Nat) : Except String Nat :=
          if j ≥ n then .error s!"line {line}: unterminated quoted symbol"
          else
            let d := b.get! j
            if d == u '\\' then scanQuoted (j+2)
            else if d == u '"' then .ok j
            else scanQuoted (j+1)
        let j ← scanQuoted (i+2)
        go (j+1) line (acc.push { kind := .at, text := slice b (i+2) j, line := line })
      else
        let rec scanName (j : Nat) : Nat :=
          -- `-` also occurs in type aliases derived from file paths (lambda
          -- types: `!rec_…cir2c-eb2a332…`), but never as the arrow `->`
          if j < n && (isNameChar (b.get! j) || b.get! j == u '-' &&
              (kind == .percent || ((kind == .bang || kind == .hash) && j+1 < n &&
                b.get! (j+1) != u '>'))) then
            scanName (j+1) else j
        let j := scanName (i+1)
        go j line (acc.push { kind := kind, text := slice b (i+1) j, line := line })
    -- numbers (also negative numbers)
    else if isDigit c || (c == u '-' && i+1 < n && isDigit (b.get! (i+1))) then
      let start := i
      let i0 := if c == u '-' then i+1 else i
      if b.get! i0 == u '0' && i0+1 < n && (b.get! (i0+1) == u 'x' || b.get! (i0+1) == u 'X')
          && i0+2 < n && isHex (b.get! (i0+2)) then
        let rec scanHex (j : Nat) : Nat := if j < n && isHex (b.get! j) then scanHex (j+1) else j
        let j := scanHex (i0+2)
        go j line (acc.push { kind := .int, text := slice b start j, line := line })
      else
        let rec scanDigits (j : Nat) : Nat := if j < n && isDigit (b.get! j) then scanDigits (j+1) else j
        let j := scanDigits i0
        -- fraction
        let (j, isFloat) :=
          if j+1 < n && b.get! j == u '.' && isDigit (b.get! (j+1)) then (scanDigits (j+1), true)
          else (j, false)
        -- exponent
        let (j, isFloat) :=
          if j < n && (b.get! j == u 'e' || b.get! j == u 'E') then
            let k := if j+1 < n && (b.get! (j+1) == u '+' || b.get! (j+1) == u '-') then j+2 else j+1
            if k < n && isDigit (b.get! k) then (scanDigits k, true) else (j, isFloat)
          else (j, isFloat)
        go j line (acc.push { kind := if isFloat then .float else .int, text := slice b start j, line := line })
    -- identifiers
    else if isAlpha c || c == u '_' then
      let rec scanIdent (j : Nat) : Nat := if j < n && isNameChar (b.get! j) then scanIdent (j+1) else j
      let j := scanIdent (i+1)
      go j line (acc.push { kind := .ident, text := slice b i j, line := line })
    -- multi-character punctuation
    else if c == u '-' && i+1 < n && b.get! (i+1) == u '>' then
      go (i+2) line (acc.push { kind := .punct, text := "->", line := line })
    else if c == u '.' && i+2 < n && b.get! (i+1) == u '.' && b.get! (i+2) == u '.' then
      go (i+3) line (acc.push { kind := .punct, text := "...", line := line })
    else
      go (i+1) line (acc.push { kind := .punct, text := slice b i (i+1), line := line })
  go 0 1 #[]

/-! ## String literal decoding (MLIR escapes: `\\`, `\"`, `\n`, `\t`, `\XX`) -/

namespace Lex

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def isHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Decode the raw text of a string token into bytes. -/
partial def decodeBytes (raw : String) : List Nat :=
  let bytes := raw.toUTF8.toList.map (·.toNat)
  let rec go : List Nat → List Nat
    | [] => []
    | 92 :: rest =>  -- backslash
      match rest with
      | 92 :: r => 92 :: go r
      | 34 :: r => 34 :: go r
      | 110 :: r => 10 :: go r   -- \n
      | 116 :: r => 9 :: go r    -- \t
      | a :: b :: r =>
        let ca := Char.ofNat a
        let cb := Char.ofNat b
        if isHexChar ca && isHexChar cb then (hexVal ca * 16 + hexVal cb) :: go r
        else a :: go (b :: r)
      | r => go r
    | x :: rest => x :: go rest
  go bytes

/-- Decode a string token for use as a name (bytes mapped to characters). -/
def decodeString (raw : String) : String :=
  if raw.any (· == '\\') then
    let bs := decodeBytes raw
    match String.fromUTF8? (ByteArray.mk (bs.map (·.toUInt8)).toArray) with
    | some s => s
    | none => String.ofList (bs.map Char.ofNat)
  else raw

end Lex

end CIR.Frontend
