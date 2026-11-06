import Std.Data.HashMap
import Std.Data.HashSet
import CIR.Module
import CIR.Frontend.Lexer

/-
  Parser for the pretty textual form of ClangIR into `CIR.Module`.

  Input: the output of
    clang++ -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering ...
  (with or without debug locations).

  Strategy:
  * a pre-pass collects the top-level alias definitions (`!rec_X = ...`,
    `#true = ...`, `#loc3 = loc(...)`); aliases are resolved lazily (and
    memoized) by re-parsing their right-hand side;
  * operations are parsed one per line; after an operation's known syntax the
    rest of its line (attribute dictionaries, `loc(...)`) is skipped. An
    operation outside the modelled subset becomes `Op.unknown`, with its result
    names, and its operands/regions are skipped with the same line rule;
  * SSA names are interned per function into consecutive `VId`s (entry block
    arguments first);
  * every `!cir.struct` / `!cir.union` body seen anywhere is registered as a
    `RecordDecl`; types refer to records by name.
-/

namespace CIR.Frontend
open Std

structure Ctx where
  toks        : Array Token
  /-- `!name` alias → token index of its right-hand side -/
  tyAliases   : HashMap String Nat
  /-- `#name` alias → token index of its right-hand side -/
  attrAliases : HashMap String Nat
  /-- record names replaced as they are read (`cir2lean --link`: the anonymous records named
  after their structure, `anonContentNames`) -/
  recRename   : HashMap String String := {}

structure PState where
  pos        : Nat := 0
  records    : Array RecordDecl := #[]
  recordIdx  : HashMap String Nat := {}
  anonNames  : HashMap String String := {}
  /-- record name → member index → the member's name, from the `cir.get_member` operations
  (record types have no member names; `cir2lean --link` names anonymous records after their
  members, `anonContentNames`) -/
  memberNames : HashMap String (HashMap Nat String) := {}
  tyMemo     : HashMap String Ty := {}
  tyBusy     : HashSet String := {}
  attrMemo   : HashMap String (Const × Option Ty) := {}
  locMemo    : HashMap String (Option Loc) := {}
  ssa        : HashMap String Nat := {}
  ssaNames   : Array (Nat × String) := #[]
  /-- source positions of the SSA values of the current function -/
  ssaLocs    : Array (Nat × Nat × Nat) := #[]
  /-- label maps of the enclosing regions, innermost first -/
  labels     : List (HashMap String Nat) := []
  /-- symbol of the function being parsed (for `cir.indirect_goto`) -/
  curFunc    : String := ""
  /-- record name → indices of its zero-width bit-field members -/
  zeroWidth  : HashMap String (List Nat) := {}
  /-- results of `cir.cast` in the current function: an asm output tied to a
  converted input is not modelled (CIR extends a narrower input as C converts
  it, Clang's and GCC's code zero-extend it) -/
  castResults : HashSet VId := {}
  /-- the exception tokens (`!cir.eh_token` arguments) of the enclosing catch handlers, innermost
  first: a `cir.throw` without operands in a handler rethrows its exception -/
  handlerTokens : List VId := []
  /-- the address of each load and store of the current function, and whether it is `volatile`
  (`nestSetjmps`) -/
  accesses : Array (VId × Bool) := #[]
  /-- the values that `cir.cast array_to_ptrdecay` defines, as last defined (`cir.va_arg` through
  a pointer to a `va_list`: `Op.vaArgP`) -/
  decays : HashSet VId := {}
  /-- the module is C (`cir.lang = #cir.lang<c>`): no constructors or destructors -/
  langC : Bool := false
  /-- the entry block arguments (parameters) of the current function -/
  argIds : List VId := []
  /-- the slots the current function stores its parameters into -/
  paramSlots : Array VId := #[]
  /-- the depth of loops (`cir.for`, `cir.while`, `cir.do`) around the operation being parsed -/
  loopDepth : Nat := 0
  /-- the `Op.allocaConst` results of the current function, with their loop depths -/
  constDepth : HashMap VId Nat := {}
  /-- the const objects written from inside a loop around them: CIR hoists the alloca of a C++
  range-for variable out of the loop, and each iteration initializes it again -/
  reinitSlots : Array VId := #[]
  /-- the current function has a label: a backward `goto` reaches a declaration again, and
  initializes its object again (C11 6.2.4p6) -/
  hasLabel : Bool := false
  /-- operations to put before the one being parsed (`Op.alignCheck`) -/
  preOps : Array Op := #[]

abbrev P := ReaderT Ctx (StateT PState (Except String))

instance {α} : Inhabited (P α) := ⟨fun _ _ => .error "unreachable"⟩

namespace P

def eofTok : Token := { kind := .eof, text := "", line := 0 }

@[inline] def tokAt (i : Nat) : P Token := do
  return (← read).toks[i]?.getD eofTok
@[inline] def peek : P Token := do tokAt (← get).pos
@[inline] def peek2 : P Token := do tokAt ((← get).pos + 1)
@[inline] def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }
@[inline] def next : P Token := do let t ← peek; advance; pure t
@[inline] def getPos : P Nat := do return (← get).pos
@[inline] def setPos (i : Nat) : P Unit := modify fun s => { s with pos := i }

def err {α} (msg : String) : P α := do
  let t ← peek
  throw s!"line {t.line}: {msg} (found {reprStr t.kind} `{t.text}`)"

@[inline] def isP (t : Token) (p : String) : Bool := t.kind == .punct && t.text == p
@[inline] def isI (t : Token) (s : String) : Bool := t.kind == .ident && t.text == s

def expectP (p : String) : P Unit := do
  if isP (← peek) p then advance else err s!"expected `{p}`"
def expectI (s : String) : P Unit := do
  if isI (← peek) s then advance else err s!"expected `{s}`"
def optP (p : String) : P Bool := do
  if isP (← peek) p then advance; return true else return false
def optI (s : String) : P Bool := do
  if isI (← peek) s then advance; return true else return false

def lastLine : P Nat := do
  let s ← get
  if s.pos == 0 then return 0 else return (← tokAt (s.pos - 1)).line

def isOpen (t : Token) : Bool :=
  t.kind == .punct && (t.text == "(" || t.text == "[" || t.text == "{" || t.text == "<")
def isClose (t : Token) : Bool :=
  t.kind == .punct && (t.text == ")" || t.text == "]" || t.text == "}" || t.text == ">")

/-- At an opening bracket: skip to (and past) the matching closing one.
Elsewhere: skip one token. -/
partial def skipBalanced : P Unit := do
  let t ← next
  unless isOpen t do return
  let rec loop (d : Nat) : P Unit := do
    let t ← next
    if t.kind == .eof then throw s!"line {t.line}: unbalanced brackets"
    else if isOpen t then loop (d+1)
    else if isClose t then (if d == 0 then return else loop (d-1))
    else loop d
  loop 0

/-- The entries `#cir.global_ctor<"f", p>` (`tag` = `cir.global_ctor`, or `cir.global_dtor`)
among the tokens `[i, j)` (a module's attribute dictionary), in order. -/
partial def structorsIn (tag : String) (i j : Nat) (acc : Array (String × Nat) := #[]) :
    P (Array (String × Nat)) := do
  if i + 5 ≥ j then return acc
  let t ← tokAt i
  if t.kind == .hash && t.text == tag then
    let t1 ← tokAt (i+1); let t2 ← tokAt (i+2); let t3 ← tokAt (i+3); let t4 ← tokAt (i+4)
    if isP t1 "<" && t2.kind == .str && isP t3 "," && t4.kind == .int then
      if let some p := t4.text.toNat? then
        return ← structorsIn tag (i+5) j (acc.push (Lex.decodeString t2.text, p))
  structorsIn tag (i+1) j acc

/-- `cir.lang = #cir.lang<c>` among the tokens `[i, j)` (a module's attribute dictionary). -/
partial def langCIn (i j : Nat) : P Bool := do
  if i + 5 ≥ j then return false
  let t ← tokAt i
  if t.kind == .ident && t.text == "cir.lang" then
    let t1 ← tokAt (i+1); let t2 ← tokAt (i+2); let t3 ← tokAt (i+3); let t4 ← tokAt (i+4)
    if isP t1 "=" && t2.kind == .hash && t2.text == "cir.lang" && isP t3 "<" && isI t4 "c" then
      return true
  langCIn (i+1) j

/-- The pointer size in bits of address space 0 among the tokens `[i, j)` (a module's attribute
dictionary): the first `!llvm.ptr = dense<N>` or `dense<[N, …]>` of its `dlti.dl_spec`. -/
partial def ptrBitsIn (i j : Nat) : P (Option Nat) := do
  if i + 4 ≥ j then return none
  let t ← tokAt i
  if t.kind == .bang && t.text == "llvm.ptr" then
    let t1 ← tokAt (i+1); let t2 ← tokAt (i+2); let t3 ← tokAt (i+3); let t4 ← tokAt (i+4)
    if isP t1 "=" && isI t2 "dense" && isP t3 "<" then
      let n ← if isP t4 "[" then tokAt (i+5) else pure t4
      if n.kind == .int then return n.text.toNat?
  ptrBitsIn (i+1) j

/-- Whether the tokens `[i, j)` (a module's attribute dictionary) hold `cir.lang = #cir.lang<cxx>`. -/
partial def langCxxIn (i j : Nat) : P Bool := do
  if i + 2 ≥ j then return false
  let t ← tokAt i
  if t.kind == .hash && t.text == "cir.lang" then
    let t1 ← tokAt (i+1); let t2 ← tokAt (i+2)
    if isP t1 "<" && t2.kind == .ident then return t2.text == "cxx"
  langCxxIn (i+1) j

/-- Skip tokens up to (not including) a closing bracket at depth 0, or a
token for which `stop` holds at depth 0. -/
partial def skipUntil (stop : Token → Bool) : P Unit := do
  let t ← peek
  if t.kind == .eof || isClose t || stop t then return
  if isOpen t then skipBalanced else advance
  skipUntil stop

/-! ### Numbers -/

def hexToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + Lex.hexVal c) 0

def intOfText (s : String) : Int :=
  let (neg, body) := if s.startsWith "-" then (true, s.drop 1) else (false, s)
  let body := body.toString
  let n : Nat :=
    if body.startsWith "0x" || body.startsWith "0X" then hexToNat (body.drop 2).toString
    else body.toNat!
  if neg then -(n : Int) else (n : Int)

/-- Decimal float text (`-1.5e+03`) to `Float`. -/
def floatOfText (s : String) : Float :=
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  if body.startsWith "0x" || body.startsWith "0X" then
    let f := Float.ofBits (hexToNat (body.drop 2).toString).toUInt64
    if neg then -f else f
  else
    let (mant, expo) := match body.splitOn "e" with
      | [m, e] => (m, e)
      | _ => match body.splitOn "E" with
        | [m, e] => (m, e)
        | _ => (body, "0")
    let (ip, fp) := match mant.splitOn "." with
      | [i, f] => (i, f)
      | _ => (mant, "")
    let digits := (ip ++ fp).toNat!
    let e : Int := (intOfText (if expo.startsWith "+" then (expo.drop 1).toString else expo)) - fp.length
    let v : Float :=
      if e ≥ 0 then OfScientific.ofScientific digits false e.toNat
      else OfScientific.ofScientific digits true (-e).toNat
    if neg then -v else v

/-- An IEEE format with `ew` exponent bits and `fw` fraction bits (implicit
leading bit), from its bit pattern `n`, as the nearest `Float`. -/
def ieeeBitsToFloat (ew fw : Nat) (n : Nat) : Float :=
  let bias : Int := 2 ^ (ew - 1) - 1
  let e : Nat := (n / 2 ^ fw) % 2 ^ ew
  let f : Nat := n % 2 ^ fw
  let mag : Float :=
    if e == 2 ^ ew - 1 then Float.ofBits (if f == 0 then 0x7FF0000000000000 else 0x7FF8000000000000)
    else if e == 0 then Float.scaleB (Float.ofNat f) (1 - bias - fw)
    else Float.scaleB (Float.ofNat (2 ^ fw + f)) (Int.ofNat e - bias - fw)
  if (n / 2 ^ (ew + fw)) % 2 == 1 then -mag else mag

/-- The x87 80-bit extended format (explicit integer bit) from its bit
pattern, as the nearest `Float`. -/
def x87BitsToFloat (n : Nat) : Float :=
  let e : Nat := (n / 2 ^ 64) % 2 ^ 15
  let m : Nat := n % 2 ^ 64
  let mag : Float :=
    if e == 2 ^ 15 - 1 then Float.ofBits (if m % 2 ^ 63 == 0 then 0x7FF0000000000000 else 0x7FF8000000000000)
    else Float.scaleB (Float.ofNat m) ((if e == 0 then 1 else Int.ofNat e) - 16383 - 63)
  if (n / 2 ^ 79) % 2 == 1 then -mag else mag

/-- A hexadecimal FP literal (`#cir.fp<0x7F800000> : !cir.float`) is the bit
pattern of its type's format, not of a binary64: its value as a `Float`
(formats wider than binary64 rounded; `long double` is x87's on x86-64). -/
def fixHexFloat (c : Const) (ty : Ty) : Const :=
  match c, ty with
  | .float txt _, .float k =>
    if txt.startsWith "0x" || txt.startsWith "0X" then
      let n := hexToNat (txt.drop 2).toString
      let v : Float := match k with
        | .double => Float.ofBits n.toUInt64
        | .single => (Float32.ofBits n.toUInt32).toFloat
        | .bf16 => (Float32.ofBits (n * 65536).toUInt32).toFloat
        | .fp16 => ieeeBitsToFloat 5 10 n
        | .fp128 => ieeeBitsToFloat 15 112 n
        | .fp80 => x87BitsToFloat n
        | .longDouble => if txt.length > 22 then ieeeBitsToFloat 15 112 n else x87BitsToFloat n
      .float txt v
    else c
  | _, _ => c

def expectInt : P Int := do
  let t ← peek
  if t.kind == .int then advance; return intOfText t.text
  else err "expected integer"

def expectNat : P Nat := do return (← expectInt).toNat

/-! ### SSA names -/

def intern (name : String) : P VId := do
  let s ← get
  match s.ssa[name]? with
  | some v => return v
  | none =>
    let v := s.ssa.size
    set { s with ssa := s.ssa.insert name v, ssaNames := s.ssaNames.push (v, "%" ++ name) }
    return v

def operand : P VId := do
  let t ← peek
  if t.kind == .percent then advance; intern t.text
  else err "expected SSA value"

/-- `%a, %b, ...` (possibly empty when the next token is not `%`). -/
partial def operandList : P (List VId) := do
  if (← peek).kind != .percent then return []
  let v ← operand
  if (← optP ",") then
    if (← peek).kind == .percent then return v :: (← operandList)
    else
      -- a `,` that does not start another operand belongs to the caller
      modify fun s => { s with pos := s.pos - 1 }
      return [v]
  else return [v]

/-! ### Locations -/

mutual
partial def resolveLocAlias (name : String) : P (Option Loc) := do
  if let some r := (← get).locMemo[name]? then return r
  match (← read).attrAliases[name]? with
  | none => return none
  | some i =>
    -- mark busy (cycle guard)
    modify fun s => { s with locMemo := s.locMemo.insert name none }
    let save ← getPos
    setPos i
    let r ← if isI (← peek) "loc" then parseLoc else pure none
    setPos save
    modify fun s => { s with locMemo := s.locMemo.insert name r }
    return r

partial def parseLocBody : P (Option Loc) := do
  let t ← peek
  match t.kind with
  | .str =>
    advance
    if isP (← peek) ":" then
      advance
      let l ← expectNat
      let c ← if (← optP ":") then expectNat else pure 0
      return some { line := l, col := c }
    else if isP (← peek) "(" then
      advance
      let r ← parseLocBody
      return r
    else return none
  | .hash => advance; resolveLocAlias t.text
  | .ident =>
    if t.text == "fused" then
      advance
      if isP (← peek) "<" then skipBalanced
      expectP "["
      let mut first : Option Loc := none
      repeat
        let r ← parseLocBody
        if first.isNone then first := r
        if !(← optP ",") then break
      return first
    else if t.text == "callsite" then
      advance; expectP "("; parseLocBody
    else return none
  | _ => return none

/-- `loc(...)`: best-effort source position; always consumes the whole
`loc(...)`. -/
partial def parseLoc : P (Option Loc) := do
  expectI "loc"
  let start ← getPos
  advance
  let r ← tryCatch parseLocBody (fun _ => pure none)
  setPos start
  skipBalanced
  return r
end

mutual
/-- The file of a location alias (`#loc3 = loc("f.cpp":1:2)`); `fuel` bounds alias chains. -/
partial def locFileAlias (name : String) (fuel : Nat) : P (Option String) := do
  match fuel, (← read).attrAliases[name]? with
  | 0, _ | _, none => return none
  | fuel + 1, some i =>
    let save ← getPos
    setPos i
    let r ← if isI (← peek) "loc" && isP (← peek2) "(" then do advance; advance; locFileBody fuel
      else pure none
    setPos save
    return r

/-- The file of a location: its `"file":line:col`, through aliases, or the first part of a `fused`
or `callsite` location that has one. -/
partial def locFileBody (fuel : Nat) : P (Option String) := do
  let t ← peek
  match t.kind with
  | .str => advance; return some (Lex.decodeString t.text)
  | .hash => advance; locFileAlias t.text fuel
  | .ident =>
    if t.text == "fused" then
      advance
      if isP (← peek) "<" then skipBalanced
      expectP "["
      let mut r : Option String := none
      repeat
        r ← locFileBody fuel
        if r.isSome then break
        if !(← optP ",") then break
      return r
    else if t.text == "callsite" then
      advance; expectP "("; locFileBody fuel
    else return none
  | _ => return none
end

/-- The file of the `loc(...)` at the current position, if there is one; the position is
unchanged. -/
def peekLocFile : P (Option String) := do
  if !(isI (← peek) "loc" && isP (← peek2) "(") then return none
  let save ← getPos
  advance; advance
  let r ← tryCatch (locFileBody 16) (fun _ => pure none)
  setPos save
  return r

/-- Skip the rest of the current line (respecting brackets that open on it),
returning the first `loc(...)` found there. Stops before a closing bracket
that belongs to an enclosing construct. -/
partial def skipRestOfLine : P (Option Loc) := do
  let ll ← lastLine
  let rec loop (d : Nat) (ll : Nat) (found : Option Loc) : P (Option Loc) := do
    let t ← peek
    if t.kind == .eof then return found
    if d == 0 && t.line != ll then return found
    if d == 0 && isI t "loc" && isP (← peek2) "(" then
      let l ← parseLoc
      loop d (← lastLine) (if found.isSome then found else l)
    else if isOpen t then advance; loop (d+1) t.line found
    else if isClose t then
      if d == 0 then return found
      advance; loop (d-1) t.line found
    else advance; loop d t.line found
  loop 0 ll none

/-! ### Types and attributes -/

/-- The size of a vector element type, in bytes. -/
def vecElemBytes : Ty → Option Nat
  | .int _ w => some ((w + 7) / 8)
  | .bool => some 1
  | .float .single => some 4
  | .float .double => some 8
  | .float .fp16 | .float .bf16 => some 2
  | .ptr _ => some 8
  | _ => none

/-- The alignment LLVM gives the vector that the type `ty`, spelled from token `p` on, is or
holds as the element of arrays (`!cir.array<!cir.vector<4 x !cir.float> x 2>`): its size rounded
up to a power of two. -/
partial def vecTypeAlign (p : Nat) (ty : Ty) : P (Option Nat) := do
  let t ← tokAt p
  match ty with
  | .array e n =>
    if t.kind == .bang && t.text == "cir.vector" then
      pure ((vecElemBytes e).map fun s => (n * s).nextPowerOfTwo)
    else if t.kind == .bang && t.text == "cir.array" then vecTypeAlign (p + 2) e
    else pure none
  | _ => pure none

def registerRecord (n : String) (kind : RecordKind) (members : Option (List (MemberKind × Ty)))
    (packed incomplete : Bool) (padding : List Ty) (zeroWidth : List Nat := [])
    (vecAligns : List (Nat × Nat) := []) : P Unit := do
  let s ← get
  let decl : RecordDecl :=
    { name := n, kind := kind, members := members.getD [], packed := packed,
      complete := members.isSome && !incomplete, padding := padding, vecAligns := vecAligns }
  let zw := if zeroWidth.isEmpty then s.zeroWidth else s.zeroWidth.insert n zeroWidth
  match s.recordIdx[n]? with
  | some i =>
    if members.isSome && !(s.records[i]!.complete) then
      set { s with records := s.records.set! i decl, zeroWidth := zw }
  | none =>
    set { s with records := s.records.push decl, recordIdx := s.recordIdx.insert n s.records.size,
                 zeroWidth := zw }

/-- `#cir.const_record<{v : T}> : !rec_U` of a union: one value, typed by the
member it initializes (the first, or a designated one). The union's value has
that member active with `v` and the others indeterminate (the union model: a
read of another member reinterprets the active one, `Ctx.unionView?`). The tail
padding of the decl (`padding = {...}`) is not a member, so the constant fits
the members. A union constant whose type matches no member is kept as it is. -/
def unionConst (c : Const) (fs : List (Const × Option Ty)) (ty : Ty) : P Const := do
  let s ← get
  match c, fs, ty with
  | .record [x], [(_, some t)], .record n =>
    match s.recordIdx[n]? with
    | some i =>
      let r := s.records[i]!
      if r.kind = .union then
        match r.members.findIdx? (fun mt => Ty.beq mt.2 t) with
        | some k => return .record ((List.replicate r.members.length Const.undef).set k x)
        | none => return c
      else return c
    | none => return c
  | _, _, _ => return c

/-- `#cir.const_record` lists no initializers for zero-width bit-fields: a
`#cir.zero` for each, so that the fields match the record's members. -/
def withZeroWidth (c : Const) (ty : Ty) : P Const := do
  let s ← get
  match c, ty with
  | .record cs, .record n =>
    match s.zeroWidth[n]?, s.recordIdx[n]? with
    | some zw, some i =>
      let len := s.records[i]!.members.length
      if cs.length + zw.length != len then return c
      let (out, _) := (List.range len).foldl (fun (acc : Array Const × List Const) k =>
        if zw.contains k then (acc.1.push .zero, acc.2)
        else match acc.2 with
          | x :: rest => (acc.1.push x, rest)
          | [] => acc) (#[], cs)
      return .record out.toList
    | _, _ => return c
  | _, _ => return c

def tokensText (i j : Nat) : P String := do
  let c ← read
  let ts := (c.toks.extract i j).toList.map fun t =>
    match t.kind with
    | .percent => "%" ++ t.text | .at => "@" ++ t.text | .caret => "^" ++ t.text
    | .bang => "!" ++ t.text | .hash => "#" ++ t.text | .str => "\"" ++ t.text ++ "\""
    | _ => t.text
  return " ".intercalate ts

mutual
partial def parseType : P Ty := do
  let t ← peek
  if t.kind == .ident then
    -- builtin MLIR types (`i32`, `f32`, `index`, `vector<4xi64>`, ...)
    advance
    if isP (← peek) "<" then skipBalanced
    return .other t.text
  if t.kind != .bang then err "expected type"
  advance
  let name := t.text
  if name.startsWith "cir." then parseCirType (name.drop 4).toString
  else if name.startsWith "llvm." then
    if isP (← peek) "<" then skipBalanced
    return .other name
  else resolveTypeAlias name

partial def resolveTypeAlias (name : String) : P Ty := do
  if let some ty := (← get).tyMemo[name]? then return ty
  let some i := (← read).tyAliases[name]? | err s!"unknown type alias !{name}"
  if (← get).tyBusy.contains name then
    -- recursive reference through an alias: use the record name if visible
    let t0 ← tokAt i
    let t1 ← tokAt (i+1)
    let t2 ← tokAt (i+2)
    let t3 ← tokAt (i+3)
    if t0.kind == .bang && (t0.text == "cir.struct" || t0.text == "cir.union") && isP t1 "<" then
      let rn := (← read).recRename
      if t2.kind == .str then let n := Lex.decodeString t2.text; return .record (rn.getD n n)
      if isI t2 "class" && t3.kind == .str then let n := Lex.decodeString t3.text; return .record (rn.getD n n)
    err s!"recursive type alias !{name}"
  modify fun s => { s with tyBusy := s.tyBusy.insert name }
  let save ← getPos
  setPos i
  let ty ← parseType
  setPos save
  modify fun s => { s with tyMemo := s.tyMemo.insert name ty, tyBusy := s.tyBusy.erase name }
  return ty

partial def parseCirType (k : String) : P Ty := do
  match k with
  | "int" =>
    expectP "<"
    let sg ← next
    expectP ","
    let w ← expectNat
    skipUntil (fun _ => false)
    expectP ">"
    return .int (sg.text == "s") w
  | "bool" => return .bool
  | "void" => return .void
  | "float" => return .float .single
  | "double" => return .float .double
  | "f16" => return .float .fp16
  | "bf16" => return .float .bf16
  | "f80" => return .float .fp80
  | "f128" => return .float .fp128
  | "long_double" =>
    if isP (← peek) "<" then skipBalanced
    return .float .longDouble
  | "vptr" => return .vptr
  | "eh_token" => return .ehToken
  | "catch_token" => return .catchToken
  | "cleanup_token" => return .cleanupToken
  | "ptr" =>
    expectP "<"
    let t ← parseType
    if (← optP ",") then skipUntil (fun _ => false)
    expectP ">"
    return .ptr t
  | "array" =>
    expectP "<"
    let t ← parseType
    expectI "x"
    let n ← expectNat
    expectP ">"
    return .array t n
  | "complex" =>
    -- `!cir.complex<T>`: the type `T[2]` (`Op.complexCreate`)
    expectP "<"
    let t ← parseType
    expectP ">"
    return .array t 2
  | "vector" =>
    -- `!cir.vector<N x T>`: the type `T[N]` (`Op.vecCreate`)
    expectP "<"
    let n ← expectNat
    expectI "x"
    let t ← parseType
    expectP ">"
    return .array t n
  | "func" =>
    expectP "<"
    let mut params : Array Ty := #[]
    let mut vararg := false
    let mut ret : Ty := .void
    if (← optP "(") then
      if !(← optP ")") then
        repeat
          if (← optP "...") then vararg := true
          else params := params.push (← parseType)
          if !(← optP ",") then break
        expectP ")"
      if (← optP "->") then ret ← parseType
    else
      -- older form: `!cir.func<R (A, B)>`
      ret ← parseType
      expectP "("
      if !(← optP ")") then
        repeat
          if (← optP "...") then vararg := true
          else params := params.push (← parseType)
          if !(← optP ",") then break
        expectP ")"
    expectP ">"
    return .func params.toList ret vararg
  | "struct" => parseRecordType false
  | "union" => parseRecordType true
  | "bitfield" =>
    -- `!cir.bitfield<!u8i, [decls]>`: the storage unit (an integer, or an
    -- array of bytes `!cir.array<!u8i x N>`); `!cir.bitfield<[decls]>`:
    -- zero-width bit-fields, without storage (zero bytes)
    expectP "<"
    if isP (← peek) "[" then
      skipBalanced
      expectP ">"
      return .array (.int false 8) 0
    let t ← parseType
    skipUntil (fun _ => false)
    expectP ">"
    return t
  | _ =>
    let start ← getPos
    if isP (← peek) "<" then skipBalanced
    let txt ← tokensText start (← getPos)
    return .other ("cir." ++ k ++ txt)

/-- The members of a record body, the indices of its zero-width bit-fields
(`!cir.bitfield<[…]>`), and the alignments of its vector members (`RecordDecl.vecAligns`). -/
partial def parseMembers : P (List (MemberKind × Ty) × List Nat × List (Nat × Nat)) := do
  if (← optP "}") then return ([], [], [])
  let mut acc : Array (MemberKind × Ty) := #[]
  let mut zeroWidth : Array Nat := #[]
  let mut vecAligns : Array (Nat × Nat) := #[]
  repeat
    let t ← peek
    let kind : MemberKind ←
      if isI t "data" then advance; pure .data
      else if isI t "pad" then advance; pure .pad
      else if isI t "empty" then advance; pure .empty
      else if isI t "bitfield" then advance; pure .bitfield
      else pure .data
    let t ← peek
    if t.kind == .bang && t.text == "cir.bitfield" && isP (← peek2) "<" &&
        isP (← tokAt ((← getPos) + 2)) "[" then
      zeroWidth := zeroWidth.push acc.size
    let p0 ← getPos
    let ty ← parseType
    if let some a ← vecTypeAlign p0 ty then vecAligns := vecAligns.push (acc.size, a)
    acc := acc.push (kind, ty)
    if !(← optP ",") then break
  expectP "}"
  return (acc.toList, zeroWidth.toList, vecAligns.toList)

partial def parseRecordType (isUnion : Bool) : P Ty := do
  let start ← getPos
  expectP "<"
  let mut isClass := false
  let mut name : Option String := none
  let mut packed := false
  let mut incomplete := false
  let mut members : Option (List (MemberKind × Ty)) := none
  let mut zeroWidth : List Nat := []
  let mut padding : List Ty := []
  let mut vecAligns : List (Nat × Nat) := []
  repeat
    let t ← peek
    if isP t ">" then advance; break
    else if t.kind == .eof then err "unterminated record type"
    else if isI t "class" then isClass := true; advance
    else if isI t "struct" then advance
    else if t.kind == .str then name := some (Lex.decodeString t.text); advance
    else if isI t "packed" then packed := true; advance
    else if isI t "incomplete" then incomplete := true; advance
    else if isI t "padding" then
      -- a union's tail padding: `padding = {!cir.array<!u8i x 3>}`
      advance; expectP "="; expectP "{"
      padding := (← parseMembers).1.map (·.2)
    else if isP t "{" then
      advance
      let (ms, zw, va) ← parseMembers
      members := some ms; zeroWidth := zw; vecAligns := va
    else if isOpen t then skipBalanced
    else advance
  let kind : RecordKind := if isUnion then .union else if isClass then .class else .struct
  let rn := (← read).recRename
  match name with
  | some n =>
    let n := rn.getD n n
    registerRecord n kind members packed incomplete padding zeroWidth vecAligns
    return .record n
  | none =>
    let key ← tokensText start (← getPos)
    let s ← get
    match s.anonNames[key]? with
    | some n => return .record n
    | none =>
      let n := s!"anon_{if isUnion then "union" else "struct"}.{s.anonNames.size}"
      let n := rn.getD n n
      set { s with anonNames := s.anonNames.insert key n }
      registerRecord n kind members packed incomplete padding zeroWidth vecAligns
      return .record n

/-- Parse an attribute (`#cir.int<1> : !s32i`, `#true`, ...), with its type
when one is printed. -/
partial def parseAttr : P (Const × Option Ty) := do
  let t ← peek
  match t.kind with
  | .hash =>
    advance
    let nm := t.text
    if nm.startsWith "cir." then
      let k := (nm.drop 4).toString
      if k == "const_array" then parseConstArray
      else if k == "const_record" then
        expectP "<"
        expectP "{"
        let fs ← parseAttrList "}"
        expectP ">"
        let c : Const := .record (fs.map (·.1))
        if isP (← peek) ":" then
          advance
          let ty ← parseType
          return (← withZeroWidth (← unionConst c fs ty) ty, some ty)
        return (c, none)
      else
        let c ← parseCirAttr k
        if isP (← peek) ":" then
          advance
          let ty ← parseType
          return (← withZeroWidth (fixHexFloat c ty) ty, some ty)
        return (c, none)
    else resolveAttrAlias nm
  | .int => advance; return (.int (intOfText t.text), none)
  | .str => advance; return (.other ("\"" ++ t.text ++ "\""), none)
  | _ =>
    let start ← getPos
    if isOpen t then skipBalanced else advance
    return (.other (← tokensText start (← getPos)), none)

partial def resolveAttrAlias (name : String) : P (Const × Option Ty) := do
  if let some r := (← get).attrMemo[name]? then return r
  let some i := (← read).attrAliases[name]? | return (.other ("#" ++ name), none)
  modify fun s => { s with attrMemo := s.attrMemo.insert name (.other ("#" ++ name), none) }
  let save ← getPos
  setPos i
  let r ← if isI (← peek) "loc" then pure (.other "loc", none) else parseAttr
  setPos save
  modify fun s => { s with attrMemo := s.attrMemo.insert name r }
  return r

partial def parseAttrList (close : String) : P (List (Const × Option Ty)) := do
  if (← optP close) then return []
  let mut acc := #[]
  repeat
    acc := acc.push (← parseAttr)
    if !(← optP ",") then break
  expectP close
  return acc.toList

partial def parseCirAttr (k : String) : P Const := do
  match k with
  | "int" =>
    expectP "<"; let v ← expectInt; expectP ">"
    return .int v
  | "bool" =>
    expectP "<"; let t ← next; expectP ">"
    return .bool (t.text == "true")
  | "fp" =>
    expectP "<"
    let t ← next
    expectP ">"
    let v := if t.kind == .float || t.kind == .int then floatOfText t.text else 0.0
    return .float t.text v
  | "ptr" =>
    expectP "<"
    let t ← next
    skipUntil (fun _ => false)
    expectP ">"
    if isI t "null" then return .null
    else if t.kind == .int then return .ptrInt (intOfText t.text)
    else return .other ("#cir.ptr<" ++ t.text ++ ">")
  | "zero" => return .zero
  | "const_complex" =>
    -- `#cir.const_complex<#re : T, #im : T>`: the array of the two parts
    expectP "<"
    let ps ← parseAttrList ">"
    return .array (ps.map (·.1))
  | "const_vector" =>
    -- `#cir.const_vector<[#e : T, ...]>`: the array of the elements
    expectP "<"
    expectP "["
    let es ← parseAttrList "]"
    expectP ">"
    return .array (es.map (·.1))
  | "undef" => return .undef
  | "poison" => return .poison
  | "const_record" | "vtable" | "typeinfo" =>
    -- a vtable global is a record holding the array of its slots; a typeinfo
    -- object (`_ZTI…`) the record of its vtable pointer, name and bases
    expectP "<"
    expectP "{"
    let fs ← parseAttrList "}"
    expectP ">"
    return .record (fs.map (·.1))
  | "block_addr_info" =>
    -- `<@fn, "lbl">`
    expectP "<"
    let t ← next
    expectP ","
    let l ← next
    expectP ">"
    return .blockAddr (Lex.decodeString t.text) (Lex.decodeString l.text)
  | "global_view" =>
    expectP "<"
    let t ← next
    let sym := if t.kind == .at then Lex.decodeString t.text else t.text
    let mut idx : Array Int := #[]
    if (← optP ",") then
      if (← optP "[") then
        if !(← optP "]") then
          repeat
            idx := idx.push (← expectInt)
            if (← optP ":") then let _ ← parseType
            if !(← optP ",") then break
          expectP "]"
    -- `, address_point true`: a vptr value (the entries of a VTT)
    let p ← getPos
    let t1 ← tokAt (p + 1)
    let t2 ← tokAt (p + 2)
    let addrPoint := isP (← peek) "," && isI t1 "address_point" && isI t2 "true"
    skipUntil (fun _ => false)
    expectP ">"
    match addrPoint, idx.toList with
    | false, _ => return .globalAddr sym idx.toList
    | true, [i, k] =>
      if 0 ≤ i ∧ 0 ≤ k then return .vtableAddr sym i.toNat k.toNat
      else return .other s!"#cir.global_view<@{sym}, {idx.toList}, address_point true>"
    | true, _ => return .other s!"#cir.global_view<@{sym}, {idx.toList}, address_point true>"
  | _ =>
    let start ← getPos
    if isP (← peek) "<" then skipBalanced
    let txt ← tokensText start (← getPos)
    return .other ("#cir." ++ k ++ txt)

/-- `#cir.const_array<[...] [, trailing_zeros]> : !cir.array<T x N>` or
`#cir.const_array<"str" : !cir.array<!s8i x n> [, trailing_zeros]> : ...`. -/
partial def parseConstArray : P (Const × Option Ty) := do
  expectP "<"
  let t ← peek
  let mut strBytes : Option (List Int) := none
  let mut elems : List Const := []
  if t.kind == .str then
    advance
    expectP ":"
    let inner ← parseType
    let signed := match inner with
      | .array (.int s _) _ => s
      | _ => true
    let bs : List Int := (Lex.decodeBytes t.text).map fun (b : Nat) =>
      if signed && b ≥ 128 then (b : Int) - 256 else (b : Int)
    strBytes := some bs
  else
    expectP "["
    elems := (← parseAttrList "]").map (·.1)
  let trailing ← if (← optP ",") then optI "trailing_zeros" else pure false
  skipUntil (fun _ => false)
  expectP ">"
  let ty? ← if (← optP ":") then some <$> parseType else pure none
  let total : Option Nat := match ty? with
    | some (.array _ n) => some n
    | _ => none
  match strBytes with
  | some bs =>
    let tz := match total with
      | some n => n - bs.length
      | none => if trailing then 1 else 0
    return (.str bs tz, ty?)
  | none =>
    if trailing then
      match total with
      | some n =>
        if n - elems.length ≤ 4096 then
          return (.array (elems ++ List.replicate (n - elems.length) .zero), ty?)
        else return (.other s!"#cir.const_array<{elems.length} elems, trailing_zeros>", ty?)
      | none => return (.array elems, ty?)
    else return (.array elems, ty?)
end

def parsePointee : P Ty := do
  match (← parseType) with
  | .ptr t => return t
  | t => return t

/-- Skip optional `{...}` attribute dictionaries. -/
partial def skipAttrDicts : P Unit := do
  if isP (← peek) "{" then skipBalanced; skipAttrDicts

/-- `skipKeywordsUntil`, telling whether the keyword `kw` was among the skipped tokens. -/
partial def skipKeywordsNoting (kw : String) (stop : Token → Bool) (seen : Bool := false) : P Bool := do
  let t ← peek
  if t.kind == .eof || stop t || isClose t then return seen
  let seen := seen || isI t kw
  if isOpen t then skipBalanced else advance
  skipKeywordsNoting kw stop seen

/-- The `align(N)` among the tokens from position `p` to before `q` (the keywords of a load or
a store before its operand). -/
partial def alignIn (p q : Nat) : P (Option Nat) := do
  if q ≤ p + 3 then return none
  let t ← tokAt p
  if isI t "align" && isP (← tokAt (p + 1)) "(" then
    let n ← tokAt (p + 2)
    if n.kind == .int then return some (intOfText n.text).toNat
  alignIn (p + 1) q

/-- The size of the scalar elements of an array type (`T[N]`, also nested), in bytes. -/
def scalarElemBytes : Ty → Option Nat
  | .array e _ => scalarElemBytes e
  | t => vecElemBytes t

/-- Before a load or a store of a vector type (spelled from token `p` on) whose stated
alignment `al` exceeds its element's: an `Op.alignCheck` of the address `a`. -/
def vecAccessCheck (a : VId) (al : Option Nat) (p : Nat) (ty : Ty) : P Unit := do
  match al with
  | some n =>
    let t ← tokAt p
    if t.kind == .bang && t.text == "cir.vector" && (scalarElemBytes ty).any (· < n) then
      modify fun s => { s with preOps := s.preOps.push (.alignCheck a n) }
  | none => pure ()

/-- Skip keywords / `kw(...)` groups up to a token satisfying `stop`. -/
partial def skipKeywordsUntil (stop : Token → Bool) : P Unit := do
  let t ← peek
  if t.kind == .eof || stop t then return
  if isClose t then return
  if isOpen t then skipBalanced else advance
  skipKeywordsUntil stop

end P

open P

/-! ### Regions and operations -/

/-- Pre-scan a region body (position just after its `{`): labels of blocks
defined at depth 0, in order. Returns the label map and whether the region
starts with a label. -/
partial def prescanLabels : P (HashMap String Nat × Bool) := do
  let c ← read
  let start ← getPos
  let rec loop (i : Nat) (d : Nat) (acc : Array String) : Array String :=
    match c.toks[i]? with
    | none => acc
    | some t =>
      if t.kind == .eof then acc
      else if isOpen t then loop (i+1) (d+1) acc
      else if isClose t then (if d == 0 then acc else loop (i+1) (d-1) acc)
      else if d == 0 && t.kind == .caret &&
          (i == 0 || (c.toks[i-1]?.map (·.line)).getD 0 < t.line) then
        loop (i+1) d (acc.push t.text)
      else loop (i+1) d acc
  let labels := loop start 0 #[]
  let first := c.toks[start]?
  let startsWithLabel := match first with
    | some t => t.kind == .caret
    | none => false
  let base := if startsWithLabel then 0 else 1
  let mut m : HashMap String Nat := {}
  for h : k in [0:labels.size] do
    m := m.insert labels[k] (base + k)
  return (m, startsWithLabel)

def blockIdOf (label : String) : P BlockId := do
  match (← get).labels with
  | m :: _ => match m[label]? with
    | some i => return i
    | none => err s!"unknown block label ^{label}"
  | [] => err "block label outside a region"

/-- Parse `^bb1` with optional `(%a : T, ...)` successor operands. -/
def successor : P (BlockId × List VId) := do
  let t ← next
  unless t.kind == .caret do throw s!"line {t.line}: expected block label"
  let b ← blockIdOf t.text
  let mut args : List VId := []
  if (← optP "(") then
    args ← operandList
    if (← optP ":") then
      repeat
        let _ ← parseType
        if !(← optP ",") then break
    expectP ")"
  return (b, args)

/-- Block argument list `(%a: T loc(..), %b: U)`. -/
partial def blockArgs : P (List VId) := do
  expectP "("
  if (← optP ")") then return []
  let mut acc : Array VId := #[]
  repeat
    let v ← operand
    expectP ":"
    let _ ← parseType
    skipAttrDicts
    if isI (← peek) "loc" then let _ ← parseLoc
    acc := acc.push v
    if !(← optP ",") then break
  expectP ")"
  return acc.toList

def parseCleanupKind : P CleanupKind := do
  let t ← next
  match t.text with
  | "normal" => return .normal
  | "eh" => return .eh
  | "all" => return .all
  | s => throw s!"line {t.line}: unknown cleanup kind {s}"

def parseCmpKind (s : String) : CmpKind :=
  match s with
  | "lt" => .lt | "le" => .le | "gt" => .gt | "ge" => .ge | "eq" => .eq | "ne" => .ne
  | "one" => .one | _ => .uno

def parseCastKind (s : String) : CastKind :=
  match s with
  | "bitcast" => .bitcast | "array_to_ptrdecay" => .arrayToPtrDecay
  | "member_ptr_to_bool" => .memberPtrToBool | "int_to_ptr" => .intToPtr
  | "ptr_to_int" => .ptrToInt | "ptr_to_bool" => .ptrToBool | "integral" => .integral
  | "int_to_bool" => .intToBool | "int_to_float" => .intToFloat
  | "float_to_int" => .floatToInt | "float_to_bool" => .floatToBool
  | "bool_to_int" => .boolToInt | "floating" => .floating
  | "address_space" => .addressSpace | "bool_to_float" => .boolToFloat
  | s => .other s

def binOpOf? (name : String) : Option BinOp :=
  match name with
  | "cir.add" => some .add | "cir.sub" => some .sub | "cir.mul" => some .mul
  | "cir.div" => some .div | "cir.rem" => some .rem | "cir.and" => some .and
  | "cir.or" => some .or | "cir.xor" => some .xor | "cir.max" => some .max
  | "cir.min" => some .min
  | _ => none

def fbinOpOf? (name : String) : Option FBinOp :=
  match name with
  | "cir.fadd" => some .fadd | "cir.fsub" => some .fsub | "cir.fmul" => some .fmul
  | "cir.fdiv" => some .fdiv | "cir.frem" => some .frem
  | _ => none

def unOpOf? (name : String) : Option UnOp :=
  match name with
  | "cir.inc" => some .inc | "cir.dec" => some .dec | "cir.minus" => some .minus
  | "cir.not" => some .not
  | _ => none

def opSetLoc (op : Op) (l : Loc) : Op :=
  match op with
  | .forOp _ c b s cl => .forOp l c b s cl
  | .whileOp _ c b cl => .whileOp l c b cl
  | .doWhileOp _ b c => .doWhileOp l b c
  | .call _ r f a at_ rt nt => .call l r f a at_ rt nt
  | op => op

/-- Flags (identifiers) before the first operand, e.g. `nsw nuw`. -/
partial def flagsBeforeOperand : P (List String) := do
  let t ← peek
  if t.kind == .ident then advance; return t.text :: (← flagsBeforeOperand)
  else return []

/-- After `cir.asm`: `(dialect, out = [], in = [], in_out = [], {"" "c"})` where
the constraints `c` are all clobbers `~{…}` (`asm volatile("" ::: "memory")`). -/
def asmIsBarrier : P Bool := do
  expectP "("
  unless (← next).kind == .ident do err "expected an asm dialect"
  for k in ["out", "in", "in_out"] do
    expectP ","; expectI k; expectP "="; expectP "["; expectP "]"
  expectP ","
  expectP "{"
  let tmpl ← next
  let cons ← next
  expectP "}"
  expectP ")"
  let clobber (c : String) : Bool := c.startsWith "~{" && c.endsWith "}"
  return tmpl.kind == .str && tmpl.text.isEmpty && cons.kind == .str &&
    (cons.text.isEmpty || (cons.text.splitOn ",").all clobber)

/-- A `cir.asm` operand list `[%v : T, ...]`; a memory operand
(`(maybe_memory)`) is an error. -/
partial def asmOperands : P (List (VId × Ty)) := do
  expectP "["
  if (← optP "]") then return []
  let mut acc : Array (VId × Ty) := #[]
  repeat
    let v ← operand
    expectP ":"
    let t ← parseType
    if isP (← peek) "(" then err "memory operand"
    acc := acc.push (v, t)
    if !(← optP ",") then break
  expectP "]"
  return acc.toList

/-- A `cir.asm` operand list `[%v : T, %p : !cir.ptr<T> (maybe_memory), ...]`, each operand with
whether it is a memory operand. -/
partial def asmOperandsM : P (List (VId × Ty × Bool)) := do
  expectP "["
  if (← optP "]") then return []
  let mut acc : Array (VId × Ty × Bool) := #[]
  repeat
    let v ← operand
    expectP ":"
    let t ← parseType
    let mem ← if isP (← peek) "(" then do
        expectP "("; expectI "maybe_memory"; expectP ")"; pure true
      else pure false
    acc := acc.push (v, t, mem)
    if !(← optP ",") then break
  expectP "]"
  return acc.toList

/-- After `cir.asm` without results, the forms with memory operands that `asmTiedForm` leaves, of an
empty template (or `nop`, which changes no operand): an output through a pointer (`=*…`, as `"+g"(x)`
and `"=g"(x)` give) tied to an input whose type is the pointee's stores that input's value there
(the template leaves their shared register as it is: `"+g"(x)` writes `x` back); a memory output
(`=*m`, as `"+m"(x)` gives) and a memory input (`*m`) are left as they are; the register inputs
are read (`Op.asmTied` without outputs). The stores go before that operation (`PState.preOps`).
Also the template `movl $0, $1` of a 32-bit register input and a memory input of its type: a
store of the first into the second. `none` for any other asm. -/
def asmMemForm (res : List VId) : P (Option Op) := do
  unless res.isEmpty do return none
  expectP "("
  unless (← next).kind == .ident do err "expected an asm dialect"
  expectP ","; expectI "out"; expectP "="
  let outs ← asmOperandsM
  expectP ","; expectI "in"; expectP "="
  let ins ← asmOperandsM
  expectP ","; expectI "in_out"; expectP "="
  let inouts ← asmOperandsM
  expectP ","
  expectP "{"
  let tmpl ← next
  let cons ← next
  expectP "}"
  expectP ")"
  let _ ← optI "side_effects"
  if isP (← peek) "->" then return none
  unless tmpl.kind == .str && cons.kind == .str do return none
  let cs := if cons.text.isEmpty then [] else cons.text.splitOn ","
  let isOut (c : String) : Bool := c.startsWith "="
  let isClobber (c : String) : Bool := c.startsWith "~{"
  let oc := cs.takeWhile isOut
  let ic := (cs.drop oc.length).takeWhile fun c => !isOut c && !isClobber c
  let inputs := ins ++ inouts
  unless (cs.drop (oc.length + ic.length)).all isClobber && ic.length == inputs.length &&
      oc.length == outs.length do return none
  let s ← get
  if tmpl.text == "movl $0, $1" then
    match outs, inputs, ic with
    | [], [(v, .int sg 32, false), (p, .ptr (.int sg' 32), true)], ["r", "*m"] =>
      return (if sg == sg' && !s.castResults.contains v then some (.store v p (.int sg 32)) else none)
    | _, _, _ => return none
  unless tmpl.text.isEmpty || tmpl.text == "nop" do return none
  -- every input: a memory operand for a memory constraint (`*…`), else a register value
  unless (inputs.zip ic).all (fun ((_, _, mem), c) => mem == c.startsWith "*") do return none
  let digit (k : Nat) : String := toString k
  let isDigits (c : String) : Bool := !c.isEmpty && c.all Char.isDigit
  -- every digit constraint names an output, and each output has at most one
  unless ic.all (fun c => !isDigits c || (List.range oc.length).any (digit · == c)) &&
      (List.range oc.length).all (fun k => (ic.filter (· == digit k)).length ≤ 1) do return none
  let mut stores : Array Op := #[]
  for ((p, pt, mem), c, k) in outs.zip (oc.zip (List.range oc.length)) do
    let .ptr t := pt | return none
    unless mem && c.startsWith "=*" do return none
    match ic.findIdx? (· == digit k) with
    | some j =>
      let some (v, vt, vmem) := inputs[j]? | return none
      unless !vmem && vt == t && !s.castResults.contains v do return none
      stores := stores.push (.store v p t)
    | none => unless c == "=*m" do return none
  let regIns := (inputs.filter fun (_, _, mem) => !mem).map (·.1)
  modify fun s => { s with preOps := s.preOps ++ stores }
  return some (.asmTied none regIns [])

/-- `cir.call_llvm_intrinsic "x86.…" %a, … : (A, …) -> R` with one result: `Op.x86Intrinsic` when
`x86Intrinsics` has the name, `none` for any other intrinsic. -/
def x86IntrinsicForm (res : List VId) : P (Option Op) := do
  let t ← next
  let args ← operandList
  expectP ":"
  expectP "("
  if !(← optP ")") then
    repeat
      let _ ← parseType
      if !(← optP ",") then break
    expectP ")"
  expectP "->"
  let ty ← parseType
  match res with
  | [r] => return (if t.kind == .str && x86Intrinsics.contains t.text then some (.x86Intrinsic r t.text args ty) else none)
  | _ => return none

/-- After `cir.asm` with results `res`: an empty template without memory
operands whose register outputs are each tied to an input of the same type
(by the input's digit constraint) that is not the result of a `cir.cast`, or
that has no outputs, as `asmTied`; `none` for any other asm. The constraints
list the outputs (`=…`), the inputs (the `in` operands, then the `in_out`
ones) and the clobbers (`~{…}`). -/
def asmTiedForm (res : List VId) : P (Option Op) := do
  expectP "("
  unless (← next).kind == .ident do err "expected an asm dialect"
  expectP ","; expectI "out"; expectP "="
  let outs ← asmOperands
  expectP ","; expectI "in"; expectP "="
  let ins ← asmOperands
  expectP ","; expectI "in_out"; expectP "="
  let inouts ← asmOperands
  expectP ","
  expectP "{"
  let tmpl ← next
  let cons ← next
  expectP "}"
  expectP ")"
  let _ ← optI "side_effects"
  let resTy ← if (← optP "->") then some <$> parseType else pure none
  unless outs.isEmpty && tmpl.kind == .str && tmpl.text.isEmpty && cons.kind == .str do return none
  let cs := if cons.text.isEmpty then [] else cons.text.splitOn ","
  let isOut (c : String) : Bool := c.startsWith "="
  let isClobber (c : String) : Bool := c.startsWith "~{"
  let oc := cs.takeWhile isOut
  let ic := (cs.drop oc.length).takeWhile fun c => !isOut c && !isClobber c
  let ops := ins ++ inouts
  unless (cs.drop (oc.length + ic.length)).all isClobber && ic.length == ops.length &&
      (oc ++ ic).all (fun c => !c.contains '*') do return none
  -- every digit constraint names an output, and each output has one
  let digit (k : Nat) : String := toString k
  let isDigits (c : String) : Bool := !c.isEmpty && c.all Char.isDigit
  unless ic.all (fun c => !isDigits c || (List.range oc.length).any (digit · == c)) &&
      (List.range oc.length).all (fun k => (ic.filter (· == digit k)).length == 1) do return none
  let ties := (List.range oc.length).filterMap fun k => ic.findIdx? (· == digit k)
  let tyOf (j : Nat) : Ty := (ops[j]?.map (·.2)).getD .void
  let s ← get
  unless ties.all (fun j => (ops[j]?.map fun o => !s.castResults.contains o.1).getD false) do
    return none
  let op : Op := .asmTied res.head? (ops.map (·.1)) ties
  match ties, res, resTy with
  | [], [], none => return some op
  | [j], [_], some t => return (if t == tyOf j then some op else none)
  | _ :: _ :: _, [_], some (.record n) =>
    let some i := s.recordIdx[n]? | return none
    let ms := s.records[i]!.members
    return (if ms.length == ties.length && ms.all (·.1 == .data) &&
        (ms.zip ties).all (fun (m, j) => m.2 == tyOf j) then some op else none)
  | _, _, _ => return none

/-- The types of the const objects that `Op.allocaConst` makes read-only once
initialized: those whose every write is part of their initialization. Scalars,
pointers and arrays of them; in C (`langC`: no constructors or destructors), also
structures of such members. Not: unions and bit-fields (a member write rewrites the
whole union, a bit-field write its storage unit), C++ classes (constructors and
destructors write const objects). -/
partial def constAllocaTy (s : PState) (langC : Bool) : Ty → Bool
  | .int _ _ | .bool | .float _ | .ptr _ => true
  | .array e _ => constAllocaTy s langC e
  | .record n =>
    langC && match s.recordIdx[n]? with
      | some i =>
        let r := s.records[i]!
        r.kind == .struct && r.complete &&
          r.members.all fun (k, t) => (k == .data || k == .pad) && constAllocaTy s langC t
      | none => false
  | _ => false

/-- A write to the const object at `a` from inside a loop that its alloca is
outside of (`PState.reinitSlots`). -/
def noteReinit (a : VId) : P Unit := do
  let s ← get
  if let some d := s.constDepth[a]? then
    if d < s.loopDepth then modify fun s => { s with reinitSlots := s.reinitSlots.push a }

mutual

/-- `{ ... }` region; `entryArgs` are the entry block arguments given by the
enclosing op's syntax. -/
partial def parseRegion (entryArgs : List VId := []) : P Region := do
  expectP "{"
  let (lbls, startsWithLabel) ← prescanLabels
  modify fun s => { s with labels := lbls :: s.labels }
  let mut blocks : Array Block := #[]
  let mut curArgs : List VId := entryArgs
  let mut curOps : Array Op := #[]
  let mut haveBlock := !startsWithLabel
  repeat
    let t ← peek
    if isP t "}" then advance; break
    else if t.kind == .eof then err "unterminated region"
    else if t.kind == .caret then
      if haveBlock then blocks := blocks.push (.mk curArgs curOps.toList)
      advance
      curArgs ← if isP (← peek) "(" then blockArgs else pure []
      expectP ":"
      curOps := #[]
      haveBlock := true
    else
      let op ← parseOp
      let s ← get
      curOps := (curOps ++ s.preOps).push op
      unless s.preOps.isEmpty do set { s with preOps := #[] }
  if haveBlock then blocks := blocks.push (.mk curArgs curOps.toList)
  modify fun s => { s with labels := s.labels.tail }
  return .mk blocks.toList

/-- `#bfi_x` (an alias) or `#cir.bitfield_info<name = "x", storage_type = !u8i,
size = 1, offset = 0, is_signed = false>`: storage type, size, offset and
signedness of a bit-field. -/
partial def parseBitfieldInfo : P (Ty × Nat × Nat × Bool) := do
  let t ← next
  unless t.kind == .hash do err "expected a bit-field info attribute"
  let save? ← if t.text == "cir.bitfield_info" then pure none else do
    let some i := (← read).attrAliases[t.text]? | err s!"unknown bit-field info #{t.text}"
    let save ← getPos
    setPos i
    let t' ← next
    unless t'.kind == .hash && t'.text == "cir.bitfield_info" do err "expected #cir.bitfield_info"
    pure (some save)
  expectP "<"
  let mut st : Ty := .int false 32
  let mut size := 0
  let mut off := 0
  let mut sg := false
  repeat
    let k ← next
    expectP "="
    match k.text with
    | "storage_type" => st ← parseType
    | "size" => size ← expectNat
    | "offset" => off ← expectNat
    | "is_signed" => sg := (← next).text == "true"
    | _ => let _ ← next
    if !(← optP ",") then break
  expectP ">"
  if let some save := save? then setPos save
  return (st, size, off, sg)

partial def parseOp : P Op := do
  -- results
  let mut res : Array VId := #[]
  if (← peek).kind == .percent then
    repeat
      res := res.push (← operand)
      if !(← optP ",") then break
    expectP "="
  let nameTok ← next
  if nameTok.kind != .ident then
    -- generic-form or unexpected syntax: keep it as an unknown op
    let _ ← skipRestOfLine
    return .unknown (if nameTok.kind == .str then nameTok.text else "?" ++ nameTok.text) res.toList
  let name := nameTok.text
  let r0 : VId := res[0]?.getD 0
  -- a name reused (in a sibling region) is no decay until a cast makes it one again
  modify fun s => { s with decays := res.foldl (fun acc v => acc.erase v) s.decays }
  let op ← parseOpBody name res.toList r0
  let l ← skipRestOfLine
  if let some l := l then
    if l.line != 0 then
      modify fun s => { s with ssaLocs := res.foldl (fun acc v => acc.push (v, l.line, l.col)) s.ssaLocs }
  return (match l with | some l => opSetLoc op l | none => op)

partial def parseOpBody (name : String) (res : List VId) (r0 : VId) : P Op := do
  match name with
  | "cir.alloca" =>
    let t ← next
    let nm := if t.kind == .str then Lex.decodeString t.text else ""
    -- `size(%n)`: a variable-length array of `n` elements; `const`: a const-qualified object
    let mut count : Option VId := none
    let mut isConst := false
    repeat
      let t ← peek
      if t.kind == .eof || isP t ":" || isClose t then break
      if isI t "size" && isP (← peek2) "(" then
        advance; advance
        count := some (← operand)
        expectP ")"
      else if isI t "const" then isConst := true; advance
      else if isOpen t then skipBalanced
      else advance
    expectP ":"
    let ty ← parsePointee
    let s ← get
    match count with
    | some n => return .allocaN r0 ty nm n
    | none =>
      if isConst && constAllocaTy s s.langC ty then
        modify fun s => { s with constDepth := s.constDepth.insert r0 s.loopDepth }
        return .allocaConst r0 ty nm
      else return .alloca r0 ty nm
  | "cir.load" =>
    let p0 ← getPos
    let vol ← skipKeywordsNoting "volatile" (fun t => t.kind == .percent)
    let al ← alignIn p0 (← getPos)
    let a ← operand
    modify fun s => { s with accesses := s.accesses.push (a, vol) }
    expectP ":"
    let _ ← parseType
    expectP ","
    let pt ← getPos
    let ty ← parseType
    vecAccessCheck a al pt ty
    return .load r0 a ty
  | "cir.store" =>
    let p0 ← getPos
    let vol ← skipKeywordsNoting "volatile" (fun t => t.kind == .percent)
    let al ← alignIn p0 (← getPos)
    let v ← operand
    expectP ","
    let a ← operand
    modify fun s => { s with accesses := s.accesses.push (a, vol) }
    skipAttrDicts
    expectP ":"
    let pt ← getPos
    let ty ← parseType
    vecAccessCheck a al pt ty
    if (← get).argIds.contains v then modify fun s => { s with paramSlots := s.paramSlots.push a }
    noteReinit a
    return .store v a ty
  | "cir.copy" =>
    let s ← operand
    skipKeywordsUntil (fun t => isI t "to")
    expectI "to"
    let d ← operand
    skipKeywordsUntil (fun t => isP t ":")
    expectP ":"
    let ty ← parsePointee
    noteReinit d
    return .copy s d ty
  | "cir.const" =>
    let (c, ty?) ← parseAttr
    let ty := ty?.getD (match c with | .bool _ => .bool | _ => .other "untyped")
    return .const r0 ty c
  | "cir.get_member" =>
    let b ← operand
    expectP "["
    let i ← expectNat
    expectP "]"
    -- the member's name, `{name = "x"}` (`PState.memberNames`)
    let p ← getPos
    let t1 ← tokAt (p + 1)
    let t2 ← tokAt (p + 2)
    let t3 ← tokAt (p + 3)
    let nm : Option String :=
      if isP (← peek) "{" && isI t1 "name" && isP t2 "=" && t3.kind == .str then
        some (Lex.decodeString t3.text)
      else none
    skipAttrDicts
    expectP ":"
    let rt ← parsePointee
    expectP "->"
    let ft ← parsePointee
    if let (.record n, some x) := (rt, nm) then
      modify fun s => { s with
        memberNames := s.memberNames.insert n ((s.memberNames.getD n {}).insert i x) }
    let isUnion ← match rt with
      | .record n => do
        let s ← get
        pure (match s.recordIdx[n]? with
          | some k => s.records[k]!.kind == .union
          | none => false)
      | _ => pure false
    return if isUnion then .unionMember r0 b i rt ft else .getMember r0 b i rt ft
  | "cir.get_element" =>
    let b ← operand
    expectP "["
    let i ← operand
    expectP ":"
    let it ← parseType
    expectP "]"
    skipAttrDicts
    expectP ":"
    let _ ← parseType
    expectP "->"
    let et ← parsePointee
    return .getElement r0 b i it et
  | "cir.ptr_stride" =>
    let b ← operand
    expectP ","
    let o ← operand
    skipAttrDicts
    expectP ":"
    expectP "("
    let et ← parsePointee
    expectP ","
    let ot ← parseType
    expectP ")"
    return .ptrStride r0 b o et ot
  | "cir.ptr_diff" =>
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let et ← parsePointee
    expectP "->"
    let rt ← parseType
    return .ptrDiff r0 a b et rt
  | "cir.get_global" =>
    skipKeywordsUntil (fun t => t.kind == .at)
    let t ← next
    expectP ":"
    let ty ← parsePointee
    return .getGlobal r0 (Lex.decodeString t.text) ty
  | "cir.block_address" =>
    -- `<@fn, "lbl"> : !cir.ptr<!void>`
    expectP "<"
    let t ← next
    expectP ","
    let l ← next
    expectP ">"
    return .blockAddress r0 (Lex.decodeString t.text) (Lex.decodeString l.text)
  | "cir.vtable.address_point" =>
    -- `(@_ZTV2Sq, address_point = <index = 0, offset = 2>) : !cir.vptr`
    expectP "("
    let t ← next
    let sym := Lex.decodeString t.text
    let mut index := 0
    let mut offset := 0
    repeat
      let t ← peek
      if isP t ")" || t.kind == .eof then break
      if isI t "index" then
        advance; expectP "="; index ← expectNat
      else if isI t "offset" then
        advance; expectP "="; offset ← expectNat
      else advance
    expectP ")"
    return .vtableAddressPoint r0 sym index offset
  | "cir.vtable.get_vptr" =>
    let o ← operand
    expectP ":"
    let ty ← parsePointee
    return .vtableGetVptr r0 o ty
  | "cir.vtable.get_virtual_fn_addr" =>
    let v ← operand
    expectP "["
    let i ← expectNat
    expectP "]"
    return .vtableGetVirtualFnAddr r0 v i
  | "cir.vtt.address_point" =>
    -- `@_ZTT…, offset = n -> …` (a VTT global) or `%vtt : !cir.ptr<…>, offset = n -> …`
    let t ← peek
    if t.kind == .at then
      advance
      expectP ","
      expectI "offset"
      expectP "="
      return .vttGlobalAddr r0 (Lex.decodeString t.text) (← expectNat)
    else
      let v ← operand
      expectP ":"
      let _ ← parseType
      expectP ","
      expectI "offset"
      expectP "="
      return .vttParamAddr r0 v (← expectNat)
  | "cir.base_class_addr" | "cir.derived_class_addr" =>
    skipKeywordsUntil (fun t => t.kind == .percent)
    let p ← operand
    expectP "["
    let off ← expectNat
    expectP "]"
    expectP ":"
    let st ← parsePointee
    expectP "->"
    let dt ← parsePointee
    return if name == "cir.base_class_addr" then .baseClassAddr r0 p off st dt
      else .derivedClassAddr r0 p off st dt
  | "cir.extract_member" =>
    let a ← operand
    expectP "["
    let i ← expectNat
    expectP "]"
    expectP ":"
    let at_ ← parseType
    expectP "->"
    let ft ← parseType
    return .extractMember r0 a i at_ ft
  | "cir.fmuladd" =>
    let a ← operand; expectP ","
    let b ← operand; expectP ","
    let c ← operand
    expectP ":"
    return .fmuladd r0 a b c (← parseType)
  | "cir.ceil" | "cir.floor" | "cir.round" | "cir.fabs" | "cir.sqrt" | "cir.trunc" | "cir.rint"
  | "cir.nearbyint" =>
    let a ← operand
    expectP ":"
    return .fmath r0 (name.drop 4).toString a (← parseType)
  | "cir.is_fp_class" =>
    let a ← operand
    expectP ","
    let start ← getPos
    while !isP (← peek) ":" && (← peek).kind != .eof do advance
    let cls ← tokensText start (← getPos)
    expectP ":"
    expectP "("
    let t ← parseType
    expectP ")"
    expectP "->"
    let _ ← parseType
    return .isFpClass r0 a cls t
  | "cir.signbit" =>
    -- `cir.signbit %a : !cir.double -> !cir.bool`: the pseudo-class `signbit`
    let a ← operand
    expectP ":"
    let t ← parseType
    expectP "->"
    let _ ← parseType
    return .isFpClass r0 a "signbit" t
  | "cir.clz" | "cir.ctz" =>
    let a ← operand
    let pz ← if isI (← peek) "poison_zero" then do advance; pure true else pure false
    expectP ":"
    return .bitCount r0 (name == "cir.clz") pz a (← parseType)
  | "cir.popcount" | "cir.parity" | "cir.ffs" | "cir.clrsb" | "cir.byte_swap" | "cir.bitreverse" =>
    let a ← operand
    expectP ":"
    return .bitOp r0 (name.drop 4).toString a (← parseType)
  | "cir.rotate" =>
    let left ← if (← optI "left") then pure true
      else if (← optI "right") then pure false
      else throw s!"line {(← peek).line}: expected `left` or `right` in cir.rotate"
    let a ← operand
    expectP ","
    let n ← operand
    expectP ":"
    return .rotate r0 left a n (← parseType)
  | "cir.copysign" | "cir.fmaxnum" | "cir.fminnum" =>
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let t ← parseType
    return if name == "cir.copysign" then .copysign r0 a b t else .fminmax r0 (name == "cir.fmaxnum") a b t
  | "cir.prefetch" =>
    skipKeywordsUntil (fun t => t.kind == .percent)
    let p ← operand
    expectP ":"
    let _ ← parseType
    return .prefetch p
  | "cir.stacksave" =>
    expectP ":"
    let _ ← parseType
    return .stackSave r0
  | "cir.stackrestore" =>
    let p ← operand
    expectP ":"
    let _ ← parseType
    return .stackRestore p
  | "cir.call_llvm_intrinsic" =>
    -- modelled: the x86 intrinsics of `x86Intrinsics`; any other stays unknown
    let s0 ← get
    match ← tryCatch (x86IntrinsicForm res) (fun _ => pure none) with
    | some op => return op
    | none =>
      set s0
      return .unknown name res
  | "cir.eh.setjmp" =>
    -- `__builtin_setjmp(buf)`: a call that `nestSetjmps` nests as it does `setjmp`'s
    let _ ← optI "builtin"
    let env ← operand
    expectP ":"
    expectP "("
    let et ← parseType
    expectP ")"
    expectP "->"
    let rt ← parseType
    return .call {} res.head? (.direct "__builtin_setjmp") [env] [et] rt true
  | "cir.eh.longjmp" =>
    -- `__builtin_longjmp(buf, 1)`: GCC requires the value 1, so CIR does not pass it
    let buf ← operand
    expectP ":"
    let bt ← parseType
    return .call {} none (.direct "__builtin_longjmp") [buf] [bt] .void true
  | "cir.va_copy" =>
    let src ← operand
    unless (← optI "to") do throw s!"line {(← peek).line}: expected `to` in cir.va_copy"
    let dst ← operand
    expectP ":"
    let _ ← parseType
    expectP ","
    let _ ← parseType
    return .vaCopy src dst
  | "cir.mul.overflow" | "cir.add.overflow" | "cir.sub.overflow" =>
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let src ← parseType
    expectP "->"
    let dst ← parseType
    let k : BinOp := if name == "cir.mul.overflow" then .mul else if name == "cir.add.overflow" then .add else .sub
    return .arithOverflow r0 (res[1]?.getD r0) k a b src dst
  | "cir.abs" =>
    let a ← operand
    let mp ← if isI (← peek) "min_is_poison" then do advance; pure true else pure false
    expectP ":"
    return .iabs r0 mp a (← parseType)
  | "cir.atomic.fetch" =>
    let k ← next
    let mut ff := false
    while (← peek).kind != .percent && (← peek).kind != .eof do
      if isI (← peek) "fetch_first" then ff := true
      if isI (← peek) "syncscope" then advance; skipBalanced else advance
    let p ← operand
    expectP ","
    let v ← operand
    -- `fetch_first` and `volatile`, in any order: a volatile access is an
    -- ordinary one here (no other thread or device observes memory)
    while isI (← peek) "fetch_first" || isI (← peek) "volatile" do
      if isI (← peek) "fetch_first" then ff := true
      advance
    expectP ":"
    expectP "("
    let _ ← parseType
    expectP ","
    let ty ← parseType
    expectP ")"
    expectP "->"
    let _ ← parseType
    return .atomicFetch r0 k.text ff p v ty
  | "cir.atomic.xchg" =>
    -- `<order> syncscope(...) %p, %v [volatile] : (!cir.ptr<ty>, ty) -> ty`
    skipKeywordsUntil (fun t => t.kind == .percent)
    let p ← operand
    expectP ","
    let v ← operand
    skipKeywordsUntil (fun t => isP t ":")
    expectP ":"
    expectP "("
    let _ ← parseType
    expectP ","
    let ty ← parseType
    expectP ")"
    expectP "->"
    let _ ← parseType
    return .atomicXchg r0 p v ty
  | "cir.atomic.cmpxchg" =>
    -- `[weak] success(<order>) failure(<order>) syncscope(...) %p, %expected, %desired
    -- align(n) [volatile] : (!cir.ptr<ty>, ty, ty) -> (ty, !cir.bool)`
    let mut succ := "seq_cst"
    let mut fail := "seq_cst"
    repeat
      let t ← peek
      if t.kind == .eof || t.kind == .percent || isClose t then break
      if (isI t "success" || isI t "failure") && isP (← peek2) "(" then
        advance
        advance
        let o ← next
        expectP ")"
        if isI t "success" then succ := o.text else fail := o.text
      else if isOpen t then skipBalanced else advance
    let p ← operand
    expectP ","
    let e ← operand
    expectP ","
    let d ← operand
    skipKeywordsUntil (fun t => isP t ":")
    expectP ":"
    expectP "("
    let _ ← parseType
    expectP ","
    let ty ← parseType
    expectP ","
    let _ ← parseType
    expectP ")"
    expectP "->"
    expectP "("
    let _ ← parseType
    expectP ","
    let _ ← parseType
    expectP ")"
    return .atomicCmpXchg r0 (res[1]?.getD r0) p e d ty succ fail
  | "cir.va_start" | "cir.va_end" =>
    let a ← operand
    expectP ":"
    let _ ← parseType
    return if name == "cir.va_start" then .vaStart a else .vaEnd a
  | "cir.va_arg" =>
    let a ← operand
    expectP ":"
    expectP "("
    let _ ← parseType
    expectP ")"
    expectP "->"
    -- through a `va_list` object (`ap`, or `*pap`: an array decayed), or a `va_list` parameter
    if (← get).decays.contains a then return .vaArgP r0 a (← parseType)
    return .vaArg r0 a (← parseType)
  | "cir.is_constant" =>
    let a ← operand
    expectP ":"
    let _ ← parseType
    expectP "->"
    let _ ← parseType
    return .isConstant r0 a
  | "cir.get_bitfield" | "cir.set_bitfield" =>
    if isI (← peek) "align" then advance; skipBalanced
    expectP "("
    let (st, size, off, sg) ← parseBitfieldInfo
    expectP ","
    let p ← operand
    -- `{is_volatile}`: after the pointer of a get, after the operands of a set
    skipAttrDicts
    expectP ":"
    let _ ← parseType
    if name == "cir.get_bitfield" then
      expectP ")"; expectP "->"
      return .getBitfield r0 p st size off sg (← parseType)
    expectP ","
    let v ← operand
    expectP ":"
    let _ ← parseType
    expectP ")"
    skipAttrDicts
    expectP "->"
    return .setBitfield r0 p v st size off sg (← parseType)
  | "cir.fneg" =>
    let _ ← flagsBeforeOperand
    let a ← operand
    expectP ":"
    return .fneg r0 a (← parseType)
  | "cir.shift" =>
    expectP "("
    let dir ← next
    expectP ","
    let a ← operand
    expectP ":"
    let ty ← parseType
    expectP ","
    let b ← operand
    expectP ":"
    let bt ← parseType
    expectP ")"
    return .shift r0 (dir.text == "left") a b ty bt
  | "cir.cmp" =>
    let k ← next
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let ty ← parseType
    -- of complex values (`T[2]`: CIR compares no arrays), only `eq` and `ne` are defined
    match ty, parseCmpKind k.text with
    | .array t 2, .eq => return .complexEq r0 false a b t
    | .array t 2, .ne => return .complexEq r0 true a b t
    | _, ck => return .cmp r0 ck a b ty
  | "cir.complex.create" =>
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let t ← parseType
    expectP "->"
    let _ ← parseType
    return .complexCreate r0 a b t
  | "cir.complex.real" | "cir.complex.imag" =>
    let c ← operand
    expectP ":"
    let _ ← parseType
    expectP "->"
    return .complexPart r0 (name == "cir.complex.imag") c (← parseType)
  | "cir.complex.real_ptr" | "cir.complex.imag_ptr" =>
    -- the address of a part: element 0 or 1 of the complex value's `T[2]`
    let p ← operand
    expectP ":"
    let ct ← parsePointee
    expectP "->"
    let t ← parsePointee
    return .getMember r0 p (if name == "cir.complex.imag_ptr" then 1 else 0) ct t
  | "cir.complex.add" | "cir.complex.sub" | "cir.complex.fadd" | "cir.complex.fsub" =>
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let t := match ← parseType with
      | .array t 2 => t
      | t => t
    return .complexArith r0 (name == "cir.complex.sub" || name == "cir.complex.fsub") a b t
  | "cir.vec.create" =>
    expectP "("
    let mut es : Array VId := #[]
    if !isP (← peek) ":" then
      repeat
        es := es.push (← operand)
        if !(← optP ",") then break
    expectP ":"
    let t ← parseType
    while (← optP ",") do let _ ← parseType
    expectP ")"
    expectP ":"
    let _ ← parseType
    return .vecCreate r0 es.toList t
  | "cir.vec.splat" =>
    let x ← operand
    expectP ":"
    let t ← parseType
    expectP ","
    let n := match ← parseType with
      | .array _ n => n
      | _ => 0
    return .vecSplat r0 x n t
  | "cir.vec.extract" =>
    let v ← operand
    expectP "["
    let i ← operand
    expectP ":"
    let _ ← parseType
    expectP "]"
    expectP ":"
    let t := match ← parseType with
      | .array t _ => t
      | t => t
    return .vecExtract r0 v i t
  | "cir.vec.insert" =>
    let x ← operand
    expectP ","
    let v ← operand
    expectP "["
    let i ← operand
    expectP ":"
    let _ ← parseType
    expectP "]"
    expectP ":"
    let t := match ← parseType with
      | .array t _ => t
      | t => t
    return .vecInsert r0 v x i t
  | "cir.vec.cmp" =>
    expectP "("
    let k ← next
    expectP ","
    let a ← operand
    expectP ","
    let b ← operand
    expectP ")"
    expectP ":"
    let t := match ← parseType with
      | .array t _ => t
      | t => t
    expectP ","
    let rt := match ← parseType with
      | .array t _ => t
      | t => t
    return .vecCmp r0 (parseCmpKind k.text) a b t rt
  | "cir.vec.shuffle" =>
    expectP "("
    let a ← operand
    expectP ","
    let b ← operand
    expectP ":"
    let _ ← parseType
    expectP ")"
    expectP "["
    let ks ← parseAttrList "]"
    expectP ":"
    let _ ← parseType
    let idx := ks.map fun (c, _) => match c with
      | .int v => v
      | _ => -1
    return .vecShuffle r0 a b idx
  | "cir.vec.ternary" =>
    expectP "("
    let c ← operand
    expectP ","
    let a ← operand
    expectP ","
    let b ← operand
    expectP ")"
    expectP ":"
    let _ ← parseType
    expectP ","
    let _ ← parseType
    return .vecTernary r0 c a b
  | "cir.cast" =>
    let k ← next
    let a ← operand
    expectP ":"
    let st ← parseType
    expectP "->"
    let dt ← parseType
    modify fun s => { s with castResults := s.castResults.insert r0 }
    let kind := parseCastKind k.text
    if kind == .arrayToPtrDecay then modify fun s => { s with decays := s.decays.insert r0 }
    return .cast r0 kind a st dt
  | "cir.select" =>
    expectI "if"
    let c ← operand
    expectI "then"
    let a ← operand
    expectI "else"
    let b ← operand
    expectP ":"
    expectP "("
    let _ ← parseType; expectP ","
    let _ ← parseType; expectP ","
    let ty ← parseType
    expectP ")"
    return .select r0 c a b ty
  | "cir.call" =>
    let t ← next
    let (callee, indirect) ← match t.kind with
      | .at => pure (Callee.direct (Lex.decodeString t.text), false)
      | .percent => do pure (Callee.indirect (← intern t.text), true)
      | _ => throw s!"line {t.line}: expected callee"
    expectP "("
    let args ← operandList
    expectP ")"
    -- flags and attribute dictionary up to the type
    let mut nothrow := false
    repeat
      let t ← peek
      if isP t ":" || t.kind == .eof then break
      if isI t "nothrow" then nothrow := true
      if isOpen t then skipBalanced else advance
    expectP ":"
    expectP "("
    let mut tys : Array Ty := #[]
    if !(← optP ")") then
      repeat
        tys := tys.push (← parseType)
        skipAttrDicts
        if !(← optP ",") then break
      expectP ")"
    expectP "->"
    let mut ret : Ty := .void
    if (← optP "(") then
      if !(← optP ")") then
        ret ← parseType
        skipAttrDicts
        expectP ")"
    else ret ← parseType
    let argTys := if indirect then tys.toList.drop 1 else tys.toList
    return .call {} res.head? callee args argTys ret nothrow
  | "cir.scope" =>
    let body ← parseRegion
    let _ ← optP ":" -- `: T` result type (skipped with the rest of the line)
    return .scope res.head? body
  | "cir.cleanup.scope" =>
    let body ← parseRegion
    expectI "cleanup"
    let k ← parseCleanupKind
    let cl ← parseRegion
    return .cleanupScope k body cl
  | "cir.if" =>
    let c ← operand
    let thn ← parseRegion
    let els ← if (← optI "else") then parseRegion else pure (Region.mk [])
    return .ifOp c thn els
  | "cir.ternary" =>
    expectP "("
    let c ← operand
    expectP ","
    expectI "true"
    let t ← parseRegion
    expectP ","
    expectI "false"
    let f ← parseRegion
    expectP ")"
    return .ternary res.head? c t f
  | "cir.for" =>
    expectP ":"
    expectI "cond"
    modify fun s => { s with loopDepth := s.loopDepth + 1 }
    let c ← parseRegion
    expectI "body"
    let b ← parseRegion
    expectI "step"
    let s ← parseRegion
    let cl ← if (← optI "cleanup") then
        (do let k ← parseCleanupKind; let r ← parseRegion; pure (some (k, r)))
      else pure none
    modify fun s => { s with loopDepth := s.loopDepth - 1 }
    return .forOp {} c b s cl
  | "cir.while" =>
    modify fun s => { s with loopDepth := s.loopDepth + 1 }
    let c ← parseRegion
    expectI "do"
    let b ← parseRegion
    let cl ← if (← optI "cleanup") then
        (do let k ← parseCleanupKind; let r ← parseRegion; pure (some (k, r)))
      else pure none
    modify fun s => { s with loopDepth := s.loopDepth - 1 }
    return .whileOp {} c b cl
  | "cir.do" =>
    modify fun s => { s with loopDepth := s.loopDepth + 1 }
    let b ← parseRegion
    expectI "while"
    let c ← parseRegion
    modify fun s => { s with loopDepth := s.loopDepth - 1 }
    return .doWhileOp {} b c
  | "cir.switch" =>
    expectP "("
    let c ← operand
    expectP ":"
    let ty ← parseType
    expectP ")"
    skipKeywordsUntil (fun t => isP t "{")
    let body ← parseRegion
    return .switch c ty body
  | "cir.case" =>
    expectP "("
    let k ← next
    expectP ","
    expectP "["
    let vals ← parseAttrList "]"
    expectP ")"
    let body ← parseRegion
    let kind : CaseKind := match k.text with
      | "equal" => .equal | "anyof" => .anyof | "range" => .range | _ => .default
    let ints := vals.filterMap fun (c, _) => match c with | .int v => some v | _ => none
    return .case kind ints body
  | "cir.try" =>
    let _ ← optI "cleanup"
    let body ← parseRegion
    let mut handlers : Array (CatchKind × Region) := #[]
    let mut unwind : Option Region := none
    repeat
      if (← optI "catch") then
        let kind ← if (← optI "all") then pure CatchKind.all
          else do
            expectP "["
            let _ ← optI "type"
            let (c, _) ← parseAttr
            expectP "]"
            pure (match c with
              | .globalAddr s _ => CatchKind.type s
              | _ => CatchKind.all)
        let args ← if isP (← peek) "(" then blockArgs else pure []
        let outer := (← get).handlerTokens
        modify fun s => { s with handlerTokens := args.take 1 ++ outer }
        let r ← parseRegion args
        modify fun s => { s with handlerTokens := outer }
        handlers := handlers.push (kind, r)
      else if (← optI "unwind") then
        let args ← if isP (← peek) "(" then blockArgs else pure []
        unwind := some (← parseRegion args)
      else break
    return .tryOp body handlers.toList unwind
  | "cir.yield" =>
    let vs ← operandList
    return .yield vs
  | "cir.condition" =>
    expectP "("
    let c ← operand
    expectP ")"
    return .condition c
  | "cir.libc.memcpy" | "cir.libc.memmove" =>
    -- `%n bytes from %src align(..) to %dst align(..) : …`
    let n ← operand
    skipKeywordsUntil (fun t => t.kind == .percent)
    let src ← operand
    skipKeywordsUntil (fun t => t.kind == .percent)
    let dst ← operand
    return .libc ((name.drop 9).toString) [dst, src, n]
  | "cir.libc.memset" =>
    -- `%n bytes at %dst align(..) to %val : …`
    let n ← operand
    skipKeywordsUntil (fun t => t.kind == .percent)
    let dst ← operand
    skipKeywordsUntil (fun t => t.kind == .percent)
    let v ← operand
    return .libc "memset" [dst, v, n]
  | "cir.goto" =>
    let t ← next
    return .goto (Lex.decodeString t.text)
  | "cir.indirect_goto" =>
    -- `%p : !cir.ptr<!void>`
    let t ← operand
    return .indirectGoto t (← get).curFunc
  | "cir.label" =>
    let t ← next
    modify fun s => { s with hasLabel := true }
    return .label (Lex.decodeString t.text)
  | "cir.break" => return .brk
  | "cir.continue" => return .cont
  | "cir.return" =>
    let vs ← operandList
    return .ret vs.head?
  | "cir.br" =>
    let (b, args) ← successor
    return .br b args
  | "cir.brcond" =>
    let c ← operand
    let (t, ta) ← successor
    expectP ","
    let (f, fa) ← successor
    return .brcond c t ta f fa
  | "cir.trap" => return .trap
  | "cir.unreachable" => return .unreachable
  | "cir.throw" =>
    if (← peek).kind == .percent then
      let o ← operand
      expectP ":"
      let ty ← parsePointee
      let ti ← if (← optP ",") then
          (do let t ← next; pure (if t.kind == .at then some (Lex.decodeString t.text) else none))
        else pure none
      return .throw (some o) ty ti
    else
      -- `throw;` in a catch handler: the handled exception propagates again,
      -- as from its token (elsewhere the current exception is not known)
      match (← get).handlerTokens with
      | t :: _ => return .resume t
      | [] => return .throw none .void none
  | "cir.resume" =>
    let t ← operand
    return .resume t
  | "cir.alloc.exception" =>
    let n ← expectNat
    expectP "->"
    let ty ← parsePointee
    return .allocException r0 n ty
  | "cir.begin_catch" =>
    let eh ← operand
    let r1 := res[1]?.getD 0
    return .beginCatch r0 r1 eh
  | "cir.end_catch" =>
    return .endCatch (← operand)
  | "cir.init_catch_param" =>
    let k ← next
    let e ← operand
    expectI "to"
    let d ← operand
    expectP ":"
    let _ ← parseType
    expectP ","
    let ty ← parsePointee
    return .initCatchParam k.text e d ty
  | "cir.eh.terminate" =>
    return .ehTerminate (← operand)
  | "cir.assume" =>
    return .assume (← operand)
  | "cir.asm" =>
    -- modelled: a compiler barrier, an empty template whose outputs are each
    -- tied to an input (or that has none), its forms with memory operands and
    -- `nop` (`asmMemForm`); any other asm stays unknown
    let s0 ← get
    if res.isEmpty && (← tryCatch asmIsBarrier (fun _ => pure false)) then return .asmBarrier
    set s0
    match ← tryCatch (asmTiedForm res) (fun _ => pure none) with
    | some op => return op
    | none =>
      set s0
      match ← tryCatch (asmMemForm res) (fun _ => pure none) with
      | some op => return op
      | none =>
        set s0
        return .unknown name res
  | _ =>
    if let some k := binOpOf? name then
      let flags ← flagsBeforeOperand
      let a ← operand
      expectP ","
      let b ← operand
      expectP ":"
      return .binop r0 k (flags.contains "nsw") (flags.contains "nuw") a b (← parseType)
    else if let some k := fbinOpOf? name then
      let _ ← flagsBeforeOperand
      let a ← operand
      expectP ","
      let b ← operand
      expectP ":"
      return .fbinop r0 k a b (← parseType)
    else if let some k := unOpOf? name then
      let flags ← flagsBeforeOperand
      let a ← operand
      expectP ":"
      return .unop r0 k (flags.contains "nsw") a (← parseType)
    else
      -- not modelled: the dispatcher skips the rest of the line (and any
      -- regions opening on it)
      return .unknown name res

end

/-! ### setjmp

A call of `setjmp` returns twice. In C11 it may only be the whole controlling expression of a
selection or iteration statement (also compared with an integer constant, or under `!`), or an
expression statement (7.13.1.1p4), so after the call comes the rest of that statement's block:
`nestSetjmps` makes the call an `Op.setjmp` that holds the rest of its block, which runs again
when a `longjmp` comes back. Only functions that call `setjmp` change. GCC's `__builtin_setjmp`
(`cir.eh.setjmp`) is nested the same way. -/

def setjmpSyms : List String := ["_setjmp", "setjmp", "__sigsetjmp", "sigsetjmp", "__builtin_setjmp"]

/-- A call of `setjmp`: its result and its `jmp_buf` argument. -/
def setjmpCall? : Op → Option (VId × VId)
  | .call _ (some r) (.direct s) (env :: _) _ _ _ => if setjmpSyms.contains s then some (r, env) else none
  | _ => none

def isBranch : Op → Bool
  | .br .. | .brcond .. | .indirectGoto .. => true
  | _ => false

/-- The regions nested in an operation. -/
def opRegions : Op → List Region
  | .scope _ r | .switch _ _ r | .case _ _ r | .setjmp _ _ _ _ _ r | .setjmpRun _ _ _ r => [r]
  | .cleanupScope _ a b | .ifOp _ a b | .ternary _ _ a b | .doWhileOp _ a b => [a, b]
  | .forOp _ a b c cl => [a, b, c] ++ (cl.map (·.2)).toList
  | .whileOp _ a b cl => [a, b] ++ (cl.map (·.2)).toList
  | .tryOp b hs u => b :: hs.map (·.2) ++ u.toList
  | _ => []

/-- The values an operation reads, for the operations that a controlling expression, an
assignment or an initializer can use (the others: none). -/
def opReads : Op → List VId
  | .load _ a _ => [a]
  | .store v a _ => [v, a]
  | .copy s d _ => [s, d]
  | .getMember _ b _ _ _ => [b]
  | .getElement _ b i _ _ => [b, i]
  | .ptrStride _ b o _ _ => [b, o]
  | .binop _ _ _ _ a b _ => [a, b]
  | .shift _ _ a b _ _ => [a, b]
  | .unop _ _ _ a _ => [a]
  | .cmp _ _ a b _ => [a, b]
  | .cast _ _ a _ _ => [a]
  | .select _ c a b _ => [c, a, b]
  | .complexCreate _ a b _ | .complexArith _ _ a b _ | .complexEq _ _ a b _ => [a, b]
  | .complexPart _ _ c _ => [c]
  | .vecCreate _ es _ => es
  | .vecSplat _ x _ _ => [x]
  | .vecExtract _ v i _ => [v, i]
  | .vecInsert _ v x i _ => [v, x, i]
  | .vecCmp _ _ a b _ _ | .vecShuffle _ a b _ => [a, b]
  | .vecTernary _ c a b => [c, a, b]
  | .call _ _ callee args _ _ _ => (match callee with | .indirect f => [f] | .direct _ => []) ++ args
  | .ifOp c _ _ => [c]
  | .ternary _ c _ _ => [c]
  | .switch c _ _ => [c]
  | .yield vs => vs
  | .condition c => [c]
  | .ret v => v.toList
  | .br _ vs => vs
  | .brcond c _ ts _ fs => c :: ts ++ fs
  | _ => []

mutual
/-- The operations among `ops` and their regions that read `v`. -/
partial def usesIn (v : VId) (ops : List Op) : List Op :=
  ops.flatMap fun op =>
    (if (opReads op).contains v then [op] else []) ++ (opRegions op).flatMap (usesInRegion v)
partial def usesInRegion (v : VId) : Region → List Op
  | .mk bs => bs.flatMap fun (.mk _ ops) => usesIn v ops
end

/-- `c` is the whole controlling expression of an `if`, a `switch` or a loop. -/
def controls (c : VId) (ops : List Op) : Bool :=
  match usesIn c ops with
  | [.ifOp c' _ _] | [.condition c'] | [.switch c' _ _] => c' == c
  | _ => false

/-- The use of `setjmp`'s result `r` in the rest of its block is one of the contexts of C11
7.13.1.1p4 (`consts`: the function's values that are integer constants). -/
def setjmpContextOk (consts : List VId) (r : VId) (ops : List Op) : Bool :=
  let cmpOk (x : VId) (op : Op) : Bool := match op with
    | .cmp c _ a b _ => ((a == x && consts.contains b) || (b == x && consts.contains a)) && controls c ops
    | _ => false
  match usesIn r ops with
  -- an expression statement
  | [] => true
  | [.switch c _ _] => c == r
  -- `if (setjmp(b))`, `if (!setjmp(b))`
  | [.cast b .intToBool _ _ _] =>
    controls b ops ||
      (match usesIn b ops with
       | [.unop n .not _ _ _] => controls n ops
       | _ => false)
  -- compared with an integer constant, possibly after a conversion
  | [op@(.cmp ..)] => cmpOk r op
  | [.cast c .integral _ _ _] =>
    match usesIn c ops with
    | [op] => cmpOk c op
    | _ => false
  | _ => false

/-- `ops` without a last `cir.yield` that yields nothing. -/
def dropYield (ops : List Op) : List Op :=
  match ops.getLast? with
  | some (.yield []) => ops.dropLast
  | _ => ops

/-- `ops` (a block) ending with a `setjmp`, possibly inside trailing `cir.scope`s without results:
`post` (the ops after the outermost of those scopes) appended to the rest of that `setjmp`. A
statement's `cir.scope` ends before the statements after it, which a `longjmp` back to the
`setjmp` must run again; the scope's objects then live until the end of the enclosing block. -/
partial def appendTrailing (ops post : List Op) : Option (List Op) :=
  match ops.getLast? with
  | some (.setjmp r env vol svol ok (.mk [.mk [] rest])) =>
    some (ops.dropLast ++ [.setjmp r env vol svol ok (.mk [.mk [] (dropYield rest ++ post)])])
  | some (.scope none (.mk [.mk [] inner])) =>
    (appendTrailing inner post).map fun inner' => ops.dropLast ++ [.scope none (.mk [.mk [] inner'])]
  | _ => none

mutual
partial def nestOps (vol : List VId) (svol : List (VId × List Nat × Bool)) (consts : List VId) :
    List Op → List Op
  | [] => []
  | op :: rest =>
    match setjmpCall? op with
    | some (r, env) =>
      -- the rest of the block, unless it branches to another block: then `setjmp` returns 0
      -- once (a `longjmp` back is undefined: no invocation to return to), and its context is
      -- checked here
      if rest.any isBranch then
        (if setjmpContextOk consts r rest then op else .fail "setjmp outside the contexts of C11 7.13.1.1p4") ::
          nestOps vol svol consts rest
      else [.setjmp r env vol svol (setjmpContextOk consts r rest) (.mk [.mk [] (nestOps vol svol consts rest)])]
    | none =>
      let op' := nestOp vol svol consts op
      -- a statement's scope that ends with a `setjmp`: the rest of this block joins its rest
      match op', rest.any isBranch with
      | .scope none (.mk [.mk [] inner]), false =>
        match appendTrailing inner (nestOps vol svol consts rest) with
        | some inner' => [.scope none (.mk [.mk [] inner'])]
        | none => op' :: nestOps vol svol consts rest
      | _, _ => op' :: nestOps vol svol consts rest
partial def nestOp (vol : List VId) (svol : List (VId × List Nat × Bool)) (consts : List VId) : Op → Op
  | .scope res r => .scope res (nestRegion vol svol consts r)
  | .cleanupScope k a b => .cleanupScope k (nestRegion vol svol consts a) (nestRegion vol svol consts b)
  | .ifOp c a b => .ifOp c (nestRegion vol svol consts a) (nestRegion vol svol consts b)
  | .ternary res c a b => .ternary res c (nestRegion vol svol consts a) (nestRegion vol svol consts b)
  | .forOp loc a b c cl =>
    .forOp loc (nestRegion vol svol consts a) (nestRegion vol svol consts b) (nestRegion vol svol consts c)
      (cl.map fun (k, r) => (k, nestRegion vol svol consts r))
  | .whileOp loc a b cl =>
    .whileOp loc (nestRegion vol svol consts a) (nestRegion vol svol consts b)
      (cl.map fun (k, r) => (k, nestRegion vol svol consts r))
  | .doWhileOp loc a b => .doWhileOp loc (nestRegion vol svol consts a) (nestRegion vol svol consts b)
  | .switch c t r => .switch c t (nestRegion vol svol consts r)
  | .case k vs r => .case k vs (nestRegion vol svol consts r)
  | .tryOp b hs u =>
    .tryOp (nestRegion vol svol consts b) (hs.map fun (k, r) => (k, nestRegion vol svol consts r))
      (u.map (nestRegion vol svol consts))
  | op => op
partial def nestRegion (vol : List VId) (svol : List (VId × List Nat × Bool)) (consts : List VId) :
    Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (nestOps vol svol consts ops))
end

mutual
partial def allOps (ops : List Op) : List Op :=
  ops.flatMap fun op => op :: (opRegions op).flatMap allOpsRegion
partial def allOpsRegion : Region → List Op
  | .mk bs => bs.flatMap fun (.mk _ ops) => allOps ops
end

/-- `body` with its `setjmp` calls nested (`nestOps`; once the models are known, the frontend
notes the stores of every function of the module, `Frontend.sjNotes`). `accesses`: the address
of each load and store, and whether it is `volatile`.
CIR does not type volatile objects, so the function's objects (its `cir.alloca`s) are classified
by their own accesses, through members (and their elements: a path of member indices): a path
some of whose accesses are not `volatile` is not volatile-qualified (or the program is undefined,
C11 6.7.3p6), one whose accesses are all `volatile` (one of them not through a cast:
`*(volatile int *)&x` does not make `x` volatile) is volatile; the `volatile` accesses through
other pointers (into objects the function reaches only so) are evidence at run time. -/
def nestSetjmps (accesses : List (VId × Bool)) (body : Region) : Region :=
  let ops := allOpsRegion body
  let allocas : Std.HashSet VId := ops.foldl (fun h op => match op with
    | .alloca r .. | .allocaN r .. => h.insert r
    | _ => h) {}
  -- one step from a pointer to the pointer it is computed from: a member (its index), an element,
  -- a pointer offset, a decay (`none`) or a cast (`true`)
  let step : Std.HashMap VId (VId × Option Nat × Bool) := ops.foldl (fun h op => match op with
    | .getMember r b i _ _ => h.insert r (b, some i, false)
    | .getElement r b _ _ _ | .ptrStride r b _ _ _ | .cast r .arrayToPtrDecay b _ _ => h.insert r (b, none, false)
    | .cast r .bitcast b _ _ => h.insert r (b, none, true)
    | _ => h) {}
  -- the object a pointer designates part of: its alloca, the path of members down to the first
  -- element, offset or cast (what lies below is part of that member), and whether a cast is on
  -- the way
  let rec root (fuel : Nat) (v : VId) (path : List Nat) (cast : Bool) : Option (VId × List Nat × Bool) :=
    if allocas.contains v then some (v, path, cast) else
    match fuel, step[v]? with
    | fuel + 1, some (b, some i, c) => root fuel b (i :: path) (cast || c)
    | fuel + 1, some (b, none, c) => root fuel b [] (cast || c)
    | _, _ => none
  let rooted := accesses.filterMap fun (a, vol) => (root 64 a [] false).map fun (o, p, c) => (o, p, vol, c)
  let svol : List (VId × List Nat × Bool) := ((rooted.map fun (o, p, _, _) => (o, p)).eraseDups).filterMap
    fun (o, p) =>
      let acc := rooted.filter fun (o', p', _, _) => o' == o && p' == p
      if acc.any (fun (_, _, v, _) => !v) then some (o, p, false)
      else if acc.any (fun (_, _, _, c) => !c) then some (o, p, true)
      else none
  let vol := (accesses.filterMap fun (a, v) => if v && (root 64 a [] false).isNone then some a else none).eraseDups
  let consts := ops.filterMap fun op => match op with
    | .const r _ (.int _) => some r
    | _ => none
  nestRegion vol svol consts body

/-! ### va_end before a return -/

/-- `op` with `f` applied to its nested regions. -/
def mapRegions (f : Region → Region) : Op → Op
  | .scope res r => .scope res (f r)
  | .cleanupScope k a b => .cleanupScope k (f a) (f b)
  | .ifOp c a b => .ifOp c (f a) (f b)
  | .ternary res c a b => .ternary res c (f a) (f b)
  | .forOp loc a b c cl => .forOp loc (f a) (f b) (f c) (cl.map fun (k, r) => (k, f r))
  | .whileOp loc a b cl => .whileOp loc (f a) (f b) (cl.map fun (k, r) => (k, f r))
  | .doWhileOp loc a b => .doWhileOp loc (f a) (f b)
  | .switch c t r => .switch c t (f r)
  | .case k vs r => .case k vs (f r)
  | .tryOp b hs u => .tryOp (f b) (hs.map fun (k, r) => (k, f r)) (u.map f)
  | op => op

/-- `Op.allocaConst` back to `Op.alloca` for `slots`, in nested regions too. A
const object keeps a plain stack slot when it is a parameter (`T *const p`,
`const int n`, a C++ reference parameter: the slot its argument is stored into,
possibly inside a `cir.try`), initialized again in each iteration of a loop
(`PState.reinitSlots`), or declared in a function with a label or a `setjmp`
call (a backward `goto` or a `longjmp` runs its declaration again): modifying
it is not detected. (The parameters' slots unchanged, the generated modules of
existing proofs stay the same: cJSON has 88 const parameters and no other const
object.) -/
partial def plainSlots (slots : Array VId) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (ops.map fun op => match op with
    | .allocaConst r t n => if slots.contains r then .alloca r t n else op
    | op => mapRegions (plainSlots slots) op))

mutual
/-- Whether some operation of `ops` or of their regions satisfies `p`. -/
partial def anyOp (p : Op → Bool) (ops : List Op) : Bool :=
  ops.any fun op => p op || (match op with
    | .scope _ r | .switch _ _ r | .case _ _ r => anyOpRegion p r
    | .cleanupScope _ a b | .ifOp _ a b | .ternary _ _ a b | .doWhileOp _ a b =>
      anyOpRegion p a || anyOpRegion p b
    | .forOp _ a b c cl => anyOpRegion p a || anyOpRegion p b || anyOpRegion p c ||
      cl.any fun (_, r) => anyOpRegion p r
    | .whileOp _ a b cl => anyOpRegion p a || anyOpRegion p b || cl.any fun (_, r) => anyOpRegion p r
    | .tryOp b hs u => anyOpRegion p b || hs.any (fun (_, r) => anyOpRegion p r) || u.any (anyOpRegion p)
    | _ => false)
partial def anyOpRegion (p : Op → Bool) : Region → Bool
  | .mk bs => bs.any fun (.mk _ ops) => anyOp p ops
end

mutual
/-- `ops` with a `vaEndCheck` before each `cir.return`, in nested regions too. -/
partial def checkVaEndOps : List Op → List Op
  | [] => []
  | op@(.ret _) :: rest => .vaEndCheck :: op :: checkVaEndOps rest
  | op :: rest => mapRegions checkVaEndRegion op :: checkVaEndOps rest
partial def checkVaEndRegion : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (checkVaEndOps ops))
end

/-! ### `__builtin_longjmp` beside `__builtin_setjmp`

GCC's manual (Nonlocal Gotos): "Because `__builtin_longjmp` depends on the function return mechanism
to restore the stack context, it cannot be called from the same function calling `__builtin_setjmp`
to initialize `buf`. It can only be called from a function called (directly or indirectly) from the
function calling `__builtin_setjmp`." In a function that calls both, each call of `__builtin_longjmp`
becomes an `Op.fail`, whatever buffer it is given: undefined for the function's own buffer, and not
modelled (reported as undefined) for a buffer that a caller set (a handler re-raising), which GCC
allows; telling them apart needs the activation that set the buffer, at run time. -/

mutual
/-- `ops` with each call of `__builtin_longjmp` an `Op.fail`, in nested regions too. -/
partial def failBuiltinLongjmpOps : List Op → List Op
  | [] => []
  | .call _ _ (.direct "__builtin_longjmp") _ _ _ _ :: rest =>
    .fail ("__builtin_longjmp in the function that calls __builtin_setjmp (GCC: only from a function it " ++
      "calls; to a buffer a caller set, not modelled)") ::
      failBuiltinLongjmpOps rest
  | op :: rest => mapRegions failBuiltinLongjmpRegion op :: failBuiltinLongjmpOps rest
partial def failBuiltinLongjmpRegion : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (failBuiltinLongjmpOps ops))
end

/-! ### The words of `__builtin_setjmp`'s buffer

Before a `cir.eh.setjmp`, CIR stores the frame address (`cir.frame_address`) in the first word of the
buffer and the stack pointer (`cir.stacksave`) in its third, as GCC's protocol has it; the second,
the resume address, is left to the lowering of the setjmp. The semantics keeps its own token in the
second word (`Std.jmpTokenAt`) and needs neither, so those six operations are dropped: the buffer
may then be an array of pointers or of `intptr_t` (as GCC's manual declares it), and the frame
address, of which the semantics has no model, is not needed. `cir.frame_address` elsewhere
(`__builtin_frame_address`) stays `Op.unknown`. -/

mutual
/-- `ops` without the stores of the frame address and the stack pointer before each call of
`__builtin_setjmp`, in nested regions too. -/
partial def dropSetjmpWordOps : List Op → List Op
  | [] => []
  | op :: rest =>
    match op :: rest with
    | .unknown "cir.frame_address" [f] :: .store f' e _ :: .stackSave s :: .const c _ (.int 2) ::
        .ptrStride q e' c' _ _ :: .store s' q' _ ::
        sj@(.call _ _ (.direct "__builtin_setjmp") (e'' :: _) _ _ _) :: rest' =>
      if f == f' && s == s' && c == c' && q == q' && e == e' && e == e'' then sj :: dropSetjmpWordOps rest'
      else mapRegions dropSetjmpWordRegion op :: dropSetjmpWordOps rest
    | _ => mapRegions dropSetjmpWordRegion op :: dropSetjmpWordOps rest
partial def dropSetjmpWordRegion : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (dropSetjmpWordOps ops))
end

mutual
/-- `ops`, in the region of the `va_list` objects `aps` (`top`: at its top level) or nested in it
(`loop`, `sw`: inside a loop or a switch that is itself in that region), with `vaEndCheckOf aps`
before each exit from that region: its `cir.yield`, a `break` or `continue` of a loop or switch
around it, a `goto` to a label outside it (`labels`: those inside; a `return` has `vaEndCheck`). -/
partial def vaExitOps (aps : List VId) (labels : List String) (top loop sw : Bool) : List Op → List Op
  | [] => []
  | op :: rest =>
    let exits := match op with
      | .yield _ => top
      | .brk => !loop && !sw
      | .cont => !loop
      | .goto l => !labels.contains l
      | _ => false
    (if exits then [.vaEndCheckOf aps] else []) ++ vaExitOp aps labels loop sw op ::
      vaExitOps aps labels top loop sw rest
partial def vaExitOp (aps : List VId) (labels : List String) (loop sw : Bool) : Op → Op
  | .forOp l a b c cl =>
    .forOp l (vaExitRegion aps labels true sw a) (vaExitRegion aps labels true sw b) (vaExitRegion aps labels true sw c)
      (cl.map fun (k, r) => (k, vaExitRegion aps labels true sw r))
  | .whileOp l a b cl =>
    .whileOp l (vaExitRegion aps labels true sw a) (vaExitRegion aps labels true sw b)
      (cl.map fun (k, r) => (k, vaExitRegion aps labels true sw r))
  | .doWhileOp l a b => .doWhileOp l (vaExitRegion aps labels true sw a) (vaExitRegion aps labels true sw b)
  | .switch c t r => .switch c t (vaExitRegion aps labels loop true r)
  | op => mapRegions (vaExitRegion aps labels loop sw) op
partial def vaExitRegion (aps : List VId) (labels : List String) (loop sw : Bool) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (vaExitOps aps labels false loop sw ops))
end

mutual
/-- `ops` with each nested region that has `va_list` objects of its own (`cir.alloca`s of
`__va_list_tag[1]` at its top level) checking them at each of its exits (`vaExitOps`): the end
of their block without `va_end` is undefined (C11 7.16.1p1, 7.16.1.3p2), which the check before
a `return` does not see once the block is gone. -/
partial def vaScopeOps (ops : List Op) : List Op := ops.map (mapRegions vaScopeRegion)
partial def vaScopeRegion : Region → Region
  | .mk bs =>
    let bs := bs.map fun (.mk args ops) => Block.mk args (vaScopeOps ops)
    let aps := bs.flatMap fun (.mk _ ops) => ops.filterMap fun op => match op with
      | .alloca r (.array (.record "__va_list_tag") 1) _ => some r
      | _ => none
    if aps.isEmpty then .mk bs else
    let labels := (allOpsRegion (.mk bs)).filterMap fun op => match op with
      | .label l => some l
      | _ => none
    -- a block without a terminator ends the region there (CIR's implicit `cir.yield`)
    let ends (ops : List Op) : Bool := match ops.getLast? with
      | some (.yield _) | some .brk | some .cont | some (.goto _) | some (.ret _) | some (.br ..)
      | some (.brcond ..) | some (.condition _) | some .trap | some .unreachable | some (.throw ..)
      | some (.resume _) | some (.indirectGoto ..) => false
      | _ => true
    .mk (bs.map fun (.mk args ops) =>
      .mk args (vaExitOps aps labels true false false ops ++ (if ends ops then [.vaEndCheckOf aps] else [])))
end

/-! ### `initializer_list` begins

CIR builds an `std::initializer_list<T>` by storing the address of its backing array, a
`T(*)[N]`, through a bitcast of the address of its `const T*` field:

    %c = cir.cast bitcast %f : !cir.ptr<!cir.ptr<T>> -> !cir.ptr<!cir.ptr<!cir.array<T x N>>>
    cir.store %arr, %c : !cir.ptr<!cir.array<T x N>>, !cir.ptr<!cir.ptr<!cir.array<T x N>>>

The field points to the first element (C++ [dcl.init.list]p5: `begin()` is a pointer to it), so
the store becomes the store of `&arr[0]` into the field as declared, through a fresh value:

    %d = cir.cast array_to_ptrdecay %arr : !cir.ptr<!cir.array<T x N>> -> !cir.ptr<T>
    cir.store %d, %f : !cir.ptr<T>, !cir.ptr<!cir.ptr<T>>

The bitcast stays (its result is not used any more). -/

/-- The stores to rewrite in a function body whose operations are `ops`: for each bitcast from
the address of a `T*` to the address of a `T(*)[N]` that exactly one store of a `T(*)[N]` uses
as its address, (bitcast result, fresh value from `next` on, bitcast source, `T`). -/
def initListBegins (ops : List Op) (next : Nat) : List (VId × VId × VId × Ty) :=
  let casts := ops.filterMap fun op => match op with
    | .cast c .bitcast f (.ptr (.ptr t)) (.ptr (.ptr (.array t' _))) => if t == t' then some (c, f, t) else none
    | _ => none
  let stores (c : VId) (t : Ty) : Nat := (ops.filter fun op => match op with
    | .store _ a (.ptr (.array t' _)) => a == c && t == t'
    | _ => false).length
  (casts.filter fun (c, _, t) => stores c t == 1).zipIdx.map fun ((c, f, t), k) => (c, next + k, f, t)

mutual
/-- `ops` with the stores of `initListBegins` rewritten, in nested regions too. -/
partial def initListOps (begins : List (VId × VId × VId × Ty)) : List Op → List Op
  | [] => []
  | op@(.store v a ty) :: rest =>
    match begins.find? (·.1 == a), ty with
    | some (_, d, f, t), .ptr (.array t' _) =>
      if t == t' then .cast d .arrayToPtrDecay v ty (.ptr t) :: .store d f (.ptr t) :: initListOps begins rest
      else op :: initListOps begins rest
    | _, _ => op :: initListOps begins rest
  | op :: rest => mapRegions (initListRegion begins) op :: initListOps begins rest
partial def initListRegion (begins : List (VId × VId × VId × Ty)) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (initListOps begins ops))
end

/-! ### Functions, globals, module -/

partial def parseFunc : P FuncDecl := do
  -- fresh SSA numbering
  modify fun s =>
    { s with ssa := {}, ssaNames := #[], ssaLocs := #[], castResults := {}, accesses := #[], decays := {} }
  let mut internal := false
  repeat
    let t ← peek
    if t.kind == .at || t.kind == .eof then break
    if isI t "internal" || isI t "cir_private" then internal := true
    if isOpen t then skipBalanced else advance
  let symTok ← next
  unless symTok.kind == .at do throw s!"line {symTok.line}: expected function symbol"
  let sym := Lex.decodeString symTok.text
  modify fun s => { s with curFunc := sym }
  expectP "("
  let mut params : Array Ty := #[]
  let mut argIds : Array VId := #[]
  -- the file of the first parameter's location (the definition's file when the body has none)
  let mut paramFile : Option String := none
  if !(← optP ")") then
    repeat
      let t ← peek
      if isP t "..." then advance
      else if t.kind == .percent then
        let v ← operand
        expectP ":"
        let ty ← parseType
        skipAttrDicts
        if isI (← peek) "loc" then
          if paramFile.isNone then paramFile ← peekLocFile
          let _ ← parseLoc
        argIds := argIds.push v
        params := params.push ty
      else
        let ty ← parseType
        skipAttrDicts
        params := params.push ty
      if !(← optP ",") then break
    expectP ")"
  let mut ret : Ty := .void
  if (← optP "->") then
    if (← optP "(") then
      if !(← optP ")") then
        ret ← parseType
        skipAttrDicts
        expectP ")"
    else ret ← parseType
  -- trailing header items up to the body `{` or the end of the line
  let mut nothrow := false
  let mut noreturn := false
  let mut special : SpecialMember := .none
  let mut body : Option Region := none
  let mut alias : Option String := none
  let hdrLine ← lastLine
  repeat
    let t ← peek
    if t.kind == .eof || t.line != hdrLine then break
    if isI t "alias" && isP (← peek2) "(" then
      -- `alias(@g)`: another name of `g` (`Frontend.resolveAliases`)
      advance; advance
      let g ← next
      unless g.kind == .at do throw s!"line {g.line}: expected the symbol of an alias's target"
      alias := some (Lex.decodeString g.text)
      expectP ")"
    else if isI t "func_info" then
      advance
      let start ← getPos
      skipBalanced
      let txt ← tokensText start (← getPos)
      if (txt.splitOn "cxx_ctor").length > 1 then special := .ctor
      else if (txt.splitOn "cxx_dtor").length > 1 then special := .dtor
      else if (txt.splitOn "cxx_assign").length > 1 then
        special := if (txt.splitOn "move").length > 1 then .moveAssign else .copyAssign
    else if isI t "attributes" then
      advance
      let start ← getPos
      skipBalanced
      let c ← read
      for i in [start:(← getPos)] do
        let tk := c.toks[i]!
        if tk.kind == .ident && tk.text == "nothrow" then nothrow := true
        if tk.kind == .ident && tk.text == "noreturn" then noreturn := true
    else if isP t "{" then
      modify fun s => { s with argIds := argIds.toList, paramSlots := #[], loopDepth := 0 }
      modify fun s => { s with constDepth := {}, reinitSlots := #[], hasLabel := false }
      let r ← parseRegion argIds.toList
      let s ← get
      -- a backward `goto` or a `longjmp` runs a declaration again
      let rerun := s.hasLabel || (allOpsRegion r).any fun op => (setjmpCall? op).isSome
      let slots := s.paramSlots ++ s.reinitSlots ++
        (if rerun then s.constDepth.fold (fun acc a _ => acc.push a) #[] else #[])
      body := some (if slots.isEmpty then r else plainSlots slots r)
      break
    else if isI t "loc" && isP (← peek2) "(" then
      let _ ← parseLoc
    else if isOpen t then skipBalanced
    else advance
  -- a definition's location follows its body's closing brace
  let bodyFile ← if body.isSome then peekLocFile else pure none
  let _ ← skipRestOfLine
  let s ← get
  -- an initializer_list's begin points to the first element of its backing array (before
  -- `nestSetjmps`, like the va_end check below)
  let begins := match body with
    | some b => initListBegins (allOpsRegion b) s.ssa.size
    | none => []
  let bodyL := body.map (initListRegion begins)
  let names := begins.map fun (c, d, _, _) =>
    (d, ((s.ssaNames.toList.lookup c).getD s!"%{c}") ++ ".begin")
  -- a function that initializes a va_list checks before each return that it was ended (before
  -- `nestSetjmps`: `mapRegions` does not enter an `Op.setjmp`)
  let bodyV := match bodyL with
    | some (.mk bs) =>
      if bs.any (fun (.mk _ ops) => anyOp (fun op => match op with
          | .vaStart _ | .vaCopy .. => true
          | _ => false) ops) then some (vaScopeRegion (checkVaEndRegion (.mk bs))) else some (.mk bs)
    | none => none
  -- `__builtin_setjmp`: the buffer words of GCC's protocol dropped, and no `__builtin_longjmp` in
  -- the same function (GCC's rule; before `nestSetjmps`, like the va_end check)
  let bodyJ := bodyV.map fun b =>
    let calls (f : String) : Bool := (allOpsRegion b).any fun op => match op with
      | .call _ _ (.direct t) _ _ _ _ => t == f
      | _ => false
    if !calls "__builtin_setjmp" then b
    else if calls "__builtin_longjmp" then failBuiltinLongjmpRegion (dropSetjmpWordRegion b)
    else dropSetjmpWordRegion b
  -- a function that calls `setjmp`: each call holds the rest of its block
  let body' := match bodyJ with
    | some b => if (allOpsRegion b).any (fun op => (setjmpCall? op).isSome) then
        some (nestSetjmps s.accesses.toList b) else some b
    | none => none
  return { sym := sym, params := params.toList, ret := ret, body := body', internal := internal,
           nothrow := nothrow, noreturn := noreturn, special := special,
           ssaNames := s.ssaNames.toList ++ names, ssaLocs := s.ssaLocs.toList, alias := alias,
           srcFile := (bodyFile <|> paramFile).getD "",
           volPtrs := (s.accesses.toList.filterMap fun (a, v) => if v then some a else none).eraseDups }

partial def parseGlobal : P GlobalDecl := do
  let mut constant := false
  let mut internal := false
  repeat
    let t ← peek
    if t.kind == .at || t.kind == .eof then break
    if isI t "constant" then constant := true
    if isI t "internal" || isI t "cir_private" then internal := true
    if isOpen t then skipBalanced else advance
  let symTok ← next
  let sym := Lex.decodeString symTok.text
  let mut ty : Ty := .other "?"
  let mut init : Option Const := none
  -- `alias(@g)`: another name of the global `g` (`Frontend.resolveAliases`)
  let mut alias : Option String := none
  if isI (← peek) "alias" && isP (← peek2) "(" then
    advance; advance
    let g ← next
    unless g.kind == .at do throw s!"line {g.line}: expected the symbol of an alias's target"
    alias := some (Lex.decodeString g.text)
    expectP ")"
  if (← optP "=") then
    if isI (← peek) "ctor" || isI (← peek) "dtor" then
      -- a definition whose dynamic initialization or destruction is a region: zero-initialized
      -- first (C++ [basic.start.static]p2); `init := none` is a declaration's (`Module.initMem`)
      advance
      init := some .zero
      if (← optP ":") then ty ← parseType
    else
      let (c, ty?) ← parseAttr
      init := some c
      if let some t := ty? then ty := t
  else if (← optP ":") then
    ty ← parseType
  -- the guard variable of a dynamic initialization (`_ZGV…`, an `i64` in the Itanium ABI) is read
  -- inline only through its first byte (a `!s8i` load through a cast pointer), and the rest
  -- belongs to the `__cxa_guard_*` models: here it is that byte
  if sym.startsWith "_ZGV" && ty == .int true 64 then ty := .int true 8
  let _ ← skipRestOfLine
  return { sym := sym, ty := ty, init := init, constant := constant, internal := internal, alias := alias }

/-- Top-level operation sequence (inside the module braces, or the file). -/
partial def parseTopOps (inModule : Bool) : P (Array FuncDecl × Array GlobalDecl) := do
  let mut funcs : Array FuncDecl := #[]
  let mut globals : Array GlobalDecl := #[]
  repeat
    let t ← peek
    if t.kind == .eof then break
    if inModule && isP t "}" then advance; break
    if (t.kind == .bang || t.kind == .hash) && isP (← peek2) "=" then
      -- alias definition (only at file level)
      advance; advance
      let _ ← skipRestOfLine
    else if isI t "cir.func" then
      advance
      funcs := funcs.push (← parseFunc)
    else if isI t "cir.global" then
      advance
      globals := globals.push (← parseGlobal)
    else if isI t "module" && !inModule then
      break
    else
      advance
      let _ ← skipRestOfLine
  return (funcs, globals)

partial def parseTop (modName : String) : P Module := do
  -- skip leading aliases until `module` (or the first op when there is none)
  let mut found := false
  repeat
    let t ← peek
    if t.kind == .eof then break
    if isI t "module" then found := true; break
    if isI t "cir.func" || isI t "cir.global" then break
    advance
    let _ ← skipRestOfLine
  let mut name := modName
  let mut ptrBits : Option Nat := none
  let mut cxx := false
  let mut ctors : Array (String × Nat) := #[]
  let mut dtors : Array (String × Nat) := #[]
  let (funcs, globals) ← if found then do
      advance
      if (← peek).kind == .at then
        let t ← next
        if name.isEmpty then name := Lex.decodeString t.text
      if (← optI "attributes") then
        let i ← getPos
        skipBalanced
        ptrBits ← ptrBitsIn i (← getPos)
        cxx ← langCxxIn i (← getPos)
        ctors ← structorsIn "cir.global_ctor" i (← getPos)
        dtors ← structorsIn "cir.global_dtor" i (← getPos)
        let lc ← langCIn i (← getPos)
        modify fun s => { s with langC := lc }
      expectP "{"
      parseTopOps true
    else parseTopOps false
  let s ← get
  return { name := name, records := s.records.toList, globals := globals.toList,
           funcs := funcs.toList, ptrBytes := if ptrBits == some 32 then 4 else 8, cxx := cxx,
           ctors := ctors.toList, dtors := dtors.toList }

/-- Collect top-level alias definitions (first token of a line, followed by
`=`, outside any braces). -/
def collectAliases (toks : Array Token) : HashMap String Nat × HashMap String Nat := Id.run do
  let mut ty : HashMap String Nat := {}
  let mut at_ : HashMap String Nat := {}
  let mut depth : Nat := 0
  for h : i in [0:toks.size] do
    let t := toks[i]
    if t.kind == .punct && t.text == "{" then depth := depth + 1
    else if t.kind == .punct && t.text == "}" then depth := depth - 1
    else if depth == 0 && (t.kind == .bang || t.kind == .hash) &&
        (i == 0 || toks[i-1]!.line < t.line) then
      match toks[i+1]? with
      | some e =>
        if e.kind == .punct && e.text == "=" then
          if t.kind == .bang then ty := ty.insert t.text (i+2)
          else at_ := at_.insert t.text (i+2)
      | none => pure ()
  return (ty, at_)

/-- Parse a CIR module from its text, with the members' names that the `cir.get_member`
operations give (record name → member index → name, `PState.memberNames`). Demangled names and
library models are filled in by `CIR.Frontend.loadModule`. `recRename` replaces record names as
they are read. -/
def parseModuleNames (src : String) (modName : String := "") (recRename : HashMap String String := {}) :
    Except String (Module × HashMap String (HashMap Nat String)) := do
  let toks ← lex src
  let (tyA, atA) := collectAliases toks
  let ctx : Ctx := { toks := toks, tyAliases := tyA, attrAliases := atA, recRename := recRename }
  let (m, s) ← (parseTop modName).run ctx |>.run {}
  return (m, s.memberNames)

/-- Parse a CIR module from its text (`parseModuleNames` without the members' names). -/
def parseModule (src : String) (modName : String := "") (recRename : HashMap String String := {}) :
    Except String Module := do
  return (← parseModuleNames src modName recRename).1

end CIR.Frontend
