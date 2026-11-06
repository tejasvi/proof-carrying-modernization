/-
# Resolver: surface IR → core IR

Trusted Lean code that turns the extractor's output into the core IR the semantics runs:

* computes the storage layout from the data division and puts the resolved descriptor,
  table strides and `OCCURS` bounds into every data reference;
* resolves paragraph / section names to indices, numbers `PERFORM` statements;
* encodes literals in the program's character set (CP037 for EBCDIC);
* lowers `ADD`/`SUBTRACT`/`MULTIPLY`/`DIVIDE`/`COMPUTE` to `ArithOp`s, `EVALUATE` to `IF`
  chains, `SET ... TO TRUE` / `INITIALIZE` to `MOVE`s, level-88 names to comparisons;
* makes the intermediate scale of every division explicit, if the extractor did not give one
  (IBM rule: `max(d2 - d1, dmax)` decimal places, `d2` the dividend's and `d1` the divisor's
  (`decPlaces`), plus one when a receiver is `ROUNDED`); a `COMPUTE` whose whole expression is one
  division, with no `ROUNDED` receiver and only numeric receivers, keeps the scale `max(d1, dmax)`
  of earlier versions, which stores the same values; one with a receiver whose `ROUNDED MODE` IBM
  does not have (any other than `NEAREST-AWAY-FROM-ZERO` and `TRUNCATION`) is lowered as
  `DIVIDE ... GIVING` (`ArithOp.divGiving`): the exact quotient, rounded once into each receiver; a
  quotient inside a larger expression keeps IBM's intermediate scale under every mode;
* gives a power whose exponent is an integral data item or expression (`Surface.Expr.powE`)
  the intermediate scale `dmax` (IBM's fixed-point rule for such an exponent), and so a power by a
  literal exponent whose places reach 30 digits by IBM's exponentiation table (`capW`);
* lowers a power by the literal exponent 0 to `Expr.pow0`: its base is evaluated, and zero raised
  to zero power is a size error, the statement's in a `COMPUTE` with `ON SIZE ERROR`, unsupported
  in one with only `NOT ON SIZE ERROR` (`markPow0`);
* carries an intermediate result that can need more than 30 digits with the places IBM carries
  (`cap30`: `Expr.ir30`; `Expr.ir30open` where IBM's text leaves them open), except in an
  expression with a division whose places the extractor gave;
* takes IBM's `dmax`: in a `COMPUTE`, the most decimal places of its receivers (a numeric-edited
  receiver's digit positions after the point too) and of its operands outside divisors and
  exponents, an integer function contributing none (`dScales`); for the arithmetic expressions of
  conditions, in a relation the most decimal places
  of any operand of either comparand, in a sign condition and for an `EVALUATE` subject or object
  (`Surface.Cond.relOwn`) those of the expression's own operands; for the arithmetic expressions
  inside a function's arguments, in every statement, the function's inner-dmax (`innerDmax`), which
  depends on its arguments only;
* computes a `PROGRAM COLLATING SEQUENCE` given by an `ALPHABET` of literals (`collation`) and
  applies it: nonnumeric comparisons by its positions (`Cond.alnumCmpSeq`), `HIGH-VALUE` and
  `LOW-VALUE` as its highest and lowest characters, `ORD`, `CHAR`, `MAX`, `MIN`, `ORD-MAX` and
  `ORD-MIN` by it (by the native order in every other program).
-/
import Cobol.Frontend.Surface
import Cobol.Target.Codepage

namespace Cobol.Resolve
open Surface

/-- A collating sequence in the program's character set: the position of each byte value
(characters given with `ALSO` share one), the character `FUNCTION CHAR` returns for each
position (the first one given there), and the `HIGH-VALUE` and `LOW-VALUE` characters. -/
structure Collation where
  pos : List Nat
  chars : List UInt8
  high : UInt8
  low : UInt8

/-- The native collating sequence: the byte order of the character set. -/
def Collation.native : Collation :=
  { pos := List.range 256, chars := (List.range 256).map UInt8.ofNat, high := 0xFF, low := 0 }

structure Ctx where
  cfg : Config
  dialect : Dialect
  L : Layout
  /-- Data division (for `INITIALIZE`). -/
  data : List Item
  /-- Condition names: id ↦ (parent id, values). -/
  conds : List (Nat × Nat × List CondVal)
  paraIdx : List (String × Nat)
  /-- Section name ↦ (first paragraph, last paragraph). -/
  sections : List (String × Nat × Nat)
  files : List Surface.FileDecl := []
  /-- `PROGRAM COLLATING SEQUENCE` with an `ALPHABET` given by literals (`none`: native order). -/
  seq : Option Collation := none
  /-- `OCCURS DEPENDING ON` tables. -/
  odo : List OdoDecl := []
  /-- Not read by this resolver: the expressions inside function arguments take the function's
  inner-dmax (`innerDmax`). The resolver before it, which `tests/DmaxResolve.lean` keeps as a
  verbatim copy for its old == new check, set and read this field. -/
  dmaxIn : Option Int := none

/-- Resolution monad: errors, and the next `PERFORM` statement id. -/
abbrev RM := StateT Nat (Except String)

def item (ctx : Ctx) (id : Nat) : Except String Placed :=
  match ctx.L.find? id with
  | some p => pure p
  | none => throw s!"unknown data item {id}"

/-- Encode source text in the program's character set. -/
def encodeStr (c : Config) (s : String) : Except String (List UInt8) :=
  match c.charset with
  | .ascii => pure (s.toList.map (fun ch => UInt8.ofNat ch.toNat))
  | .ebcdic =>
    match Codepage.encode037 s with
    | some bs => pure bs
    | none => throw s!"literal not representable in CP037: {s}"

def hexDigit (ch : Char) : Except String Nat :=
  if '0' ≤ ch ∧ ch ≤ '9' then pure (ch.toNat - '0'.toNat)
  else if 'A' ≤ ch ∧ ch ≤ 'F' then pure (ch.toNat - 'A'.toNat + 10)
  else if 'a' ≤ ch ∧ ch ≤ 'f' then pure (ch.toNat - 'a'.toNat + 10)
  else throw s!"bad hex digit {ch}"

partial def hexBytes : List Char → Except String (List UInt8)
  | [] => pure []
  | a :: b :: rest => do
    pure (UInt8.ofNat ((← hexDigit a) * 16 + (← hexDigit b)) :: (← hexBytes rest))
  | _ => throw "odd number of hex digits"

def figurative (c : Config) (name : String) : Except String Figurative :=
  match name.toUpper with
  | "ZERO" | "ZEROS" | "ZEROES" => pure .zero
  | "SPACE" | "SPACES" => pure .space
  | "HIGH-VALUE" | "HIGH-VALUES" => pure .high
  | "LOW-VALUE" | "LOW-VALUES" => pure .low
  | "QUOTE" | "QUOTES" => pure .quote
  | n => let _ := c; throw s!"unknown figurative constant {n}"

def sub (ctx : Ctx) : Sub → Except String SubExpr
  | .lit n => pure (.lit n)
  | .item id k => do pure (.ref (← item ctx id).desc k)
  | .idx i k => pure (.idx i k)

/-! ### `OCCURS DEPENDING ON`

The layout gives an `OCCURS integer-1 TO integer-2 DEPENDING ON` table `integer-2` occurrences,
as IBM allocates it. A group containing the table has that maximum length, which is what a
receiving group containing the table's object uses (IBM's maximum length rule); a reference made
while the object holds `v` (`Ref.odo = some v`) gets the group with `v` occurrences. Only tables
that end every group containing them are accepted: no variably located items. -/

/-- The groups containing item `id`, outermost first (`none`: no such item). -/
partial def itemPath (id : Nat) : List Item → Option (List Item)
  | [] => none
  | it :: rest =>
    if it.id == id then some []
    else match itemPath id it.children with
      | some p => some (it :: p)
      | none => itemPath id rest

/-- Placement, element length and `integer-2` of an `OCCURS DEPENDING ON` table, which must not be
inside another table. -/
def odoTable (ctx : Ctx) (o : OdoDecl) : Except String (Placed × Nat × Nat) := do
  let tp ← item ctx o.subject
  match tp.dims with
  | [(stride, mx)] => pure (tp, stride, mx)
  | _ => throw s!"OCCURS DEPENDING ON table {tp.name} inside another table"

/-- Descriptor of the item of reference `r` (placement `p`): the declared one, or with `odo = some v`
the group with `v` occurrences of the `OCCURS DEPENDING ON` table it contains. -/
def odoDesc (ctx : Ctx) (r : Ref) (p : Placed) : Except String FieldDesc :=
  match r.odo with
  | none => pure p.desc
  | some v => do
    let some o := ctx.odo.find? (fun o =>
        ((itemPath o.subject ctx.data).getD []).any (·.id == r.item))
      | throw s!"item {p.name}: not a group containing an OCCURS DEPENDING ON table"
    let (tp, stride, mx) ← odoTable ctx o
    unless o.min ≤ v ∧ v ≤ mx do
      throw s!"item {p.name}: {v} occurrences of {tp.name}, outside {o.min} to {mx}"
    unless tp.desc.off + mx * stride == p.desc.off + p.desc.len do
      throw s!"item {p.name}: the OCCURS DEPENDING ON table {tp.name} does not end it"
    pure { p.desc with len := p.desc.len - (mx - v) * stride }

def ref (ctx : Ctx) (r : Ref) : Except String DataRef := do
  let p ← item ctx r.item
  if r.subs.length ≠ p.dims.length then
    throw s!"item {p.name}: {r.subs.length} subscripts for {p.dims.length} table levels"
  let subs ← (r.subs.zip p.dims).mapM (fun (s, stride, n) => do
    pure ({ e := ← sub ctx s, stride, max := n } : Subscript))
  let refmod ← match r.refStart with
    | none => pure none
    | some st => do pure (some ({ start := ← sub ctx st, len := ← r.refLen.mapM (sub ctx) } : RefMod))
  pure { item := r.item, desc := ← odoDesc ctx r p, subs, refmod }

def lit (ctx : Ctx) : Lit → Except String Operand
  | .num v s d => pure (.num v s d)
  | .str s => do pure (.alnum (← encodeStr ctx.cfg s))
  | .hex h => do pure (.alnum (← hexBytes h.toList))
  | .fig n => do
    let f ← figurative ctx.cfg n
    -- in a program collating sequence, HIGH-VALUE and LOW-VALUE are its highest and lowest characters
    match ctx.seq, f with
    | some s, .high => pure (.fig (.all [s.high]))
    | some s, .low => pure (.fig (.all [s.low]))
    | _, _ => pure (.fig f)
  | .all s => do pure (.fig (.all (← encodeStr ctx.cfg s)))

def operand (ctx : Ctx) : Surface.Operand → Except String Cobol.Operand
  | .ref r => do pure (.ref (← ref ctx r))
  | .lit l => lit ctx l
  | .fn name args => do
    match name.toUpper, args with
    | "UPPER-CASE", [a] => pure (.afn .upperCase (← operand ctx a))
    | "LOWER-CASE", [a] => pure (.afn .lowerCase (← operand ctx a))
    | "REVERSE", [a] => pure (.afn .reverse (← operand ctx a))
    -- functions of the collating sequence (alphanumeric MAX / MIN come as nested pairs from the
    -- front end: MAX (MAX (a, b), c) is MAX (a, b, c), the leftmost greatest)
    | "CHAR", [a] => pure (.chr (← operand ctx a) (ctx.seq.getD .native).chars)
    | "MAX", [a] => operand ctx a
    | "MIN", [a] => operand ctx a
    | "MAX", [a, b] => pure (.amax true (← operand ctx a) (← operand ctx b) (ctx.seq.getD .native).pos)
    | "MIN", [a, b] => pure (.amax false (← operand ctx a) (← operand ctx b) (ctx.seq.getD .native).pos)
    | n, _ => throw s!"unsupported intrinsic function {n}"

/-- The operand is numeric (numeric item or numeric literal). -/
def isNumeric (ctx : Ctx) : Surface.Operand → Bool
  | .ref r =>
    match ctx.L.find? r.item with
    | some p => r.refStart.isNone && (match p.desc.kind with | .num _ => true | _ => false)
    | none => false
  | .lit (.num ..) => true
  | _ => false

/-- Scale of an item (0 if not numeric). -/
def refScale (ctx : Ctx) (id : Nat) : Int :=
  match ctx.L.find? id with
  | some { desc := { kind := .num f, .. }, .. } => f.scale
  | _ => 0

/-- Decimal places of a receiving item: a numeric item's scale, a numeric-edited item's digit
positions after the decimal point (IBM's `dmax` counts "the number of decimal places needed for the
final result field or fields"; `Sem.storeEdited` stores to those places), 0 otherwise. -/
def rcvScale (ctx : Ctx) (id : Nat) : Int :=
  match ctx.L.find? id with
  | some { desc := { kind := .numEdited pic _, .. }, .. } => (Edit.fracDigits ((Edit.classify pic).getD []) : Int)
  | _ => refScale ctx id

/-- Reference `r` is a numeric (not numeric-edited, not reference-modified) item with at most
`min s t` decimal places. -/
def numRcvWithin (ctx : Ctx) (r : Surface.Ref) (s t : Int) : Bool :=
  match ctx.L.find? r.item with
  | some { desc := { kind := .num f, .. }, .. } => r.refStart.isNone && decide (f.scale ≤ min s t)
  | _ => false

/-- IBM's number of decimal places `d` of an operand or intermediate result (Programming Guide,
"Terminology used for intermediate results" and the table "Addition, subtraction, multiplication,
and division"): a literal's or data item's decimal places (none for an item scaled by `P`s left of
its assumed decimal point, whose scale is negative here), the larger of the operands' for `+` and
`-`, their sum for `*`; any other result its scale (a quotient's places, a function's). -/
def decPlaces : Cobol.Expr → Int
  | .neg a => decPlaces a
  | .add a b | .sub a b => max (decPlaces a) (decPlaces b)
  | .mul a b => decPlaces a + decPlaces b
  | e => max 0 e.scale

/-- Decimal places of the leaves of an expression, excluding divisors and exponents (the
operands that count for IBM's `dmax`). -/
def dScales (ctx : Ctx) : Surface.Expr → List Int
  | .lit _ s => [s]
  | .ref r => [refScale ctx r.item]
  | .idx _ => [0]
  | .neg a => dScales ctx a
  | .add a b | .sub a b | .mul a b => dScales ctx a ++ dScales ctx b
  | .div a _ _ => dScales ctx a
  | .pow a _ => dScales ctx a
  | .fn name args =>
    -- integer functions of integer arguments contribute no decimal places (IBM outer-dmax 0)
    if ["FACTORIAL", "INTEGER-OF-DATE", "DATE-OF-INTEGER", "INTEGER-OF-DAY",
        "DAY-OF-INTEGER"].contains name.toUpper then [0]
    -- ORD-MAX / ORD-MIN are integer functions of arguments of any scale
    else if ["ORD-MAX", "ORD-MIN"].contains name.toUpper then [0]
    -- INTEGER, INTEGER-PART and MOD too (IBM: "Integer intrinsic functions return an integer; thus
    -- their outer-dmax is always zero")
    else if ["INTEGER", "INTEGER-PART", "MOD"].contains name.toUpper then [0]
    else args.flatMap (dScales ctx)
  | .afn _ _ => [0]
  | .powE a _ => dScales ctx a

/-- IBM's inner-dmax of function `name` with arguments `args`: the `dmax` of the arithmetic
expressions inside its arguments. IBM (Programming Guide, "Terminology used for intermediate
results"): the largest of "The number of decimal places defined for any of its elementary
arguments", "The dmax for any of its arithmetic expression arguments" and "The outer-dmax for any
of its embedded functions", that is the most decimal places of `dScales` over all of its arguments;
0 for the integer functions whose arguments must all be integers ("Intrinsic functions evaluated in
fixed-point arithmetic": "the inner-dmax is thus also always zero", the functions its table lists
with 0). It depends on the function's arguments only (Language Reference, "Function definition and
evaluation": "function evaluation is not affected by operations or operands outside the function";
"Arguments": "The computation of an arithmetic expression that appears as a function argument is
affected by other arguments for that function"). -/
def innerDmax (ctx : Ctx) (name : String) (args : List Surface.Expr) : Int :=
  if ["DATE-OF-INTEGER", "DATE-TO-YYYYMMDD", "DAY-OF-INTEGER", "DAY-TO-YYYYDDD", "FACTORIAL",
      "INTEGER-OF-DATE", "INTEGER-OF-DAY", "MOD", "YEAR-TO-YYYY"].contains name.toUpper then 0
  else (args.flatMap (dScales ctx)).foldl max 0

/-- `FUNCTION ORD-MAX` (`mx`) / `ORD-MIN` of numeric arguments as an exact integer expression.
With `best` the greatest (least) argument so far and `i` its position, argument `k` takes over
iff `g = [x > best]` (`[x < best]`) is 1: `i := i * (1 - g) + k * g`, so ties keep the leftmost.
`[x > y]` is `MIN (1, MAX (0, (x - y) * 10^s))`, `s` the scale of `x - y`: the difference in
units of `10^-s` is an integer. -/
def ordMinMax (mx : Bool) (a : Cobol.Expr) (rest : List Cobol.Expr) : Cobol.Expr :=
  let gt (x y : Cobol.Expr) : Cobol.Expr :=
    let d := Cobol.Expr.sub x y
    .min (.lit 1 0) (.max (.lit 0 0) (.mul d (.lit 1 (-d.scale))))
  let step := fun (acc : Cobol.Expr × Cobol.Expr × Nat) (x : Cobol.Expr) =>
    let (best, i, k) := acc
    let g := if mx then gt x best else gt best x
    ((if mx then Cobol.Expr.max best x else .min best x),
     Cobol.Expr.add (.mul i (.sub (.lit 1 0) g)) (.mul (.lit (k : Int) 0) g), k + 1)
  (rest.foldl step (a, .lit 1 0, 2)).2.1

/-- Lower an arithmetic expression; `dmax` and `rounded` drive the division rule. -/
partial def expr (ctx : Ctx) (dmax : Int) (rounded : Bool) : Surface.Expr → Except String Cobol.Expr
  | .lit v s => pure (.lit v s)
  | .ref r => do
    let d ← ref ctx r
    match d.desc.kind with
    | .num _ => if d.refmod.isNone then pure (.ref d) else throw "reference-modified operand in arithmetic"
    | _ => throw s!"non-numeric item {r.item} in an arithmetic expression"
  | .idx i => pure (.idx i)
  | .neg a => do pure (.neg (← expr ctx dmax rounded a))
  | .add a b => do pure (.add (← expr ctx dmax rounded a) (← expr ctx dmax rounded b))
  | .sub a b => do pure (.sub (← expr ctx dmax rounded a) (← expr ctx dmax rounded b))
  | .mul a b => do pure (.mul (← expr ctx dmax rounded a) (← expr ctx dmax rounded b))
  | .div a b s => do
    let a' ← expr ctx dmax rounded a
    let b' ← expr ctx dmax rounded b
    -- IBM: "(d2 - d1) or dmax, whichever is greater" decimal places (d2 the dividend's, d1 the
    -- divisor's), one more when a receiver is ROUNDED
    let sc := match s with
      | some s => s
      | none => max (decPlaces a' - decPlaces b') dmax + (if rounded && ctx.dialect.divExtraForRounded then 1 else 0)
    pure (.div a' b' sc .truncation)
  | .pow a n => do
    let a' ← expr ctx dmax rounded a
    -- the literal exponent 0: the base is still evaluated, 0 ** 0 is a size error (`Expr.pow0`; the
    -- statement's SIZE ERROR phrases are marked by `markPow0`)
    if n = 0 then return .pow0 a' false false
    pure ((List.replicate n a').foldl (fun acc x => .mul acc x) (.lit 1 0))
  | .fn name args => do
    -- the arguments with the function's inner-dmax, whatever the statement around the function
    -- (its receivers, its other operands, its ROUNDED phrase)
    let as ← args.mapM (expr ctx (innerDmax ctx name args) false)
    match name.toUpper, as with
    | "ABS", [a] => pure (.abs a)
    | "INTEGER", [a] => pure (.integer a)
    | "INTEGER-PART", [a] => pure (.integerPart a)
    | "MOD", [a, b] => pure (.mod a b)
    | "REM", [a, b] => pure (.rem a b)
    | "MIN", a :: rest => pure (rest.foldl .min a)
    | "MAX", a :: rest => pure (rest.foldl .max a)
    -- IBM: SUM adds the arguments in order to 0; RANGE subtracts MIN from MAX (exact)
    | "SUM", a :: rest => pure (rest.foldl .add a)
    | "RANGE", a :: rest => pure (.sub (rest.foldl .max a) (rest.foldl .min a))
    | "FACTORIAL", [a] => pure (.factorial a)
    | "INTEGER-OF-DATE", [a] => pure (.dateFn .integerOfDate a)
    | "DATE-OF-INTEGER", [a] => pure (.dateFn .dateOfInteger a)
    | "INTEGER-OF-DAY", [a] => pure (.dateFn .integerOfDay a)
    | "DAY-OF-INTEGER", [a] => pure (.dateFn .dayOfInteger a)
    | "ORD-MAX", a :: rest => pure (ordMinMax true a rest)
    | "ORD-MIN", a :: rest => pure (ordMinMax false a rest)
    | n, _ => throw s!"unsupported intrinsic function {n}"
  | .afn name args => do
    let as ← args.mapM (operand ctx)
    let pos := (ctx.seq.getD .native).pos
    match name.toUpper, as with
    | "ORD", [a] => pure (.ord a pos)
    | "ORD-MAX", _ :: _ => pure (.ordA true as pos)
    | "ORD-MIN", _ :: _ => pure (.ordA false as pos)
    | n, _ => throw s!"unsupported intrinsic function {n}"
  | .powE a e => do
    -- IBM: with an integral data-name or variable as the exponent, the power is held with dmax
    -- decimal places; with ROUNDED one more place "might be carried", which is not modelled
    if rounded then throw "exponent other than a literal under ROUNDED"
    pure (.powInt (← expr ctx dmax rounded a) (← expr ctx dmax rounded e) dmax)

/-! ### Intermediate results of more than 30 digits

IBM carries a fixed-point intermediate result with the integer and decimal places `i`, `d` of the
Programming Guide's table "Addition, subtraction, multiplication, and division"; when `i + d` exceeds
30 (compatibility mode, `ARITH(COMPAT)`), with those of the table after it: `30 - d` integer and `d`
decimal places if `d ≤ dmax`; `i` integer and `30 - i` decimal places if `d > dmax` and
`i + dmax ≤ 30`; `30 - dmax` integer and `dmax` decimal places otherwise.  The decimal places are cut
at compile time; an integer digit cut at run time that is not 0 makes IBM write message IGZ0036W and
go on (`Expr.ir30`).  The final result of an arithmetic statement with one receiver and no `ROUNDED`
is no intermediate result (IBM's example: "Add ir5 to ir1 yielding Y"); every operation of a
condition, a function's steps and result, and a power are.  A power by a literal exponent `n` has
`d = d1 * n` and `i = i1 * n` (for a literal base the integer digits of the power); with `i + d` over
30, or 30 and an even number of digits in the base, IBM holds it as for an integral data-name
exponent, with `dmax` decimal and `30 - dmax` integer places (`Expr.powInt`).  `ADD` and `SUBTRACT`
carry enough places (IBM: with a composite of operands of at most 30 digits "no significant digits
are lost") and stay as they are, and so does an expression with a division whose places the
extractor gave (`--div-scale`, the GnuCOBOL comparison profile, not IBM's rule).  Where IBM's text
leaves the places open and they decide the result, the result is `Expr.ir30open`: `ROUNDED` ("one
more integer [decimal] place might be carried"), unary minus ("Multiplication by -1"), the `dmax`
inside function arguments (open reading R1), index names and binary items that can hold more digits
than their PICTURE, `MAX` / `MIN` whose arguments need more than 30 digits together. -/

/-- Decimal digits of `n` (`0` has none). -/
def natDigits (n : Nat) : Int := if n = 0 then 0 else ((Nat.toDigits 10 n).length : Int)

/-- IBM's integer (`i`) and decimal (`d`) places of an operand or intermediate result, as ranges
over the readings IBM's text leaves open. -/
structure Places where
  iLo : Int
  iHi : Int
  dLo : Int
  dHi : Int
  deriving Inhabited

def Places.exact (i d : Int) : Places := ⟨i, i, d, d⟩

/-- Places of an expression shape the 30-digit rule does not know (never taken as within 30). -/
def Places.unknown : Places := ⟨0, 99, 0, 99⟩

/-- Places of a sum or difference: "(i1 or i2) + 1, whichever is greater", "d1 or d2, whichever is
greater". -/
def Places.add (a b : Places) : Places :=
  ⟨max a.iLo b.iLo + 1, max a.iHi b.iHi + 1, max a.dLo b.dLo, max a.dHi b.dHi⟩

/-- Places of a product: "i1 + i2", "d1 + d2". -/
def Places.mul (a b : Places) : Places :=
  ⟨a.iLo + b.iLo, a.iHi + b.iHi, a.dLo + b.dLo, a.dHi + b.dHi⟩

/-- How a result is used: the final result of an arithmetic statement (no intermediate result), an
intermediate result, or either one (a unary minus may or may not be an operation of its own). -/
inductive IrUse where
  | final | ir | maybe
  deriving DecidableEq, Inhabited

/-- The `dmax` range of an expression (one value outside function arguments), whether its statement
has `ROUNDED`, and the `dmax` and extra `ROUNDED` place `expr` gave its divisions. -/
structure IrEnv where
  mLo : Int
  mHi : Int
  rounded : Bool
  lowD : Int
  divExtra : Bool
  /-- Inside a function argument, which `expr` lowers with the function's inner-dmax (`innerDmax`)
  and without `ROUNDED`: a quotient there whose operand this analysis cut stops (`inArgWhy`), since
  `lowD` and `rounded` are the statement's. -/
  inArg : Bool := false
  /-- Inside an argument of a function whose inner-dmax lies outside this range (0 for `MOD`,
  `FACTORIAL` and the integer-date functions): a 30-digit cut there stops (`inArgWhy`). -/
  zeroArg : Bool := false
  deriving Inhabited

/-- IBM's places of a numeric item: its PICTURE's integer and decimal places; a binary item that can
hold more digits than its PICTURE (`COMP-5`, `COMP` under `TRUNC(BIN)`) up to its storage's digits. -/
def itemPlaces (c : Config) (f : NumFmt) : Places :=
  let i := max 0 ((f.digits : Int) - f.scale)
  let d := max 0 f.scale
  if f.usage == .comp5 || (f.usage == .binary && c.trunc == .bin) then
    let cap : Int := match c.binBytes f.digits with
      | 1 => 3 | 2 => 5 | 4 => 10 | _ => 20
    ⟨i, max i (cap - f.scale), d, d⟩
  else Places.exact i d

/-- IBM's places of a literal: the integer digits of its value (the front end keeps no leading zeros;
IBM counts a literal base of a power by "the value") and its decimal places. -/
def litPlaces (v s : Int) : Places :=
  let ip := if 0 ≤ s then v.natAbs / 10 ^ s.toNat else v.natAbs * 10 ^ (-s).toNat
  Places.exact (natDigits ip) (max 0 s)

/-- The open point of an intermediate result over 30 digits inside a function argument where this
analysis does not follow `expr`, which lowers the argument with the function's inner-dmax and
without `ROUNDED`: the argument's `dmax` range (`capW`'s `envA`) does not hold that inner-dmax (0
for `MOD`, `FACTORIAL` and the integer-date functions), or a quotient's operand was cut, so the
places `expr` gave the quotient no longer apply. -/
def inArgWhy : String :=
  "intermediate result over 30 digits inside a function argument, places carried open (inner-dmax)"

/-- The open points that leave the places of an intermediate result undecided. -/
def openWhy (env : IrEnv) (u : IrUse) (p : Places) : String :=
  let pts := (if env.rounded then ["ROUNDED"] else []) ++
    (if env.mLo != env.mHi then ["dmax in a function argument"] else []) ++
    (if u == .maybe then ["unary minus"] else []) ++
    (if p.iLo != p.iHi || p.dLo != p.dHi then ["an index, binary or negated operand"] else [])
  "intermediate result over 30 digits, places carried open (" ++ ", ".intercalate pts ++ ")"

/-- IBM's places carried for the intermediate result `e` of places `p` used as `u`: `e` itself within
30 digits; else `Expr.ir30` with the places of IBM's table, or `Expr.ir30open` where the readings in
`p`, the `dmax` range or `u` carry it differently.  The flag tells whether `e` was wrapped. -/
def carry30 (env : IrEnv) (u : IrUse) (p : Places) (e : Cobol.Expr) : Cobol.Expr × Places × Bool :=
  if u == .final then (e, p, false) else
  let why := openWhy env u p
  -- ROUNDED: "one more integer [decimal] place might be carried"
  let p := if env.rounded then { p with iHi := p.iHi + 1, dHi := p.dHi + 1 } else p
  if p.iHi + p.dHi ≤ 30 then (e, p, false)
  else if env.zeroArg then (.ir30open e inArgWhy, p, true)
  else if p.dHi ≤ env.mLo then
    -- d ≤ dmax: "30-d integer and d decimal places": no decimal place is cut; the integer digits
    -- are checked against the fewest of the readings
    (.ir30 e (decPlaces e) (30 - p.dHi).toNat,
      { p with iLo := min p.iLo (30 - p.dHi), iHi := min p.iHi (30 - p.dLo) }, true)
  else if u == .ir && !env.rounded && env.mHi < p.dLo && 30 < p.iLo + p.dLo then
    if p.iLo == p.iHi && p.iHi + env.mHi ≤ 30 then
      -- d > dmax, i + dmax ≤ 30: "i integer and 30-i decimal places"
      (.ir30 e (30 - p.iLo) p.iLo.toNat, Places.exact p.iLo (30 - p.iLo), true)
    else if env.mLo == env.mHi && 30 < p.iLo + env.mLo then
      -- d > dmax, i + dmax > 30: "30-dmax integer and dmax decimal places"
      (.ir30 e env.mLo (30 - env.mLo).toNat, Places.exact (30 - env.mLo) env.mLo, true)
    else (.ir30open e why, p, true)
  else (.ir30open e why, p, true)

/-- `carry30` for a quotient whose decimal places are removed next (the first step of `FUNCTION
REM`): only its integer digits count, checked against the fewest any row of IBM's table carries. -/
def carryInt30 (env : IrEnv) (p : Places) (e : Cobol.Expr) : Cobol.Expr × Places × Bool :=
  let p := if env.rounded then { p with iHi := p.iHi + 1, dHi := p.dHi + 1 } else p
  if p.iHi + p.dHi ≤ 30 then (e, p, false)
  else if env.zeroArg then (.ir30open e inArgWhy, p, true)
  else
    let k := 30 - max p.dHi env.mHi
    (.ir30 e (decPlaces e) k.toNat, { p with iLo := min p.iLo k }, true)

/-- The operands of a left-nested chain of `k` operands of a binary node (`node x y` = `(x, y)`). -/
def unchain (node : Cobol.Expr → Option (Cobol.Expr × Cobol.Expr)) : Nat → Cobol.Expr →
    Option (List Cobol.Expr)
  | 0, _ => none
  | 1, e => some [e]
  | k + 2, e => do
    let (l, r) ← node e
    let xs ← unchain node (k + 1) l
    pure (xs ++ [r])

def minNode : Cobol.Expr → Option (Cobol.Expr × Cobol.Expr)
  | .min a b => some (a, b)
  | _ => none

def maxNode : Cobol.Expr → Option (Cobol.Expr × Cobol.Expr)
  | .max a b => some (a, b)
  | _ => none

def addNode : Cobol.Expr → Option (Cobol.Expr × Cobol.Expr)
  | .add a b => some (a, b)
  | _ => none

/-- The lowering of a power with the literal exponent `n` (`expr`): `1 * a * … * a`. -/
def powChain (n : Nat) (a : Cobol.Expr) : Cobol.Expr :=
  (List.replicate n a).foldl (fun acc x => .mul acc x) (.lit 1 0)

/-- IBM's places of `a ** n` for a literal `n ≥ 1` ("d = d1 * |op2|"; "i = i1 * |op2|", or for a
literal `a` = `v` at scale `s` "the number of integers in the value of op1 ** |op2|") and whether
IBM's exponentiation table carries them (`some true`), uses `dmax` decimal and `30 - dmax` integer
places as for an integral data-name exponent (`some false`), or depends on an open point (`none`;
`dg`: the candidates for the number of digits of `a`). -/
def powPlaces (pa : Places) (lit : Option (Int × Int)) (dg : List Int) (n : Nat) :
    Places × Option Bool :=
  let nn : Int := n
  let p : Places := match lit with
    | some (v, s) => litPlaces ((v.natAbs ^ n : Nat) : Int) (s * nn)
    | none => ⟨pa.iLo * nn, pa.iHi * nn, pa.dLo * nn, pa.dHi * nn⟩
  let how : Option Bool :=
    if p.iHi + p.dHi < 30 then some true
    else if 30 < p.iLo + p.dLo then some false
    else if p.iLo + p.dLo == 30 && p.iHi + p.dHi == 30 then
      -- "=30": an odd number of digits in op1: i and d carried; even: as an integral data-name,
      -- "Exception: for a 30-digit integer raised to the power of literal 1, i integer and d decimal
      -- places are carried"
      if n == 1 && p.dHi == 0 && dg.all (· == 30) then some true
      else if dg.all (· % 2 == 1) then some true
      else if dg.all (· % 2 == 0) then some false
      else none
    else none
  (p, how)

/-- The most decimal places of any literal or numeric item in `e` (a bound of every `dmax` in it). -/
partial def placesMax (ctx : Ctx) : Surface.Expr → Int
  | .lit _ s => max 0 s
  | .ref r => max 0 (refScale ctx r.item)
  | .idx _ => 0
  | .neg a | .pow a _ => placesMax ctx a
  | .add a b | .sub a b | .mul a b | .div a b _ | .powE a b => max (placesMax ctx a) (placesMax ctx b)
  | .fn _ args => args.foldl (fun m a => max m (placesMax ctx a)) 0
  | .afn _ _ => 0

/-- Upper bounds of IBM's integer and decimal places of `e` and of the digits of every intermediate
result in it, every operation counted as one (`dm` bounds every `dmax` in `e`; `r = 1` under
`ROUNDED`: one more integer and decimal place at every operation, as `carry30` widens them). -/
partial def irBound (ctx : Ctx) (dm r : Int) : Surface.Expr → Int × Int × Int
  | .lit v s => let p := litPlaces v s; (p.iHi, p.dHi, 0)
  | .ref x =>
    match ctx.L.find? x.item with
    | some { desc := { kind := .num f, .. }, .. } => let p := itemPlaces ctx.cfg f; (p.iHi, p.dHi, 0)
    | _ => (0, 0, 0)
  | .idx _ => (10, 0, 0)
  | .neg a =>
    let (i, d, m) := irBound ctx dm r a
    (i + 1 + r, d + r, max m (i + 1 + d + 2 * r))
  | .add a b | .sub a b =>
    let (i1, d1, m1) := irBound ctx dm r a
    let (i2, d2, m2) := irBound ctx dm r b
    let i := max i1 i2 + 1 + r
    let d := max d1 d2 + r
    (i, d, max (max m1 m2) (i + d))
  | .mul a b =>
    let (i1, d1, m1) := irBound ctx dm r a
    let (i2, d2, m2) := irBound ctx dm r b
    (i1 + i2 + r, d1 + d2 + r, max (max m1 m2) (i1 + i2 + d1 + d2 + 2 * r))
  | .div a b s =>
    let (i1, d1, m1) := irBound ctx dm r a
    let (_, d2, m2) := irBound ctx dm r b
    let i := i1 + d2 + r
    let d := (match s with | some x => x | none => max d1 dm) + r
    (i, d, max (max m1 m2) (i + d))
  | .pow a n =>
    let (i1, d1, m1) := irBound ctx dm r a
    let i := match a with
      | .lit v s => (litPlaces ((v.natAbs ^ n : Nat) : Int) (s * (n : Int))).iHi
      | _ => i1 * n
    let d := d1 * n
    -- from 30 digits on (28 under ROUNDED) IBM may carry 30 - dmax integer and dmax decimal places
    if i + d + 2 * r < 30 then (i, d, max m1 (i + d))
    else (max i 30, max d dm, max m1 (i + d + 2 * r + 1))
  | .powE a e =>
    let (_, _, m1) := irBound ctx dm r a
    let (_, _, m2) := irBound ctx dm r e
    (30, dm, max (max m1 m2) 30)
  | .fn name args =>
    let bs := args.map (irBound ctx dm r)
    let mA := bs.foldl (fun acc (_, _, m) => max acc m) 0
    let iM := bs.foldl (fun acc (i, _, _) => max acc i) 0
    let dM := bs.foldl (fun acc (_, d, _) => max acc d) 0
    match name.toUpper, bs with
    | "ABS", [(i, d, _)] => (i + r, d + r, max mA (i + d + 2 * r))
    | "INTEGER", [(i, d, _)] => (i + d + 1 + r, r, max mA (i + d + 1 + 2 * r))
    | "INTEGER-PART", [(i, d, _)] => (i + d + r, r, max mA (i + d + 2 * r))
    | "MOD", [(i1, _, _), (i2, _, _)] => (min i1 i2 + r, r, max mA (min i1 i2 + 2 * r))
    | "REM", [(i1, d1, _), (i2, d2, _)] =>
      let iq := i1 + d2 + r
      let dq := max d1 dm + r
      let ip := iq + i2 + r
      let dp := d2 + r
      let ir := max i1 ip + 1 + r
      let dr := max d1 dp + r
      (ir, dr, max mA (max (iq + dq) (max (ip + dp) (ir + dr))))
    | "MIN", _ | "MAX", _ => (iM, dM, max mA (iM + dM + 2 * r))
    | "RANGE", _ => (iM + 1 + r, dM + r, max mA (iM + 1 + dM + 2 * r))
    | "SUM", _ =>
      bs.foldl (fun (ia, da, ma) (ib, db, _) =>
        let i := max ia ib + 1 + r
        let d := max da db + r
        (i, d, max ma (i + d))) (0, 0, mA)
    | "FACTORIAL", _ => (30, 0, max mA 30)
    | "DATE-OF-INTEGER", _ => (8, 0, max mA 8)
    | "INTEGER-OF-DATE", _ | "INTEGER-OF-DAY", _ | "DAY-OF-INTEGER", _ => (7, 0, max mA 7)
    | "ORD-MAX", _ | "ORD-MIN", _ => (9, 0, max mA 9)
    | _, _ => (30, dm, 99)
  | .afn name _ => (if name.toUpper == "ORD" then 3 else 9, 0, 0)

/-- `e'` (the lowering of `e` by `expr`) with IBM's places carried for the intermediate results of
more than 30 digits in it (`carry30`), and IBM's places of its value; `u`: how its result is used.
The walk pairs `e` with the shapes `expr` gives; any other shape is left as it is, with unknown
places. -/
partial def capW (ctx : Ctx) (env : IrEnv) (u : IrUse) :
    Surface.Expr → Cobol.Expr → Cobol.Expr × Places × Bool
  | .lit _ _, e@(.lit v s) => (e, litPlaces v s, false)
  | .ref _, e@(.ref d) =>
    match d.desc.kind with
    | .num f => (e, itemPlaces ctx.cfg f, false)
    | _ => (e, Places.unknown, false)
  | .idx _, e@(.idx _) => (e, ⟨1, 10, 0, 0⟩, false)
  | .neg a, .neg a' =>
    -- "Multiplication by -1": maybe an operation with one more integer place
    let (a'', p, c) := capW ctx env (if u == .final then .maybe else .ir) a a'
    let (r, q, c2) := carry30 env (if u == .final then .final else .maybe)
      { p with iHi := p.iHi + 1 } (.neg a'')
    (r, q, c || c2)
  | .add a b, .add a' b' =>
    let (a'', pa, c1) := capW ctx env .ir a a'
    let (b'', pb, c2) := capW ctx env .ir b b'
    let (r, q, c3) := carry30 env u (Places.add pa pb) (.add a'' b'')
    (r, q, c1 || c2 || c3)
  | .sub a b, .sub a' b' =>
    let (a'', pa, c1) := capW ctx env .ir a a'
    let (b'', pb, c2) := capW ctx env .ir b b'
    let (r, q, c3) := carry30 env u (Places.add pa pb) (.sub a'' b'')
    (r, q, c1 || c2 || c3)
  | .mul a b, .mul a' b' =>
    let (a'', pa, c1) := capW ctx env .ir a a'
    let (b'', pb, c2) := capW ctx env .ir b b'
    let (r, q, c3) := carry30 env u (Places.mul pa pb) (.mul a'' b'')
    (r, q, c1 || c2 || c3)
  | .div a b s, .div a' b' sc m =>
    let (a'', pa, c1) := capW ctx env .ir a a'
    let (b'', pb, c2) := capW ctx env .ir b b'
    -- an operand whose decimal places were cut gives the quotient other places than `expr` took
    -- from the uncut one
    let cutOp := s.isNone && (decPlaces a'' != decPlaces a' || decPlaces b'' != decPlaces b')
    let sc := if cutOp then
        max (decPlaces a'' - decPlaces b'') env.lowD + (if env.rounded && env.divExtra then 1 else 0)
      else sc
    -- "i2 + d1" integer and "(d2 - d1) or dmax, whichever is greater" decimal places (op1 the
    -- divisor, op2 the dividend), or the extractor's scale
    let p : Places := ⟨pa.iLo + pb.dLo, pa.iHi + pb.dHi,
      (match s with | some x => x | none => max (pa.dLo - pb.dHi) env.mLo),
      (match s with | some x => x | none => max (pa.dHi - pb.dLo) env.mHi)⟩
    -- inside a function argument `expr` took the places with the inner-dmax and without `ROUNDED`,
    -- not with `lowD` and `rounded`
    if cutOp && env.inArg then (.ir30open (.div a'' b'' sc m) inArgWhy, p, true) else
    let (r, q, c3) := carry30 env u p (.div a'' b'' sc m)
    (r, q, c1 || c2 || c3)
  | .pow a n, ce =>
    -- a power is an intermediate result ("the intermediate results ir of the exponentiation")
    match n, ce with
    | 0, .pow0 a' t u =>
      -- the base is evaluated (its own intermediate results carried), the power is 1
      let (a'', _, c) := capW ctx env .ir a a'
      (.pow0 a'' t u, Places.exact 1 0, c)
    | k + 1, .mul _ a' =>
      if powChain (k + 1) a' != ce then (ce, Places.unknown, false) else
      let (a'', pa, c) := capW ctx env .ir a a'
      let lit := match a with
        | .lit v s => some (v, s)
        | _ => none
      let dg : List Int := match a, a' with
        | .lit v _, _ => [natDigits v.natAbs]
        | .ref _, .ref d => match d.desc.kind with
          | .num f => [(f.digits : Int), pa.iHi + pa.dHi]
          | _ => [0, 1]
        | _, _ => if pa.iLo == pa.iHi && pa.dLo == pa.dHi then [pa.iLo + pa.dLo]
          else [pa.iLo + pa.dLo, pa.iLo + pa.dLo + 1]
      let (p, how) := powPlaces pa lit dg (k + 1)
      -- the places IBM carries for the power
      let pc : Places := match how with
        | some true => p
        | some false => ⟨30 - env.mHi, 30 - env.mLo, env.mLo, env.mHi⟩
        | none => ⟨min p.iLo (30 - env.mHi), max p.iHi (30 - env.mLo), min p.dLo env.mLo,
                   max p.dHi env.mHi⟩
      let chain := powChain (k + 1) a''
      -- ROUNDED: "one more integer [decimal] place might be carried", so from 28 digits on the row of
      -- the exponentiation table is open
      if env.rounded && 28 ≤ p.iHi + p.dHi then
        (.ir30open chain "power by a literal of 28 or more digits under ROUNDED, places carried open",
          pc, true)
      else match how with
        | some true => (chain, pc, c)
        -- "Same action as when op2 is an integral data-name or variable": "dmax decimal places and
        -- 30-dmax ... integer places" (`Sem.powIntVal`)
        | some false =>
          if env.mLo == env.mHi && !env.zeroArg then
            (.powInt a'' (.lit ((k + 1 : Nat) : Int) 0) env.mLo, pc, true)
          else (.ir30open chain
            "power by a literal over 30 digits in a function argument, places carried open", pc, true)
        | none => (.ir30open chain "power by a literal of about 30 digits, places carried open", pc, true)
    | _, _ => (ce, Places.unknown, false)
  | .powE a e, .powInt a' e' s =>
    let (a'', _, c1) := capW ctx env .ir a a'
    let (e'', _, c2) := capW ctx env .ir e e'
    -- "dmax decimal places and 30-dmax ... integer places"
    (.powInt a'' e'' s, ⟨30 - max s env.mHi, 30 - min s env.mLo, min s env.mLo, max s env.mHi⟩,
      c1 || c2)
  | .fn name args, ce =>
    let inner := (args.map (fun a => (dScales ctx a).foldl max 0)).foldl max 0
    -- the dmax of an argument's operations: the statement's, the function's inner dmax or the
    -- argument's own (open reading R1)
    let envA (a : Surface.Expr) : IrEnv :=
      let own := (dScales ctx a).foldl max 0
      let lo := min (min env.mLo own) inner
      { env with mLo := lo, mHi := max (max env.mHi own) inner,
                 lowD := ctx.dmaxIn.getD env.lowD, inArg := true,
                 zeroArg := env.zeroArg || innerDmax ctx name args < lo }
    -- the dmax of the function's steps and result: the statement's or the function's inner dmax
    let envF : IrEnv := { env with mLo := min env.mLo inner, mHi := max env.mHi inner }
    let arg (a : Surface.Expr) (a' : Cobol.Expr) := capW ctx (envA a) .ir a a'
    let maxL (l : List Int) : Int := l.foldl max 0
    match name.toUpper, args, ce with
    | "ABS", [a], .abs a' =>
      let (a'', p, c) := arg a a'
      let (r, q, c2) := carry30 envF .ir p (.abs a'')
      (r, q, c || c2)
    | "INTEGER", [a], .integer a' =>
      let (a'', p, c) := arg a a'
      -- "one more digit than in the argument"
      let (r, q, c2) := carry30 envF .ir ⟨p.iLo + p.dLo + 1, p.iHi + p.dHi + 1, 0, 0⟩ (.integer a'')
      (r, q, c || c2)
    | "INTEGER-PART", [a], .integerPart a' =>
      let (a'', p, c) := arg a a'
      -- "same number of digits as in the argument"
      let (r, q, c2) := carry30 envF .ir ⟨p.iLo + p.dLo, p.iHi + p.dHi, 0, 0⟩ (.integerPart a'')
      (r, q, c || c2)
    | "MOD", [a, b], .mod a' b' =>
      let (a'', pa, c1) := arg a a'
      let (b'', pb, c2) := arg b b'
      -- "min(i1 i2)"
      let (r, q, c3) := carry30 envF .ir ⟨min pa.iLo pb.iLo, min pa.iHi pb.iHi, 0, 0⟩ (.mod a'' b'')
      (r, q, c1 || c2 || c3)
    | "REM", [a, b], .rem a' b' =>
      let (a'', pa, c1) := arg a a'
      let (b'', pb, c2) := arg b b'
      -- "Divide argument one by argument two" (i2 + d1 integer, (d2 - d1) or dmax decimal places)
      let pq : Places := ⟨pa.iLo + pb.dLo, pa.iHi + pb.dHi, max (pa.dLo - pb.dHi) envF.mLo,
        max (pa.dHi - pb.dLo) envF.mHi⟩
      let (q, pq', cq) := carryInt30 envF pq (.div a'' b'' (max 0 pq.dHi) .truncation)
      -- "Remove all noninteger digits", "Multiply the result of step 2 by argument two"
      let (pr, pp, cp) := carry30 envF .ir ⟨pq'.iLo + pb.iLo, pq'.iHi + pb.iHi, pb.dLo, pb.dHi⟩
        (.mul (.integerPart q) b'')
      -- "Subtract the result of step 3 from argument one"
      let (r, prr, cr) := carry30 envF .ir (Places.add pa pp) (.sub a'' pr)
      if cq || cp || cr then (r, prr, true) else (.rem a'' b'', prr, c1 || c2)
    | "MIN", _ :: _, _ | "MAX", _ :: _, _ =>
      let isMin := name.toUpper == "MIN"
      let build (xs : List Cobol.Expr) : Cobol.Expr := match xs with
        | x :: rest => if isMin then rest.foldl .min x else rest.foldl .max x
        | [] => ce
      match unchain (if isMin then minNode else maxNode) args.length ce with
      | some cs =>
        if build cs != ce then (ce, Places.unknown, false) else
        let rs := (args.zip cs).map (fun (a, a') => arg a a')
        let p : Places := ⟨maxL (rs.map (·.2.1.iLo)), maxL (rs.map (·.2.1.iHi)),
          maxL (rs.map (·.2.1.dLo)), maxL (rs.map (·.2.1.dHi))⟩
        let e := build (rs.map (·.1))
        -- "Assign the first argument to the function result" ...: one result field for them all
        if p.iHi + p.dHi + (if env.rounded then 2 else 0) ≤ 30 then (e, p, rs.any (·.2.2))
        else (.ir30open e "FUNCTION MAX / MIN of arguments needing more than 30 digits together", p,
          true)
      | none => (ce, Places.unknown, false)
    | "SUM", _ :: _, _ =>
      match unchain addNode args.length ce with
      | some (c0 :: cs) =>
        if cs.foldl .add c0 != ce then (ce, Places.unknown, false) else
        match (args.zip (c0 :: cs)).map (fun (a, a') => arg a a') with
        | (e1, p1, c1) :: rest =>
          -- "Assign the value 0 to the function result", then "Add the argument to the function
          -- result" for each argument
          let (s1, q1, d1) := carry30 envF .ir (Places.add (Places.exact 0 0) p1) e1
          rest.foldl (fun (acc, pacc, ch) (ek, pk, ck) =>
            let (r, pr, cr) := carry30 envF .ir (Places.add pacc pk) (.add acc ek)
            (r, pr, ch || ck || cr)) (s1, q1, c1 || d1)
        | [] => (ce, Places.unknown, false)
      | _ => (ce, Places.unknown, false)
    | "RANGE", _ :: _, .sub mx mn =>
      match unchain maxNode args.length mx with
      | some (c0 :: cs) =>
        if cs.foldl .max c0 != mx || cs.foldl .min c0 != mn then (ce, Places.unknown, false) else
        match (args.zip (c0 :: cs)).map (fun (a, a') => arg a a') with
        | (e1, p1, c1) :: rest =>
          let es := rest.map (·.1)
          let ps := p1 :: rest.map (·.2.1)
          let p : Places := ⟨maxL (ps.map (·.iLo)), maxL (ps.map (·.iHi)), maxL (ps.map (·.dLo)),
            maxL (ps.map (·.dHi))⟩
          let e := Cobol.Expr.sub (es.foldl .max e1) (es.foldl .min e1)
          let ch := c1 || rest.any (·.2.2)
          if p.iHi + p.dHi + (if env.rounded then 2 else 0) > 30 then
            (.ir30open e "FUNCTION RANGE of arguments needing more than 30 digits together", p, true)
          else
            -- "Subtract the minimum argument from the maximum"
            let (r, q, c2) := carry30 envF .ir (Places.add p p) e
            (r, q, ch || c2)
        | [] => (ce, Places.unknown, false)
      | _ => (ce, Places.unknown, false)
    | "FACTORIAL", [a], .factorial a' =>
      let (a'', _, c) := arg a a'
      (.factorial a'', Places.exact 30 0, c)
    | "DATE-OF-INTEGER", [a], .dateFn f a' =>
      let (a'', _, c) := arg a a'
      (.dateFn f a'', Places.exact 8 0, c)
    | "INTEGER-OF-DATE", [a], .dateFn f a' | "INTEGER-OF-DAY", [a], .dateFn f a'
    | "DAY-OF-INTEGER", [a], .dateFn f a' =>
      let (a'', _, c) := arg a a'
      (.dateFn f a'', Places.exact 7 0, c)
    | "ORD-MAX", _, _ | "ORD-MIN", _, _ =>
      -- the result has 9 digits; the arguments are taken as they are unless one of them can hold an
      -- intermediate result of more than 30 digits (with the function's inner-dmax `inner`, which
      -- `expr` lowers them with)
      let dm := max env.mHi inner
      if args.all (fun a =>
          (irBound ctx (max dm (placesMax ctx a)) (if env.rounded then 1 else 0) a).2.2 ≤ 30) then
        (ce, Places.exact 9 0, false)
      else (.ir30open ce "FUNCTION ORD-MAX / ORD-MIN of an argument over 30 digits", Places.exact 9 0,
        true)
    | _, _, _ => (ce, Places.unknown, false)
  | .afn name _, ce => (ce, Places.exact (if name.toUpper == "ORD" then 3 else 9) 0, false)
  | _, ce => (ce, Places.unknown, false)

/-- A division whose places the extractor gave (`--div-scale`, the GnuCOBOL comparison profile, not
IBM's rule) in `e`. -/
partial def divScaled : Surface.Expr → Bool
  | .div a b s => s.isSome || divScaled a || divScaled b
  | .neg a | .pow a _ => divScaled a
  | .add a b | .sub a b | .mul a b | .powE a b => divScaled a || divScaled b
  | .fn _ args => args.any divScaled
  | _ => false

/-- `e'`, the lowering of `e` by `expr ctx dmax rounded`, with IBM's places carried for its
intermediate results of more than 30 digits (`capW`); `e'` itself when none of them can exceed 30
digits (`irBound`), or when `e` has a division with the extractor's places, which is outside IBM's
rules.  `final`: `e` is the final result of an arithmetic statement with one receiver and no
`ROUNDED`. -/
def cap30 (ctx : Ctx) (dmax : Int) (rounded final : Bool) (e : Surface.Expr) (e' : Cobol.Expr) :
    Cobol.Expr :=
  if divScaled e then e'
  else if (irBound ctx (max dmax (placesMax ctx e)) (if rounded then 1 else 0) e).2.2 ≤ 30 then e'
  else (capW ctx { mLo := dmax, mHi := dmax, rounded, lowD := dmax,
                   divExtra := ctx.dialect.divExtraForRounded } (if final then .final else .ir) e e').1

/-- An arithmetic statement whose intermediate result is formed inside its operation (`DIVIDE` with
several `GIVING` receivers, `ROUNDED` or `REMAINDER`; `MULTIPLY … ROUNDED` without `GIVING`) and can
need more than 30 digits (`digits`, with `ROUNDED`'s two places): unsupported, the places IBM carries
there are not modelled. -/
def opOver30 (digits : Int) (rounded : Bool) : Bool := 30 < digits + (if rounded then 2 else 0)

/-- `e` with every power by the literal 0 (`Expr.pow0`) marked with its statement's SIZE ERROR
phrases: `trap`, an `ON SIZE ERROR` phrase, makes a zero base the statement's size error (IBM, "SIZE
ERROR phrases": zero raised to zero power, "The SIZE ERROR imperative is executed"); `notOnly`, a
`NOT ON SIZE ERROR` phrase without one, makes it unsupported (the size error skips that phrase while
the value 1 is stored). -/
def markPow0 (trap notOnly : Bool) : Cobol.Expr → Cobol.Expr
  | .pow0 a _ _ => .pow0 (markPow0 trap notOnly a) trap notOnly
  | .neg a => .neg (markPow0 trap notOnly a)
  | .add a b => .add (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .sub a b => .sub (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .mul a b => .mul (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .div a b s m => .div (markPow0 trap notOnly a) (markPow0 trap notOnly b) s m
  | .rescale a s m => .rescale (markPow0 trap notOnly a) s m
  | .abs a => .abs (markPow0 trap notOnly a)
  | .min a b => .min (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .max a b => .max (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .integer a => .integer (markPow0 trap notOnly a)
  | .integerPart a => .integerPart (markPow0 trap notOnly a)
  | .mod a b => .mod (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .rem a b => .rem (markPow0 trap notOnly a) (markPow0 trap notOnly b)
  | .factorial a => .factorial (markPow0 trap notOnly a)
  | .dateFn f a => .dateFn f (markPow0 trap notOnly a)
  | .powInt a e s => .powInt (markPow0 trap notOnly a) (markPow0 trap notOnly e) s
  | .ir30 a s ip => .ir30 (markPow0 trap notOnly a) s ip
  | .ir30open a why => .ir30open (markPow0 trap notOnly a) why
  | e => e

def cmpOp : String → Except String CmpOp
  | "=" | "EQUAL" => pure .eq
  | "<>" | "NOT =" | "NOT EQUAL" => pure .ne
  | "<" | "LESS" => pure .lt
  | "<=" | "NOT >" => pure .le
  | ">" | "GREATER" => pure .gt
  | ">=" | "NOT <" => pure .ge
  | o => throw s!"unknown relational operator {o}"

/-- A numeric operand as an expression (`ZERO` is `0`). -/
def operandExpr (ctx : Ctx) : Surface.Operand → Except String Cobol.Expr
  | .ref r => expr ctx 0 false (.ref r)
  | .lit (.num v s _) => pure (.lit v s)
  | .lit (.fig n) => do
    match ← figurative ctx.cfg n with
    | .zero => pure (.lit 0 0)
    | _ => throw "figurative constant in a numeric comparison"
  | _ => throw "non-numeric operand in a numeric comparison"

def isZeroFig : Surface.Operand → Bool
  | .lit (.fig n) => ["ZERO", "ZEROS", "ZEROES"].contains n.toUpper
  | _ => false

def valueOperand (ctx : Ctx) : Value → Except String Surface.Operand
  | .num v s => pure (.lit (.num v s))
  | .alnum bs => let _ := ctx; pure (.lit (.hex (String.ofList (bs.flatMap (fun b =>
      let h := "0123456789ABCDEF".toList
      [h.getD (b.toNat / 16) '0', h.getD (b.toNat % 16) '0'])))))
  | .fig f => pure (.lit (.fig (match f with
      | .zero => "ZERO" | .space => "SPACE" | .high => "HIGH-VALUE" | .low => "LOW-VALUE"
      | .quote => "QUOTE" | .all _ => "SPACE")))

/-- A level-88 value as the source of `SET ... TO TRUE`: `ALL literal` is the figurative constant
`ALL literal` (IBM: the literal repeated to the size of the conditional variable); any other
value is `valueOperand`'s operand. -/
def valueSrc (ctx : Ctx) : Value → Except String Cobol.Operand
  | .fig (.all bs) => pure (.fig (.all bs))
  | v => do operand ctx (← valueOperand ctx v)

partial def cond (ctx : Ctx) : Surface.Cond → Except String Cobol.Cond
  | .const b => pure (.const b)
  | .rel op a b => do
    let o ← cmpOp op
    if (isNumeric ctx a || isZeroFig a) && (isNumeric ctx b || isZeroFig b) &&
        (isNumeric ctx a || isNumeric ctx b) then
      pure (.numCmp o (← operandExpr ctx a) (← operandExpr ctx b))
    else if let some s := ctx.seq then
      -- PROGRAM COLLATING SEQUENCE: nonnumeric comparisons by its positions
      pure (.alnumCmpSeq o (← operand ctx a) (← operand ctx b) s.pos)
    else pure (.alnumCmp o (← operand ctx a) (← operand ctx b))
  | .relExpr op a b => do
    -- IBM: in a relation condition with an arithmetic expression, `dmax` is the most decimal
    -- places of any operand of either comparand, divisors and exponents excluded
    let dmax := (dScales ctx a ++ dScales ctx b).foldl max 0
    -- every operation of a condition is an intermediate result (IBM's 30-digit rule: `cap30`)
    pure (.numCmp (← cmpOp op) (cap30 ctx dmax false false a (← expr ctx dmax false a))
      (cap30 ctx dmax false false b (← expr ctx dmax false b)))
  | .cls t r => do
    let test ← match t.toUpper with
      | "NUMERIC" => pure ClassTest.numeric
      | "ALPHABETIC" => pure .alphabetic
      | "ALPHABETIC-LOWER" => pure .alphabeticLower
      | "ALPHABETIC-UPPER" => pure .alphabeticUpper
      | n => throw s!"unknown class {n}"
    pure (.cls test (← ref ctx r))
  | .sign t e => do
    -- the expression with the `dmax` of its own operands (no relational operator, IBM)
    let e' ← expr ctx ((dScales ctx e).foldl max 0) false e
    let e' := cap30 ctx ((dScales ctx e).foldl max 0) false false e e'
    match t.toUpper with
    | "POSITIVE" => pure (.numCmp .gt e' (.lit 0 0))
    | "NEGATIVE" => pure (.numCmp .lt e' (.lit 0 0))
    | "ZERO" => pure (.numCmp .eq e' (.lit 0 0))
    | n => throw s!"unknown sign condition {n}"
  | .cond88 id subs => do
    let some (parent, vals) := ctx.conds.lookup id | throw s!"unknown condition name {id}"
    let pr : Surface.Operand := .ref { item := parent, subs }
    -- `pr op v`: an `ALL literal` value is compared as the relation with that figurative constant
    -- is (nonnumeric, the literal repeated to the size of the conditional variable, IBM)
    let rel (op : String) (v : Value) (o : Surface.Operand) : Except String Cobol.Cond :=
      match v with
      | .fig (.all bs) => do
        let c ← cmpOp op
        let a ← operand ctx pr
        match ctx.seq with
        | some s => pure (.alnumCmpSeq c a (.fig (.all bs)) s.pos)
        | none => pure (.alnumCmp c a (.fig (.all bs)))
      | _ => cond ctx (.rel op pr o)
    let arms ← vals.mapM (fun v => do
      let lo ← valueOperand ctx v.lo
      match v.hi with
      | none => rel "=" v.lo lo
      | some h => do
        let hi ← valueOperand ctx h
        pure (Cobol.Cond.and (← rel ">=" v.lo lo) (← rel "<=" h hi)))
    match arms with
    | [] => pure (.const false)
    | a :: rest => pure (rest.foldl .or a)
  | .not c => do pure (.not (← cond ctx c))
  | .and a b => do pure (.and (← cond ctx a) (← cond ctx b))
  | .or a b => do pure (.or (← cond ctx a) (← cond ctx b))
  | .odoCheck s => do
    -- the object as the subscript of a dimension of `integer-2 - integer-1 + 1` occurrences and
    -- stride 0 (`object + 1 - integer-1`): in range exactly when the object is, and then the
    -- reference is the object itself, equal to itself
    let some o := ctx.odo.find? (·.subject == s) | throw s!"unknown OCCURS DEPENDING ON table {s}"
    let (_, _, mx) ← odoTable ctx o
    let op ← item ctx o.obj
    let chk : DataRef := { item := o.obj, desc := op.desc,
                           subs := [{ e := .ref op.desc (1 - (o.min : Int)), stride := 0,
                                      max := mx - o.min + 1 }] }
    pure (.numCmp .eq (.ref chk) (.ref chk))
  | .relOwn op a b => do
    -- an `EVALUATE` subject and object: each "evaluated without regard to the attributes of its
    -- comparand" (IBM), with the `dmax` of its own operands
    pure (.numCmp (← cmpOp op)
      (cap30 ctx ((dScales ctx a).foldl max 0) false false a
        (← expr ctx ((dScales ctx a).foldl max 0) false a))
      (cap30 ctx ((dScales ctx b).foldl max 0) false false b
        (← expr ctx ((dScales ctx b).foldl max 0) false b)))

def roundingMode : Option String → Except String RoundingMode
  | none => pure .truncation
  | some m =>
    match m.toUpper with
    | "NEAREST-AWAY-FROM-ZERO" | "" => pure .nearestAwayFromZero
    | "AWAY-FROM-ZERO" => pure .awayFromZero
    | "NEAREST-EVEN" => pure .nearestEven
    | "NEAREST-TOWARD-ZERO" => pure .nearestTowardZero
    | "TOWARD-GREATER" => pure .towardGreater
    | "TOWARD-LESSER" => pure .towardLesser
    | "TRUNCATION" => pure .truncation
    | "PROHIBITED" => pure .prohibited
    | n => throw s!"unknown rounding mode {n}"

def receiver (ctx : Ctx) (r : Surface.Receiver) : Except String Cobol.Receiver := do
  pure { ref := ← ref ctx r.ref, mode := ← roundingMode r.rounded }

/-- First paragraph and exit point of a `PERFORM` target (`first [THRU last]`, paragraph or
section names): a section name as the end gives the section's exit point. -/
def range (ctx : Ctx) (first : String) (last : Option String) : Except String (Nat × ExitPt) := do
  let bounds (n : String) : Except String (Nat × ExitPt) :=
    match ctx.sections.lookup n with
    | some (f, l) => pure (f, .sect l)
    | none => match ctx.paraIdx.lookup n with
      | some k => pure (k, .para k)
      | none => throw s!"unknown procedure {n}"
  let (f, e0) ← bounds first
  match last with
  | none => pure (f, e0)
  | some n => do let (_, e) ← bounds n; pure (f, e)

def target (ctx : Ctx) (n : String) : Except String Nat := do
  let (f, _) ← range ctx n none
  pure f

def nextId : RM Nat := do
  let n ← get
  set (n + 1)
  pure n

def liftE {α : Type} (x : Except String α) : RM α := StateT.lift x

/-- Elementary items at or below `it` to initialize: not `FILLER`, neither described with
`REDEFINES` nor subordinate to such an item. -/
partial def initLeaves (it : Item) : List Item :=
  if it.redefines.isSome then []
  else match it.pic with
    | some _ => if it.name.toUpper == "FILLER" then [] else [it]
    | none => it.children.flatMap initLeaves

/-- Elementary items an `INITIALIZE` of `it` sets. IBM rule 1a skips the items below `it`
with or under a `REDEFINES` clause, but "identifier-1 might itself have a REDEFINES clause":
the root's own clause does not count. -/
def initTargets (it : Item) : List Item := initLeaves { it with redefines := none }

/-- `INITIALIZE` of a reference-modified identifier. IBM: the reference is "an elementary data
item" of category alphanumeric (data-name-1 of usage `DISPLAY`, a group included), so it
receives `SPACE`, whatever the items below data-name-1. Data-name-1 must have usage `DISPLAY`:
a `COMP`, `COMP-3` or `COMP-5` item stops as unsupported. -/
def initRefMod (ctx : Ctx) (d : Ref) : Except String (List Cobol.Stmt) := do
  let r ← ref ctx d
  match r.desc.kind with
  | .num f =>
    match f.usage with
    | .display => pure [.move (.fig .space) [r]]
    | _ => pure [.unsupported "INITIALIZE of a reference-modified COMP, COMP-3 or COMP-5 item"]
  | _ => pure [.move (.fig .space) [r]]

/-- Literal subscripts of every occurrence of nested tables. -/
def litOccs : List (Nat × Nat) → List (List Sub)
  | [] => [[]]
  | (_, n) :: rest => (List.range n).flatMap (fun (i : Nat) =>
      (litOccs rest).map (fun o => Sub.lit (Int.ofNat i + 1) :: o))

partial def findItem (id : Nat) : List Item → Option Item
  | [] => none
  | it :: rest => if it.id == id then some it else
      match findItem id it.children with
      | some x => some x
      | none => findItem id rest

def openMode : String → Except String OpenMode
  | "INPUT" => pure .input
  | "OUTPUT" => pure .output
  | "I-O" => pure .io
  | "EXTEND" => pure .extend
  | m => throw s!"unknown OPEN mode {m}"

def closeOpt : String → Except String CloseOpt
  | "REEL" => pure .reel
  | "REEL-NO-REWIND" => pure .reelNoRewind
  | "REEL-REMOVAL" => pure .reelRemoval
  | "NO-REWIND" => pure .noRewind
  | "LOCK" => pure .lock
  | o => throw s!"unknown CLOSE phrase {o}"

/-- Index of the key of reference `id` of a file: `0` = record key, `j + 1` = alternate key `j`. -/
def keyIndex (fd : Surface.FileDecl) (id : Nat) : Except String Nat :=
  if fd.key == some id then pure 0
  else match (fd.alt.map (·.1)).idxOf? id with
    | some j => pure (j + 1)
    | none => throw s!"item {id} is not a key of file {fd.id}"

/-- Resolve a file declaration: key positions within the record area. -/
def fileDecl (ctx : Ctx) (fd : Surface.FileDecl) : Except String Cobol.FileDecl := do
  let area ← item ctx fd.record
  let keyOf (id : Nat) (dups : Bool) : Except String KeyDecl := do
    let k ← item ctx id
    unless k.dims.isEmpty do throw s!"key {k.name} is in a table"
    unless area.desc.off ≤ k.desc.off ∧ k.desc.off + k.desc.len ≤ area.desc.off + area.desc.len do
      throw s!"key {k.name} is outside the record area of file {fd.id}"
    pure { off := k.desc.off - area.desc.off, len := k.desc.len, dups }
  let key ← fd.key.mapM (keyOf · false)
  let alt ← fd.alt.mapM (fun (i, d) => keyOf i d)
  let status ← fd.status.mapM (fun i => do
    let s ← item ctx i
    unless s.desc.len = 2 ∧ s.dims.isEmpty do throw s!"FILE STATUS item {s.name} must be 2 bytes"
    pure s.desc)
  let org ← match fd.org with
    | "sequential" => pure FileOrg.sequential
    | "indexed" => pure .indexed
    | o => throw s!"unsupported file organization {o}"
  let access ← match fd.access with
    | "sequential" => pure AccessMode.sequential
    | "random" => pure .random
    | "dynamic" => pure .dynamic
    | a => throw s!"unknown access mode {a}"
  if org == .indexed && key.isNone then throw s!"indexed file {fd.id} without RECORD KEY"
  -- variable-length records: lengths from `FROM` (default 1) to `TO` (default: the record area)
  let dependsOn ← fd.dependsOn.mapM (fun i => do
    let it ← item ctx i
    unless it.dims.isEmpty do throw s!"DEPENDING ON item {it.name} is in a table"
    match it.desc.kind with
    | .num _ => pure it.desc
    | _ => throw s!"DEPENDING ON item {it.name} of file {fd.id} is not numeric")
  let varying := if fd.minLen.isSome || fd.maxLen.isSome || fd.dependsOn.isSome then
      some (fd.minLen.getD 1, fd.maxLen.getD area.desc.len) else none
  if let some (mn, mx) := varying then
    unless mn ≤ mx ∧ mx ≤ area.desc.len do
      throw s!"file {fd.id}: record lengths {mn} to {mx} do not fit the record area ({area.desc.len})"
  pure { id := fd.id, org, access, area := area.desc, key, alt, status, varying, dependsOn,
         optional := fd.optional.getD false }

mutual
partial def stmts (ctx : Ctx) (ss : List Surface.Stmt) : RM (List Cobol.Stmt) := do
  let r ← ss.mapM (stmt ctx)
  pure r.flatten

partial def stmt (ctx : Ctx) : Surface.Stmt → RM (List Cobol.Stmt)
  | .move src dsts => liftE do pure [.move (← operand ctx src) (← dsts.mapM (ref ctx))]
  | .compute rcv e onSize notOnSize => do
    -- IBM's dmax: the receivers' places (a numeric-edited receiver's too, `rcvScale`) and the operands'
    let dmax := (rcv.map (fun r => rcvScale ctx r.ref.item) ++ dScales ctx e).foldl max 0
    let rounded := rcv.any (·.rounded.isSome)
    let e' ← liftE (expr ctx dmax rounded e)
    -- one division as the whole expression, no ROUNDED receiver, every receiver a numeric item with
    -- at most both scales' places: the quotient keeps the scale max(d1, dmax) of earlier versions,
    -- which stores the same values as IBM's (truncation toward zero: trunc_r (trunc_s q) = trunc_r q
    -- for r ≤ s)
    let e' := match e, e' with
      | .div _ _ none, .div a' b' sc m =>
        let old := max b'.scale dmax
        if !rounded && rcv.all (fun r => numRcvWithin ctx r.ref old sc) then .div a' b' old m else e'
      | _, _ => e'
    -- intermediate results of more than 30 digits (`cap30`; the final result is one only with
    -- several receivers or ROUNDED)
    let e' := cap30 ctx dmax rounded (rcv.length == 1 && !rounded) e e'
    -- a power by the literal 0 with a zero base is the statement's size error (`markPow0`)
    let e' := if onSize.isSome then markPow0 true false e'
      else if notOnSize.isEmpty then e' else markPow0 false true e'
    let rs ← liftE (rcv.mapM (receiver ctx))
    -- one division as the whole expression and a receiver with a ROUNDED MODE IBM does not have:
    -- the DIVIDE ... GIVING form, the exact quotient rounded once into each receiver; a receiver
    -- with NEAREST-AWAY-FROM-ZERO or TRUNCATION stores the same value as from the intermediate
    -- scale, which has at least one place more than every receiver (one receiver is ROUNDED)
    let ibmMode (m : RoundingMode) : Bool := m == .nearestAwayFromZero || m == .truncation
    let op : ArithOp := match e, (e' : Cobol.Expr) with
      | .div _ _ none, .div a' b' _ _ =>
        if rs.all (fun (r : Cobol.Receiver) => ibmMode r.mode) then .giving e' else .divGiving a' b'
      | _, _ => .giving e'
    pure [.arith op rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .add ops rcv giving onSize notOnSize => do
    let es ← liftE (ops.mapM (expr ctx 0 false))
    let sum ← match es with
      | [] => liftE (throw "ADD without operands")
      | e :: rest => pure (rest.foldl .add e)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let op := if giving then ArithOp.giving sum else ArithOp.addTo sum
    pure [.arith op rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .subtract ops rcv giving onSize notOnSize => do
    let es ← liftE (ops.mapM (expr ctx 0 false))
    let sum ← match es with
      | [] => liftE (throw "SUBTRACT without operands")
      | e :: rest => pure (rest.foldl .add e)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let op ← match giving with
      | some m => do pure (ArithOp.giving (.sub (← liftE (expr ctx 0 false m)) sum))
      | none => pure (ArithOp.subFrom sum)
    pure [.arith op rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .multiply a rcv giving onSize notOnSize => do
    let a' ← liftE (expr ctx 0 false a)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let op ← match giving with
      | some b => do pure (ArithOp.giving (.mul a' (← liftE (expr ctx 0 false b))))
      | none => pure (ArithOp.mulBy a')
    let hs ← stmts ctx (onSize.getD [])
    let ns ← stmts ctx notOnSize
    -- the 30-digit rule (IBM's dmax: the receivers' places and the operands'): the product of
    -- GIVING is an intermediate result with several receivers or ROUNDED (`cap30`); without
    -- GIVING each receiver's product is one under ROUNDED (`opOver30`)
    let rounded := rcv.any (·.rounded.isSome)
    let dmax := (rcv.map (fun r => rcvScale ctx r.ref.item) ++ dScales ctx a ++
      (giving.map (dScales ctx)).getD []).foldl max 0
    let op := match giving, op with
      | some b, .giving e' => ArithOp.giving (cap30 ctx dmax rounded (rcv.length == 1 && !rounded)
          (.mul a b) e')
      | _, op => op
    let (ia, da, _) := irBound ctx (max dmax (placesMax ctx a)) 0 a
    if giving.isNone && rounded && rcv.any (fun r =>
        let (ir, dr, _) := irBound ctx dmax 0 (.ref r.ref)
        opOver30 (ia + ir + da + dr) rounded) then
      return [.unsupported "MULTIPLY ROUNDED with a product that can need more than 30 digits"]
    pure [.arith op rs onSize.isSome hs ns]
  | .divide dividend divisor rcv giving rem onSize notOnSize => do
    let a ← liftE (expr ctx 0 false dividend)
    let b ← liftE (expr ctx 0 false divisor)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let hs ← stmts ctx (onSize.getD [])
    let ns ← stmts ctx notOnSize
    -- the quotient is an intermediate result with several GIVING receivers, ROUNDED or REMAINDER
    -- (IBM's dmax: the result fields' places and the dividend's): unsupported when it can need more
    -- than 30 digits ("i2 + d1" integer, "(d2 - d1) or dmax" decimal places; `opOver30`)
    let rounded := rcv.any (·.rounded.isSome)
    let dmax := (rcv.map (fun r => rcvScale ctx r.ref.item) ++
      (rem.map (fun r => [rcvScale ctx r.item])).getD [] ++ dScales ctx dividend).foldl max 0
    let (ia, da, _) := irBound ctx (max dmax (placesMax ctx dividend)) 0 dividend
    let (_, db, _) := irBound ctx dmax 0 divisor
    -- without GIVING (`DIVIDE a INTO r`) each receiver is a dividend
    let over := if giving then opOver30 (ia + db + max da dmax) rounded
      else rcv.any (fun r =>
        let (ir, dr, _) := irBound ctx dmax 0 (.ref r.ref)
        opOver30 (ir + db + max dr dmax) rounded)
    if ((giving && 1 < rcv.length) || rounded || rem.isSome) && over then
      return [.unsupported "DIVIDE with an intermediate quotient that can need more than 30 digits"]
    match rem, rs with
    | some r, [q] => do
      let rr ← liftE (ref ctx r)
      pure [.divRem a b q { ref := rr } onSize.isSome hs ns]
    | some _, _ => liftE (throw "DIVIDE ... REMAINDER needs exactly one quotient")
    | none, _ =>
      pure [.arith (if giving then .divGiving a b else .divInto b) rs onSize.isSome hs ns]
  | .ite c t e => do
    pure [.ite (← liftE (cond ctx c)) (← stmts ctx t) (← stmts ctx e)]
  | .evaluate arms other => do
    let o ← stmts ctx other
    let rec build : List (Surface.Cond × List Surface.Stmt) → RM (List Cobol.Stmt)
      | [] => pure o
      | (c, body) :: rest => do
        pure [.ite (← liftE (cond ctx c)) (← stmts ctx body) (← build rest)]
    build arms
  | .perform first last loop => do
    let (f, l) ← liftE (range ctx first last)
    let id ← nextId
    match loop with
    | .once => pure [.perform id f l]
    | .times n => do pure [.performTimes id (← liftE (expr ctx 0 false n)) f l]
    | .until ta c => do pure [.performUntil id ta (← liftE (cond ctx c)) f l]
    | .varying ta var fromE byE c => do
      let (ini, step) ← liftE (varyingParts ctx var fromE byE)
      pure [.performVarying id ta ini (← liftE (cond ctx c)) step f l]
    | .varyingIdx ta i fromE byE c => do
      let (ini, step) ← liftE (varyingIdxParts ctx i fromE byE)
      pure [.performVarying id ta ini (← liftE (cond ctx c)) step f l]
  | .performInline body loop => do
    let b ← stmts ctx body
    match loop with
    | .once => pure [.block b]
    | .times n => do pure [.inlineTimes (← liftE (expr ctx 0 false n)) b]
    | .until ta c => do pure [.inlineUntil ta (← liftE (cond ctx c)) b]
    | .varying ta var fromE byE c => do
      let (ini, step) ← liftE (varyingParts ctx var fromE byE)
      pure [.inlineVarying ta ini (← liftE (cond ctx c)) step b]
    | .varyingIdx ta i fromE byE c => do
      let (ini, step) ← liftE (varyingIdxParts ctx i fromE byE)
      pure [.inlineVarying ta ini (← liftE (cond ctx c)) step b]
  | .goTo t => do pure [.goTo (← liftE (target ctx t))]
  | .goToDep ts e => do
    pure [.goToDep (← liftE (expr ctx 0 false e)) (← liftE (ts.mapM (target ctx)))]
  | .exitPerform => pure [.exitPerform]
  | .exitCycle => pure [.exitCycle]
  | .exitPara => pure [.exitPara]
  | .exitSection => pure [.exitSection]
  | .nextSentence => pure [.nextSentence]
  | .cont => pure [.cont]
  | .stopRun => pure [.stop .run]
  | .goback => pure [.stop .goback]
  | .exitProgram => pure [.stop .exitProgram]
  | .setIdx i e => do pure [.setIdx i (← liftE (expr ctx 0 false e))]
  | .setIdxBy i e down => do pure [.setIdxBy i (← liftE (expr ctx 0 false e)) down]
  | .setTrue id subs => liftE do
    let some (parent, vals) := ctx.conds.lookup id | throw s!"unknown condition name {id}"
    let some v := vals.head? | throw "condition name without values"
    let src ← valueSrc ctx v.lo
    pure [.move src [← ref ctx { item := parent, subs }]]
  | .display ops => liftE do pure [.display (← ops.mapM (operand ctx))]
  | .initialize dsts => liftE do
    let mut out : List Cobol.Stmt := []
    for d in dsts do
      if d.refStart.isSome then
        out := out ++ (← initRefMod ctx d)
        continue
      let some root := findItem d.item ctx.data | throw s!"unknown item {d.item}"
      let rootP ← item ctx d.item
      for leaf in initTargets root do
        let lp ← item ctx leaf.id
        -- occurrences of tables inside the root: literal subscripts
        let inner := lp.dims.drop rootP.dims.length
        for o in litOccs inner do
          let r ← ref ctx { item := leaf.id, subs := d.subs ++ o }
          let src : Cobol.Operand := match lp.desc.kind with
            | .num _ | .numEdited _ _ => .fig .zero
            | _ => .fig .space
          out := out ++ [.move src [r]]
    pure out
  | .call prog args => liftE do pure [.call prog (← args.mapM (ref ctx))]
  | .read file r into atEnd notAtEnd => do
    let rr ← liftE (ref ctx r)
    let ii ← liftE (into.mapM (ref ctx))
    pure [.read file rr ii (← stmts ctx atEnd) (← stmts ctx notAtEnd)]
  | .write file r => liftE do pure [.write file (← ref ctx r)]
  | .unsupported w => pure [.unsupported w]
  | .fopen file mode => liftE do pure [.fopen file (← openMode mode)]
  | .fclose file => pure [.fclose file]
  | .fread file key into trap exc noExc => do
    let some fd := ctx.files.find? (·.id == file) | liftE (throw s!"READ of undeclared file {file}")
    let k ← liftE (key.mapM (keyIndex fd))
    let ii ← liftE (into.mapM (ref ctx))
    pure [.fread file k ii trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .fwrite file r trap exc noExc => do
    let rr ← liftE (ref ctx r)
    pure [.fwrite file rr trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .frewrite file r trap exc noExc => do
    let rr ← liftE (ref ctx r)
    pure [.frewrite file rr trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .fdelete file trap exc noExc => do
    pure [.fdelete file trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .fstart file op key trap exc noExc => do
    let some fd := ctx.files.find? (·.id == file)
      | liftE (throw s!"START of an undeclared file {file}")
    let d ← liftE (fileDecl ctx fd)
    let some rk := d.key | liftE (throw s!"START of file {file}, which is not indexed")
    let op' ← liftE (match op with
      | "=" => pure CmpOp.eq
      | ">" => pure .gt
      | ">=" => pure .ge
      | o => throw s!"START KEY {o}")
    -- the record key or an alternate key, or a leading part of one (IBM: a data item whose
    -- leftmost character position is the key's, of at most the key's size)
    let k ← match key with
      | none => pure (some rk)
      | some i => liftE do
        let it ← item ctx i
        pure (((rk :: d.alt).find? fun kd =>
            it.desc.off == d.area.off + kd.off && it.desc.len ≤ kd.len).map fun kd =>
          { kd with len := it.desc.len })
    match k with
    | none => pure [.unsupported "START KEY item that is not a key of the file or a leading part of one"]
    | some k => pure [.fstart file op' k trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .clock dst start len => liftE do pure [.clock (← ref ctx dst) start len]
  | .abend code => liftE do pure [.abend (← expr ctx 0 false code)]
  | .inspect target tally repl => liftE do
    let phrase (p : Surface.InspPhrase) : Except String InspPhrase := do
      let kind ← match p.kind with
        | "chars" => pure InspKind.chars
        | "all" => pure .all
        | "leading" => pure .leading
        | "first" => pure .first
        | k => throw s!"unknown INSPECT phrase {k}"
      pure { kind, pat := ← p.pat.mapM (operand ctx), rep := ← p.rep.mapM (operand ctx),
             before := ← p.before.mapM (operand ctx), after := ← p.after.mapM (operand ctx),
             counter := ← p.counter.mapM (ref ctx) }
    pure [.inspect (← ref ctx target) (← tally.mapM phrase) (← repl.mapM phrase)]
  | .search idx occurs varIdx varRef atEnd conds bodies => do
    let cs ← liftE (conds.mapM (cond ctx))
    let bs ← bodies.mapM fun b => do pure (Cobol.Stmt.block (← stmts ctx b))
    -- the index, and the `VARYING` index or item, go up by one per step
    let vbump ← match varIdx, varRef with
      | some j, _ => pure [Cobol.Stmt.setIdxBy j (.lit 1) false]
      | none, some r => liftE do
        pure [Cobol.Stmt.arith (.addTo (.lit 1)) [{ ref := ← ref ctx r }] false [] []]
      | none, none => pure []
    pure [.search (.numCmp .gt (.idx idx) (.lit occurs)) cs bs
      (Cobol.Stmt.setIdxBy idx (.lit 1) false :: vbump) (← stmts ctx atEnd)]
  | .searchAll idx occurs keys atEnd c body => do
    let ks ← liftE (keys.mapM fun k => do pure (k.asc, ← ref ctx k.key))
    -- the KEY-order check of `Sem.searchAllPick` compares alphanumeric keys in native order
    if ctx.seq.isSome && ks.any (fun (_, r) => match r.desc.kind with | .num _ => false | _ => true) then
      return [.unsupported "SEARCH ALL with an alphanumeric KEY in a program collating sequence"]
    pure [.searchAll idx occurs ks (← liftE (cond ctx c)) (← stmts ctx body) (← stmts ctx atEnd)]
  | .unstring src delims into ptr tally onOvf notOnOvf => do
    let ds ← liftE (delims.mapM fun d => do pure (d.all, ← operand ctx d.op))
    let rs ← liftE (into.mapM fun r => do
      pure ({ rcv := ← ref ctx r.rcv, delim := ← r.delim.mapM (ref ctx),
              count := ← r.count.mapM (ref ctx) } : UnstrInto))
    pure [.unstring (← liftE (ref ctx src)) ds rs (← liftE (ptr.mapM (ref ctx)))
      (← liftE (tally.mapM (ref ctx))) onOvf.isSome (← stmts ctx (onOvf.getD []))
      (← stmts ctx notOnOvf)]
  | .stringInto groups into ptr onOvf notOnOvf => do
    let srcs ← liftE ((groups.flatMap fun g => g.srcs.map (·, g.delim)).mapM fun (s, d) => do
      pure (← operand ctx s, ← d.mapM (operand ctx)))
    pure [.stringInto srcs (← liftE (ref ctx into)) (← liftE (ptr.mapM (ref ctx))) onOvf.isSome
      (← stmts ctx (onOvf.getD [])) (← stmts ctx notOnOvf)]
  | .setAddress dst ptr => liftE do pure [.setAddress (← ref ctx dst) (← ref ctx ptr)]
  | .callLocal para binds => liftE do
    pure [.callLocal (← target ctx para) (← binds.mapM fun (a, p) => do pure (← ref ctx a, ← ref ctx p))]
  | .callDyn prog _ _ _ _ =>
    -- (messages short enough for one line of `repr`)
    pure [.unsupported (match prog with
      | some p => s!"CALL {p} ON EXCEPTION: not in the run unit, availability not modelled"
      | none => "CALL identifier: no program of the run unit has that name")]
  | .cancel prog _ =>
    pure [.unsupported (match prog with
      | some p => s!"CANCEL {p}: not linked into the program that cancels it"
      | none => "CANCEL identifier: no linked program has that name")]
  | .convert target src dst before after => liftE do
    pure [.convert (← ref ctx target) (← operand ctx src) (← operand ctx dst)
      (← before.mapM (operand ctx)) (← after.mapM (operand ctx))]
  | .accept dst => liftE do pure [.accept (← ref ctx dst)]
  | .fcloseOpt file opt => liftE do pure [.fcloseOpt file (← closeOpt opt)]
  | .fopenRev file => pure [.fopenRev file]

/-- `VARYING v FROM f BY b`: initialization and augmentation statements. -/
partial def varyingParts (ctx : Ctx) (var : Ref) (fromE byE : Surface.Expr) :
    Except String (List Cobol.Stmt × List Cobol.Stmt) := do
  let v ← ref ctx var
  let f ← expr ctx 0 false fromE
  let b ← expr ctx 0 false byE
  pure ([.arith (.giving f) [{ ref := v }] false [] []],
        [.arith (.addTo b) [{ ref := v }] false [] []])

/-- `VARYING i FROM f BY b` of an index name: `SET i TO f` and `SET i UP BY b`. -/
partial def varyingIdxParts (ctx : Ctx) (i : Nat) (fromE byE : Surface.Expr) :
    Except String (List Cobol.Stmt × List Cobol.Stmt) := do
  pure ([.setIdx i (← expr ctx 0 false fromE)], [.setIdxBy i (← expr ctx 0 false byE) false])
end

/-- The statements nested in a statement. -/
def subStmts : Cobol.Stmt → List (List Cobol.Stmt)
  | .arith _ _ _ a b | .divRem _ _ _ _ _ a b => [a, b]
  | .ite _ t e => [t, e]
  | .performVarying _ _ i _ s _ _ => [i, s]
  | .block b | .inlineTimes _ b | .inlineUntil _ _ b => [b]
  | .inlineVarying _ i _ s b => [i, s, b]
  | .read _ _ _ a b | .fread _ _ _ _ a b | .fwrite _ _ _ a b | .frewrite _ _ _ a b
  | .fdelete _ _ a b | .fstart _ _ _ _ a b => [a, b]
  | .search _ _ bodies bump atEnd => [bodies, bump, atEnd]
  | .searchAll _ _ _ _ b a => [b, a]
  | .unstring _ _ _ _ _ _ a b | .stringInto _ _ _ _ a b => [a, b]
  | _ => []

/-- Some statement of `ss`, or one nested in it, satisfies `p`. -/
partial def anyStmt (p : Cobol.Stmt → Bool) (ss : List Cobol.Stmt) : Bool :=
  ss.any fun s => p s || (subStmts s).any (anyStmt p)

/-- A statement that can make an alternate key the key of reference of file `d`: a `START` by
an alternate key (or a leading part of one), or, in dynamic access, a `READ` by one. -/
def altKeyUse (d : Cobol.FileDecl) : Cobol.Stmt → Bool
  | .fstart f _ k _ _ _ => f == d.id && d.alt.any (·.off == k.off)
  | .fread f (some (_ + 1)) _ _ _ _ => f == d.id && d.access == .dynamic
  | _ => false

/-- A `CLOSE … WITH LOCK` of file `d`. -/
def lockUse (d : Cobol.FileDecl) : Cobol.Stmt → Bool
  | .fcloseOpt f .lock => f == d.id
  | _ => false

/-- Collect level-88 condition names of the data division. -/
partial def collectConds : List Item → List (Nat × Nat × List CondVal)
  | [] => []
  | it :: rest =>
    it.conds.map (fun (cid, _, vs) => (cid, it.id, vs)) ++ collectConds it.children ++
      collectConds rest

/-! ## `PROGRAM COLLATING SEQUENCE` with an `ALPHABET` given by literals (IBM rules) -/

/-- The characters of one literal of an `ALPHABET` clause; a numeric literal `n` is the
character at ordinal position `n` of the native character set, `HIGH-VALUE` / `LOW-VALUE` are
the native ones. -/
def alphaChars (c : Config) : Lit → Except String (List UInt8)
  | .str s => encodeStr c s
  | .hex h => hexBytes h.toList
  | .num v s _ =>
    if s = 0 ∧ 1 ≤ v ∧ v ≤ 256 then pure [UInt8.ofNat (v.toNat - 1)]
    else throw s!"ALPHABET: {v} is not an ordinal position (1 to 256)"
  | .fig n => do
    match ← figurative c n with
    | .high => pure [0xFF]
    | .low => pure [0]
    | .space => pure [c.space]
    | .quote => pure [c.quote]
    | .zero => pure [c.zeroChar]
    | .all _ => throw "ALPHABET: ALL literal"
  | .all _ => throw "ALPHABET: ALL literal"

/-- The positions one phrase gives, in ascending order, each as the characters sharing it (the
first one given first): each character of a literal; `THROUGH`: the native characters from the
first to the second, ascending or descending; `ALSO`: one position. -/
def alphaGroups (c : Config) (p : AlphaPhrase) : Except String (List (List UInt8)) := do
  let a ← alphaChars c p.lit
  match p.thru, p.also with
  | none, [] => pure (a.map ([·]))
  | some t, [] => do
    match a, ← alphaChars c t with
    | [x], [y] =>
      let lo := x.toNat
      let hi := y.toNat
      pure (if lo ≤ hi then (List.range (hi - lo + 1)).map (fun i => [UInt8.ofNat (lo + i)])
            else (List.range (lo - hi + 1)).map (fun i => [UInt8.ofNat (lo - i)]))
    | _, _ => throw "ALPHABET: THROUGH with a literal of more than one character"
  | none, als => do
    let bs ← als.mapM (alphaChars c)
    match a with
    | [x] =>
      if bs.all (·.length == 1) then pure [x :: bs.flatten]
      else throw "ALPHABET: ALSO with a literal of more than one character"
    | _ => throw "ALPHABET: ALSO with a literal of more than one character"
  | some _, _ :: _ => throw "ALPHABET: THROUGH and ALSO in one phrase"

/-- The collating sequence of an `ALPHABET` given by literals: the positions in the order given,
then each character not given, in native order ("Any characters that are not explicitly
specified assume positions in this collating sequence higher than any of the explicitly
specified characters"). `HIGH-VALUE` is the last character of the last position ("the last
character specified (or defaulted to ...)"), `LOW-VALUE` the first of the first ("the first
character specified"). A character given twice, or numeric and alphanumeric literals mixed, is
an error (IBM: a compile-time error). -/
def collation (c : Config) (ps : List AlphaPhrase) : Except String Collation := do
  let lits := ps.flatMap (fun p => p.lit :: (p.thru.toList ++ p.also))
  let isNum : Lit → Bool := fun l => match l with | .num .. => true | _ => false
  unless lits.all isNum || lits.all (fun l => !isNum l) do
    throw "ALPHABET: numeric and alphanumeric literals mixed"
  let given := (← ps.mapM (alphaGroups c)).flatten
  let gs := given.flatten
  unless gs.length == gs.eraseDups.length do throw "ALPHABET: a character is given more than once"
  let rest := ((List.range 256).map UInt8.ofNat).filter (fun b => !gs.contains b)
  let groups := given ++ rest.map ([·])
  let pos := (List.range 256).map (fun b =>
    (groups.findIdx? (fun g => g.contains (UInt8.ofNat b))).getD 0)
  pure { pos, chars := groups.map (·.headD 0), high := (groups.getLastD []).getLastD 0xFF,
         low := (groups.headD []).headD 0 }

/-- The data division with `VALUE HIGH-VALUE` / `LOW-VALUE` as the characters of the program
collating sequence `s` (for the initial storage). -/
partial def seqValues (s : Collation) (it : Item) : Item :=
  { it with
    value := match it.value with
      | some (.fig .high) => some (.fig (.all [s.high]))
      | some (.fig .low) => some (.fig (.all [s.low]))
      | v => v
    children := it.children.map (seqValues s) }

/-- Check an `OCCURS DEPENDING ON` table (IBM's rules for the tables this model accepts): `integer-1`
is below `integer-2`; the table's only dimension is its own and it ends every group containing it
(no variably located item); its object is an integer item outside the table and every table. -/
def odoDeclOk (ctx : Ctx) (o : OdoDecl) : Except String Unit := do
  let (tp, stride, mx) ← odoTable ctx o
  unless o.min < mx do throw s!"OCCURS DEPENDING ON table {tp.name}: {o.min} TO {mx}"
  let op ← item ctx o.obj
  unless op.dims.isEmpty do throw s!"OCCURS DEPENDING ON object {op.name} is in a table"
  match op.desc.kind with
  | .num f => unless f.scale == 0 do throw s!"OCCURS DEPENDING ON object {op.name} is not an integer"
  | _ => throw s!"OCCURS DEPENDING ON object {op.name} is not numeric"
  let tEnd := tp.desc.off + mx * stride
  unless op.desc.off + op.desc.len ≤ tp.desc.off ∨ tEnd ≤ op.desc.off do
    throw s!"OCCURS DEPENDING ON object {op.name} lies in the table {tp.name}"
  let some groups := itemPath o.subject ctx.data | throw s!"unknown item {o.subject}"
  for g in groups do
    let gp ← item ctx g.id
    unless gp.desc.off + gp.desc.len == tEnd do
      throw s!"item {gp.name} has items after the OCCURS DEPENDING ON table {tp.name}"

/-- Resolve a surface program. -/
def program (sp : Surface.Program) : Except String Cobol.Program := do
  let L := layout sp.config sp.data
  let paraIdx := sp.paras.zipIdx.map (fun (p, i) => (p.name, i))
  let sectNames := (sp.paras.filterMap (·.sect)).eraseDups
  let sections := sectNames.filterMap (fun s =>
    let idxs := sp.paras.zipIdx.filterMap (fun (p, i) => if p.sect == some s then some i else none)
    match idxs.head?, idxs.getLast? with
    | some f, some l => some (s, f, l)
    | _, _ => none)
  let seq ← sp.collating.mapM (collation sp.config)
  let ctx : Ctx := { cfg := sp.config, dialect := sp.dialect, L, data := sp.data,
                     conds := collectConds sp.data, paraIdx, sections, files := sp.files, seq,
                     odo := sp.odo.getD [] }
  for o in ctx.odo do odoDeclOk ctx o
  -- `State.files` holds the system input device under the id 0 (`Stmt.accept`): no file may have it
  if sp.files.any (·.id == 0) then throw "file id 0 is reserved for the system input device"
  let files ← sp.files.mapM (fileDecl ctx)
  let (paras, nid) ← (sp.paras.mapM (fun (p : Surface.Paragraph) => do
      let body ← p.sentences.mapM (stmts ctx)
      pure ({ name := p.name, body } : Cobol.Paragraph))).run 0
  -- files whose key of reference can be an alternate key, or with an alternate key that allows
  -- duplicates (`FileDecl.keyRef`)
  let files := files.map fun d =>
    if d.alt.any (·.dups) || paras.any (·.body.any (anyStmt (altKeyUse d))) then
      { d with keyRef := true } else d
  -- files that some `CLOSE … WITH LOCK` names (`FileDecl.lockable`)
  let files := files.map fun d =>
    if paras.any (·.body.any (anyStmt (lockUse d))) then { d with lockable := true } else d
  let secEnd := sp.paras.zipIdx.map (fun ((p : Surface.Paragraph), i) =>
    match p.sect with
    | some s => match sections.lookup s with | some (_, l) => l | none => i
    | none => i)
  -- a declarative runs as an out-of-line PERFORM of its section, with a statement number of
  -- its own (after those of the PERFORM statements)
  let useProcs ← sp.use.zipIdx.mapM (fun ((u : Surface.UseDecl), i) => do
    let (f, l) ← match sections.lookup u.sect with
      | some fl => pure fl
      | none => throw s!"USE: unknown section {u.sect}"
    let mode ← match u.mode with
      | some m => some <$> openMode m
      | none => pure none
    pure ({ files := u.files, mode, id := nid + i, first := f, exit := .sect l } : UseProc))
  let inits := match seq with
    | none => L.inits sp.config
    | some s => (layout sp.config (sp.data.map (seqValues s))).inits sp.config
  pure { name := sp.name, cfg := sp.config, paras := paras.toArray, secEnd := secEnd.toArray,
         memSize := L.size, inits := inits, isMain := sp.isMain, files, useProcs }

end Cobol.Resolve
