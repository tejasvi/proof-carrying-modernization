/-
# Expressions, conditions and arithmetic statements

Expressions are evaluated exactly over scaled integers; each node has a static scale
(`Expr.scale`); an intermediate result that IBM carries with fewer places than it can need
(more than 30 digits) is an explicit `Expr.ir30` node.  Arithmetic statements (`ADD`,
`SUBTRACT`, `MULTIPLY`, `DIVIDE`, `COMPUTE`) evaluate their operands once, form each
receiver's exact new value, round it into the receiver (its `ROUNDED MODE`, truncation by
default) and then check the size:

* size error (result does not fit the receiver, division by zero, zero raised to the literal
  power 0, or an inexact result under `ROUNDED MODE PROHIBITED`) with `ON SIZE ERROR`: that
  receiver is left unchanged, the other receivers are still stored, and the `ON SIZE ERROR`
  statements run afterwards;
* without `ON SIZE ERROR`: the high-order-truncated result is stored (IBM), division by zero
  is an abend (`Fault.divByZero`), zero raised to the literal power 0 is 1 (`Expr.pow0`;
  unsupported under `NOT ON SIZE ERROR` alone);
* otherwise the `NOT ON SIZE ERROR` statements run.
-/
import Cobol.Sem.Data

namespace Cobol

/-- Static scale of an expression. -/
def Expr.scale : Expr → Int
  | .lit _ s => s
  | .ref r =>
    match r.refmod, r.desc.kind with
    | none, .num f => f.scale
    | _, _ => 0
  | .idx _ => 0
  | .neg a => a.scale
  | .add a b => Max.max a.scale b.scale
  | .sub a b => Max.max a.scale b.scale
  | .mul a b => a.scale + b.scale
  | .div _ _ s _ => s
  | .rescale _ s _ => s
  | .abs a => a.scale
  | .min a b => Max.max a.scale b.scale
  | .max a b => Max.max a.scale b.scale
  | .integer _ => 0
  | .integerPart _ => 0
  | .mod _ _ => 0
  | .rem a b => Max.max a.scale b.scale
  | .factorial _ => 0
  | .dateFn _ _ => 0
  | .ord _ _ => 0
  | .ordA _ _ _ => 0
  | .powInt _ _ s => s
  | .ir30 _ s _ => s
  | .ir30open a _ => a.scale
  | .pow0 _ _ _ => 0

/-- Operand expressions of an arithmetic operation. -/
def ArithOp.exprs : ArithOp → List Expr
  | .giving e | .addTo e | .subFrom e | .mulBy e | .divInto e => [e]
  | .divGiving a b => [a, b]

/-- The receiver's current value is an input of the operation. -/
def ArithOp.readsReceiver : ArithOp → Bool
  | .giving _ | .divGiving _ _ => false
  | _ => true

namespace Sem

/-- Align a scaled integer from scale `s` to a scale `t ≥ s`. -/
def align (v : Int) (s t : Int) : Int := v * 10 ^ (t - s).toNat

/-- `(x * 10^-sx) / (y * 10^-sy)` rounded to scale `t` by `mode` (`y ≠ 0`). -/
def quot (mode : RoundingMode) (x sx y sy t : Int) : Int :=
  let e := t - sx + sy
  if 0 ≤ e then divRoundZ mode (x * 10 ^ e.toNat) y else divRoundZ mode x (y * 10 ^ (-e).toNat)

/-- The quotient of `quot` is exact. -/
def quotExact (x sx y sy t : Int) : Bool :=
  let e := t - sx + sy
  if 0 ≤ e then (x * 10 ^ e.toNat) % y == 0 else x % (y * 10 ^ (-e).toNat) == 0

/-- Rounding `v` from scale `s` to `t` loses no digit. -/
def rescaleExact (v s t : Int) : Bool :=
  s ≤ t || v % (10 ^ (s - t).toNat : Int) == 0

/-- Combine two evaluated operands. -/
def bin2 (x y : SemM Int) (f : Int → Int → SemM Int) : SemM Int :=
  match x with
  | .error e => .error e
  | .ok a =>
    match y with
    | .error e => .error e
    | .ok b => f a b

/-! ## Integer intrinsic functions -/

/-- `n!`. -/
def factorialNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialNat n

/-- The value `x` (at scale `s`) as an integer, if it has no fractional part. -/
def intArg (x s : Int) : Option Int :=
  if s ≤ 0 then some (x * 10 ^ (-s).toNat)
  else if x % 10 ^ s.toNat = 0 then some (x / 10 ^ s.toNat) else none

/-- Gregorian leap year. -/
def leapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- Days of month `m` (1-12) of year `y`. -/
def monthDays (y m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if leapYear y then 29 else 28
  | _ => 0

/-- Days of the years `1601 ..< y` (`y ≥ 1601`). -/
def daysBeforeYear (y : Nat) : Nat :=
  let f := fun n : Nat => n / 4 - n / 100 + n / 400
  365 * (y - 1601) + (f (y - 1) - f 1600)

/-- Days of the months `1 ..< m` of year `y`. -/
def daysBeforeMonth (y m : Nat) : Nat :=
  ((List.range (m - 1)).map (fun i => monthDays y (i + 1))).sum

/-- Year and day of the year of integer date `n ≥ 1` (day 1 = 1601-01-01; the Gregorian
cycles from 1601 are those from year 1). -/
def yearDay (n : Nat) : Nat × Nat :=
  let k := n - 1
  let n400 := k / 146097
  let k := k % 146097
  let n100 := k / 36524
  let k := k % 36524
  let n4 := k / 1461
  let k := k % 1461
  let n1 := k / 365
  let k := k % 365
  let y := 1601 + 400 * n400 + 100 * n100 + 4 * n4 + n1
  if n1 == 4 || n100 == 4 then (y - 1, 366) else (y, k + 1)

/-- Month and day of the `d`-th day of year `y`. -/
def monthDay (y : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, m, d => (m, d)
  | fuel + 1, m, d => if d ≤ monthDays y m then (m, d) else monthDay y fuel (m + 1) (d - monthDays y m)

/-- An integer date function of an integer argument, or `none` if the argument is out of
the function's domain (IBM: a run-time error). -/
def dateFnVal : DateFn → Int → Option Int
  | .integerOfDate, v =>
    let n := v.toNat
    let y := n / 10000
    let m := n / 100 % 100
    let d := n % 100
    if 0 ≤ v ∧ 1601 ≤ y ∧ y ≤ 9999 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ monthDays y m then
      some (daysBeforeYear y + daysBeforeMonth y m + d)
    else none
  | .integerOfDay, v =>
    let n := v.toNat
    let y := n / 1000
    let d := n % 1000
    if 0 ≤ v ∧ 1601 ≤ y ∧ y ≤ 9999 ∧ 1 ≤ d ∧ d ≤ (if leapYear y then 366 else 365) then
      some (daysBeforeYear y + d)
    else none
  | .dateOfInteger, v =>
    if 1 ≤ v ∧ v ≤ 3067671 then
      let (y, dd) := yearDay v.toNat
      let (m, d) := monthDay y 12 1 dd
      some (y * 10000 + m * 100 + d)
    else none
  | .dayOfInteger, v =>
    if 1 ≤ v ∧ v ≤ 3067671 then
      let (y, dd) := yearDay v.toNat
      some (y * 1000 + dd)
    else none

/-- `x ** y` (`x` at scale `sx`, `y` at scale `sy`) for an exponent that is an integral data item
or expression, or a literal for which IBM's exponentiation table takes the same action (from 30
digits on), at scale `s` (IBM, "Fixed-point data and intermediate results": "When op2 is an
integral data-name or variable, dmax decimal places and 30-dmax ... integer places are used"; in
its example the power is moved to an intermediate result of `dmax` decimal places, and for a
negative exponent 1 is divided by that result, again to `dmax` places).  Unsupported: an exponent
with a fractional part or of more than 64 in magnitude, `0 ** 0` (IBM: a size error, or 1 with a
message) and an intermediate result of more than 30 digits (IBM truncates it with a message).
`0` raised to a negative power, or a negative power of a value whose truncated power is `0`,
divides by zero (IBM: a size error, or an abend without `ON SIZE ERROR`). -/
def powIntVal (x sx y sy s : Int) : SemM Int :=
  match intArg y sy with
  | none => .error (.unsupported "exponent with a fractional part")
  | some n =>
    if 64 < n.natAbs then .error (.unsupported "exponent of more than 64 in absolute value")
    else if n = 0 then
      if x = 0 then .error (.unsupported "zero raised to the power zero")
      else .ok (rescale .truncation 1 0 s)
    else
      let p := rescale .truncation (x ^ n.natAbs) (sx * n.natAbs) s
      if 10 ^ 30 ≤ p.natAbs then
        .error (.unsupported "exponentiation: intermediate result of more than 30 digits")
      else if 0 < n then .ok p
      else if p = 0 then .error .divByZero
      else
        let q := quot .truncation 1 0 p s s
        if 10 ^ 30 ≤ q.natAbs then
          .error (.unsupported "exponentiation: intermediate result of more than 30 digits")
        else .ok q

/-- An intermediate result that can need more than 30 digits as IBM carries it (`ARITH(COMPAT)`;
Programming Guide, "Fixed-point data and intermediate results"): `x` (at scale `sx`) truncated to
`s ≥ 0` decimal places, with `ip` integer places.  When an integer digit cut there is not 0, IBM
writes message IGZ0036W ("Truncation of high order digit positions occurred") and the program goes
on: not modelled (`unsupported`). -/
def ir30Val (x sx s : Int) (ip : Nat) : SemM Int :=
  let v := rescale .truncation x sx s
  if 10 ^ (ip + s.toNat) ≤ v.natAbs then
    .error (.unsupported "intermediate result cut to 30 digits with a nonzero high-order digit (IGZ0036W)")
  else .ok v

/-- Evaluate an expression to its value at scale `e.scale`. -/
def evalExpr (c : Config) (st : State) : Expr → SemM Int
  | .lit v _ => .ok v
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      match numOf c st d with
      | .error e => .error e
      | .ok (v, _) => .ok v
  | .idx i => idxVal st i
  | .neg a =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x => .ok (-x)
  | .add a b =>
    let s := max a.scale b.scale
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y => .ok (align x a.scale s + align y b.scale s))
  | .sub a b =>
    let s := max a.scale b.scale
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y => .ok (align x a.scale s - align y b.scale s))
  | .mul a b => bin2 (evalExpr c st a) (evalExpr c st b) (fun x y => .ok (x * y))
  | .div a b s m =>
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y =>
      if y = 0 then .error .divByZero else .ok (quot m x a.scale y b.scale s))
  | .rescale a s m =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x => .ok (rescale m x a.scale s)
  | .abs a =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x => .ok (x.natAbs : Int)
  | .min a b =>
    let s := max a.scale b.scale
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y => .ok (min (align x a.scale s) (align y b.scale s)))
  | .max a b =>
    let s := max a.scale b.scale
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y => .ok (max (align x a.scale s) (align y b.scale s)))
  | .integer a =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x => .ok (rescale .towardLesser x a.scale 0)
  | .integerPart a =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x => .ok (rescale .truncation x a.scale 0)
  | .mod a b =>
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y =>
      if a.scale ≠ 0 ∨ b.scale ≠ 0 then .error (.unsupported "FUNCTION MOD of non-integers")
      else if y = 0 then .error .divByZero
      else .ok (x - y * divRoundZ .towardLesser x y))
  | .rem a b =>
    let s := max a.scale b.scale
    bin2 (evalExpr c st a) (evalExpr c st b) (fun x y =>
      let x' := align x a.scale s
      let y' := align y b.scale s
      if y' = 0 then .error .divByZero else .ok (x' - y' * divRoundZ .truncation x' y'))
  | .factorial a =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x =>
      match intArg x a.scale with
      | some n => if 0 ≤ n ∧ n ≤ 28 then .ok (factorialNat n.toNat) else .error .range
      | none => .error .range
  | .dateFn f a =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x =>
      match intArg x a.scale with
      | some n =>
        match dateFnVal f n with
        | some v => .ok v
        | none => .error .range
      | none => .error .range
  | .ord a pos =>
    match fnBytes c st a with
    | .error e => .error e
    | .ok [b] => .ok ((pos.getD b.toNat 0 + 1 : Nat) : Int)
    | .ok _ => .error (.unsupported "FUNCTION ORD of an argument that is not one character")
  | .ordA mx args pos =>
    match fnBytesAll c st args with
    | .error e => .error e
    | .ok vs => .ok ((pickIdx c pos mx vs : Nat) : Int)
  | .powInt a e s =>
    bin2 (evalExpr c st a) (evalExpr c st e) (fun x y => powIntVal x a.scale y e.scale s)
  | .ir30 a s ip =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x => ir30Val x a.scale s ip
  | .ir30open a why =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok _ => .error (.unsupported why)
  | .pow0 a trap notOnly =>
    match evalExpr c st a with
    | .error e => .error e
    | .ok x =>
      if trap && x == 0 then .error .divByZero
      else if notOnly && x == 0 then
        .error (.unsupported "zero raised to the literal power 0 under NOT ON SIZE ERROR without ON SIZE ERROR")
      else .ok 1

/-! ## Conditions -/

/-- Apply a relational operator to a comparison result. -/
def cmpOp (op : CmpOp) (o : Ordering) : Bool :=
  match op with
  | .eq => o == .eq
  | .ne => o != .eq
  | .lt => o == .lt
  | .le => o != .gt
  | .gt => o == .gt
  | .ge => o != .lt

/-- Lexicographic comparison of byte strings of equal length. -/
def cmpBytes : List UInt8 → List UInt8 → Ordering
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else cmpBytes as bs
  | _, _ => .eq

/-- A comparison operand as a byte string; figurative constants are expanded to `len`. -/
def cmpOperand (c : Config) (st : State) (len : Nat) : Operand → SemM (List UInt8)
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      match d.kind with
      | .num f =>
        match numOf c st d with
        | .error e => .error e
        | .ok (v, s) =>
          if s ≤ 0 then .ok (digitChars c (intWidth f) (v.natAbs * 10 ^ (-s).toNat))
          else .error (.unsupported "non-integer numeric item in a nonnumeric comparison")
      | _ => .ok (readBytes st d)
  | .num v s n =>
    if s ≤ 0 then
      let m := v.natAbs * 10 ^ (-s).toNat
      .ok (digitChars c (if n = 0 then numDigits m else n) m)
    else .error (.unsupported "non-integer literal in a nonnumeric comparison")
  | .alnum bs => .ok bs
  | .fig f => .ok (fillPattern (figBytes c f) len)
  | .afn f a => afnArg c st (.afn f a)
  | .chr a cs => fnBytes c st (.chr a cs)
  | .amax mx a b pos => fnBytes c st (.amax mx a b pos)

/-- Natural length of a comparison operand (`0` for figurative constants). -/
def operandLen (st : State) (c : Config) : Operand → Nat
  | .ref r => match resolve c st r with
    | .ok d => match d.kind with
      | .num f => intWidth f
      | _ => d.len
    | .error _ => 0
  | .num v s n => if n = 0 then numDigits (v.natAbs * 10 ^ (-s).toNat) else n
  | .alnum bs => bs.length
  | .fig _ => 0
  | .afn _ a => operandLen st c a
  | .chr _ _ => 1
  | .amax mx a b pos =>
    match fnBytes c st (.amax mx a b pos) with
    | .ok bs => bs.length
    | .error _ => 0

/-- Letters and space of the platform character set. -/
def isUpperByte (c : Config) (b : UInt8) : Bool :=
  match c.charset with
  | .ascii => 0x41 ≤ b && b ≤ 0x5A
  | .ebcdic => (0xC1 ≤ b && b ≤ 0xC9) || (0xD1 ≤ b && b ≤ 0xD9) || (0xE2 ≤ b && b ≤ 0xE9)

def isLowerByte (c : Config) (b : UInt8) : Bool :=
  match c.charset with
  | .ascii => 0x61 ≤ b && b ≤ 0x7A
  | .ebcdic => (0x81 ≤ b && b ≤ 0x89) || (0x91 ≤ b && b ≤ 0x99) || (0xA2 ≤ b && b ≤ 0xA9)

/-- Class condition on a resolved item. -/
def classTest (c : Config) (st : State) (t : ClassTest) (d : FieldDesc) : SemM Bool :=
  let bs := readBytes st d
  match t, d.kind with
  | .numeric, .num f =>
    if f.usage == .display || f.usage == .packed then .ok (decodeNum c f bs).isSome
    else .error (.unsupported "NUMERIC test of a binary item")
  | .numeric, _ => .ok (bs.all (fun b => (c.decDigit b).isSome))
  | .alphabetic, .num _ => .error (.unsupported "ALPHABETIC test of a numeric item")
  | .alphabetic, _ => .ok (bs.all (fun b => isUpperByte c b || isLowerByte c b || b == c.space))
  | .alphabeticLower, _ => .ok (bs.all (fun b => isLowerByte c b || b == c.space))
  | .alphabeticUpper, _ => .ok (bs.all (fun b => isUpperByte c b || b == c.space))

/-- Combine two evaluated conditions (both evaluated: a fault in either is a fault). -/
def bool2 (x y : SemM Bool) (f : Bool → Bool → Bool) : SemM Bool :=
  match x with
  | .error e => .error e
  | .ok a =>
    match y with
    | .error e => .error e
    | .ok b => .ok (f a b)

/-- Evaluate a condition.  Both operands of `AND` / `OR` are evaluated (no short-circuit):
a fault in either operand is a fault, since IBM may evaluate them in any order. -/
def evalCond (c : Config) (st : State) : Cond → SemM Bool
  | .const b => .ok b
  | .numCmp op a b =>
    let s := max a.scale b.scale
    match evalExpr c st a with
    | .error e => .error e
    | .ok x =>
      match evalExpr c st b with
      | .error e => .error e
      | .ok y => .ok (cmpOp op (compare (align x a.scale s) (align y b.scale s)))
  | .alnumCmp op a b =>
    let len := max (max (operandLen st c a) (operandLen st c b)) 1
    match cmpOperand c st len a with
    | .error e => .error e
    | .ok x =>
      match cmpOperand c st len b with
      | .error e => .error e
      | .ok y =>
        let n := max x.length y.length
        .ok (cmpOp op (cmpBytes (padRight c x n) (padRight c y n)))
  | .cls t r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d => classTest c st t d
  | .not a =>
    match evalCond c st a with
    | .error e => .error e
    | .ok x => .ok (!x)
  | .and a b => bool2 (evalCond c st a) (evalCond c st b) (· && ·)
  | .or a b => bool2 (evalCond c st a) (evalCond c st b) (· || ·)
  | .alnumCmpSeq op a b pos =>
    let len := max (max (operandLen st c a) (operandLen st c b)) 1
    match cmpOperand c st len a with
    | .error e => .error e
    | .ok x =>
      match cmpOperand c st len b with
      | .error e => .error e
      | .ok y =>
        let n := max x.length y.length
        .ok (cmpOp op (cmpSeq pos (padRight c x n) (padRight c y n)))

/-! ## Arithmetic statements -/

/-- Exact new value (rounded to the receiver's scale `t`) of one receiver, or `none` for a
size error that is not an overflow (division by zero, inexact under `PROHIBITED`). -/
def newValue (op : ArithOp) (ops : List Int) (rv rs t : Int) (mode : RoundingMode) :
    Option Int :=
  let rnd (x sx : Int) : Option Int :=
    if mode == .prohibited && !rescaleExact x sx t then none else some (rescale mode x sx t)
  let qt (x sx y sy : Int) : Option Int :=
    if y = 0 then none
    else if mode == .prohibited && !quotExact x sx y sy t then none
    else some (quot mode x sx y sy t)
  match op, ops with
  | .giving e, [v] => rnd v e.scale
  | .addTo e, [v] => let s := max rs e.scale; rnd (align rv rs s + align v e.scale s) s
  | .subFrom e, [v] => let s := max rs e.scale; rnd (align rv rs s - align v e.scale s) s
  | .mulBy e, [v] => rnd (rv * v) (rs + e.scale)
  | .divInto e, [v] => qt rv rs v e.scale
  | .divGiving a b, [x, y] => qt x a.scale y b.scale
  | _, _ => none

/-- Store an arithmetic result into a resolved receiver.  `trap` = an `ON SIZE ERROR`
phrase is present.  Returns the new state and whether a size error occurred. -/
def storeArith (c : Config) (st : State) (d : FieldDesc) (f : NumFmt) (nv : Option Int)
    (trap : Bool) : SemM (State × Bool) :=
  match nv with
  | none => if trap then .ok (st, true) else .error .divByZero
  | some v =>
    let r := fitNum c f v
    if r.1 && trap then .ok (st, r.1)
    else if r.1 && (overflowUndefined c f || !c.sizeErrorTruncates) then .error .sizeUndefined
    else .ok (writeBytes st d (encodeNum c f r.2), r.1)

/-- Turn a division by zero into `none` (a size error), keep other faults. -/
def catchDiv {α : Type} (x : SemM α) : SemM (Option α) :=
  match x with
  | .ok v => .ok (some v)
  | .error .divByZero => .ok none
  | .error e => .error e

/-- Evaluate a list of expressions. -/
def evalExprs (c : Config) (st : State) : List Expr → SemM (List Int)
  | [] => .ok []
  | e :: es =>
    match evalExpr c st e with
    | .error f => .error f
    | .ok v =>
      match evalExprs c st es with
      | .error f => .error f
      | .ok vs => .ok (v :: vs)

/-- Evaluate operands; `none` if a division by zero occurred inside them. -/
def evalOps (c : Config) (st : State) (es : List Expr) : SemM (Option (List Int)) :=
  catchDiv (evalExprs c st es)

/-- Store into a numeric-edited receiver (only `GIVING` forms may have one). -/
def storeEdited (c : Config) (st : State) (d : FieldDesc) (pic : List ESym) (bwz : Bool)
    (nv : Option Int) (trap : Bool) : SemM (State × Bool) :=
  let ps := (Edit.classify pic).getD []
  let t := Edit.fracDigits ps
  match nv with
  | none => if trap then .ok (st, true) else .error .divByZero
  | some v =>
    if v.natAbs < 10 ^ Edit.numDigitPos ps then
      match Edit.edit c pic bwz v t with
      | some bs => .ok (writeBytes st d bs, false)
      | none => .error (.unsupported "numeric-edited picture")
    else if trap then .ok (st, true)
    else if !c.sizeErrorTruncates then .error .sizeUndefined
    else
      match Edit.edit c pic bwz v t with
      | some bs => .ok (writeBytes st d bs, true)
      | none => .error (.unsupported "numeric-edited picture")

/-- Store the result of an arithmetic operation into each receiver in turn. -/
def arithList (c : Config) (op : ArithOp) (ops : Option (List Int)) (trap : Bool) :
    State → Bool → List Receiver → SemM (State × Bool)
  | st, err, [] => .ok (st, err)
  | st, err, r :: rs =>
    match resolve c st r.ref with
    | .error e => .error e
    | .ok d =>
      let res : SemM (State × Bool) :=
        match d.kind with
        | .num f =>
          match ops with
          | none => storeArith c st d f none trap
          | some vs =>
            if op.readsReceiver then
              match numOf c st d with
              | .error e => .error e
              | .ok (rv, rs) => storeArith c st d f (newValue op vs rv rs f.scale r.mode) trap
            else storeArith c st d f (newValue op vs 0 0 f.scale r.mode) trap
        | .numEdited pic bwz =>
          let t := Edit.fracDigits ((Edit.classify pic).getD [])
          storeEdited c st d pic bwz (match ops with
            | none => none
            | some vs => newValue op vs 0 0 t r.mode) trap
        | _ => .error (.unsupported "non-numeric receiver of an arithmetic statement")
      match res with
      | .error e => .error e
      | .ok (st', e) => arithList c op ops trap st' (err || e) rs

/-- Execute the data part of an arithmetic statement.  Returns the new state and whether
a size error occurred (for any receiver). -/
def arith (c : Config) (st : State) (op : ArithOp) (rcv : List Receiver) (trap : Bool) :
    SemM (State × Bool) :=
  match evalOps c st op.exprs with
  | .error e => .error e
  | .ok ops => arithList c op ops trap st false rcv

/-- `DIVIDE a BY b GIVING q REMAINDER r`.  The remainder is `a - q' * b`, where `q'` is the
quotient truncated to `q`'s decimal places, signed and not truncated at the high-order end
(even when `q` is `ROUNDED`, unsigned, or overflows).  A size error on the quotient leaves
both receivers unchanged (with `ON SIZE ERROR`). -/
def divRem (c : Config) (st : State) (a b : Expr) (q r : Receiver) (trap : Bool) :
    SemM (State × Bool) :=
  match evalExpr c st a, evalExpr c st b, resolve c st q.ref with
  | .error e, _, _ => .error e
  | _, .error e, _ => .error e
  | _, _, .error e => .error e
  | .ok x, .ok y, .ok dq =>
    match dq.kind with
    | .num fq =>
      if y = 0 then (if trap then .ok (st, true) else .error .divByZero) else
      let qv := newValue (.divGiving a b) [x, y] 0 0 fq.scale q.mode
      let qTrunc := quot .truncation x a.scale y b.scale fq.scale
      match storeArith c st dq fq qv trap with
      | .error e => .error e
      | .ok (st1, e1) =>
        if e1 && trap then .ok (st1, true) else
        -- The remainder uses the quotient truncated to the receiver's decimal places, held in
        -- a signed work area (the sign of an unsigned receiver and high-order digits that do
        -- not fit are dropped only when the quotient is stored).
        let s := max a.scale (fq.scale + b.scale)
        let remv := align x a.scale s - align (qTrunc * y) (fq.scale + b.scale) s
        match resolve c st1 r.ref with
        | .error e => .error e
        | .ok dr =>
          match dr.kind with
          | .num fr =>
            match storeArith c st1 dr fr (some (rescale r.mode remv s fr.scale)) trap with
            | .error e => .error e
            | .ok (st2, e2) => .ok (st2, e1 || e2)
          | _ => .error (.unsupported "non-numeric DIVIDE remainder")
    | _ => .error (.unsupported "non-numeric DIVIDE quotient")

end Sem
end Cobol
