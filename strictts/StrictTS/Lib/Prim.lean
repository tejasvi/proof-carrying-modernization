/-
StrictTS library: semantics of the pure primitive operations.

Every operation takes exactly its declared argument types; the ECMAScript argument
conversions that remain (ToIntegerOrInfinity of index arguments, ToLength, ToInt32 of radixes)
are spelled out here, so nothing is implicit.
-/
import StrictTS.Lib.Conv
import StrictTS.Lib.Dyn
import StrictTS.Lib.BigInt
import StrictTS.Num.Format
import StrictTS.Num.Parse
import StrictTS.Str.Case

namespace StrictTS

variable {TT : TypeTable}

namespace Prim

def ofErr {α : Type} : Except ErrVal α → Except Exc α
  | .ok a => .ok a
  | .error e => .error (.thrown e)

def rangeError {α : Type} (msg : String) : Except Exc α :=
  .error (.thrown (mkErr .rangeError (JSStr.ofString msg)))

def syntaxError {α : Type} (msg : JSStr) : Except Exc α :=
  .error (.thrown (mkErr .syntaxError msg))

/-- Decimal string of an integer (BigInt::toString). -/
def intToJSStr (n : Int) : JSStr := NumFormat.bigintToJSString n

/-- An index argument after ToIntegerOrInfinity, as an integer (`±∞` beyond any length). -/
def intArg (x : F64) (len : Nat) : Int :=
  match Conv.toIntegerOrInf x with
  | .negInf => -(len : Int) - 1
  | .posInf => (len : Int) + 1
  | .fin n => n

/-- A position argument clamped to `[0, len]` (indexOf, includes, startsWith, …). -/
def posArg (x : F64) (len : Nat) : Nat :=
  match Conv.toIntegerOrInf x with
  | .negInf => 0
  | .posInf => len
  | .fin n => min n.toNat len

/-- ECMA-262 ToLength, as a natural number (`+∞` ↦ 2^53 - 1). -/
def toLength (x : F64) : Nat :=
  match Conv.toIntegerOrInf x with
  | .negInf => 0
  | .posInf => 2 ^ 53 - 1
  | .fin n => min n.toNat (2 ^ 53 - 1)

def numCmp : Cmp → F64 → F64 → Bool
  | .lt => F64.lt | .le => F64.le | .gt => F64.gt | .ge => F64.ge | .eq => F64.eq

/-- Binary number operations. `**`/`Math.pow` give the results ECMA-262 fixes (`F64.powSpec?`:
`x ** ±0 = 1`, NaN rules, infinities, zeros) and consult the implementation's `I.pow` only for the
implementation-approximated case. -/
def numBin (I : Impl) : NumBin → F64 → F64 → F64
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·) | .div => (· / ·) | .rem => (· % ·)
  | .pow => F64.pow I.pow
  | .band => F64.band | .bor => F64.bor | .bxor => F64.bxor
  | .shl => F64.shl | .sar => F64.sar | .shr => F64.shr
  | .min => F64.min | .max => F64.max | .imul => F64.imul
  | .atan2 => I.atan2 | .hypot => I.hypot

def numUn (I : Impl) : NumUn → F64 → F64
  | .neg => (- ·) | .bnot => F64.bnot | .abs => F64.abs | .floor => F64.floor | .ceil => F64.ceil
  | .trunc => F64.trunc | .round => F64.jsRound | .sign => F64.sign | .sqrt => F64.sqrt
  | .fround => F64.fround | .clz32 => F64.clz32
  | op => I.un op

def numPred : NumPred → F64 → Bool
  | .isInteger => F64.isInteger | .isSafeInteger => F64.isSafeInteger
  | .isFinite => F64.isFinite | .isNaN => F64.isNaN

def strCmp : Cmp → JSStr → JSStr → Bool
  | .lt => JSStr.lt | .le => JSStr.le | .gt => JSStr.gt | .ge => JSStr.ge | .eq => fun a b => a == b

/-- ToIndex for `BigInt.asIntN` / `asUintN` bit counts. -/
def toIndex? (x : F64) : Option Nat :=
  match Conv.toIntegerOrInf x with
  | .fin n => if 0 ≤ n ∧ n ≤ 2 ^ 53 - 1 then some n.toNat else none
  | _ => none

def caseMap (I : Impl) (upper : Bool) (s : JSStr) : JSStr :=
  if s.isASCII then (if upper then s.toUpperASCII else s.toLowerASCII)
  else (if upper then I.toUpper s else I.toLower s)

end Prim

open Prim in
/-- Semantics of a primitive operation on its argument values. -/
def PrimOp.eval (I : Impl) {args : List Ty} {t : Ty} (op : PrimOp args t) (vs : Vals TT args) :
    Except Exc (Val TT t) :=
  match op with
  | .numBin o => .ok (.num (Prim.numBin I o vs.a0.toNum vs.a1.toNum))
  | .numUn o => .ok (.num (Prim.numUn I o vs.a0.toNum))
  | .numCmp o => .ok (.bool (Prim.numCmp o vs.a0.toNum vs.a1.toNum))
  | .numPred o => .ok (.bool (Prim.numPred o vs.a0.toNum))
  | .bigBin o => (ofErr (BigOps.bin o vs.a0.toBig vs.a1.toBig)).map .bigint
  | .bigNeg => .ok (.bigint (-vs.a0.toBig))
  | .bigNot => .ok (.bigint (-vs.a0.toBig - 1))
  | .bigCmp o => .ok (.bool (BigOps.cmp o vs.a0.toBig vs.a1.toBig))
  | .bigAsIntN => match toIndex? vs.a0.toNum with
    | some n => .ok (.bigint (BigOps.asIntN n vs.a1.toBig))
    | none => rangeError "Invalid value: not (convertible to) a safe integer"
  | .bigAsUintN => match toIndex? vs.a0.toNum with
    | some n => .ok (.bigint (BigOps.asUintN n vs.a1.toBig))
    | none => rangeError "Invalid value: not (convertible to) a safe integer"
  | .bigOfNum => match F64.toBigInt? vs.a0.toNum with
    | some n => .ok (.bigint n)
    | none => rangeError s!"The number {NumFormat.toJSString vs.a0.toNum} cannot be converted to a BigInt because it is not an integer"
  | .numOfBig => .ok (.num (F64.ofBigInt vs.a0.toBig))
  | .not => .ok (.bool (!vs.a0.toBool))
  | .seq t _ => .ok (.bool (Conv.strictEq t vs.a0 vs.a1))
  | .strCmp o => .ok (.bool (Prim.strCmp o vs.a0.toStr vs.a1.toStr))
  | .strConcat => .ok (.str (vs.a0.toStr ++ vs.a1.toStr))
  | .numToStr => .ok (.str (NumFormat.toJSString vs.a0.toNum))
  | .numToStrRadix =>
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin r =>
      if 2 ≤ r ∧ r ≤ 36 then
        if r = 10 then .ok (.str (NumFormat.toJSString vs.a0.toNum))
        else match NumFormat.toStringRadix vs.a0.toNum r.toNat with
          | some s => .ok (.str s)
          | none => .error (.panic "toString(radix) of a non-integer is implementation-approximated")
      else rangeError "toString() radix must be between 2 and 36"
    | _ => rangeError "toString() radix must be between 2 and 36"
  | .bigToStr => .ok (.str (intToJSStr vs.a0.toBig))
  | .boolToStr => .ok (.str (NumFormat.boolToJSString vs.a0.toBool))
  | .enumToStr cs => .ok (.str (JSStr.ofString (cs.get vs.a0.enumIdx)))
  | .strToNum => .ok (.num (NumParse.stringToNumber vs.a0.toStr))
  | .strToBig => match NumParse.stringToBigInt vs.a0.toStr with
    | some n => .ok (.bigint n)
    | none => syntaxError (JSStr.ofString "Cannot convert " ++ vs.a0.toStr ++ JSStr.ofString " to a BigInt")
  | .parseFloat => .ok (.num (NumParse.parseFloat vs.a0.toStr))
  | .parseInt => .ok (.num (NumParse.parseInt vs.a0.toStr (F64.toInt32 vs.a1.toNum).toInt))
  | .toFixed =>
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin f =>
      if 0 ≤ f ∧ f ≤ 100 then
        match NumFormat.toFixed vs.a0.toNum f.toNat with
        | some s => .ok (.str s)
        | none => rangeError "toFixed() digits argument must be between 0 and 100"
      else rangeError "toFixed() digits argument must be between 0 and 100"
    | _ => rangeError "toFixed() digits argument must be between 0 and 100"
  | .toPrecision =>
    let x := vs.a0.toNum
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin p =>
      if !x.isFinite then .ok (.str (NumFormat.toJSString x))
      else if 1 ≤ p ∧ p ≤ 100 then
        match NumFormat.toPrecision x p.toNat with
        | some s => .ok (.str s)
        | none => rangeError "toPrecision() argument must be between 1 and 100"
      else rangeError "toPrecision() argument must be between 1 and 100"
    | _ =>
      if !x.isFinite then .ok (.str (NumFormat.toJSString x))
      else rangeError "toPrecision() argument must be between 1 and 100"
  | .toExponential =>
    let x := vs.a0.toNum
    let fd : Except Exc (Option Nat) := match vs.a1 with
      | .none => .ok none
      | .some f => match Conv.toIntegerOrInf f.toNum with
        | .fin n => if 0 ≤ n ∧ n ≤ 100 then .ok (some n.toNat)
          else if !x.isFinite then .ok none
          else rangeError "toExponential() argument must be between 0 and 100"
        | _ => if !x.isFinite then .ok none else rangeError "toExponential() argument must be between 0 and 100"
    match fd with
    | .error e => .error e
    | .ok f =>
      if !x.isFinite then .ok (.str (NumFormat.toJSString x))
      else match NumFormat.toExponential x f with
        | some s => .ok (.str s)
        | none => rangeError "toExponential() argument must be between 0 and 100"
  | .strLength => .ok (.num (F64.ofNat vs.a0.toStr.length))
  | .charCodeAt =>
    let s := vs.a0.toStr
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin n => if 0 ≤ n then
        match s.charCodeAt? n.toNat with
        | some u => .ok (.num (F64.ofNat u.toNat))
        | none => .ok (.num F64.nan)
      else .ok (.num F64.nan)
    | _ => .ok (.num F64.nan)
  | .codePointAt =>
    let s := vs.a0.toStr
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin n => if 0 ≤ n then
        match s.codePointAt? n.toNat with
        | some c => .ok (.some (.num (F64.ofNat c)))
        | none => .ok .none
      else .ok .none
    | _ => .ok .none
  | .charAt =>
    let s := vs.a0.toStr
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin n => .ok (.str (if 0 ≤ n then s.charAt n.toNat else JSStr.empty))
    | _ => .ok (.str JSStr.empty)
  | .strAt =>
    let s := vs.a0.toStr
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin n => .ok (match s.at? n with | some c => .some (.str c) | none => .none)
    | _ => .ok .none
  | .strSlice =>
    let s := vs.a0.toStr
    let stop : Int := match vs.a2 with
      | .none => s.length
      | .some e => intArg e.toNum s.length
    .ok (.str (s.slice (intArg vs.a1.toNum s.length) stop))
  | .substring =>
    let s := vs.a0.toStr
    let stop : Int := match vs.a2 with
      | .none => s.length
      | .some e => intArg e.toNum s.length
    .ok (.str (s.substring (intArg vs.a1.toNum s.length) stop))
  | .indexOf =>
    let s := vs.a0.toStr
    .ok (.num (F64.ofInt (s.indexOf vs.a1.toStr (posArg vs.a2.toNum s.length))))
  | .lastIndexOf =>
    let s := vs.a0.toStr
    let x := vs.a2.toNum
    let pos := if x.isNaN then s.length else posArg x s.length
    .ok (.num (F64.ofInt (s.lastIndexOf vs.a1.toStr pos)))
  | .strIncludes =>
    let s := vs.a0.toStr
    .ok (.bool (s.includes vs.a1.toStr (posArg vs.a2.toNum s.length)))
  | .startsWith =>
    let s := vs.a0.toStr
    .ok (.bool (s.startsWith vs.a1.toStr (posArg vs.a2.toNum s.length)))
  | .endsWith =>
    let s := vs.a0.toStr
    let e : Nat := match vs.a2 with
      | .none => s.length
      | .some x => posArg x.toNum s.length
    .ok (.bool (s.endsWith vs.a1.toStr e))
  | .trim => .ok (.str vs.a0.toStr.trim)
  | .trimStart => .ok (.str vs.a0.toStr.trimStart)
  | .trimEnd => .ok (.str vs.a0.toStr.trimEnd)
  | .padStart => .ok (.str (vs.a0.toStr.padStart (toLength vs.a1.toNum) vs.a2.toStr))
  | .padEnd => .ok (.str (vs.a0.toStr.padEnd (toLength vs.a1.toNum) vs.a2.toStr))
  | .strRepeat =>
    match Conv.toIntegerOrInf vs.a1.toNum with
    | .fin n => if 0 ≤ n then .ok (.str (vs.a0.toStr.repeat n.toNat))
      else rangeError s!"Invalid count value: {n}"
    | .posInf => rangeError "Invalid count value: Infinity"
    | .negInf => rangeError "Invalid count value: -Infinity"
  | .replace => .ok (.str (vs.a0.toStr.replaceFirst vs.a1.toStr vs.a2.toStr))
  | .replaceAll => .ok (.str (vs.a0.toStr.replaceAll vs.a1.toStr vs.a2.toStr))
  | .toUpper => .ok (.str (caseMap I true vs.a0.toStr))
  | .toLower => .ok (.str (caseMap I false vs.a0.toStr))
  | .fromCharCode => .ok (.str (JSStr.fromCharCodes [(F64.toBitsN 16 vs.a0.toNum).toNat]))
  | .localeCompare => .ok (.num (I.localeCompare vs.a0.toStr vs.a1.toStr))
  | .errNew k => .ok (.err (mkErr k vs.a0.toStr))
  | .errMessage => .ok (.str vs.a0.toErr.message)
  | .errName => .ok (.str vs.a0.toErr.name)
  | .toDyn t => .ok (.dyn t vs.a0)
  | .dynTypeof => match Dyn.typeof vs.a0 with
    | some s => .ok (.str s)
    | none => .error (.panic "typeof of an external object")
  | .dynIsArray => match Dyn.isArrayTy (Dyn.base vs.a0).1 with
    | some b => .ok (.bool b)
    | none => .error (.panic "Array.isArray of an external object")
  | .dynTruthy => .ok (.bool (Dyn.truthy vs.a0))
  | .dynCast t => .ok (match Dyn.cast t vs.a0 with | some x => .some x | none => .none)
  | .dynEq => match Dyn.eq vs.a0 vs.a1 with
    | some b => .ok (.bool b)
    | none => .error (.panic "comparison of values without identity")

/-- Store conversion of a typed-array element. -/
def TAKind.toElem : (k : TAKind) → Val TT k.elem → BitVec k.width
  | .i8, v => F64.toBitsN 8 v.toNum
  | .u8, v => F64.toBitsN 8 v.toNum
  | .u8c, v => F64.toUint8Clamp v.toNum
  | .i16, v => F64.toBitsN 16 v.toNum
  | .u16, v => F64.toBitsN 16 v.toNum
  | .i32, v => F64.toBitsN 32 v.toNum
  | .u32, v => F64.toBitsN 32 v.toNum
  | .f32, v => F64.toF32Bits v.toNum
  | .f64, v => F64.toBits v.toNum
  | .bi64, v => BitVec.ofInt 64 v.toBig
  | .bu64, v => BitVec.ofInt 64 v.toBig

/-- Load conversion of a typed-array element. -/
def TAKind.ofElem : (k : TAKind) → BitVec k.width → Val TT k.elem
  | .i8, b => .num (F64.ofIntN b)
  | .u8, b => .num (F64.ofUintN b)
  | .u8c, b => .num (F64.ofUintN b)
  | .i16, b => .num (F64.ofIntN b)
  | .u16, b => .num (F64.ofUintN b)
  | .i32, b => .num (F64.ofIntN b)
  | .u32, b => .num (F64.ofUintN b)
  | .f32, b => .num (F64.ofF32Bits b)
  | .f64, b => .num (F64.ofBits b)
  | .bi64, b => .bigint b.toInt
  | .bu64, b => .bigint b.toNat

/-- `log(1 + x)` without the rounding of `1 + x` (Kahan's correction: `x / (u - 1)` is the factor by
which the rounded `u = 1 + x` misses), to a few ulps; Lean's `Float` has no `log1p`. -/
def Impl.log1p (x : Float) : Float :=
  let u := 1 + x
  if x.isInf && x > 0 then x else if u == 1 then x else Float.log u * x / (u - 1)

/-- `exp(x) - 1` without the cancellation near 0 (Kahan's correction), to a few ulps. -/
def Impl.expm1 (x : Float) : Float :=
  let u := Float.exp x
  if x.isInf && x > 0 then x else if u == 1 then x else if u - 1 == -1 then -1 else (u - 1) * x / Float.log u

/-- Default `Impl` used for running programs: the host's libm through Lean's `Float`
(implementation-approximated functions may differ from V8 in the last bit) and the Unicode
default case mapping (`StrictTS.Str.Case`, tables from Node's ICU). -/
def Impl.host : Impl where
  pow x y := F64.ofBits (Float.toBits (Float.pow (Float.ofBits x.toBits.toNat.toUInt64) (Float.ofBits y.toBits.toNat.toUInt64))).toNat
  atan2 x y := F64.ofBits (Float.toBits (Float.atan2 (Float.ofBits x.toBits.toNat.toUInt64) (Float.ofBits y.toBits.toNat.toUInt64))).toNat
  hypot x y :=
    let a := Float.ofBits x.toBits.toNat.toUInt64
    let b := Float.ofBits y.toBits.toNat.toUInt64
    -- (as V8 does it: an infinite argument wins over NaN, and the larger magnitude is factored
    -- out, so the squares neither overflow nor underflow)
    let m := if a.abs < b.abs then b.abs else a.abs
    let n := if a.abs < b.abs then a.abs else b.abs
    let r : Float :=
      if a.isInf || b.isInf then 1.0 / 0.0
      else if a.isNaN || b.isNaN then a + b
      else if m == 0 then 0
      else Float.sqrt (1 + (n / m) * (n / m)) * m
    F64.ofBits (Float.toBits r).toNat
  un op x :=
    let a := Float.ofBits x.toBits.toNat.toUInt64
    let r : Float := match op with
      | .cbrt => Float.cbrt a | .exp => Float.exp a | .expm1 => Impl.expm1 a
      | .log => Float.log a | .log1p => Impl.log1p a | .log2 => Float.log2 a | .log10 => Float.log10 a
      | .sin => Float.sin a | .cos => Float.cos a | .tan => Float.tan a
      | .asin => Float.asin a | .acos => Float.acos a | .atan => Float.atan a
      | .sinh => Float.sinh a | .cosh => Float.cosh a | .tanh => Float.tanh a
      | .asinh => Float.asinh a | .acosh => Float.acosh a | .atanh => Float.atanh a
      | _ => a
    F64.ofBits (Float.toBits r).toNat
  toUpper := JSStr.toUpperFull
  toLower := JSStr.toLowerFull
  localeCompare a b := match JSStr.compare a b with
    | .lt => F64.ofInt (-1) | .eq => F64.zero | .gt => F64.ofNat 1

end StrictTS
