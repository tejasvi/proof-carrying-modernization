/-
StrictTS proof layer: evaluation of closed `number` terms inside proofs.

Concrete executions (test cases, constant subexpressions) produce closed `F64` terms such as
`F64.ofNat 1 - F64.ofNat 2`, `Conv.isPos (…)` or `F64.mkFin false 4503599627370496 (-53) * 100`.
`decide` evaluates them with `Meta.whnf`, which runs out of recursion depth inside `round`
(`Nat.log2` has no fast path there), and `simp` has no lemmas for them.

The simprocs of this file (in `simp` and `ts_sym`) compute such a term with the compiled
definitions of `StrictTS.Num.F64` and replace it by its value in **canonical literal form**, the
translator's literal forms after `F64.lit_eq_ofNat`:

* `F64.ofNat n` for the integers `0 ≤ n ≤ 2^53` (`+0` is `F64.ofNat 0`),
* `F64.ofInt (-n)` for the integers `-2^53 ≤ -n < 0`,
* `F64.zero true` for `-0`, `F64.nan`, `F64.inf false` and `F64.inf true`,
* `F64.mkFin neg man exp` for every other double (`man`, `exp` the fields of its `Fin64`).

They are `dsimproc`s: the value is definitionally equal to the term, and the kernel checks that
equality by evaluation (its `Nat` operations, `Nat.log2` included, use GMP), so no `Meta`-level
reduction is involved; one evaluation costs a few milliseconds of kernel time. The other literal
forms (`OfNat.ofNat n`, `F64.ofInt n` with `n ≥ 0`, `F64.mkFin` of an integer, `F64.zero false`,
`F64.fin ⟨…⟩`, the named constants `F64.posInf`, `F64.one`, …) are accepted as arguments and
normalised to the canonical form.

Evaluated: `+ - * / %` and unary `-` (also as `F64.add`, …), `Math.abs/floor/ceil/trunc/round/
sign/sqrt/fround/clz32/min/max/imul`, the bitwise operators, the comparisons (`F64.lt/le/gt/ge/
eq`, `Conv.numEq`, `Conv.numSVZ`, SameValue(Zero)), the predicates (`Conv.isPos`, `isNaN`,
`isFinite`, `isInteger`, `isSafeInteger`, `isZero`, `signBit`), the conversions behind indices
and lengths (`Conv.toIntegerOrInf`, `F64.toInt?`, `F64.truncInt`, `Conv.arrayIndex?`,
`Conv.relIndex`, `Conv.atIndex`, `Prim.posArg`, `Prim.intArg`, `Prim.toLength`, `Prim.toIndex?`,
`F64.toInt32`, `F64.ofInt32`, `F64.ofUint32`), the specified cases of `**`/`Math.pow`
(`F64.pow`: `x ** ±0 = 1`, NaN, infinities, zeros; otherwise the implementation's `I.pow x y`),
`Number::toString` (`NumFormat.toJSString`, to a
`JSStr.ofString` literal), and the equality `x = y` of two literals (`True`/`False`, the latter
proved by `decide` in the kernel).
-/
import StrictTS.Proof.Literals
import StrictTS.Lib.Prim

namespace StrictTS
open Lean Meta Simp

namespace F64Eval

/-! ### Literals -/

def getBool? (e : Lean.Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | _ => none

def getNat? (e : Lean.Expr) : MetaM (Option Nat) := getNatValue? e

/-- Integer literals: `OfNat.ofNat n`, `-OfNat.ofNat n`, `Int.ofNat n`, `Int.negSucc n`, `(n : Int)`. -/
def getInt? (e : Lean.Expr) : MetaM (Option Int) := do
  let e := e.consumeMData
  if let some i ← getIntValue? e then return some i
  match_expr e with
  | Int.ofNat n => return (← getNat? n).map Int.ofNat
  | Int.negSucc n => return (← getNat? n).map Int.negSucc
  | Nat.cast t _ n =>
    unless t.isConstOf ``Int do return none
    return (← getNat? n).map Int.ofNat
  | _ => return none

/-- The value of a closed `F64` literal (any of the forms listed in the module comment). -/
def getF64? (e : Lean.Expr) : MetaM (Option F64) := do
  let e := e.consumeMData
  if let .const n _ := e then
    return match n with
      | ``F64.nan => some .nan
      | ``F64.posInf => some F64.posInf
      | ``F64.negInf => some F64.negInf
      | ``F64.posZero => some F64.posZero
      | ``F64.negZero => some F64.negZero
      | ``F64.one => some F64.one
      | ``F64.maxValue => some F64.maxValue
      | ``F64.minValue => some F64.minValue
      | ``F64.epsilon => some F64.epsilon
      | ``F64.maxSafeInteger => some F64.maxSafeInteger
      | ``F64.minSafeInteger => some F64.minSafeInteger
      | _ => none
  match_expr e with
  | OfNat.ofNat t n _ =>
    unless t.isConstOf ``F64 do return none
    return (getRawNatValue? n).map F64.ofNat
  | F64.ofNat n => return (← getNat? n).map F64.ofNat
  | F64.ofInt i => return (← getInt? i).map F64.ofInt
  | F64.mkFin b m x =>
    let some b := getBool? b | return none
    let some m ← getNat? m | return none
    let some x ← getInt? x | return none
    return some (F64.mkFin b m x)
  | F64.inf b => return (getBool? b).map F64.inf
  | F64.zero b => return (getBool? b).map (fun b => F64.zero b)
  | F64.fin x =>
    let_expr Fin64.mk b m ex _ := x.consumeMData | return none
    let some b := getBool? b | return none
    let some m ← getNat? m | return none
    let some ex ← getInt? ex | return none
    -- the proof of validity is irrelevant: the value is `mkFin b m ex`
    return some (F64.mkFin b m ex)
  | _ => return none

/-- Canonical literal of a double (see the module comment). -/
def toExprF64 : F64 → Lean.Expr
  | .nan => mkConst ``F64.nan
  | .inf b => mkApp (mkConst ``F64.inf) (toExpr b)
  | .fin x =>
    if x.man = 0 then
      if x.neg then mkApp (mkConst ``F64.zero) (toExpr true) else mkApp (mkConst ``F64.ofNat) (mkNatLit 0)
    else
      let fin := mkApp3 (mkConst ``F64.mkFin) (toExpr x.neg) (mkNatLit x.man) (toExpr x.exp)
      match (F64.fin x).toInt? with
      | some i =>
        if i.natAbs ≤ 2 ^ 53 then
          if 0 ≤ i then mkApp (mkConst ``F64.ofNat) (mkNatLit i.toNat)
          else mkApp (mkConst ``F64.ofInt) (toExpr i)
        else fin
      | none => fin

/-- `e` is already the canonical literal of its value. -/
def isCanonical (e : Lean.Expr) (v : F64) : Bool := toExprF64 v == e.consumeMData

def getEInt? (e : Lean.Expr) : MetaM (Option EInt) := do
  let e := e.consumeMData
  if e.isConstOf ``EInt.negInf then return some .negInf
  if e.isConstOf ``EInt.posInf then return some .posInf
  let_expr EInt.fin i := e | return none
  return (← getInt? i).map .fin

def toExprEInt : EInt → Lean.Expr
  | .negInf => mkConst ``EInt.negInf
  | .posInf => mkConst ``EInt.posInf
  | .fin i => mkApp (mkConst ``EInt.fin) (toExpr i)

def toExprOptNat : Option Nat → Lean.Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
  | some n => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) (mkNatLit n)

def toExprOptInt : Option Int → Lean.Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Int)
  | some i => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Int) (toExpr i)

/-! ### Reduction steps -/

/-- A literal not in canonical form becomes canonical (`F64.ofNat n` with a raw literal `n`, as
`F64.lit_eq_ofNat` produces it, counts as canonical). -/
def normalize (e : Lean.Expr) : SimpM DStep := do
  let some v ← getF64? e | return .continue
  if isCanonical e v then return .continue
  if let some n := (e.consumeMData.app1? ``F64.ofNat).bind getRawNatValue? then
    if n ≤ 2 ^ 53 then return .continue
  return .done (toExprF64 v)

def reduceUn (declName : Name) (arity : Nat) (op : F64 → F64) (e : Lean.Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some x ← getF64? e.appArg! | return .continue
  return .done (toExprF64 (op x))

def reduceBin (declName : Name) (arity : Nat) (op : F64 → F64 → F64) (e : Lean.Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some x ← getF64? e.appFn!.appArg! | return .continue
  let some y ← getF64? e.appArg! | return .continue
  return .done (toExprF64 (op x y))

def reduceBinPred (declName : Name) (arity : Nat) (op : F64 → F64 → Bool) (e : Lean.Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some x ← getF64? e.appFn!.appArg! | return .continue
  let some y ← getF64? e.appArg! | return .continue
  return .done (toExpr (op x y))

/-- A function of one double into a type with literals (`Bool`, `Nat`, `EInt`, …). -/
def reduceTo (declName : Name) (arity : Nat) (op : F64 → Lean.Expr) (e : Lean.Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some x ← getF64? e.appArg! | return .continue
  return .done (op x)

/-- A function of a double and a natural number (a length). -/
def reduceWithLen (declName : Name) (arity : Nat) (op : F64 → Nat → Lean.Expr) (e : Lean.Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some x ← getF64? e.appFn!.appArg! | return .continue
  let some n ← getNat? e.appArg! | return .continue
  return .done (op x n)

end F64Eval

open F64Eval

/-! ### Normalisation of literal forms -/

dsimproc [simp, ts_sym] reduceF64OfNat (F64.ofNat _) := normalize
dsimproc [simp, ts_sym] reduceF64OfInt (F64.ofInt _) := normalize
dsimproc [simp, ts_sym] reduceF64MkFin (F64.mkFin _ _ _) := normalize
dsimproc [simp, ts_sym] reduceF64Zero (F64.zero _) := normalize
dsimproc [simp, ts_sym] reduceF64Fin (F64.fin _) := normalize
dsimproc [simp, ts_sym] reduceF64PosInf (F64.posInf) := normalize
dsimproc [simp, ts_sym] reduceF64NegInf (F64.negInf) := normalize
dsimproc [simp, ts_sym] reduceF64PosZero (F64.posZero) := normalize
dsimproc [simp, ts_sym] reduceF64NegZero (F64.negZero) := normalize
dsimproc [simp, ts_sym] reduceF64One (F64.one) := normalize
dsimproc [simp, ts_sym] reduceF64MaxValue (F64.maxValue) := normalize
dsimproc [simp, ts_sym] reduceF64MinValue (F64.minValue) := normalize
dsimproc [simp, ts_sym] reduceF64Epsilon (F64.epsilon) := normalize
dsimproc [simp, ts_sym] reduceF64MaxSafe (F64.maxSafeInteger) := normalize
dsimproc [simp, ts_sym] reduceF64MinSafe (F64.minSafeInteger) := normalize

/-! ### Arithmetic -/

dsimproc [simp, ts_sym] reduceF64Add ((_ + _ : F64)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, ts_sym] reduceF64Sub ((_ - _ : F64)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, ts_sym] reduceF64Mul ((_ * _ : F64)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, ts_sym] reduceF64Div ((_ / _ : F64)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, ts_sym] reduceF64Mod ((_ % _ : F64)) := reduceBin ``HMod.hMod 6 (· % ·)
dsimproc [simp, ts_sym] reduceF64Neg ((- _ : F64)) := reduceUn ``Neg.neg 3 (- ·)
dsimproc [simp, ts_sym] reduceF64AddFn (F64.add _ _) := reduceBin ``F64.add 2 F64.add
dsimproc [simp, ts_sym] reduceF64SubFn (F64.sub _ _) := reduceBin ``F64.sub 2 F64.sub
dsimproc [simp, ts_sym] reduceF64MulFn (F64.mul _ _) := reduceBin ``F64.mul 2 F64.mul
dsimproc [simp, ts_sym] reduceF64DivFn (F64.div _ _) := reduceBin ``F64.div 2 F64.div
dsimproc [simp, ts_sym] reduceF64RemFn (F64.rem _ _) := reduceBin ``F64.rem 2 F64.rem
dsimproc [simp, ts_sym] reduceF64NegFn (F64.neg _) := reduceUn ``F64.neg 1 F64.neg
dsimproc [simp, ts_sym] reduceF64Abs (F64.abs _) := reduceUn ``F64.abs 1 F64.abs
dsimproc [simp, ts_sym] reduceF64Floor (F64.floor _) := reduceUn ``F64.floor 1 F64.floor
dsimproc [simp, ts_sym] reduceF64Ceil (F64.ceil _) := reduceUn ``F64.ceil 1 F64.ceil
dsimproc [simp, ts_sym] reduceF64Trunc (F64.trunc _) := reduceUn ``F64.trunc 1 F64.trunc
dsimproc [simp, ts_sym] reduceF64JsRound (F64.jsRound _) := reduceUn ``F64.jsRound 1 F64.jsRound
dsimproc [simp, ts_sym] reduceF64Sign (F64.sign _) := reduceUn ``F64.sign 1 F64.sign
dsimproc [simp, ts_sym] reduceF64Sqrt (F64.sqrt _) := reduceUn ``F64.sqrt 1 F64.sqrt
dsimproc [simp, ts_sym] reduceF64Fround (F64.fround _) := reduceUn ``F64.fround 1 F64.fround
dsimproc [simp, ts_sym] reduceF64Clz32 (F64.clz32 _) := reduceUn ``F64.clz32 1 F64.clz32
dsimproc [simp, ts_sym] reduceF64Bnot (F64.bnot _) := reduceUn ``F64.bnot 1 F64.bnot
dsimproc [simp, ts_sym] reduceF64Min (F64.min _ _) := reduceBin ``F64.min 2 F64.min
dsimproc [simp, ts_sym] reduceF64Max (F64.max _ _) := reduceBin ``F64.max 2 F64.max
dsimproc [simp, ts_sym] reduceF64Imul (F64.imul _ _) := reduceBin ``F64.imul 2 F64.imul
dsimproc [simp, ts_sym] reduceF64Band (F64.band _ _) := reduceBin ``F64.band 2 F64.band
dsimproc [simp, ts_sym] reduceF64Bor (F64.bor _ _) := reduceBin ``F64.bor 2 F64.bor
dsimproc [simp, ts_sym] reduceF64Bxor (F64.bxor _ _) := reduceBin ``F64.bxor 2 F64.bxor
dsimproc [simp, ts_sym] reduceF64Shl (F64.shl _ _) := reduceBin ``F64.shl 2 F64.shl
dsimproc [simp, ts_sym] reduceF64Sar (F64.sar _ _) := reduceBin ``F64.sar 2 F64.sar
dsimproc [simp, ts_sym] reduceF64Shr (F64.shr _ _) := reduceBin ``F64.shr 2 F64.shr

/-! ### `**` and `Math.pow` -/

/-- `F64.pow f x y` (`**`, `Math.pow` with `f = I.pow`): the result ECMA-262 fixes when `powSpec?`
gives one (`y` NaN or a zero needs no literal `x`), otherwise `f x y`, the implementation's value. -/
dsimproc [simp, ts_sym] reduceF64Pow (F64.pow _ _ _) := fun e => do
  let_expr F64.pow f x y := e | return .continue
  let some b ← getF64? y | return .continue
  if b.isNaN then return .done (toExprF64 .nan)
  if b.isZero then return .done (toExprF64 F64.one)
  let some a ← getF64? x | return .continue
  match F64.powSpec? a b with
  | some v => return .done (toExprF64 v)
  | none => return .done (mkApp2 f x y)

/-! ### Comparisons and predicates -/

dsimproc [simp, ts_sym] reduceF64Lt (F64.lt _ _) := reduceBinPred ``F64.lt 2 F64.lt
dsimproc [simp, ts_sym] reduceF64Le (F64.le _ _) := reduceBinPred ``F64.le 2 F64.le
dsimproc [simp, ts_sym] reduceF64Gt (F64.gt _ _) := reduceBinPred ``F64.gt 2 F64.gt
dsimproc [simp, ts_sym] reduceF64Ge (F64.ge _ _) := reduceBinPred ``F64.ge 2 F64.ge
dsimproc [simp, ts_sym] reduceF64Eq (F64.eq _ _) := reduceBinPred ``F64.eq 2 F64.eq
dsimproc [simp, ts_sym] reduceF64SameValue (F64.sameValue _ _) := reduceBinPred ``F64.sameValue 2 F64.sameValue
dsimproc [simp, ts_sym] reduceF64SameValueZero (F64.sameValueZero _ _) :=
  reduceBinPred ``F64.sameValueZero 2 F64.sameValueZero
dsimproc [simp, ts_sym] reduceNumEq (Conv.numEq _ _) := reduceBinPred ``Conv.numEq 2 Conv.numEq
dsimproc [simp, ts_sym] reduceNumSVZ (Conv.numSVZ _ _) := reduceBinPred ``Conv.numSVZ 2 Conv.numSVZ
dsimproc [simp, ts_sym] reduceIsPos (Conv.isPos _) := reduceTo ``Conv.isPos 1 (toExpr ∘ Conv.isPos)
dsimproc [simp, ts_sym] reduceF64IsNaN (F64.isNaN _) := reduceTo ``F64.isNaN 1 (toExpr ∘ F64.isNaN)
dsimproc [simp, ts_sym] reduceF64IsFinite (F64.isFinite _) := reduceTo ``F64.isFinite 1 (toExpr ∘ F64.isFinite)
dsimproc [simp, ts_sym] reduceF64IsZero (F64.isZero _) := reduceTo ``F64.isZero 1 (toExpr ∘ F64.isZero)
dsimproc [simp, ts_sym] reduceF64SignBit (F64.signBit _) := reduceTo ``F64.signBit 1 (toExpr ∘ F64.signBit)
dsimproc [simp, ts_sym] reduceF64IsInteger (F64.isInteger _) := reduceTo ``F64.isInteger 1 (toExpr ∘ F64.isInteger)
dsimproc [simp, ts_sym] reduceF64IsSafeInteger (F64.isSafeInteger _) :=
  reduceTo ``F64.isSafeInteger 1 (toExpr ∘ F64.isSafeInteger)

/-- `x = y` on two literals: `True` or `False` (SameValue; the latter proved by `decide` in the
kernel). -/
simproc [simp, ts_sym] reduceF64EqProp ((_ : F64) = _) := fun e => do
  let_expr Eq t a b := e | return .continue
  unless t.isConstOf ``F64 do return .continue
  let some x ← getF64? a | return .continue
  let some y ← getF64? b | return .continue
  if x = y then
    -- `a` and `b` are definitionally equal: the kernel checks `Eq.refl`
    let pf := mkApp2 (mkConst ``eq_true) e (← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [(Level.succ .zero)]) t a) e)
    return .done { expr := mkConst ``True, proof? := some pf }
  else
    let inst := mkApp2 (mkConst ``instDecidableEqF64) a b
    let hf := mkApp2 (mkConst ``Eq.refl [(Level.succ .zero)]) (mkConst ``Bool) (mkConst ``Bool.false)
    let ne := mkApp3 (mkConst ``of_decide_eq_false) e inst hf
    return .done { expr := mkConst ``False, proof? := some (mkApp2 (mkConst ``eq_false) e ne) }

/-! ### Conversions (indices, lengths, integer views) -/

dsimproc [simp, ts_sym] reduceToIntegerOrInf (Conv.toIntegerOrInf _) :=
  reduceTo ``Conv.toIntegerOrInf 1 (toExprEInt ∘ Conv.toIntegerOrInf)
dsimproc [simp, ts_sym] reduceF64ToInt? (F64.toInt? _) := reduceTo ``F64.toInt? 1 (toExprOptInt ∘ F64.toInt?)
dsimproc [simp, ts_sym] reduceF64TruncInt (F64.truncInt _) := reduceTo ``F64.truncInt 1 (toExpr ∘ F64.truncInt)
dsimproc [simp, ts_sym] reduceArrayIndex? (Conv.arrayIndex? _) :=
  reduceTo ``Conv.arrayIndex? 1 (toExprOptNat ∘ Conv.arrayIndex?)
dsimproc [simp, ts_sym] reducePosArg (Prim.posArg _ _) :=
  reduceWithLen ``Prim.posArg 2 fun x n => mkNatLit (Prim.posArg x n)
dsimproc [simp, ts_sym] reduceIntArg (Prim.intArg _ _) :=
  reduceWithLen ``Prim.intArg 2 fun x n => toExpr (Prim.intArg x n)
dsimproc [simp, ts_sym] reduceToLength (Prim.toLength _) := reduceTo ``Prim.toLength 1 (mkNatLit ∘ Prim.toLength)
dsimproc [simp, ts_sym] reduceToIndex? (Prim.toIndex? _) := reduceTo ``Prim.toIndex? 1 (toExprOptNat ∘ Prim.toIndex?)
dsimproc [simp, ts_sym] reduceF64ToInt32 (F64.toInt32 _) := reduceTo ``F64.toInt32 1 (toExpr ∘ F64.toInt32)

dsimproc [simp, ts_sym] reduceOfInt32 (F64.ofInt32 _) := fun e => do
  let_expr F64.ofInt32 b := e | return .continue
  let some ⟨n, b⟩ ← getBitVecValue? b | return .continue
  if h : n = 32 then return .done (toExprF64 (F64.ofInt32 (h ▸ b))) else return .continue

dsimproc [simp, ts_sym] reduceOfUint32 (F64.ofUint32 _) := fun e => do
  let_expr F64.ofUint32 b := e | return .continue
  let some ⟨n, b⟩ ← getBitVecValue? b | return .continue
  if h : n = 32 then return .done (toExprF64 (F64.ofUint32 (h ▸ b))) else return .continue

dsimproc [simp, ts_sym] reduceRelIndex (Conv.relIndex _ _) := fun e => do
  let_expr Conv.relIndex x n := e | return .continue
  let some x ← getEInt? x | return .continue
  let some n ← getNat? n | return .continue
  return .done (mkNatLit (Conv.relIndex x n))

dsimproc [simp, ts_sym] reduceAtIndex (Conv.atIndex _ _) := fun e => do
  let_expr Conv.atIndex x n := e | return .continue
  let some x ← getEInt? x | return .continue
  let some n ← getNat? n | return .continue
  return .done (toExprOptNat (Conv.atIndex x n))

/-! ### `Number::toString` -/

/-- `String(x)` of a literal, as the translator's string literal `JSStr.ofString "…"` (only when
the digits are ASCII, which they always are). -/
dsimproc [simp, ts_sym] reduceNumToStr (NumFormat.toJSString _) := fun e => do
  let_expr NumFormat.toJSString x := e | return .continue
  let some x ← getF64? x | return .continue
  let s := NumFormat.toJSString x
  unless s.units.all (· < 128) do return .continue
  let str := String.ofList (s.units.map fun u => Char.ofNat u.toNat)
  unless JSStr.ofString str = s do return .continue
  return .done (mkApp (mkConst ``JSStr.ofString) (mkStrLit str))

end StrictTS
