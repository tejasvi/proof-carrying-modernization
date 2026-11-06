/-
StrictTS library: values of type `unknown` (`Ty.dyn`), a value paired with its runtime type.

`typeof`, `Array.isArray`, ToBoolean, `===`, checked casts and `String(x)` look at the runtime
value behind optional (`none` is `undefined`), union, named and nested `unknown` wrappers
(`Dyn.base`). What cannot be known about a value (the `typeof` of an external object, `===` on
values without identity) is `none` here and a panic in the semantics.
-/
import StrictTS.Lib.Conv
import StrictTS.Num.Format

namespace StrictTS
namespace Dyn

variable {TT : TypeTable}

/-- The runtime value behind optional, union, named and nested `unknown` wrappers. -/
def base : {t : Ty} → Val TT t → (t' : Ty) × Val TT t'
  | _, .some x => base x
  | _, .none => ⟨.undef, .undef⟩
  | _, .inj _ x => base x
  | _, .fold x => base x
  | _, .dyn _ x => base x
  | t, v => ⟨t, v⟩

/-- `typeof` of a runtime value of type `t` (not a wrapper); `none` for external objects. -/
def typeofBase : Ty → Option String
  | .num => some "number"
  | .bigint => some "bigint"
  | .bool => some "boolean"
  | .str | .enum _ => some "string"
  | .undef => some "undefined"
  | .fn _ _ => some "function"
  | .ext _ => none
  | _ => some "object"

def typeof (v : Val TT .dyn) : Option JSStr := (typeofBase (base v).1).map JSStr.ofString

/-- `Array.isArray` of a runtime value of type `t` (tuples are arrays); `none` for external
objects. -/
def isArrayTy : Ty → Option Bool
  | .arr _ | .tup _ => some true
  | .ext _ => none
  | _ => some false

/-- ToBoolean of a runtime value. -/
def truthyBase : (t : Ty) → Val TT t → Bool
  | .num, v => Conv.numEq v.toNum v.toNum && !Conv.numEq v.toNum (F64.ofNat 0)
  | .bigint, v => v.toBig != 0
  | .bool, v => v.toBool
  | .str, v => !v.toStr.units.isEmpty
  | .enum cs, v => !(JSStr.ofString (cs.get v.enumIdx)).units.isEmpty
  | .undef, _ => false
  | .null, _ => false
  | _, _ => true

def truthy (v : Val TT .dyn) : Bool := truthyBase (base v).1 (base v).2

/-- The case of a string-literal union with the name `s`. -/
def caseIdx (s : JSStr) : (cs : List String) → Option (Fin cs.length)
  | [] => none
  | c :: cs => if JSStr.ofString c == s then some ⟨0, by simp⟩ else (caseIdx s cs).map Fin.succ

mutual
/-- A runtime value (not a wrapper) at type `t`: the same type, a string-literal-union case as a
string or at another union with that case, a string as a case, `undefined` at an optional type,
one member of a union, any value as `unknown`. Records, arrays and objects are not converted
(only the same type is accepted). -/
def castBase : (t : Ty) → (t' : Ty) → Val TT t' → Option (Val TT t)
  | .opt u, t', v => if t' = .undef then some .none else (castBase u t' v).map .some
  | .union ts, t', v => (castUnion ts t' v).map fun ⟨_, m, x⟩ => .inj m x
  | .dyn, t', v => some (.dyn t' v)
  | .str, .enum cs, v => some (.str (JSStr.ofString (cs.get v.enumIdx)))
  | .enum cs, .str, v => (caseIdx v.toStr cs).map .enum
  | .enum cs, .enum cs', v => (caseIdx (JSStr.ofString (cs'.get v.enumIdx)) cs).map .enum
  | t, t', v => if h : t' = t then some (h ▸ v) else none
/-- The first member of a union that accepts the value. -/
def castUnion : (ts : Tys) → (t' : Ty) → Val TT t' → Option ((u : Ty) × Mem u ts.toList × Val TT u)
  | .nil, _, _ => none
  | .cons u us, t', v =>
    match castBase u t' v with
    | some x => some ⟨u, .here, x⟩
    | none => (castUnion us t' v).map fun ⟨w, m, x⟩ => ⟨w, .there m, x⟩
end

/-- The value of type `unknown` at type `t`, if it is one (checked casts and narrowing). -/
def cast (t : Ty) (v : Val TT .dyn) : Option (Val TT t) :=
  if h : v.dynTy = t then some (h ▸ v.dynVal) else castBase t (base v).1 (base v).2

/-- The string of a runtime string or string-literal-union case. -/
def strOf : (t : Ty) → Val TT t → Option JSStr
  | .str, v => some v.toStr
  | .enum cs, v => some (JSStr.ofString (cs.get v.enumIdx))
  | _, _ => none

/-- `===`: strings by content, values of the same runtime type by `Conv.strictEq` (`none` for
values without identity: records, tuples, functions), values of different types differ. -/
def eq (a b : Val TT .dyn) : Option Bool :=
  match base a, base b with
  | ⟨ta, x⟩, ⟨tb, y⟩ =>
    match strOf ta x, strOf tb y with
    | some s, some s' => some (s == s')
    | _, _ => if h : tb = ta then (if ta.eqable then some (Conv.strictEq ta x (h ▸ y)) else none) else some false

/-- `String(x)` of a primitive runtime value. -/
def primStr : (t : Ty) → Val TT t → Option JSStr
  | .num, v => some (NumFormat.toJSString v.toNum)
  | .bigint, v => some (NumFormat.bigintToJSString v.toBig)
  | .bool, v => some (JSStr.ofString (if v.toBool then "true" else "false"))
  | .str, v => some v.toStr
  | .enum cs, v => some (JSStr.ofString (cs.get v.enumIdx))
  | .undef, _ => some (JSStr.ofString "undefined")
  | .null, _ => some (JSStr.ofString "null")
  | _, _ => none

/-- `Error.prototype.toString`. -/
def errStr (e : ErrVal) : JSStr :=
  if e.message.units.isEmpty then e.name
  else if e.name.units.isEmpty then e.message
  else e.name ++ JSStr.ofString ": " ++ e.message

/-- The field named `k` of a record type, with its position. -/
def fieldMem (k : JSStr) : (fs : Fields) → Option ((u : Ty) × Mem u fs.types)
  | .nil => none
  | .cons n u fs => if JSStr.ofString n == k then some ⟨u, .here⟩ else (fieldMem k fs).map fun ⟨w, m⟩ => ⟨w, .there m⟩

/-- The element at position `i`. -/
def nth : {ts : List Ty} → Vals TT ts → Nat → Option ((u : Ty) × Val TT u)
  | _, .nil, _ => none
  | u :: _, .cons v _, 0 => some ⟨u, v⟩
  | _, .cons _ vs, i + 1 => nth vs i

def lengthKey : JSStr := JSStr.ofString "length"

/-- The elements with their types. -/
def sigmas : {ts : List Ty} → Vals TT ts → List ((u : Ty) × Val TT u)
  | _, .nil => []
  | u :: _, .cons v vs => ⟨u, v⟩ :: sigmas vs

/-- The strings joined with commas. -/
def joinComma : List JSStr → JSStr
  | [] => ⟨[]⟩
  | [s] => s
  | s :: ss => s ++ JSStr.ofString "," ++ joinComma ss

end Dyn
end StrictTS
