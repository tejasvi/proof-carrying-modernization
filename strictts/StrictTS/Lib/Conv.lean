/-
StrictTS library: conversions used by the interpreter (index conversion, SameValueZero,
strict equality, Map/Set key equality).
-/
import StrictTS.Core.World

namespace StrictTS

/-- Integers extended with ±∞ (results of ToIntegerOrInfinity). -/
inductive EInt where
  | negInf
  | posInf
  | fin (n : Int)
  deriving DecidableEq, Repr

namespace Conv

/-- ECMA-262 ToIntegerOrInfinity. -/
def toIntegerOrInf : F64 → EInt
  | .nan => .fin 0
  | .inf true => .negInf
  | .inf false => .posInf
  | .fin x => .fin (F64.fin x).truncInt

/-- Exact integer value of an integral finite number. -/
abbrev toInt? (x : F64) : Option Int := x.toInt?

/-- `x` used as an array index: `some i` iff `x` is a canonical array index
(an integer in `[0, 2^32 - 2]`; `-0` counts as `0`). Other numbers name ordinary
properties, which StrictTS arrays do not have. -/
def arrayIndex? (x : F64) : Option Nat :=
  match toInt? x with
  | some n => if 0 ≤ n ∧ n < 2 ^ 32 - 1 then some n.toNat else none
  | none => none

/-- Clamp a relative index (as in `slice`, `at`, `fill`): negative counts from `len`. -/
def relIndex (x : EInt) (len : Nat) : Nat :=
  match x with
  | .negInf => 0
  | .posInf => len
  | .fin n => if n < 0 then (len + n).toNat else min n.toNat len

/-- Relative index of `at(i)`: `none` when out of range. -/
def atIndex (x : EInt) (len : Nat) : Option Nat :=
  match x with
  | .fin n =>
    let k : Int := if n < 0 then len + n else n
    if 0 ≤ k ∧ k < len then some k.toNat else none
  | _ => none

/-- `x > 0` (false for NaN and zeros). -/
def isPos : F64 → Bool
  | .fin x => !x.neg && x.man != 0
  | .inf neg => !neg
  | .nan => false

/-- IEEE equality (`===` on numbers): NaN is unequal to itself, `+0 = -0`. -/
def numEq : F64 → F64 → Bool
  | .fin a, .fin b => (a.man = 0 && b.man = 0) || decide (a = b)
  | .inf a, .inf b => a == b
  | _, _ => false

/-- SameValueZero on numbers (`Map`/`Set` keys, `includes`): NaN equals NaN, `+0 = -0`. -/
def numSVZ : F64 → F64 → Bool
  | .nan, .nan => true
  | x, y => numEq x y

variable {TT : TypeTable}

mutual
/-- Strict equality `===` (meaningful on `eqable` types; `false` elsewhere). -/
def strictEq : (t : Ty) → Val TT t → Val TT t → Bool
  | .num, x, y => numEq x.toNum y.toNum
  | .bigint, x, y => x.toBig == y.toBig
  | .bool, x, y => x.toBool == y.toBool
  | .str, x, y => x.toStr == y.toStr
  | .undef, _, _ => true
  | .null, _, _ => true
  | .arr _, x, y => x.arrAddr == y.arrAddr
  | .tarr _, x, y => x.tarrAddr == y.tarrAddr
  | .map _ _, x, y => x.mapAddr == y.mapAddr
  | .set _, x, y => x.setAddr == y.setAddr
  | .obj _, x, y => x.objAddr == y.objAddr
  | .promise _, x, y => x.promAddr == y.promAddr
  | .box _, x, y => x.boxAddr == y.boxAddr
  | .ext _, x, y => x.extId == y.extId
  | .dict _, x, y => x.dictAddr == y.dictAddr
  | .enum _, x, y => x.enumIdx == y.enumIdx
  | .opt _, .none, .none => true
  | .opt t, .some x, .some y => strictEq t x y
  | .opt _, _, _ => false
  | .union ts, .inj m x, .inj m' y => unionEq ts m x m' y
  | _, _, _ => false
/-- Strict equality of two union members (equal only when they are the same member). -/
def unionEq : (ts : Tys) → {t t' : Ty} → Mem t ts.toList → Val TT t → Mem t' ts.toList → Val TT t' → Bool
  | .cons u _, _, _, .here, x, .here, y => strictEq u x y
  | .cons _ us, _, _, .there m, x, .there m', y => unionEq us m x m' y
  | _, _, _, _, _, _, _ => false
end

mutual
/-- SameValueZero, the key equality of `Map`, `Set` and `Array.prototype.includes`. -/
def svz : (t : Ty) → Val TT t → Val TT t → Bool
  | .num, x, y => numSVZ x.toNum y.toNum
  | .opt _, .none, .none => true
  | .opt t, .some x, .some y => svz t x y
  | .opt _, _, _ => false
  | .union ts, .inj m x, .inj m' y => unionSVZ ts m x m' y
  | t, x, y => strictEq t x y
def unionSVZ : (ts : Tys) → {t t' : Ty} → Mem t ts.toList → Val TT t → Mem t' ts.toList → Val TT t' → Bool
  | .cons u _, _, _, .here, x, .here, y => svz u x y
  | .cons _ us, _, _, .there m, x, .there m', y => unionSVZ us m x m' y
  | _, _, _, _, _, _, _ => false
end

/-- Code points of a string as one- or two-unit strings (the iteration of `for … of`). -/
def codePointStrs : List UInt16 → List JSStr
  | [] => []
  | [u] => [⟨[u]⟩]
  | u :: v :: rest =>
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00 ∧ 0xDC00 ≤ v.toNat ∧ v.toNat < 0xE000 then
      ⟨[u, v]⟩ :: codePointStrs rest
    else ⟨[u]⟩ :: codePointStrs (v :: rest)

end Conv

namespace JSMap
variable {K V : Type}

/-- Value of the first live entry whose key is equal to `k`. -/
def lookup (eq : K → K → Bool) : List (Option (K × V)) → K → Option V
  | [], _ => none
  | none :: rest, k => lookup eq rest k
  | some (k', v) :: rest, k => if eq k' k then some v else lookup eq rest k

/-- Update the value of the first live entry with key equal to `k` (keeping its key, as
specified); `none` if there is no such entry. -/
def updAux (eq : K → K → Bool) (k : K) (v : V) : List (Option (K × V)) → Option (List (Option (K × V)))
  | [] => none
  | none :: rest => (updAux eq k v rest).map (none :: ·)
  | some (k', v') :: rest =>
    if eq k' k then some (some (k', v) :: rest) else (updAux eq k v rest).map (some (k', v') :: ·)

/-- Turn the live entries with key equal to `k` into tombstones (there is at most one in
any map a program builds); the flag says whether one was found. -/
def delAll (eq : K → K → Bool) (k : K) : List (Option (K × V)) → List (Option (K × V)) × Bool
  | [] => ([], false)
  | none :: rest => let r := delAll eq k rest; (none :: r.1, r.2)
  | some (k', v') :: rest =>
    let r := delAll eq k rest
    if eq k' k then (none :: r.1, true) else (some (k', v') :: r.1, r.2)

def get? (eq : K → K → Bool) (m : JSMap K V) (k : K) : Option V := lookup eq m.entries k

def has (eq : K → K → Bool) (m : JSMap K V) (k : K) : Bool := (m.get? eq k).isSome

/-- `set`: update in place if present, otherwise append (insertion order). -/
def set (eq : K → K → Bool) (m : JSMap K V) (k : K) (v : V) : JSMap K V :=
  match updAux eq k v m.entries with
  | some l => ⟨l⟩
  | none => ⟨m.entries ++ [some (k, v)]⟩

/-- `delete`: leaves a tombstone; returns whether the key was present. -/
def delete (eq : K → K → Bool) (m : JSMap K V) (k : K) : JSMap K V × Bool :=
  let r := delAll eq k m.entries
  (⟨r.1⟩, r.2)

/-- `clear`: every entry becomes a tombstone (live iterators then stop). -/
def clear (m : JSMap K V) : JSMap K V := ⟨m.entries.map fun _ => none⟩

/-- Live entries in insertion order. -/
def toList (m : JSMap K V) : List (K × V) := m.entries.filterMap id

def size (m : JSMap K V) : Nat := m.toList.length

/-- The next live entry at or after entry index `i` (for live iteration). -/
def nextFrom (m : JSMap K V) (i : Nat) : Option (Nat × K × V) :=
  go (m.entries.drop i) i
where
  go : List (Option (K × V)) → Nat → Option (Nat × K × V)
  | [], _ => none
  | none :: rest, j => go rest (j + 1)
  | some (k, v) :: _, j => some (j, k, v)

end JSMap
namespace Dict

/-- Properties of `Object.prototype`, inherited by every plain object. -/
def protoKeys : List String :=
  ["constructor", "__defineGetter__", "__defineSetter__", "hasOwnProperty", "__lookupGetter__",
   "__lookupSetter__", "isPrototypeOf", "propertyIsEnumerable", "toString", "valueOf", "__proto__",
   "toLocaleString"]

def isProtoKey (k : JSStr) : Bool := protoKeys.any fun p => k == JSStr.ofString p

/-- String-keyed properties of `Array.prototype` other than `length` (ECMA-262 2023, as in
Node 22), inherited by every array. -/
def arrayProtoKeys : List String :=
  ["constructor", "at", "concat", "copyWithin", "fill", "find", "findIndex", "findLast",
   "findLastIndex", "lastIndexOf", "pop", "push", "reverse", "shift", "unshift", "slice", "sort",
   "splice", "includes", "indexOf", "join", "keys", "entries", "values", "forEach", "filter", "flat",
   "flatMap", "map", "every", "some", "reduce", "reduceRight", "toReversed", "toSorted",
   "toSpliced", "with", "toLocaleString", "toString"]

/-- A property an array inherits (from `Array.prototype` or `Object.prototype`). -/
def isArrayProtoKey (k : JSStr) : Bool := isProtoKey k || arrayProtoKeys.any fun p => k == JSStr.ofString p

/-- The value of `k` if it is an array index (ECMA-262 §6.1.7): the canonical decimal string of
an integer below 2^32 - 1. -/
def arrayIndex? (k : JSStr) : Option Nat :=
  match k.units with
  | [] => none
  | u :: rest =>
    if u == 48 then (if rest.isEmpty then some 0 else none)
    else
      let ds := k.units.map UInt16.toNat
      if ds.all (fun d => decide (48 ≤ d) && decide (d ≤ 57)) then
        let n := ds.foldl (fun acc d => acc * 10 + (d - 48)) 0
        if n < 2 ^ 32 - 1 then some n else none
      else none

/-- Own string keys in ECMA-262 order (OrdinaryOwnPropertyKeys): array indices ascending, then
the other keys in insertion order. -/
def ordered {V : Type} (l : List (JSStr × V)) : List (JSStr × V) :=
  let idx := l.filter fun p => (arrayIndex? p.1).isSome
  let rest := l.filter fun p => (arrayIndex? p.1).isNone
  idx.mergeSort (fun a b => decide ((arrayIndex? a.1).getD 0 ≤ (arrayIndex? b.1).getD 0)) ++ rest

end Dict

end StrictTS
