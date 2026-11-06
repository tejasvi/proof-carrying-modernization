/-
StrictTS library: the ECMAScript BigInt operations on `Int`.
-/
import StrictTS.Core.World

namespace StrictTS.BigOps

/-- Two's-complement `&` on unbounded integers. -/
def land : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (b &&& a))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

/-- Two's-complement `|`. -/
def lor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b ^^^ (b &&& a))
  | .negSucc a, .ofNat b => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

/-- Two's-complement `^`. -/
def lxor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-- `a << b` (negative `b` shifts right, rounding toward -∞). -/
def shl (a b : Int) : Int := if 0 ≤ b then a <<< b.toNat else a >>> (-b).toNat

/-- `a >> b`. -/
def sar (a b : Int) : Int := if 0 ≤ b then a >>> b.toNat else a <<< (-b).toNat

/-- `BigInt.asUintN(bits, x)`. -/
def asUintN (bits : Nat) (x : Int) : Int := x % (2 ^ bits : Nat)

/-- `BigInt.asIntN(bits, x)`. -/
def asIntN (bits : Nat) (x : Int) : Int :=
  if bits = 0 then 0
  else
    let m := x % (2 ^ bits : Nat)
    if (2 ^ (bits - 1) : Nat) ≤ m then m - (2 ^ bits : Nat) else m

def rangeError (msg : String) : ErrVal := mkErr .rangeError (JSStr.ofString msg)

/-- Binary BigInt operators (ECMA-262 BigInt::*); `/` and `%` truncate toward zero. -/
def bin : BigBin → Int → Int → Except ErrVal Int
  | .add, a, b => .ok (a + b)
  | .sub, a, b => .ok (a - b)
  | .mul, a, b => .ok (a * b)
  | .div, a, b => if b = 0 then .error (rangeError "Division by zero") else .ok (a.tdiv b)
  | .rem, a, b => if b = 0 then .error (rangeError "Division by zero") else .ok (a.tmod b)
  | .pow, a, b => if b < 0 then .error (rangeError "Exponent must be non-negative") else .ok (a ^ b.toNat)
  | .band, a, b => .ok (land a b)
  | .bor, a, b => .ok (lor a b)
  | .bxor, a, b => .ok (lxor a b)
  | .shl, a, b => .ok (shl a b)
  | .sar, a, b => .ok (sar a b)

def cmp : Cmp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (b < a)
  | .ge, a, b => decide (b ≤ a)
  | .eq, a, b => a == b

end StrictTS.BigOps
