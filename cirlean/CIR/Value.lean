import CIR.Module

/-!
  Runtime values of the CIR semantics.

  Memory is a set of blocks holding *structured* values: a class object is an
  `agg` of its fields, an array an `arr` of its elements, a `std::vector<T>`
  the list of its elements. Pointers are a block plus a path into that value,
  so pointers into class members, array elements and container elements are
  exact and need no byte layout.
-/

namespace CIR

/-- One step of a pointer path. -/
inductive PathElem where
  /-- Field `i` of a record or element `i` of an array. -/
  | idx (i : Nat)
  /-- Element `i` of a standard container whose current generation is `gen`.
  Every operation that may reallocate the container bumps its generation,
  so a stale iterator or element pointer no longer resolves. -/
  | vel (gen : Nat) (i : Nat)
  /-- Byte `k` of the object the path before it designates: a character
  pointer into an integer, floating or `bool` object (C11 6.5p7, 6.2.6.1p4),
  `0 < k <` its size; byte 0 is the object pointer itself. Pointer arithmetic
  (`Ctx.stride?`) gives byte views too: a character pointer at a byte where no
  subobject starts (of the innermost scalar that contains it, or of a union
  when the byte lies outside its active member, `Ctx.canonByte`), the pointer
  one past an object that is no array element (`k =` the size of the pointer's
  type), and a stride in other units than an array's elements. Through a byte
  view only a character access is defined. -/
  | byte (k : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Pointer values. -/
inductive Ptr where
  | null
  /-- Into block `blk` at `path`. -/
  | loc (blk : Nat) (path : List PathElem)
  /-- Address of a function. -/
  | fn (sym : String)
  /-- Slot `slot` of array `index` of the vtable global `sym`: vptr values
  and the addresses of virtual functions. Vtables are constant, so loads
  through such a pointer read the module's initializer, not memory. -/
  | vtable (sym : String) (index slot : Nat)
  /-- A non-null integer address that designates no object (`(char *) 1`, the
  address of an object that has died, `Ctx.ptrOfAddr`): it compares by its
  address and converts back to that integer; any access through it is undefined. -/
  | addr (a : Int)
  /-- The address of label `lbl` of function `fn` (GNU `&&lbl`): it can be
  compared and stored; only `fn`'s `cir.indirect_goto` jumps to it; any access
  through it, or a call, is undefined. -/
  | label (fn : String) (lbl : String)
  deriving Repr, DecidableEq, Inhabited

/-- An exception in flight: the exception object and its `typeinfo` symbol. -/
structure Exn where
  obj      : Ptr
  typeinfo : String
  deriving Repr, DecidableEq, Inhabited

/-- Runtime values. -/
inductive Val where
  /-- Indeterminate (uninitialised) value. Reading it as a scalar is UB. -/
  | undef
  /-- Integer, kept normalised to the range of its CIR type. In a `bool` or
  floating object: its bytes as an unsigned number, when a character store or
  a byte-wise copy left them no value of the type (`setByteRepr`,
  `Std.scalarOfBytes`). -/
  | int (v : Int)
  | bool (b : Bool)
  /-- Floating point (binary64; binary32 values are kept rounded). -/
  | float (f : Float)
  | ptr (p : Ptr)
  /-- Record object: its fields in order (base subobjects included). -/
  | agg (fs : List Val)
  /-- C array: its elements in order. Pointer arithmetic is only defined
  inside `arr` and `vec` values. -/
  | arr (xs : List Val)
  /-- Contents of a `std::vector<T>` or `std::string` (the string keeps its
  terminating `'\0'` as last element). `gen` is the generation. -/
  | vec (gen : Nat) (xs : List Val)
  /-- Contents of a `std::optional<T>`. -/
  | opt (v : Option Val)
  /-- An `!cir.eh_token` / `!cir.catch_token`: the exception it refers to. -/
  | tok (e : Exn)
  deriving Repr, Inhabited

namespace Val

/-- Read the sub-value at a path. -/
def get? : Val → List PathElem → Option Val
  | v, [] => some v
  | .agg fs, .idx i :: p => match fs[i]? with
    | some f => f.get? p
    | none => none
  | .arr xs, .idx i :: p => match xs[i]? with
    | some x => x.get? p
    | none => none
  | .vec g xs, .vel g' i :: p =>
    if g = g' then match xs[i]? with
      | some x => x.get? p
      | none => none
    else none
  | .opt (some v), .idx 0 :: p => v.get? p
  | _, _ => none

/-- Replace the sub-value at a path. Writing an element does not change a
container's generation. -/
def set? : Val → List PathElem → Val → Option Val
  | _, [], w => some w
  | .agg fs, .idx i :: p, w => match fs[i]? with
    | some f => match f.set? p w with
      | some f' => some (.agg (fs.set i f'))
      | none => none
    | none => none
  | .arr xs, .idx i :: p, w => match xs[i]? with
    | some x => match x.set? p w with
      | some x' => some (.arr (xs.set i x'))
      | none => none
    | none => none
  | .vec g xs, .vel g' i :: p, w =>
    if g = g' then match xs[i]? with
      | some x => match x.set? p w with
        | some x' => some (.vec g (xs.set i x'))
        | none => none
      | none => none
    else none
  | .opt (some v), .idx 0 :: p, w => match v.set? p w with
    | some v' => some (.opt (some v'))
    | none => none
  | _, _, _ => none

mutual
/-- The value holds a defined scalar somewhere (a union member that was
written). -/
def holds : Val → Bool
  | .undef => false
  | .agg fs => holdsAny fs
  | .arr xs => holdsAny xs
  | _ => true

/-- Some value of the list holds a defined scalar (`Val.holds`). -/
def holdsAny : List Val → Bool
  | [] => false
  | v :: vs => holds v || holdsAny vs
end

mutual
/-- Writing `w` over `v`: `none` if it changes a determinate scalar of `v` (or
the shape of `v`), else whether it gives an indeterminate position of `v` a
determinate value. -/
def fillsOver : Val → Val → Option Bool
  | .undef, w => some w.holds
  | .int a, .int b => if a = b then some false else none
  | .bool a, .bool b => if a = b then some false else none
  | .float a, .float b => if a.toBits = b.toBits then some false else none
  | .ptr p, .ptr q => if p = q then some false else none
  | .agg fs, .agg gs => fillsOverAll fs gs
  | .arr xs, .arr ys => fillsOverAll xs ys
  | _, _ => none
/-- `fillsOver` elementwise, `none` for lists of different lengths. -/
def fillsOverAll : List Val → List Val → Option Bool
  | [], [] => some false
  | v :: vs, w :: ws => match fillsOver v w, fillsOverAll vs ws with
    | some a, some b => some (a || b)
    | _, _ => none
  | _, _ => none
end

/-- Writing `w` over `v` belongs to the initialization of a const object (a
`readonly` block): `v` holds no defined scalar, or `w` keeps each determinate
scalar of `v` and gives one of its indeterminate positions a determinate value
(the library models write a `memset` that zero-fills the rest of a partly
initialized array as a write of the whole array). -/
def initBy (v w : Val) : Bool := !v.holds || v.fillsOver w == some true

end Val

/-! ### Integers -/

/-- Smallest value of an integer type. -/
def intMin (signed : Bool) (w : Nat) : Int :=
  if signed then -((2 : Int) ^ (w - 1)) else 0

/-- Largest value of an integer type. -/
def intMax (signed : Bool) (w : Nat) : Int :=
  if signed then (2 : Int) ^ (w - 1) - 1 else (2 : Int) ^ w - 1

/-- `(2 : Int) ^ n`, the powers that the integer widths 8, 16, 32 and 64 need given as
literals: compiled code computes `intMin`, `intMax` and `wrap` through it (`@[csimp]`), and
so never raises 2 to a power for those widths. -/
def pow2Fast (n : Nat) : Int :=
  match n with
  | 7 => 128
  | 8 => 256
  | 15 => 32768
  | 16 => 65536
  | 31 => 2147483648
  | 32 => 4294967296
  | 63 => 9223372036854775808
  | 64 => 18446744073709551616
  | n => (2 : Int) ^ n

theorem pow2Fast_eq (n : Nat) : pow2Fast n = (2 : Int) ^ n := by
  unfold pow2Fast
  split <;> first | rfl | decide

/-- `intMin` with `pow2Fast` (compiled code). -/
def intMinFast (signed : Bool) (w : Nat) : Int :=
  if signed then -(pow2Fast (w - 1)) else 0

/-- `intMax` with `pow2Fast` (compiled code). -/
def intMaxFast (signed : Bool) (w : Nat) : Int :=
  if signed then pow2Fast (w - 1) - 1 else pow2Fast w - 1

@[csimp] theorem intMin_eq_intMinFast : @intMin = @intMinFast := by
  funext signed w
  simp only [intMin, intMinFast, pow2Fast_eq]

@[csimp] theorem intMax_eq_intMaxFast : @intMax = @intMaxFast := by
  funext signed w
  simp only [intMax, intMaxFast, pow2Fast_eq]

/-- `x` is representable in the integer type. -/
def inRange (signed : Bool) (w : Nat) (x : Int) : Bool :=
  decide (intMin signed w ≤ x) && decide (x ≤ intMax signed w)

/-- Reduce modulo `2^w` into the range of the type (two's complement). -/
def wrap (signed : Bool) (w : Nat) (x : Int) : Int :=
  let m := x % (2 : Int) ^ w
  if signed && decide ((2 : Int) ^ (w - 1) ≤ m) then m - (2 : Int) ^ w else m

/-- `wrap` with `pow2Fast` (compiled code). -/
def wrapFast (signed : Bool) (w : Nat) (x : Int) : Int :=
  let m := x % pow2Fast w
  if signed && decide (pow2Fast (w - 1) ≤ m) then m - pow2Fast w else m

@[csimp] theorem wrap_eq_wrapFast : @wrap = @wrapFast := by
  funext signed w x
  simp only [wrap, wrapFast, pow2Fast_eq]

/-- Bitwise operation through the two's complement representation. -/
def bitwise (signed : Bool) (w : Nat) (f : BitVec w → BitVec w → BitVec w) (x y : Int) : Int :=
  let r := f (BitVec.ofInt w x) (BitVec.ofInt w y)
  if signed then r.toInt else r.toNat

end CIR
