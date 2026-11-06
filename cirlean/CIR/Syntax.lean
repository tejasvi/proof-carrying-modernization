/-
  ClangIR (`cir` MLIR dialect) abstract syntax.

  This is a direct, structured rendering of the CIR operations emitted by
  `clang -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering`
  (llvm-project main, LLVM 24 cycle). Structured control flow is kept as is:
  `cir.for` / `cir.while` / `cir.do` loops, `cir.scope` lexical scopes,
  `cir.cleanup.scope` RAII cleanups, `cir.if`, `cir.ternary`, `cir.switch`,
  `cir.try`. Nothing is lowered to a control-flow graph.

  Conventions:
  * SSA values (`%3`, `%arg0`, `%catch_token`) are interned per function into
    `VId`s (natural numbers) by the frontend.
  * Record types are referenced by their C++ name; their member lists live in
    `Module.records`, which also allows recursive types.
  * Every op that defines values names its result `VId`s explicitly.
-/

namespace CIR

/-- SSA value identifier. -/
abbrev VId := Nat

/-- Index of a block inside its region (entry block = 0). -/
abbrev BlockId := Nat

/-- A source position (`loc("file.cpp":line:col)`), used to name loops and
calls in diagnostics and in loop-invariant annotations. -/
structure Loc where
  line : Nat := 0
  col  : Nat := 0
  deriving Repr, DecidableEq, Inhabited

inductive FloatKind where
  | single | double | fp16 | bf16 | fp80 | fp128 | longDouble
  deriving Repr, DecidableEq, Inhabited

/-- CIR types. -/
inductive Ty where
  /-- `!cir.int<s, 32>` / `!cir.int<u, 8>` (aliases `!s32i`, `!u8i`, ...). -/
  | int (signed : Bool) (width : Nat)
  /-- `!cir.bool` -/
  | bool
  /-- `!cir.float`, `!cir.double`, ... -/
  | float (k : FloatKind)
  /-- `!cir.void` -/
  | void
  /-- `!cir.ptr<T>` -/
  | ptr (pointee : Ty)
  /-- `!cir.array<T x N>` -/
  | array (elem : Ty) (len : Nat)
  /-- `!cir.struct<"Name" ...>` / `!cir.union<...>`, by name. -/
  | record (name : String)
  /-- `!cir.func<(A, B) -> R>` (`R = void` when absent). -/
  | func (params : List Ty) (ret : Ty) (vararg : Bool)
  /-- `!cir.vptr` -/
  | vptr
  | ehToken
  | catchToken
  | cleanupToken
  /-- Any type outside the modelled subset, kept verbatim. -/
  | other (txt : String)
  deriving Repr, Inhabited

mutual
/-- Equality of types by structural recursion (the derived `BEq` of a nested
inductive is opaque to the kernel, which evaluates test theorems). -/
def Ty.beq : Ty → Ty → Bool
  | .int s w, .int s' w' => s == s' && w == w'
  | .bool, .bool => true
  | .float k, .float k' => k == k'
  | .void, .void => true
  | .ptr a, .ptr b => Ty.beq a b
  | .array a n, .array b n' => Ty.beq a b && n == n'
  | .record a, .record b => a == b
  | .func ps r v, .func ps' r' v' => Ty.beqList ps ps' && Ty.beq r r' && v == v'
  | .vptr, .vptr => true
  | .ehToken, .ehToken => true
  | .catchToken, .catchToken => true
  | .cleanupToken, .cleanupToken => true
  | .other a, .other b => a == b
  | _, _ => false
def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

namespace Ty
def s8  : Ty := .int true 8
def s16 : Ty := .int true 16
def s32 : Ty := .int true 32
def s64 : Ty := .int true 64
def u8  : Ty := .int false 8
def u16 : Ty := .int false 16
def u32 : Ty := .int false 32
def u64 : Ty := .int false 64
end Ty

inductive RecordKind where
  | struct | «class» | union
  deriving Repr, DecidableEq, Inhabited

/-- What a record member holds (`data`, `pad`, `empty`, `bitfield`). -/
inductive MemberKind where
  | data | pad | empty | bitfield
  deriving Repr, DecidableEq, Inhabited

structure RecordDecl where
  name    : String
  kind    : RecordKind := .struct
  members : List (MemberKind × Ty) := []
  packed  : Bool := false
  /-- `incomplete` records have no member list. -/
  complete : Bool := true
  /-- The tail padding of a union (`padding = {!u8i}`), which is not a member:
  the union's size is that of its most aligned member plus the padding. -/
  padding : List Ty := []
  /-- The alignment of each member that is a vector, or an array of vectors, by index:
  `!cir.vector<N x T>` is the type `T[N]`, aligned as `T`, but LLVM aligns a vector to its
  size rounded up to a power of two, and CIR's record types, which hold no padding members,
  rely on that layout. -/
  vecAligns : List (Nat × Nat) := []
  deriving Repr, Inhabited

/-- Constant attributes (`#cir.int<5> : !s32i`, `#true`, `#cir.zero`, ...). -/
inductive Const where
  | int (v : Int)
  | bool (b : Bool)
  /-- Floating point literal: source text and its value. -/
  | float (txt : String) (v : Float)
  /-- `#cir.ptr<null>` -/
  | null
  /-- `#cir.ptr<1 : i64>`: a pointer with an integer value. -/
  | ptrInt (v : Int)
  /-- `#cir.zero`: zero-initialised value of the result type. -/
  | zero
  | undef
  | poison
  /-- `#cir.const_array<[...]>` -/
  | array (elems : List Const)
  /-- `#cir.const_array<"abc" : ...>`: the bytes (as integers) followed by
  `trailingZeros` zero elements. -/
  | str (bytes : List Int) (trailingZeros : Nat)
  /-- `#cir.const_record<{...}>` -/
  | record (fields : List Const)
  /-- `#cir.global_view<@sym, [i, j]>`: address of a global (with indices). -/
  | globalAddr (sym : String) (indices : List Int)
  /-- `#cir.global_view<@vt, [i, k], address_point true>`: the vptr value of
  slot `k` of array `i` of the vtable `vt`, as `cir.vtable.address_point`
  gives it (the entries of a VTT). -/
  | vtableAddr (vtable : String) (index slot : Nat)
  /-- `#cir.block_addr_info<@fn, "lbl">`: the address of a label (GNU `&&lbl`). -/
  | blockAddr (fn lbl : String)
  /-- Function address `#cir.global_view<@f>` of function type. -/
  | other (txt : String)
  deriving Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | rem | and | or | xor | max | min
  deriving Repr, DecidableEq, Inhabited

inductive FBinOp where
  | fadd | fsub | fmul | fdiv | frem
  deriving Repr, DecidableEq, Inhabited

inductive UnOp where
  | inc | dec | minus | not
  deriving Repr, DecidableEq, Inhabited

inductive CmpKind where
  | lt | le | gt | ge | eq | ne | one | uno
  deriving Repr, DecidableEq, Inhabited

inductive CastKind where
  | bitcast | arrayToPtrDecay | memberPtrToBool | intToPtr | ptrToInt
  | ptrToBool | integral | intToBool | intToFloat | floatToInt | floatToBool
  | boolToInt | floating | addressSpace | boolToFloat
  | other (name : String)
  deriving Repr, DecidableEq, Inhabited

inductive CleanupKind where
  | normal | eh | all
  deriving Repr, DecidableEq, Inhabited

inductive CaseKind where
  | default | equal | anyof | range
  deriving Repr, DecidableEq, Inhabited

/-- A `cir.try` handler clause. -/
inductive CatchKind where
  /-- `catch [type #cir.global_view<@_ZTIi>]` -/
  | type (typeinfo : String)
  /-- `catch all` -/
  | all
  deriving Repr, DecidableEq, Inhabited

inductive Callee where
  | direct (sym : String)
  | indirect (fn : VId)
  deriving Repr, DecidableEq, Inhabited

mutual
/-- CIR operations. Terminators (`yield`, `condition`, `brk`, `cont`, `ret`,
`br`, `brcond`, `trap`, `unreachable`, `throw`, `resume`) end a block. -/
inductive Op where
  -- values and memory
  | const (res : VId) (ty : Ty) (c : Const)
  /-- `%r = cir.alloca "name" ... : !cir.ptr<ty>`; `ty` is the allocated type. -/
  | alloca (res : VId) (ty : Ty) (name : String)
  /-- `%r = cir.alloca "name" ... const : !cir.ptr<ty>`: a const-qualified local object of a
  type whose writes are its initialization (`Parser.constAllocaTy`; not a parameter, not a
  variable that a loop, a backward `goto` or a `longjmp` initializes again,
  `Parser.plainSlots`): a `readonly` block, which only its initialization writes (C11
  6.7.3p6, `Val.initBy`), and which outlives its region (a region exit ends stack blocks only). -/
  | allocaConst (res : VId) (ty : Ty) (name : String)
  /-- `%r = cir.load %addr : !cir.ptr<ty>, ty` -/
  | load (res : VId) (addr : VId) (ty : Ty)
  /-- A `cir.load` of a scalar return slot (`cir.alloca "__retval"`) feeding a `cir.return`,
  with no CIR text of its own: the frontend marks it where it cannot show a store to the slot
  on every path (`CIR.Frontend.markRetLoads`), so that the function may reach its closing
  brace, which is undefined only if the caller uses the value (C11 6.9.1p12). A slot never
  stored gives the indeterminate value `.undef`; otherwise as `load`. -/
  | retLoad (res : VId) (addr : VId) (ty : Ty)
  /-- `cir.store %val, %addr : ty, !cir.ptr<ty>` -/
  | store (val addr : VId) (ty : Ty)
  /-- No CIR text: undefined unless the pointer `addr` is aligned to `align` bytes. The frontend
  puts it before a load or a store of a vector type whose stated alignment (`align(N)`) exceeds
  its element's: the model types a vector as `T[N]`, aligned as `T`, while a `vector_size(N)`
  type is aligned to N unless a typedef lowers that, which only the access's alignment shows
  (CIR's types do not). A misaligned pointer to such a type comes from a conversion that C
  leaves undefined (C11 6.3.2.3p7) and C++ unspecified ([expr.static.cast]p13); the access
  through it is an aligned vector move, which faults natively. -/
  | alignCheck (addr : VId) (align : Nat)
  /-- `cir.copy %src to %dst : !cir.ptr<ty>` -/
  | copy (src dst : VId) (ty : Ty)
  /-- `%r = cir.get_member %base[idx] {name = ...} : !cir.ptr<rec> -> !cir.ptr<field>` -/
  | getMember (res : VId) (base : VId) (idx : Nat) (recTy fieldTy : Ty)
  /-- `cir.get_member` into a union: member `idx` becomes the active one, the
  others indeterminate (a union holds one member at a time; in a read-only
  block nothing changes). A member that becomes active while indeterminate
  takes the scalars the previously active member stored at its offsets with
  its sizes (`Ctx.fromActive`). Stores through any member pointer activate
  their member as well (`Ctx.unionActivate?`), and reads see the active
  member's scalars (`Ctx.unionView?`). -/
  | unionMember (res : VId) (base : VId) (idx : Nat) (recTy fieldTy : Ty)
  /-- `%r = cir.get_element %base[%i : ity] : !cir.ptr<!cir.array<T x N>> -> !cir.ptr<T>` -/
  | getElement (res : VId) (base idx : VId) (idxTy elemTy : Ty)
  /-- `%r = cir.ptr_stride %base, %off : (!cir.ptr<T>, ity) -> !cir.ptr<T>` -/
  | ptrStride (res : VId) (base off : VId) (elemTy offTy : Ty)
  /-- `%r = cir.ptr_diff %a, %b : !cir.ptr<T> -> rty` -/
  | ptrDiff (res : VId) (a b : VId) (elemTy resTy : Ty)
  | getGlobal (res : VId) (sym : String) (ty : Ty)
  /-- `%r = cir.block_address <@fn, "lbl"> : !cir.ptr<!void>`: the address of a
  label (GNU `&&lbl`). -/
  | blockAddress (res : VId) (fn lbl : String)
  /-- `%r = cir.base_class_addr nonnull %p [offset] : !cir.ptr<D> -> !cir.ptr<B>` -/
  | baseClassAddr (res : VId) (base : VId) (offset : Nat) (srcTy dstTy : Ty)
  | derivedClassAddr (res : VId) (base : VId) (offset : Nat) (srcTy dstTy : Ty)
  /-- `%r = cir.vtable.address_point(@vt, address_point = <index = i, offset = o>)`:
  the vptr value of a class, element `o` of array `i` of its vtable global. -/
  | vtableAddressPoint (res : VId) (vtable : String) (index offset : Nat)
  /-- `%r = cir.vtable.get_vptr %obj : !cir.ptr<T>`: address of the vptr of
  an object of class `T`. -/
  | vtableGetVptr (res : VId) (obj : VId) (ty : Ty)
  /-- `%r = cir.vtable.get_virtual_fn_addr %vptr[i]`: address of slot `i`
  of the vtable the vptr points into. -/
  | vtableGetVirtualFnAddr (res : VId) (vptr : VId) (slot : Nat)
  /-- `%r = cir.vtt.address_point @vtt, offset = n`: the address of entry `n`
  of the VTT global `vtt`, the vptr values that the base-object constructors
  and destructors of a class with virtual bases store (a complete-object
  constructor passes each base the address of its part of the table). -/
  | vttGlobalAddr (res : VId) (vtt : String) (offset : Nat)
  /-- `%r = cir.vtt.address_point %vtt : !cir.ptr<…>, offset = n`: the address
  of entry `n` of the part of a VTT that `vtt` points to (the VTT argument of
  a base-object constructor or destructor). -/
  | vttParamAddr (res : VId) (vtt : VId) (offset : Nat)
  /-- `%r = cir.extract_member %agg[idx] : rec -> field` -/
  | extractMember (res : VId) (agg : VId) (idx : Nat) (aggTy fieldTy : Ty)
  -- arithmetic
  /-- `cir.add nsw %a, %b : ty` etc. `nsw`/`nuw`: overflow is undefined. -/
  | binop (res : VId) (k : BinOp) (nsw nuw : Bool) (a b : VId) (ty : Ty)
  | fbinop (res : VId) (k : FBinOp) (a b : VId) (ty : Ty)
  | fmuladd (res : VId) (a b c : VId) (ty : Ty)
  /-- `cir.shift(left, %a : ty, %amt : aty) -> ty` -/
  | shift (res : VId) (left : Bool) (a amt : VId) (ty amtTy : Ty)
  /-- `cir.inc nsw %a : ty`, `cir.dec`, `cir.minus`, `cir.not` -/
  | unop (res : VId) (k : UnOp) (nsw : Bool) (a : VId) (ty : Ty)
  | fneg (res : VId) (a : VId) (ty : Ty)
  /-- `cir.ceil %a : ty`, `cir.floor`, `cir.round`, `cir.trunc`, `cir.rint`, `cir.nearbyint`,
  `cir.fabs`, `cir.sqrt`. -/
  | fmath (res : VId) (fn : String) (a : VId) (ty : Ty)
  /-- `cir.is_fp_class %a, fcNan : (ty) -> !cir.bool` (`|`-separated classes);
  `cir.signbit %a : ty -> !cir.bool` is the pseudo-class `signbit`. -/
  | isFpClass (res : VId) (a : VId) (cls : String) (ty : Ty)
  /-- `cir.clz %a poison_zero : ty` (`leading`) and `cir.ctz`: the number of
  leading / trailing zero bits; with `poison_zero` the result for a zero
  argument is indeterminate (a use of it is undefined). -/
  | bitCount (res : VId) (leading poisonZero : Bool) (a : VId) (ty : Ty)
  /-- `cir.is_constant %a : ty -> !cir.bool` (`__builtin_constant_p`). -/
  | isConstant (res : VId) (a : VId)
  /-- `cir.popcount %a : ty`, `cir.parity`, `cir.ffs`, `cir.clrsb`, `cir.byte_swap`,
  `cir.bitreverse` (`fn` is the name after `cir.`): a bit operation on an integer; the result has
  the operand's type. -/
  | bitOp (res : VId) (fn : String) (a : VId) (ty : Ty)
  /-- `cir.rotate left %a, %n : ty` (`left`), `cir.rotate right`: `a` rotated by `n` modulo its
  width (`__builtin_rotateleft32`, …). -/
  | rotate (res : VId) (left : Bool) (a n : VId) (ty : Ty)
  /-- `cir.copysign %a, %b : ty`: the magnitude of `a` with the sign of `b`. -/
  | copysign (res : VId) (a b : VId) (ty : Ty)
  /-- `cir.fmaxnum %a, %b : ty` (`isMax`), `cir.fminnum`: the larger (smaller) operand, the other
  one when one is a NaN (`fmax`, `fmin`). -/
  | fminmax (res : VId) (isMax : Bool) (a b : VId) (ty : Ty)
  /-- `cir.prefetch read locality(3) %p : ty` (`__builtin_prefetch`): a hint without effect. -/
  | prefetch (p : VId)
  /-- `%r = cir.alloca "name" ... size(%n) : !cir.ptr<ty>`: a variable-length array of `n` elements
  of type `ty`; the result points to its first element. -/
  | allocaN (res : VId) (ty : Ty) (name : String) (count : VId)
  /-- `%p = cir.stacksave : !cir.ptr<!u8i>`: a token for the current top of the stack. -/
  | stackSave (res : VId)
  /-- `cir.stackrestore %p : !cir.ptr<!u8i>`: the stack blocks allocated since the `cir.stacksave`
  that gave `p` end (the variable-length arrays of one loop iteration). -/
  | stackRestore (p : VId)
  /-- `cir.va_copy %src to %dst`: `dst` designates the variadic arguments that `src` has not read
  yet. -/
  | vaCopy (src dst : VId)
  /-- `cir.va_start %ap : !cir.ptr<!rec___va_list_tag>`: `ap` designates the
  variadic arguments of the current call. -/
  | vaStart (ap : VId)
  /-- `cir.va_end %ap` -/
  | vaEnd (ap : VId)
  /-- `%v = cir.va_arg %ap : (!cir.ptr<…>) -> ty`: the next variadic argument. -/
  | vaArg (res : VId) (ap : VId) (ty : Ty)
  /-- `cir.va_arg` on a `va_list` object designated through a pointer to it (`va_arg(*pap, T)`,
  `ap` an `array_to_ptrdecay` of the object, as the parser sees it), not on a `va_list`
  parameter: as the owner's, the list stays the owner's to continue (C11 7.16p3, footnote 253). -/
  | vaArgP (res : VId) (ap : VId) (ty : Ty)
  /-- `%p = va_box %a : ty`, with no CIR text: the frontend puts it before a call to a variadic
  function with a body, for each argument after the parameters (`CIR.Frontend.boxVarargs`). A
  stack block of type `!cir.func<(ty)>`, which no object has, holds the value of `a`; the call
  passes `p` instead, so that `cir.va_arg` knows the type the argument was passed with. -/
  | vaBox (res : VId) (a : VId) (ty : Ty)
  /-- No CIR text: the parser puts it before each `cir.return` of a function that calls
  `va_start` or `va_copy`; undefined when one of the function's own `va_list` objects is still
  initialized, without its `va_end` (C11 7.16.1.3p2). -/
  | vaEndCheck
  /-- No CIR text: the parser puts it where the block of the `va_list` objects `aps` ends (at its
  end, and before a `break`, `continue` or `goto` that leaves it); undefined when one of them is
  still initialized, without its `va_end` (C11 7.16.1p1, 7.16.1.3p2). -/
  | vaEndCheckOf (aps : List VId)
  /-- No CIR text: undefined when executed (`msg`). The frontend puts it before a call it finds
  undefined, such as a `printf` whose format needs another type than an argument has. -/
  | fail (msg : String)
  /-- No CIR text: undefined (`msg`) unless the value of `a` fits `ty` (an argument of the other
  signedness than its `printf` conversion needs, which is read as that type only when its value
  fits both, as `va_arg` would, C11 7.16.1.1p2). -/
  | fitsCheck (a : VId) (ty : Ty) (msg : String)
  /-- `%r, %o = cir.mul.overflow %a, %b : src -> dst` (also `add`, `sub`):
  the result wrapped to `dst` and whether it overflowed. -/
  | arithOverflow (res ovf : VId) (k : BinOp) (a b : VId) (src dst : Ty)
  /-- `cir.abs %a min_is_poison : ty`: absolute value; the minimum value is
  undefined with `min_is_poison`. -/
  | iabs (res : VId) (minPoison : Bool) (a : VId) (ty : Ty)
  /-- `cir.atomic.fetch add <order> %p, %v : (!cir.ptr<ty>, ty) -> ty`: a
  read-modify-write (run sequentially: threads are not modelled); the result
  is the new value, or the old one with `fetch_first`. A `volatile` access is
  an ordinary one (nothing else observes memory). -/
  | atomicFetch (res : VId) (k : String) (fetchFirst : Bool) (p v : VId) (ty : Ty)
  /-- `cir.atomic.xchg <order> %p, %v : (!cir.ptr<ty>, ty) -> ty`: stores `v`;
  the result is the old value (run sequentially, as `atomicFetch`). -/
  | atomicXchg (res : VId) (p v : VId) (ty : Ty)
  /-- `%old, %ok = cir.atomic.cmpxchg [weak] success(<order>) failure(<order>)
  %p, %expected, %desired : (!cir.ptr<ty>, ty, ty) -> (ty, !cir.bool)`: if the
  object holds `expected`, stores `desired` and `ok` is true, else `ok` is
  false; `old` is the value read (the caller writes it back to its expected
  object when `ok` is false). Weak and strong are the same with one thread.
  `succ` and `fail` are the memory orders (`relaxed`, `consume`, `acquire`,
  `release`, `acq_rel`, `seq_cst`), checked against C11 7.17.7.4p2. -/
  | atomicCmpXchg (old ok : VId) (p expected desired : VId) (ty : Ty) (succ fail : String)
  /-- `cir.get_bitfield (#bfi, %p : !cir.ptr<storage>) -> ty`: the bit-field of
  `size` bits at bit `offset` of the integer storage unit `p` points to. -/
  | getBitfield (res : VId) (p : VId) (storage : Ty) (size offset : Nat) (signed : Bool) (ty : Ty)
  /-- `cir.set_bitfield (#bfi, %p, %v : ty) -> ty`: write the bit-field; the
  result is its new value. -/
  | setBitfield (res : VId) (p v : VId) (storage : Ty) (size offset : Nat) (signed : Bool) (ty : Ty)
  /-- `cir.cmp lt %a, %b : ty` -/
  | cmp (res : VId) (k : CmpKind) (a b : VId) (ty : Ty)
  /-- `cir.cast integral %a : src -> dst` -/
  | cast (res : VId) (k : CastKind) (a : VId) (src dst : Ty)
  /-- `cir.select if %c then %a else %b` -/
  | select (res : VId) (c a b : VId) (ty : Ty)
  -- complex numbers: `!cir.complex<T>` is the type `T[2]`, real part first (C11 6.2.5p13: the
  -- representation and alignment of an array of two elements of its real type), a complex value
  -- `.arr [re, im]`; `cir.complex.real_ptr` / `imag_ptr` are `getMember` 0 / 1 of it
  /-- `%r = cir.complex.create %re, %im : T -> !cir.complex<T>`; `ty` is `T`. -/
  | complexCreate (res : VId) (re im : VId) (ty : Ty)
  /-- `%r = cir.complex.real %c : !cir.complex<T> -> T`, or `cir.complex.imag` (`imag`); also of a
  real operand (`__real__ x`: `x`; `__imag__ x`: 0). -/
  | complexPart (res : VId) (imag : Bool) (c : VId) (ty : Ty)
  /-- `%r = cir.complex.add %a, %b : !cir.complex<T>`, `cir.complex.sub` (`sub`), and
  `cir.complex.fadd` / `fsub` of complex floating values: part by part, integer parts wrapping
  (Clang's complex integer arithmetic carries no overflow flags). `ty` is `T`. -/
  | complexArith (res : VId) (sub : Bool) (a b : VId) (ty : Ty)
  /-- `%r = cir.cmp eq %a, %b : !cir.complex<T>`, or `cir.cmp ne` (`ne`): two complex values are
  equal when their real parts and their imaginary parts are (C11 6.5.9p4). `ty` is `T`. -/
  | complexEq (res : VId) (ne : Bool) (a b : VId) (ty : Ty)
  -- vectors: `!cir.vector<N x T>` is the type `T[N]` and a vector value `.arr xs`; the integer,
  -- floating, unary, shift, `cir.fmuladd` and cast operations of a vector type act element by
  -- element (integer elements wrap: vector arithmetic carries no overflow flags)
  /-- `%r = cir.vec.create(%a, %b, ... : T, T, ...) : !cir.vector<N x T>`; `ty` is `T`. -/
  | vecCreate (res : VId) (elems : List VId) (ty : Ty)
  /-- `%r = cir.vec.splat %x : T, !cir.vector<N x T>`: `N` copies of `x`. -/
  | vecSplat (res : VId) (x : VId) (n : Nat) (ty : Ty)
  /-- `%r = cir.vec.extract %v[%i : I] : !cir.vector<N x T>`: element `i`, undefined outside
  `0 ≤ i < N`. -/
  | vecExtract (res : VId) (v i : VId) (ty : Ty)
  /-- `%r = cir.vec.insert %x, %v[%i : I] : !cir.vector<N x T>`: `v` with element `i` replaced by
  `x`, undefined outside `0 ≤ i < N`. -/
  | vecInsert (res : VId) (v x i : VId) (ty : Ty)
  /-- `%r = cir.vec.cmp(lt, %a, %b) : !cir.vector<N x T>, !cir.vector<N x R>`: element by element,
  `-1` (all bits set) where the comparison holds and `0` where it does not, in `R` (`resTy`). -/
  | vecCmp (res : VId) (k : CmpKind) (a b : VId) (ty resTy : Ty)
  /-- `%r = cir.vec.shuffle(%a, %b : V) [#cir.int<i> : !s64i, ...] : W`: element `i` of the
  concatenation of `a` and `b` for each index, an indeterminate element for `-1`. -/
  | vecShuffle (res : VId) (a b : VId) (idx : List Int)
  /-- `%r = cir.vec.ternary(%c, %a, %b) : C, V`: element by element, `a`'s where `c`'s is nonzero,
  else `b`'s (OpenCL's and C++'s `?:` of vectors). -/
  | vecTernary (res : VId) (c a b : VId)
  /-- `%r = cir.call_llvm_intrinsic "x86.…" %a, … : (A, …) -> R`: one of the x86 SIMD intrinsics of
  `x86Intrinsics`, a function of its operands (`Std.x86Intrinsic`); `ty` is `R`. -/
  | x86Intrinsic (res : VId) (name : String) (args : List VId) (ty : Ty)
  -- calls
  /-- `cir.call @f(%a, %b) : (A, B) -> R`. `retTy = void` when there is no
  result. `nothrow` calls cannot raise exceptions. -/
  | call (loc : Loc) (res : Option VId) (callee : Callee) (args : List VId)
      (argTys : List Ty) (retTy : Ty) (nothrow : Bool)
  -- structured control flow
  /-- `cir.scope { ... }` (optionally yielding a value). -/
  | scope (res : Option VId) (body : Region)
  /-- `cir.cleanup.scope { body } cleanup <kind> { cleanup }` -/
  | cleanupScope (kind : CleanupKind) (body cleanup : Region)
  /-- `cir.if %c { thn } else { els }` (missing else = empty region). -/
  | ifOp (cond : VId) (thn els : Region)
  /-- `%r = cir.ternary(%c, true { ... }, false { ... })` -/
  | ternary (res : Option VId) (cond : VId) (t f : Region)
  /-- `cir.for : cond {...} body {...} step {...} [cleanup <kind> {...}]` -/
  | forOp (loc : Loc) (cond body step : Region) (cleanup : Option (CleanupKind × Region))
  /-- `cir.while {...} do {...} [cleanup <kind> {...}]` -/
  | whileOp (loc : Loc) (cond body : Region) (cleanup : Option (CleanupKind × Region))
  /-- `cir.do {...} while {...}` -/
  | doWhileOp (loc : Loc) (body cond : Region)
  /-- `cir.switch(%c : ty) { cir.case(...) {...} ... }` -/
  | switch (cond : VId) (ty : Ty) (body : Region)
  /-- `cir.case(equal, [#cir.int<1> : !s32i]) {...}`; `range` has two values. -/
  | case (kind : CaseKind) (vals : List Int) (body : Region)
  /-- `cir.try { body } catch [...] (%tok) {...} ... unwind (%tok) {...}` -/
  | tryOp (body : Region) (handlers : List (CatchKind × Region)) (unwind : Option Region)
  /-- `%r = setjmp(%env)` with the rest of its block (`rest`), as the parser arranges a call of
  `_setjmp` / `setjmp` / `__sigsetjmp` (`nestSetjmps`): `rest` runs with `r` = 0, and again with
  `r` = `v` after a `longjmp` to this invocation (`Exit.longjmp`). Volatile objects (C11
  7.13.2.1p3), which CIR does not type (only its accesses are `volatile`): `svol`, for an
  object of the function (its `cir.alloca`) and a path of members, whether its own accesses
  there are all `volatile` (`true`), or some are not (`false`: not volatile-qualified, or the
  program is undefined, C11 6.7.3p6); `vol`: the pointers of `volatile` accesses that are not
  through the function's objects themselves. `ok`: the call is in one of the contexts of C11
  7.13.1.1p4. -/
  | setjmp (res : VId) (env : VId) (vol : List VId) (svol : List (VId × List Nat × Bool)) (ok : Bool)
      (rest : Region)
  /-- No CIR text: in a module with a `setjmp`, the frontend puts it after each operation of each
  function that stores into an object through `p` (`store`) or that is a `volatile` access through
  a pointer (`vol`, `Frontend.sjNotes`): the record, in each live `setjmp` invocation that holds
  the object, of the objects changed since and of those accessed `volatile` (C11 7.13.2.1p3). -/
  | sjNote (p : VId) (store vol : Bool)
  /-- The rest of a `setjmp`'s block while that invocation (token block `tok`) returns `v`
  (made by `evalOp`, never parsed). -/
  | setjmpRun (res : VId) (tok : Nat) (v : Int) (rest : Region)
  -- terminators
  | yield (vals : List VId)
  | condition (c : VId)
  | brk
  | cont
  /-- `cir.libc.memcpy` / `memmove` / `memset` (arguments: destination,
  source or byte value, size), run by the C library models; `memcpy.std`,
  `memmove.std`, `memset.std` in the C++ library's own code
  (`Frontend.tagStdMemCalls`). -/
  | libc (fn : String) (args : List VId)
  /-- `cir.goto "l"`: jump to the block labelled `l` of an enclosing region. -/
  | goto (lbl : String)
  /-- `cir.indirect_goto %p : !cir.ptr<!void>` in function `fn` (GNU `goto *p`):
  `p` must be the address of a label of `fn`; then as `goto`. -/
  | indirectGoto (target : VId) (fn : String)
  /-- `cir.label "l"`: marks the block it starts (a no-op). -/
  | label (lbl : String)
  | ret (v : Option VId)
  | br (dest : BlockId) (args : List VId)
  | brcond (c : VId) (t : BlockId) (targs : List VId) (f : BlockId) (fargs : List VId)
  | trap
  | unreachable
  /-- `cir.throw %obj : !cir.ptr<T>, @typeinfo`; `obj = none` is a rethrow. -/
  | throw (obj : Option VId) (objTy : Ty) (typeinfo : Option String)
  | resume (tok : VId)
  -- exception handling support
  /-- `%p = cir.alloc.exception N -> !cir.ptr<T>` (T = `ty`) -/
  | allocException (res : VId) (size : Nat) (ty : Ty)
  /-- `%tok, %exn = cir.begin_catch %eh` -/
  | beginCatch (tokRes exnRes : VId) (eh : VId)
  | endCatch (tok : VId)
  /-- `cir.init_catch_param <kind> %exn to %dst : !cir.ptr<!void>, !cir.ptr<T>` -/
  | initCatchParam (kind : String) (exn dst : VId) (dstTy : Ty)
  | ehTerminate (eh : VId)
  /-- `cir.assume %c ...` -/
  | assume (c : VId)
  /-- `cir.asm` with an empty template, no operands and only clobbers
  (`asm volatile("" ::: "memory")`): a compiler barrier, a no-op in the
  sequential semantics. -/
  | asmBarrier
  /-- `cir.asm` with an empty template and no memory operands, whose register
  outputs are each tied to an input (`asm("" : "=r"(y) : "0"(x))`,
  `asm("" : "+r"(x))`), or without outputs (`asm volatile("" : : "r"(p))`):
  the inputs `ins` are read, and output `k` is the value of the input
  `ins[ties[k]]` it is tied to (an empty template leaves their shared register
  unchanged). `res` holds the output, or the record of all outputs when there
  are several. Every other `cir.asm` is `unknown`. -/
  | asmTied (res : Option VId) (ins : List VId) (ties : List Nat)
  /-- An operation outside the modelled subset (`name` is e.g. `cir.asm`).
  Executing it is undefined in the semantics, so code reaching it cannot be
  verified, but the rest of the function still can. -/
  | unknown (name : String) (results : List VId)
/-- A block: entry arguments and operations (the last one is a terminator). -/
inductive Block where
  | mk (args : List VId) (ops : List Op)
/-- A region: a list of blocks, entry block first. -/
inductive Region where
  | mk (blocks : List Block)
end

instance : Inhabited Region := ⟨.mk []⟩
instance : Inhabited Block := ⟨.mk [] []⟩
instance : Inhabited Op := ⟨.unreachable⟩

/-- The x86 SIMD intrinsics that are modelled (`Op.x86Intrinsic`, `Std.x86Intrinsic`); the parser
leaves a `cir.call_llvm_intrinsic` of any other name `Op.unknown`. -/
def x86Intrinsics : List String :=
  ["x86.sse2.packssdw.128", "x86.sse2.pslli.w", "x86.sse2.psrli.w", "x86.sse.max.ps", "x86.sse.movmsk.ps"]

/-- A one-block region without arguments. -/
abbrev Region.ofOps (ops : List Op) : Region := .mk [.mk [] ops]

/-- C++ special member information (`func_info<#cir.cxx_ctor<...>>`). -/
inductive SpecialMember where
  | none | ctor | dtor | copyAssign | moveAssign
  deriving Repr, DecidableEq, Inhabited

end CIR
