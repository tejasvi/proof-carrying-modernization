import CIR.Std.Models
import CIR.Std.X86

/-!
  The definitional interpreter: the semantics of CIR.

  It executes the structured operations directly:

  * a region is executed from its entry block; `cir.br` moves between blocks
    of the same region; leaving the region (by any exit) ends the lifetime of
    every stack block allocated while it ran, and restores the SSA scope;
  * `cir.cleanup.scope` runs its cleanup region on the exits selected by its
    kind (`normal`: yield/break/continue/return, `eh`: exceptions, `all`),
    then continues the exit — this is C++ RAII;
  * `cir.for` / `cir.while` / `cir.do` iterate their regions, running the
    optional per-iteration cleanup region on every iteration exit;
  * calls run the callee body in a fresh SSA environment, or the native
    library model of the callee (`FuncDecl.model`);
  * `exit` ends the program (`Exit.halt`): it leaves every region, loop and
    call at once, running no cleanup and caught by no handler.

  The functions are defined by `partial_fixpoint`: their unfolding equations
  hold as theorems and a non-terminating execution has the value `Res.div`.
  There is no fuel; the program logic proves total correctness (the result is
  `Res.ok`).
-/

namespace CIR

/-- What a single operation did. -/
inductive Step where
  | next
  | exit (e : Exit)
  | jump (dest : BlockId) (args : List Val)
  deriving Inhabited

/-! ### Helpers outside the recursion -/

def Ty.pointee : Ty → Ty
  | .ptr t => t
  | t => t

def recordName? : Ty → Option String
  | .ptr (.record n) => some n
  | .record n => some n
  | _ => none

/-- Member `i` of a record of type `n` placed by bytes over the object at `path`
in an object of type `bty` and value `bv`, a scalar or an array (C11 6.5p7's
aggregate clause): the canonical path (`Ctx.canonByte`) of the byte at the
member's offset after the object's byte position (`Ctx.absPos?`). -/
def Ctx.placeMember (ctx : Ctx) (bty : Ty) (bv : Val) (path : List PathElem) (n : String) (i : Nat) :
    List PathElem :=
  match ctx.absPos? bty path, ctx.memberOffsets n with
  | some q, some offs =>
    match offs[i]? with
    | some o => ctx.canonByte 32 bty bv [] (q + o)
    | none => path ++ [.idx i]
  | _, _ => path ++ [.idx i]

/-- `Ctx.memberPath` when the object of type `t` at `path` is no record of type
`n`: member `i` of the subobject of that type it starts, or that starts it
(`Ctx.convertPath`: for an array of such records, element 0); else, over a
scalar or an array, the member placed by bytes (`Ctx.placeMember`); else (a
record of another type) its member `i`. -/
def Ctx.memberSlow (ctx : Ctx) (bty : Ty) (bv : Val) (path : List PathElem) (t : Ty) (n : String) (i : Nat) :
    List PathElem :=
  let p := ctx.convertPath bty path n
  if p ≠ path then p ++ [.idx i]
  else if t.isScalar || (match t with | .array _ _ => true | _ => false) then ctx.placeMember bty bv path n i
  else path ++ [.idx i]

/-- `Ctx.memberPath` takes member `i` of the object at `path`: a record of a
related type (or no record type `rt`, an invalid path). -/
def Ctx.memberRelated (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (rt : Ty) : Bool :=
  match rt, m.blocks b with
  | .record n, some blk =>
    match ctx.typeAt blk.ty path with
    | some (.record n') => isClassOrBase n' n || isClassOrBase n n'
    | some _ => false
    | none => true
  | _, _ => true

/-- `Ctx.memberPath` at an object that is no record of a related type:
`Ctx.memberSlow` at its type. -/
def Ctx.memberOther (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (rt : Ty) (i : Nat) :
    List PathElem :=
  match rt, m.blocks b with
  | .record n, some blk =>
    match ctx.typeAt blk.ty path with
    | some t => ctx.memberSlow blk.ty blk.val path t n i
    | none => path ++ [.idx i]
  | _, _ => path ++ [.idx i]

/-- The path of member `i` of the record of type `rt` that a member access
through a pointer to the object at `path` in block `b` reaches: member `i` of
that object when it is a record of that type (or a related one), else
`Ctx.memberSlow`. -/
def Ctx.memberPath (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (rt : Ty) (i : Nat) :
    List PathElem :=
  if ctx.memberRelated m b path rt then path ++ [.idx i] else ctx.memberOther m b path rt i

theorem Ctx.memberPath_of_related {ctx : Ctx} {m : Mem} {b : Nat} {path : List PathElem} {rt : Ty}
    {i : Nat} (h : ctx.memberRelated m b path rt = true) : ctx.memberPath m b path rt i = path ++ [.idx i] := by
  simp only [Ctx.memberPath, h, if_true]

/-- Path (member indices) from record `d` to its base-class subobject of class
`b` at byte offset `off`. A base subobject is a member of type `b` or
`b.base`, possibly nested inside another base subobject: `cir.base_class_addr`
may convert directly to an indirect base. An empty base class at offset 0
has no member; it shares the address of the object containing it (empty-base
optimisation), so its path is empty. -/
def Ctx.basePath (ctx : Ctx) : Nat → String → String → Nat → Option (List Nat)
  | 0, _, _, _ => none
  | fuel + 1, d, b, off =>
    match ctx.record? d, ctx.memberOffsets d with
    | some r, some offs =>
      let ms := (r.members.zip offs).zipIdx
      let direct := ms.find? fun ((mt, o), _) =>
        o == off && (match mt.2 with | .record n => isClassOrBase n b | _ => false)
      match direct with
      | some (_, i) => some [i]
      | none =>
        -- an indirect base: inside the record member that contains `off`
        let inner := ms.reverse.find? fun ((mt, o), _) =>
          o ≤ off && mt.1 != .pad && (recordName? mt.2).isSome
        let viaInner := inner.bind fun ((mt, o), i) =>
          (recordName? mt.2).bind fun n => (ctx.basePath fuel n b (off - o)).map (i :: ·)
        match viaInner with
        | some p => some p
        | none => if off == 0 && ctx.isEmptyRecord b then some [] else none
    | _, _ => none

/-- Slot `k` of array `i` of the vtable global `vt` (a function address or
null), from the module's initializer. -/
def Ctx.vtableSlot? (ctx : Ctx) (vt : String) (i k : Nat) : Option Val :=
  match ctx.mod.findGlobal? vt with
  | some g =>
    match g.init with
    | some (.record cs) =>
      match cs[i]? with
      | some (.array es) =>
        match es[k]? with
        | some c => ctx.constVal 32 (.ptr (.int false 8)) c
        | none => none
      | _ => none
    | _ => none
  | none => none

/-- A vtable slot read at type `ty`: the pointer it holds (a virtual function's
address, the class's `typeinfo`, null); read at an integer type, the offset it
holds as `#cir.ptr<n : i64>` (a virtual base offset, the offset to the top;
`#cir.ptr<null>` is 0), undefined for a slot that holds an address. -/
def vtableRead : Ty → Val → Res Val
  | .int _ _, .ptr .null => .ok (.int 0)
  | .int s w, .ptr (.addr a) => if inRange s w a then .ok (.int a) else .ub "vtable offset out of range"
  | .int _ _, _ => .ub "vtable slot read as an integer"
  | .ptr _, v => .ok v
  | _, v => .ok v

/-- Load through a pointer: from memory (record members checked,
`Ctx.typedLoad`), or, for a vtable slot, from the module. (One equation per
pointer form, so that symbolic execution of a load never looks at the other
cases.) -/
def loadPtr (ctx : Ctx) (m : Mem) (ty : Ty) : Ptr → Res Val
  | .vtable vt i k => Res.ofOption "read outside a vtable" (ctx.vtableSlot? vt i k) >>= vtableRead ty
  | .null => loadTy m ty .null
  | .loc b path => ctx.typedLoad m ty (.loc b path)
  | .fn s => loadTy m ty (.fn s)
  | .addr _ => .ub "access through an integer-valued pointer"
  | .label _ _ => .ub "access through a label address"

theorem loadPtr_loc (ctx : Ctx) (m : Mem) (ty : Ty) (b : Nat) (path : List PathElem) :
    loadPtr ctx m ty (.loc b path) = ctx.typedLoad m ty (.loc b path) := rfl
theorem loadPtr_null (ctx : Ctx) (m : Mem) (ty : Ty) : loadPtr ctx m ty .null = loadTy m ty .null := rfl
theorem loadPtr_fn (ctx : Ctx) (m : Mem) (ty : Ty) (s : String) :
    loadPtr ctx m ty (.fn s) = loadTy m ty (.fn s) := rfl
theorem loadPtr_vtable (ctx : Ctx) (m : Mem) (ty : Ty) (vt : String) (i k : Nat) :
    loadPtr ctx m ty (.vtable vt i k) =
      (Res.ofOption "read outside a vtable" (ctx.vtableSlot? vt i k) >>= vtableRead ty) := rfl

/-- Path (member indices) from an object of class `n` to its vptr: the first
member, inside the primary base class if `n` has one. -/
def Ctx.vptrPath (ctx : Ctx) : Nat → String → Option (List Nat)
  | 0, _ => none
  | fuel + 1, n =>
    match ctx.record? n with
    | some r =>
      match r.members.head? with
      | some (_, .vptr) => some [0]
      | some (_, .record n') => (ctx.vptrPath fuel n').map (0 :: ·)
      | _ => none
    | none => none

/-- The class whose vptr `cir.vtable.get_vptr` designates through a pointer
of type `ty`: that of the object at the pointer's location when the block's
type gives it (the constructors and destructors of a class with virtual bases
set a virtual base's vptr through a pointer of the class's type, moved to the
base by the offset that the vtable holds; a virtual thunk reads it through a
`char *`), else `ty`'s (a container element). -/
def Ctx.vptrClass? (ctx : Ctx) (m : Mem) (p : Ptr) (ty : Ty) : Option String :=
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match ctx.typeAt blk.ty path with
      | some (.record n) => some n
      | _ => recordName? ty
    | none => recordName? ty
  | _ => recordName? ty

/-- In C, a pointer converted by a `bitcast` must be correctly aligned for the
type it then points to (C11 6.3.2.3p7, `Ctx.castAligned`). In C++ the value of
such a pointer is unspecified ([expr.static.cast]p13), not undefined: it stays
the pointer it was. (The language is looked up only for a pointer that is not
aligned: symbolic execution does not evaluate the module.) -/
def Ctx.castCheck (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (dst : Ty) : Res Unit :=
  match k, x, dst with
  | .bitcast, .ptr (.loc b path), .ptr t =>
    if ctx.castAligned m b path t then .ok ()
    else if ctx.mod.cxx then .ok () else .ub "misaligned pointer conversion"
  | _, _, _ => .ok ()

/-- The pointer a `bitcast` converts `x` to: a pointer converted to a pointer to a record
designates the object of that type that it starts, or that starts it (`Ctx.convertPath`);
element 0 of an array of records converted to a pointer to the array's type designates the
array (`new T[n]` of a class with a constructor converts the pointer to the first element, which
the first typed view of the storage gives, to `T(*)[n]`, and decays that again). Arrays of
scalars, which vectors are, keep the element pointer, so that a vector access over one stays
the access element by element (`Reach.spread`). The destination type decides before the pointer
is looked at, so that symbolic execution reduces other casts without a case split. -/
def Ctx.convertPtr (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (dst : Ty) : Val :=
  match k, dst, x with
  | .bitcast, .ptr (.record n), .ptr (.loc b path) =>
    match m.blocks b with
    | some blk => .ptr (.loc b (ctx.convertPath blk.ty path n))
    | none => x
  | .bitcast, .ptr t@(.array (.record _) _), .ptr (.loc b path) =>
    match splitLast path, m.blocks b with
    | some (pre, .idx 0), some blk => if ctx.typeAt blk.ty pre == some t then .ptr (.loc b pre) else x
    | _, _ => x
  | _, _, _ => x

/-- A pointer whose value is not indeterminate: not into a block whose lifetime has ended
(C11 6.2.4p2), so that comparing it or converting it to an integer is defined. -/
def ptrValid (m : Mem) : Ptr → Bool
  | .loc b _ => (m.live? b).isSome
  | _ => true

def evalCast (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (dst : Ty) : Res Val :=
  match k, x, dst with
  | .integral, .int v, .int s w => .ok (.int (wrap s w v))
  -- an indeterminate value (the poison result of `cir.clz … poison_zero` of 0) stays one
  | .integral, .undef, .int _ _ => .ok .undef
  | .intToBool, .int v, _ => .ok (.bool (v != 0))
  | .boolToInt, .bool b, .int _ _ => .ok (.int (if b then 1 else 0))
  | .arrayToPtrDecay, .ptr (.loc b path), _ =>
    match m.read? (.loc b path) with
    | some (.arr _) => .ok (.ptr (.loc b (path ++ [.idx 0])))
    | _ => .ub "array-to-pointer decay of a non-array"
  | .bitcast, .ptr p, .ptr _ => .ok (.ptr p)
  | .addressSpace, v, _ => .ok v
  | .ptrToBool, .ptr p, _ => .ok (.bool (p != .null))
  -- the conversions between integers and pointers are implementation-defined (C11
  -- 6.3.2.3p5, p6): flat addresses (`Ctx.addrOf?`, `Ctx.ptrOfAddr`); a pointer to an object
  -- whose lifetime has ended converts to no integer (6.2.4p2), as it compares with nothing
  | .intToPtr, .int c, _ => .ok (.ptr (ctx.ptrOfAddr m c))
  | .ptrToInt, .ptr p, .int s w =>
    if !ptrValid m p then .ub "conversion of an invalid pointer" else
    match ctx.addrOf? m p with
    | some a => .ok (.int (ctx.intOfAddr s w a))
    | none => .ub "unsupported cast"
  | .floating, .float f, .float .single => .ok (.float (Std.roundSingle f))
  | .floating, .float f, .float _ => .ok (.float f)
  | .intToFloat, .int v, .float fk =>
    -- rounded once, to the target format
    .ok (.float (if fk = .single then Std.intToSingle v else Float.ofInt v))
  | .floatToBool, .float f, _ => .ok (.bool (Std.fkey (Std.decodeF f) != some 0))
  | .floatToInt, .float f, .int s w =>
    -- truncation toward zero; undefined unless the result is representable
    match Std.decodeF f with
    | .finite neg m e =>
      let t := Std.truncVal neg m e
      if inRange s w t then .ok (.int t) else .ub "float-to-integer conversion out of range"
    | _ => .ub "float-to-integer conversion of an infinity or NaN"
  | .boolToFloat, .bool b, .float _ => .ok (.float (if b then 1 else 0))
  | _, _, _ => .ub "unsupported cast"

/-- The elements of two vectors pairwise (`f` on each pair); the lengths must agree. -/
def vecZip (a b : Val) (f : Val → Val → Res Val) : Res (List Val) :=
  match a, b with
  | .arr xs, .arr ys =>
    if xs.length = ys.length then (xs.zip ys).mapM fun (x, y) => f x y
    else .ub "vector operands of different lengths"
  | _, _ => .ub "expected vectors"

/-- A shift of a vector element: as `evalShift`, except that a left shift wraps, as Clang's vector
shifts carry no overflow flags, like its vector arithmetic (`(v4si){-1} << 1` is `-2`); a count
outside `0 ≤ n < w` stays undefined. -/
def evalVecShift (left s : Bool) (w : Nat) (x n : Int) : Res Int :=
  if left then
    if 0 ≤ n ∧ n < w then .ok (wrap s w (x * 2 ^ n.toNat)) else .ub "shift amount out of range"
  else evalShift false s w x n

/-- The number of bytes of a value of scalar type `t` that `byteOf` / `setByte` give. -/
def scalarWidth : Ty → Option Nat
  | .int _ w => if w % 8 = 0 ∧ 0 < w then some (w / 8) else none
  | .bool => some 1
  | .float .single => some 4
  | .float .double => some 8
  | _ => none

/-- The `n` values of type `de` that the bytes of the values `xs` of type `se` make, little-endian
(`byteOf`, `setByte`): integers exactly, floats unless their bit pattern is a NaN's; undefined unless
the bytes are exactly `n` values of `de`. A value whose bytes are not all known (from an
indeterminate value or a NaN, whose bytes `Float`'s single NaN does not keep) or whose bit pattern
is a NaN's (or not a `bool`) is indeterminate (`.undef`): only a use of that element is undefined. -/
def reinterpretVals (xs : List Val) (se de : Ty) (n : Nat) : Res (List Val) :=
  match scalarWidth se, scalarWidth de with
  | some w, some w' =>
    let bs : List (Option Nat) := xs.flatMap fun x => (List.range w).map (byteOf se x)
    let zero : Val := match de with
      | .bool => .bool false
      | .float _ => .float 0
      | _ => .int 0
    let elem (i : Nat) : Val :=
      match ((bs.drop (i * w')).take w').mapM id with
      | some cs => (((List.range w').zip cs).foldlM (fun v (j, c) => setByte de v j c) zero).getD .undef
      | none => .undef
    if bs.length = n * w' then .ok ((List.range n).map elem)
    else .ub "bitcast between different sizes"
  | _, _ => .ub "bitcast of an unsupported type"

/-- A cast of the vector `xs` of `se` elements to a vector of `n` elements of `de`: element by
element (`evalCast`); a `bitcast` reinterprets the elements' bytes (`reinterpretVals`). -/
def vecCast (ctx : Ctx) (m : Mem) (k : CastKind) (xs : List Val) (se de : Ty) (n : Nat) : Res Val :=
  match k with
  | .bitcast => Val.arr <$> reinterpretVals xs se de n
  | _ => Val.arr <$> xs.mapM fun x => evalCast ctx m k x de

/-- A cast of the vector `x` (elements `xs` of `se`) to the scalar type `de`: a `bitcast`
reinterprets the value's bytes (`reinterpretVals`), a conversion of values, not an access (GCC's
vector extension: "you can also cast vectors to and from other data types of the same size");
another kind is `evalCast`'s. -/
def vecToScalar (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (xs : List Val) (se de : Ty) : Res Val :=
  match k with
  | .bitcast => do
    match ← reinterpretVals xs se de 1 with
    | [y] => pure y
    | _ => .ub "bitcast between different sizes"
  | _ => evalCast ctx m k x de

/-- A cast of the scalar `x` of type `se` to a vector of `n` elements of `de`: a `bitcast`
reinterprets the value's bytes (`reinterpretVals`); another kind is `evalCast`'s. -/
def scalarToVec (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (se de : Ty) (n : Nat) : Res Val :=
  match k with
  | .bitcast => Val.arr <$> reinterpretVals [x] se de n
  | _ => evalCast ctx m k x (.array de n)

/-- `castVal` of a `T(*)[1]` of a record `T`: an `array_to_ptrdecay` of a pointer that designates
a lone `T` gives that pointer (the element of an array of one); otherwise `evalCast`. -/
def decayOne (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (dst : Ty) : Res Val :=
  match k, x with
  | .arrayToPtrDecay, .ptr (.loc b path) =>
    match m.read? (.loc b path) with
    | some (.arr _) => evalCast ctx m k x dst
    | some _ => .ok x
    | none => evalCast ctx m k x dst
  | _, _ => evalCast ctx m k x dst

/-- The value of a `cir.cast` of `x` from `src` to `dst`: between vector types (arrays) element by
element (`vecCast`), between a vector and a scalar `vecToScalar` / `scalarToVec`, otherwise
`evalCast`. (Out of `evalSimple`, whose automatic `WF_evalSimple` proof the vector cases would
make too slow; in the `cir_exec` simp set, so that scalar casts reach `evalCast`.) -/
def castVal (ctx : Ctx) (m : Mem) (k : CastKind) (x : Val) (src dst : Ty) : Res Val :=
  match x, src, dst with
  | .arr xs, .array se _, .array de n => vecCast ctx m k xs se de n
  | .arr xs, .array se _, de => vecToScalar ctx m k x xs se de
  | _, se, .array de n => scalarToVec ctx m k x se de n
  -- a `T(*)[1]` of a record `T` that designates a lone `T` (storage for one object, which its
  -- first typed view gives the type `T`, as for `new T[1]`): its decay is that object, the
  -- element of an array of one (C11 6.5.6p7); the source type decides before the value is
  -- looked at, so that symbolic execution reduces other casts without a case split
  | _, .ptr (.array (.record _) 1), _ => decayOne ctx m k x dst
  | _, _, _ => evalCast ctx m k x dst

def roundFloat (ty : Ty) (f : Float) : Float :=
  match ty with
  | .float .single => Std.roundSingle f
  | _ => f

/-- `ceil`, `floor`, `round` (half away from zero), `trunc`, `rint` and
`nearbyint` (to nearest, half to even: the default rounding mode, C11 7.12.9.3-4),
`fabs`, `sqrt` (exact, IEEE). -/
def evalFMath (fn : String) (x : Float) : Option Float :=
  match fn with
  | "ceil" => some (Std.roundIntF 1 x)
  | "floor" => some (Std.roundIntF 0 x)
  | "round" => some (Std.roundIntF 3 x)
  | "trunc" => some (Std.roundIntF 2 x)
  | "rint" | "nearbyint" => some (Std.roundIntF 4 x)
  | "fabs" => some x.abs
  | "sqrt" => some x.sqrt
  | _ => none

/-- `is_fp_class` for one class name (`fcNan`, `fcInf`, `fcFinite`, ...). -/
def fpClass (ty : Ty) (c : String) (x : Float) : Option Bool :=
  -- the smallest normal number of the type, as a key (`Std.fkey`, multiples of 2^-1074)
  let minNormal : Int := match ty with
    | .float .single => 2 ^ 948
    | _ => 2 ^ 52
  let fin (p : Bool → Int → Bool) : Bool := match Std.decodeF x, Std.fkey (Std.decodeF x) with
    | .finite neg _ _, some k => p neg k.natAbs
    | _, _ => false
  match c, Std.decodeF x with
  | "fcNan", v | "fcSNan", v | "fcQNan", v => some (v == .nan)
  | "fcInf", v => some (v == .inf true || v == .inf false)
  | "fcPosInf", v => some (v == .inf false)
  | "fcNegInf", v => some (v == .inf true)
  | "fcFinite", _ => some (fin fun _ _ => true)
  | "fcPosFinite", _ => some (fin fun neg _ => !neg)
  | "fcNegFinite", _ => some (fin fun neg _ => neg)
  | "fcZero", _ => some (fin fun _ k => k == 0)
  | "fcPosZero", _ => some (fin fun neg k => !neg && k == 0)
  | "fcNegZero", _ => some (fin fun neg k => neg && k == 0)
  | "fcNormal", _ => some (fin fun _ k => decide (minNormal ≤ k))
  | "fcPosNormal", _ => some (fin fun neg k => !neg && decide (minNormal ≤ k))
  | "fcNegNormal", _ => some (fin fun neg k => neg && decide (minNormal ≤ k))
  | "fcSubnormal", _ => some (fin fun _ k => k != 0 && decide (k < minNormal))
  | "fcPosSubnormal", _ => some (fin fun neg k => !neg && k != 0 && decide (k < minNormal))
  | "fcNegSubnormal", _ => some (fin fun neg k => neg && k != 0 && decide (k < minNormal))
  -- LLVM's unions: the negative / positive infinity, normal, subnormal and zero (no NaN)
  | "fcNegative", v => some (v == .inf true || fin fun neg _ => neg)
  | "fcPositive", v => some (v == .inf false || fin fun neg _ => !neg)
  -- `cir.signbit` (parsed as this pseudo-class): the sign bit, NaNs and zeros included
  | "signbit", _ => some (x.toBits >>> 63 == 1)
  | _, _ => none

/-- Number of trailing zero bits (of a positive number). -/
def ctzNat (u : Nat) : Nat :=
  if h : u = 0 then 0 else if u % 2 = 1 then 0 else 1 + ctzNat (u / 2)
decreasing_by omega

/-- `clz` (`leading`) / `ctz` on a `w`-bit integer; `none` (a poison value) for 0 with
`poisonZero`. -/
def evalBitCount (leading poisonZero : Bool) (w : Nat) (x : Int) : Option Int :=
  let u := (x % (2 : Int) ^ w).toNat
  if u = 0 then (if poisonZero then none else some w)
  else some (if leading then ((w - 1 - Nat.log2 u : Nat) : Int) else (ctzNat u : Int))

/-- The number of one bits among the low `w` bits of `u`. -/
def popNat : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, u => u % 2 + popNat w (u / 2)

/-- The low `k` bytes of `u` in reverse order, after the bytes already in `acc`. -/
def bswapNat : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, u, acc => bswapNat k (u / 256) (acc * 256 + u % 256)

/-- The low `w` bits of `u` in reverse order, after the bits already in `acc`. -/
def bitrevNat : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | w + 1, u, acc => bitrevNat w (u / 2) (acc * 2 + u % 2)

/-- `cir.popcount`, `cir.parity`, `cir.ffs`, `cir.clrsb`, `cir.byte_swap` and `cir.bitreverse` on
a `w`-bit integer (`__builtin_popcount`, `__builtin_parity`, `__builtin_ffs`, `__builtin_clrsb`,
`__builtin_bswap*`, `__builtin_bitreverse*`). -/
def evalBitOp (fn : String) (signed : Bool) (w : Nat) (x : Int) : Res Int :=
  let u := (x % (2 : Int) ^ w).toNat
  match fn with
  | "popcount" => pure (popNat w u)
  | "parity" => pure (popNat w u % 2)
  | "ffs" => pure (if u = 0 then 0 else ((ctzNat u + 1 : Nat) : Int))
  | "clrsb" =>
    -- the bits after the sign bit that equal it: the leading zeros of `u`, or of its complement
    -- when the sign bit is set, minus one
    let v := if decide (2 ^ (w - 1) ≤ u) then 2 ^ w - 1 - u else u
    pure (if v = 0 then ((w - 1 : Nat) : Int) else ((w - 2 - Nat.log2 v : Nat) : Int))
  | "byte_swap" =>
    if w % 8 = 0 then pure (wrap signed w (bswapNat (w / 8) u 0))
    else .ub "byte_swap of a type that is not a whole number of bytes"
  | "bitreverse" => pure (wrap signed w (bitrevNat w u 0))
  | _ => .ub s!"unsupported bit operation {fn}"

/-- The bit-field of `size` bits at `offset` of the storage value `raw`. -/
def bfExtract (raw : Int) (sw size offset : Nat) (signed : Bool) : Int :=
  let f := ((raw % (2 : Int) ^ sw).toNat >>> offset) % 2 ^ size
  if signed && decide (2 ^ (size - 1) ≤ f) then (f : Int) - 2 ^ size else f

/-- The storage value `raw` with its bit-field replaced by the low `size`
bits of `v` (as a natural number below `2^sw`). -/
def bfInsert (raw : Int) (sw size offset : Nat) (v : Int) : Nat :=
  let u := (raw % (2 : Int) ^ sw).toNat
  let mask := (2 ^ size - 1) <<< offset
  (u - (u &&& mask)) + ((v % (2 : Int) ^ size).toNat <<< offset)

/-- The value of a storage unit of array type (`!cir.array<!u8i x N>`, for
storage whose width is not that of an integer type) from its elements of `ew`
bits: element `k` holds bits `k*ew` to `(k+1)*ew - 1` (little-endian). `none`
if an element is indeterminate. -/
def bfJoin (ew : Nat) : List Val → Option Int
  | [] => some 0
  | .int x :: xs => (bfJoin ew xs).map fun r => x % 2 ^ ew + 2 ^ ew * r
  | _ :: _ => none

/-- `bfJoin` with the bits of indeterminate elements read as 0. -/
def bfJoin0 (ew : Nat) : List Val → Int
  | [] => 0
  | .int x :: xs => x % 2 ^ ew + 2 ^ ew * bfJoin0 ew xs
  | _ :: xs => 2 ^ ew * bfJoin0 ew xs

/-- The `n` elements of `ew` bits (of signedness `s`) of an array storage unit
holding `raw`. -/
def bfSplit (s : Bool) (ew : Nat) : Nat → Int → List Val
  | 0, _ => []
  | n + 1, raw => .int (wrap s ew raw) :: bfSplit s ew n (raw / 2 ^ ew)

/-- A bit-field's value as the operation's type: `!cir.bool` for a `bool`
bit-field, else the integer. -/
def bfVal (ty : Ty) (f : Int) : Val :=
  match ty with
  | .bool => .bool (f != 0)
  | _ => .int f

/-- Where the bit-field storage unit of type `st` that `p` points to is no
member of type `st` of a record: the pointer to a structure it was taken from
points to other objects (`Ctx.memberPath`), a scalar or an array over which
the unit was placed by its offset (`Ctx.placeMember`), or a member of another
type of a record of another type. Then its block, its byte position in the
complete object and its size in bytes. -/
def Ctx.bfPlaced? (ctx : Ctx) (m : Mem) (p : Ptr) (st : Ty) : Option (Nat × Nat × Nat) :=
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      let member : Bool := match splitLast path with
        | some (pre, .idx j) =>
          match ctx.typeAt blk.ty pre with
          | some (.record n) =>
            match ctx.record? n with
            | some rd =>
              match rd.members[j]? with
              | some (_, tj) => tj == st
              | none => false
            | none => false
          | _ => false
        | _ => false
      if member then none else
      match ctx.absPos? blk.ty path, ctx.sizeAlign 32 st with
      | some q, some (nb, _) => some (b, q, nb)
      | _, _ => none
    | none => none
  | _ => none

/-- The scalar that byte `q` of the complete object of block `b` falls in
(`Ctx.scalarIn`), for a bit-field of type `ty` placed there (`Ctx.bfPlaced?`):
C11 6.5p7 classifies the access by the bit-field's declared type, not by its
storage unit's, so that scalar's type must be compatible with `ty`
(`Ty.accessCompatible`), or `ty` a character type. -/
def Ctx.bfScalarAt (ctx : Ctx) (m : Mem) (b : Nat) (ty : Ty) (q : Nat) :
    Res (List PathElem × Ty × Nat) :=
  match m.blocks b with
  | some blk =>
    match ctx.scalarIn 32 blk.ty blk.val [] q with
    | some (p, t, k) =>
      if ty.isChar || t.accessCompatible ty then .ok (p, t, k)
      else .ub "type-punned access (byte-level access not modelled)"
    | none => .ub "type-punned access (byte-level access not modelled)"
  | none => .ub "invalid memory access"

/-- The `nb` bytes from byte `q` of the complete object of block `b`, as an
unsigned number (little-endian), for a bit-field of type `ty` placed there: the
bytes of the scalars there (`Ctx.bfScalarAt`, `byteOf`). -/
def Ctx.bfLoadBytes (ctx : Ctx) (m : Mem) (b : Nat) (ty : Ty) : Nat → Nat → Res Nat
  | _, 0 => .ok 0
  | q, nb + 1 => do
    let (p, t, k) ← ctx.bfScalarAt m b ty q
    let c ← match m.read? (.loc b p) with
      | some v =>
        match byteOf t v k with
        | some c => pure c
        | none => .ub "read of an indeterminate or ill-typed value"
      | none => .ub "invalid memory read"
    let rest ← ctx.bfLoadBytes m b ty (q + 1) nb
    pure (c + 256 * rest)

/-- `Ctx.bfLoadBytes`, 0 where the bytes hold no value (the other bits of a
storage unit never written read as 0). -/
def Ctx.bfLoadBytes0 (ctx : Ctx) (m : Mem) (b : Nat) (ty : Ty) (q nb : Nat) : Nat :=
  match ctx.bfLoadBytes m b ty q nb with
  | .ok u => u
  | _ => 0

/-- The write of `u` (little-endian) into the `nb` bytes from byte `q` of the
complete object of block `b`, for a bit-field of type `ty` placed there:
character stores into the scalars there (`Ctx.bfScalarAt`, `byteStore`). -/
def Ctx.bfStoreBytes (ctx : Ctx) (b : Nat) (ty : Ty) : Mem → Nat → Nat → Nat → Res Mem
  | m, _, 0, _ => .ok m
  | m, q, nb + 1, u => do
    let (p, t, k) ← ctx.bfScalarAt m b ty q
    let m ← byteStore m (.int false 8) b p t k (.int (u % 256 : Nat))
    ctx.bfStoreBytes b ty m (q + 1) nb (u / 256)

def evalFBinop (k : FBinOp) (x y : Float) : Float :=
  match k with
  | .fadd => x + y
  | .fsub => x - y
  | .fmul => x * y
  | .fdiv => x / y
  | .frem => Std.fmodF x y

def caseMatches (x : Int) : CaseKind → List Int → Bool
  | .equal, [v] => x == v
  | .anyof, vs => vs.contains x
  | .range, [lo, hi] => decide (lo ≤ x) && decide (x ≤ hi)
  | _, _ => false

/-- Position in a simple-form switch body where execution starts. -/
def switchStart (x : Int) (ops : List Op) : Option Nat :=
  match ops.findIdx? (fun op => match op with | .case k vs _ => caseMatches x k vs | _ => false) with
  | some i => some i
  | none => ops.findIdx? (fun op => match op with | .case .default _ _ => true | _ => false)

/-- `_ZTIi`, `_ZTIc`, ...: typeinfo of a fundamental type. -/
def isFundamentalTypeinfo (s : String) : Bool :=
  s.length == 5 && s.startsWith "_ZTI" && (s.toList.getD 4 ' ').isLower

/-- The typeinfo of a pointer type, `_ZTIP` and the pointee's mangling: the pointee's
cv-qualifiers (`r`, `V`, `K`) and the mangling of its unqualified type. -/
def ptrTypeinfo? (s : String) : Option (List Char × String) :=
  if s.startsWith "_ZTIP" then
    let cs := s.toList.drop 5
    let qs := cs.takeWhile fun c => c == 'r' || c == 'V' || c == 'K'
    some (qs, String.ofList (cs.drop qs.length))
  else none

/-- The mangling of a function type (`F…E`, after `Do`, `DO`, `Dw` or `Dx` for an exception
specification): a pointer to a function converts to no `void *`. -/
def isFunctionMangling (u : String) : Bool :=
  u.startsWith "F" || u.startsWith "Do" || u.startsWith "DO" || u.startsWith "Dw" ||
    u.startsWith "Dx"

/-- The mangling of a class type (a source name, a nested name, a substitution or a local name):
a pointer to it may convert to a pointer to a base class. -/
def isClassMangling (u : String) : Bool :=
  match u.toList with
  | c :: _ => c.isDigit || c == 'N' || c == 'S' || c == 'Z'
  | [] => false

/-- Whether a handler of pointer type `t` catches an exception of type `ti` through a conversion
that [except.handle]p3 allows, but the derived-to-base one: a qualification conversion of the
pointee (`const int *` catches `int *`), the conversion of an object pointer to `void *` (as
qualified, or more), a function pointer conversion (a `noexcept` function's pointer), and
`std::nullptr_t` (`_ZTIDn`), which a handler of any pointer type catches (as a null pointer; a
pointer-to-member handler, whose null value is not a pointer, is not modelled). -/
def ptrCatches (t ti : String) : Bool :=
  if ti == "_ZTIDn" && t.startsWith "_ZTIP" then true else
  match ptrTypeinfo? t, ptrTypeinfo? ti with
  | some (qh, uh), some (qt, ut) =>
    qt.all (qh.contains ·) &&
      (uh == ut || (uh == "v" && !isFunctionMangling ut) || ut == "Do" ++ uh)
  | _, _ => false

/-- The handler a thrown exception enters (C++ [except.handle]p3): its own type, or a pointer
conversion `ptrCatches` allows. Matching through class hierarchies (a class or a pointer to a
class caught as a base) and multi-level qualification conversions are not modelled: there a
mismatch is undefined. -/
def findHandler (ti : String) : List (CatchKind × Region) → Res (Option Region)
  | [] => .ok none
  | (.all, r) :: _ => .ok (some r)
  | (.type t, r) :: hs =>
    if t == ti then .ok (some r)
    -- a fundamental type matches only itself, in either role (no conversions
    -- apply between a fundamental and any other type in exception matching)
    else if isFundamentalTypeinfo t || isFundamentalTypeinfo ti then findHandler ti hs
    else if ptrCatches t ti then .ok (some r)
    else
      match ptrTypeinfo? t, ptrTypeinfo? ti with
      | some (_, uh), some (_, ut) =>
        if isClassMangling uh && isClassMangling ut then
          .ub "exception matching through a class hierarchy is not modelled"
        else if uh.startsWith "P" || ut.startsWith "P" || uh.startsWith "M" || ut.startsWith "M"
        then .ub "exception matching through a multi-level qualification conversion is not modelled"
        else findHandler ti hs
      -- a pointer and a type that is not one never match (`std::nullptr_t` is handled above)
      | some _, none | none, some _ => findHandler ti hs
      | none, none =>
        if ti == "_ZTIDn" && t.startsWith "_ZTIM" then
          .ub "exception matching: a std::nullptr_t caught as a pointer to member is not modelled"
        else .ub "exception matching through a class hierarchy is not modelled"

/-- A thunk's symbol (Itanium C++ ABI 5.1.4: `_ZTh…` a non-virtual one, `_ZTv…`
a virtual one, `_ZTc…` a covariant one). -/
def isThunk (sym : String) : Bool :=
  sym.startsWith "_ZTh" || sym.startsWith "_ZTv" || sym.startsWith "_ZTc"

/-- Virtual dispatch: an indirect call whose `this` argument points to a base
class subobject at offset 0 (a primary base), while the callee (the final
overrider) is a member of a derived class, receives the enclosing derived
object, as with the Itanium ABI. An overrider that needs another `this`
adjustment is reached through a thunk (`isThunk`), which receives `this`
unchanged and adjusts it itself (byte arithmetic, with the offset that the
vtable holds for a virtual base). -/
def adjustThisIndirect (ctx : Ctx) (sym : String) (argTys : List Ty) (vs : List Val) :
    Res (List Val) :=
  match vs, argTys, (ctx.mod.findFunc? sym).bind (·.params.head?) with
  | .ptr (.loc b path) :: rest, .ptr (.record s) :: _, some (.ptr (.record d)) =>
    if s == d then .ok vs else
    match ctx.basePath 16 d s 0 with
    | some ps =>
      let k := path.length - ps.length
      if ps.length ≤ path.length && path.drop k == ps.map PathElem.idx then
        .ok (.ptr (.loc b (path.take k)) :: rest)
      else if isThunk sym then .ok vs
      else .ub "virtual call: the object is not of the overrider's class"
    | none => if isThunk sym then .ok vs else .ub "virtual call: unsupported class layout"
  | _, _, _ => .ok vs

/-- The arguments of a call, with `this` adjusted for virtual dispatch. -/
def adjustThis (ctx : Ctx) (callee : Callee) (sym : String) (argTys : List Ty) (vs : List Val) :
    Res (List Val) :=
  match callee with
  | .direct _ => .ok vs
  | .indirect _ => adjustThisIndirect ctx sym argTys vs

/-- The same value, floats compared by their bits (for `forgetChanged`). -/
partial def Val.same : Val → Val → Bool
  | .undef, .undef => true
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .float a, .float b => a.toBits == b.toBits
  | .ptr p, .ptr q => p == q
  | .agg xs, .agg ys | .arr xs, .arr ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.same y
  | .vec g xs, .vec h ys => g == h && xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.same y
  | .opt none, .opt none => true
  | .opt (some x), .opt (some y) => x.same y
  | _, _ => false

/-- The writes a `longjmp` back makes for one entry `[b, v0, sv, snv, dv, mods]` of a `setjmp`
snapshot: object `b`, its value `v0` at the `setjmp`, the member paths whose accesses in the
function are all `volatile` (`sv`) and those some of whose are not (`snv`, `nestSetjmps`), those
that a `volatile` access through another pointer reached (`dv`) and those stored into since
(`mods`; `Op.sjNote`, `Std.sjMarkMem`). A part that is not volatile becomes indeterminate when it
was stored into, the same value included, or holds another value (a store not noted: another
library function's) (C11 7.13.2.1p3). A
structure's members are taken one by one; anything else, and a volatile part below a member, as
a whole. -/
def forgetWrites (ctx : Ctx) (m : Mem) (e : Val) : List (Ptr × Val) :=
  match e with
  | .agg [.int b, v0, sv, snv, dv, mods] =>
    match m.live? b.toNat with
    | none => []
    | some blk =>
      -- 1 a structure, 2 a union, 0 anything else
      let kind : Nat := match blk.ty with
        | .record rn => if (ctx.record? rn).any (·.kind != .union) then 1 else 2
        | _ => 0
      let lvl (p : List Nat) : List Nat := if kind == 1 then p.take 1 else []
      let nonvol := (Std.pathsOf snv).map lvl
      let vols := (Std.pathsOf sv ++ Std.pathsOf dv).filterMap fun p =>
        let p := if kind == 0 then [] else p
        if p.length ≤ (if kind == 1 then 1 else 0) && !nonvol.contains p then some p else none
      let mods := (Std.pathsOf mods).map lvl
      let whole : List (Ptr × Val) :=
        if !mods.isEmpty || !blk.val.same v0 then [(.loc b.toNat [], ctx.initVal 32 blk.ty)] else []
      if vols.contains [] then []
      else if kind != 1 then whole
      else match blk.val, v0 with
        | .agg cur, .agg old =>
          (List.range cur.length).filterMap fun j =>
            if vols.contains [j] then none
            else if mods.contains [] || mods.contains [j] || !((cur.getD j .undef).same (old.getD j .undef)) then
              (ctx.typeAt blk.ty [.idx j]).map fun t => (.loc b.toNat [.idx j], ctx.initVal 32 t)
            else none
        | _, _ => whole
  | _ => []

/-- `m` after the writes `ws`, each one that applies. -/
def writesOn (m : Mem) (ws : List (Ptr × Val)) : Mem :=
  ws.foldl (fun m (p, v) => (m.write? p v).getD m) m

/-- After a `longjmp` back to the `setjmp` invocation of token block `tok`: the automatic objects
of its snapshot that are not volatile and have changed become indeterminate (`forgetWrites`). -/
def forgetChanged (ctx : Ctx) (tok : Nat) (m : Mem) : Mem :=
  match m.live? tok with
  | some ⟨_, _, _, .agg snap⟩ => snap.foldl (fun m e => writesOn m (forgetWrites ctx m e)) m
  | _ => m

/-- `Op.sjNote p store vol`: a store into the object `p` points into (`store`) and a `volatile`
access through `p` (`vol`), recorded in the snapshots of the live `setjmp` invocations that hold
the object (`Std.sjMarkMem`), whichever function the operation is in. -/
def sjNoteMem (ctx : Ctx) (σ : State) (p : VId) (store vol : Bool) : Mem :=
  match σ.env p with
  | some (.ptr q) => Std.sjMarkMem ctx σ.mem q store vol
  | _ => σ.mem

/-- The cleanup region calls a destructor (a C++ automatic object's), which a `throw` in place of
a `longjmp` would run. -/
def callsDestructor (ctx : Ctx) : Region → Bool
  | .mk bs => bs.any fun (.mk _ ops) => ops.any fun op =>
    match op with
    | .call _ _ (.direct s) _ _ _ _ => (ctx.mod.findFunc? s).any (·.special == .dtor)
    | _ => false

/-- `p` designates (a part of) one of the current function's own automatic objects. -/
def ownObject (σ : State) (p : Ptr) : Bool :=
  match p with
  | .loc b _ => σ.names.any (·.2 == b)
  | _ => false

/-- The current activation of a function, told apart from the others that are live: the block of
its first named object (bound at its entry: a parameter's, or the variadic arguments'), 0 when it
has none. -/
def frameId (σ : State) : Nat :=
  match σ.names.getLast? with
  | some (_, b) => b
  | none => 0

/-- `va_arg(ap, ty)` into `r` (`viaPtr`: through a pointer to the `va_list` object, `Op.vaArgP`).
The `va_list`'s state (its first member) must be 1, or 3 for the function whose `va_arg` advanced
it (its activation, `frameId`, in the second member): after another function's `va_arg` on it,
its owner may only end it (C11 7.16p3), and a third function may not use it either. A function's
`va_arg` on a `va_list` it does not own and does not reach through a pointer puts it in state 3. -/
def vaArgOp (σ : State) (r ap : VId) (ty : Ty) (viaPtr : Bool) : Res State := do
  let p ← σ.getPtr ap
  match σ.mem.read? p with
  | some (.agg [.int t, f, .ptr (.loc b path), s]) =>
    let own := viaPtr || ownObject σ p
    let fr : Int := frameId σ
    let mine : Bool := match f with
      | .int g => g == fr
      | _ => false
    if !(t == 1 || (t == 3 && !own && mine)) then
      .ub (if t == 3 then "va_arg on a va_list after another function's va_arg on it (C11 7.16p3)"
        else if t == 4 then "va_arg on a va_list after a v*printf call on it, which leaves its value indeterminate (C11 7.21.6.8p2)"
        else "va_arg on a va_list not initialized, or ended by va_end (C11 7.16.1.1p2)") else
    match path.getLast?, σ.mem.read? (.loc b path) with
    | some (.idx k), some v =>
      let v' ← match Std.vaBoxed? σ.mem v with
        | some (t, x) =>
          if Std.vaCompatible t ty x then pure x
          else .ub "va_arg: argument of another type (C11 7.16.1.1p2)"
        -- a value without its type (an indirect call): its kind is checked
        | none => match ty, v with
          | .int sg w, .int x => if inRange sg w x then pure (Val.int x) else .ub "va_arg: value out of range of the type"
          | .ptr _, .ptr q => pure (Val.ptr q)
          | .float _, .float x => pure (Val.float x)
          | _, _ => .ub "va_arg: argument of another type"
      let next : Val := .ptr (.loc b (path.dropLast ++ [.idx (k + 1)]))
      -- another function's `va_arg`: its owner may only end it now (state 3, this activation's)
      let m ← Res.ofOption "va_arg: invalid va_list"
        (σ.mem.write? p (.agg [.int (if own then t else 3), (if own then f else .int fr), next, s]))
      pure ((σ.withMem m).set r v')
    | _, _ => .ub "va_arg: no more variadic arguments"
  | _ => .ub "va_arg on a va_list not initialized, or ended by va_end (C11 7.16.1.1p2)"

/-- A live `va_list` object (`__va_list_tag[1]`), initialized and not ended. -/
def vaLiveObject : Option MemBlock → Bool
  | some ⟨_, _, .array (.record "__va_list_tag") 1, .arr [v]⟩ => Std.vaLive (some v)
  | _ => false

/-- Untyped heap storage (`.array (.other tag) n`): whether it is zero-filled. -/
def heapKind? (tag : String) : Option Bool :=
  if tag == "heap0" then some true else if tag == "heap" then some false else none

/-- The block of a region that starts with `cir.label l`. -/
def labelBlock? (l : String) (blocks : List Block) : Option Nat :=
  blocks.findIdx? fun b => match b with
    | .mk _ (.label l' :: _) => l' == l
    | _ => false

/-- Continue after a nested region that must complete normally or exit. -/
def finishRegion (e : Exit) (σ : State) : Res (Step × State) :=
  match e with
  | .yield [] => .ok (.next, σ)
  | .yield _ => .ub "unexpected yielded values"
  | .cond _ => .ub "cir.condition outside a loop condition"
  | e => .ok (.exit e, σ)

def runsCleanup (k : CleanupKind) (isEh : Bool) : Bool :=
  match k with
  | .all => true
  | .normal => !isEh
  | .eh => isEh

def evalCmp (m : Mem) (k : CmpKind) (x y : Val) : Res Bool :=
  match x, y with
  | .int i, .int j => Res.ofOption "unsupported integer comparison" (cmpInt k i j)
  | .bool i, .bool j => Res.ofOption "unsupported bool comparison" (cmpInt k i.toNat j.toNat)
  | .float u, .float v => .ok (cmpFloat k u v)
  | .ptr p, .ptr q =>
    if !(ptrValid m p && ptrValid m q) then .ub "comparison of an invalid pointer" else
    match k with
    | .eq => Res.ofOption "unspecified pointer comparison" (m.ptrEq? p q)
    | .ne => Res.ofOption "unspecified pointer comparison" ((m.ptrEq? p q).map (!·))
    | .lt => Res.ofOption "relational comparison of unrelated pointers" (m.ptrLt? p q)
    | .gt => Res.ofOption "relational comparison of unrelated pointers" (m.ptrLt? q p)
    | .le => Res.ofOption "relational comparison of unrelated pointers" ((m.ptrLt? q p).map (!·))
    | .ge => Res.ofOption "relational comparison of unrelated pointers" ((m.ptrLt? p q).map (!·))
    | _ => .ub "unsupported pointer comparison"
  | _, _ => .ub "ill-typed comparison"

/-- `evalCmp` with pointers compared by address within one complete object:
equality by `Ctx.ptrEq?` (C11 6.5.9p6); a relational comparison of elements of
one array by their indices (`evalCmp`), of other pointers into one block by
their byte positions in its complete object (`Ctx.absPos?`; 6.5.8p5: later
members and elements compare greater). -/
def Ctx.evalCmpB (ctx : Ctx) (m : Mem) (k : CmpKind) (x y : Val) : Res Bool :=
  match x, y with
  | .ptr p, .ptr q =>
    match k with
    | .eq =>
      if !(ptrValid m p && ptrValid m q) then .ub "comparison of an invalid pointer" else
      Res.ofOption "unspecified pointer comparison" (ctx.ptrEq? m p q)
    | .ne =>
      if !(ptrValid m p && ptrValid m q) then .ub "comparison of an invalid pointer" else
      Res.ofOption "unspecified pointer comparison" ((ctx.ptrEq? m p q).map (!·))
    | .lt | .le | .gt | .ge =>
      if (ctx.elemTyOf? m p).isSome && (ctx.elemTyOf? m q).isSome && p.sameParent q then evalCmp m k x y
      else
        if !(ptrValid m p && ptrValid m q) then .ub "comparison of an invalid pointer" else
        match p, q with
        | .loc b path, .loc b' path' =>
          match m.blocks b with
          | some blk =>
            match b == b', ctx.absPos? blk.ty path, ctx.absPos? blk.ty path' with
            | true, some i, some j => Res.ofOption "unsupported pointer comparison" (cmpInt k (i : Int) (j : Int))
            | _, _, _ => .ub "relational comparison of unrelated pointers"
          | none => .ub "relational comparison of unrelated pointers"
        | _, _ => .ub "relational comparison of unrelated pointers"
    | _ => evalCmp m k x y
  | _, _ => evalCmp m k x y

/-- The comparison of `cir.atomic.cmpxchg` (the object against the expected
value): integers, booleans and pointers as `==` does (`Ctx.evalCmpB`), floats
by their bit patterns (the object's bytes are compared, not the numbers: `-0.0`
is not `+0.0`). -/
def Ctx.cmpXchgEq (ctx : Ctx) (m : Mem) : Val → Val → Res Bool
  | .float u, .float v => .ok (u.toBits == v.toBits)
  | x, y => ctx.evalCmpB m .eq x y

/-- A memory order's position in `memory_order` (C11 7.17.1p4): a failure order stronger than
the success order comes later (the order GCC checks them in). -/
def memOrderRank : String → Option Nat
  | "relaxed" => some 0
  | "consume" => some 1
  | "acquire" => some 2
  | "release" => some 3
  | "acq_rel" => some 4
  | "seq_cst" => some 5
  | _ => none

/-- A store of `v` as a value of type `ty`: undefined for `.undef` as a whole value of a
structure, union or array type, which only `Op.retLoad` gives: the missing value of a call that
reached its function's closing brace, used (C11 6.9.1p12; the frontend drops the stores of
discarded results, `CIR.Frontend.markRetDiscards`; a scalar store of `.undef` is an ill-typed
store anyway). -/
def missingAggCheck (ty : Ty) (v : Val) : Res Unit :=
  match ty with
  | .record _ | .array .. =>
    match v with
    | .undef =>
      .ub "use of the value of a call that reached its function's closing brace (C11 6.9.1p12)"
    | _ => .ok ()
  | _ => .ok ()

/-- Effect of the operations that neither touch control flow nor call
functions (`evalOp` only uses it for those). -/
def evalSimple (ctx : Ctx) (op : Op) (σ : State) : Res State :=
  match op with
  | .const r ty c => do
    let v ← Res.ofOption "unsupported constant" (ctx.constVal 32 ty c)
    pure (σ.set r v)
  | .alloca r ty name =>
    let (b, m) := σ.mem.alloc .stack ty (ctx.initVal 32 ty)
    .ok ({ (σ.withMem m).set r (.ptr (.loc b [])) with names := (name, b) :: σ.names })
  | .allocaConst r ty name =>
    -- a const object: a read-only block, which its initialization writes while indeterminate
    let (b, m) := σ.mem.alloc .readonly ty (ctx.initVal 32 ty)
    .ok ({ (σ.withMem m).set r (.ptr (.loc b [])) with names := (name, b) :: σ.names })
  | .load r a ty => do
    let p ← σ.getPtr a
    let v ← loadPtr ctx σ.mem ty p
    pure (σ.set r v)
  | .retLoad r a ty => do
    -- the function reached its closing brace: the caller may only discard the result, which is
    -- `.undef` as a whole when the slot holds nothing (a structure's indeterminate members too)
    let p ← σ.getPtr a
    match σ.mem.read? p with
    | some v => if v.holds then pure (σ.set r (← loadPtr ctx σ.mem ty p)) else pure (σ.set r .undef)
    | none => pure (σ.set r (← loadPtr ctx σ.mem ty p))
  | .store v a ty => do
    let x ← σ.get v
    let p ← σ.getPtr a
    missingAggCheck ty x
    let m ← ctx.typedStore σ.mem ty p x
    pure (σ.withMem m)
  | .copy src dst ty => do
    let ps ← σ.getPtr src
    let pd ← σ.getPtr dst
    let v ← ctx.typedLoad σ.mem ty ps
    missingAggCheck ty v
    let m ← ctx.typedStore σ.mem ty pd v
    pure (σ.withMem m)
  | .getMember r base i rt _ => do
    match ← σ.getPtr base with
    | .loc b path => pure (σ.set r (.ptr (.loc b (ctx.memberPath σ.mem b path rt i))))
    | _ => .ub "member access through a null or function pointer"
  | .unionMember r base i rt ft => do
    match ← σ.getPtr base with
    | .loc b path =>
      match σ.mem.read? (.loc b path) with
      | some (.agg vs) =>
        let ms := match rt with
          | .record name => match ctx.record? name with | some rd => rd.members | none => []
          | _ => []
        -- where the write is refused (a read-only block, a const object, holding a
        -- value) the union is left as it is: a read of another member reinterprets
        -- the stored one (`Ctx.unionView?`)
        match σ.mem.write? (.loc b path) (.agg (activeMember i 0 (ctx.fromActive i ft 0 ms vs) vs)) with
        | some m => pure ((σ.withMem m).set r (.ptr (.loc b (path ++ [.idx i]))))
        | none => pure (σ.set r (.ptr (.loc b (path ++ [.idx i]))))
      | _ => .ub "union member access to a non-union object"
    | _ => .ub "member access through a null or function pointer"
  | .getElement r base idx _ _ => do
    let p ← σ.getPtr base
    let i ← σ.getInt idx
    match p, σ.mem.read? p with
    | .loc b path, some (.arr xs) =>
      if 0 ≤ i ∧ i ≤ xs.length then pure (σ.set r (.ptr (.loc b (path ++ [.idx i.toNat]))))
      else .ub "array index out of bounds"
    | _, _ => .ub "element access into a non-array"
  | .ptrStride r base off elemTy _ => do
    let p ← σ.getPtr base
    let n ← σ.getInt off
    -- in C++ a null pointer plus or minus 0 is null ([expr.add]p4.1); undefined in C
    let q ← match p with
      | .null => if ctx.mod.cxx && n == 0 then pure Ptr.null else .ub "pointer arithmetic out of bounds"
      | p => Res.ofOption "pointer arithmetic out of bounds" (ctx.stride? σ.mem p n elemTy)
    pure (σ.set r (.ptr q))
  | .ptrDiff r a b elemTy _ => do
    let p ← σ.getPtr a
    let q ← σ.getPtr b
    -- in C++ the difference of two null pointers is 0 ([expr.add]p5.1); undefined in C
    let d ← match p, q with
      | .null, .null => if ctx.mod.cxx then pure (0 : Int) else .ub "difference of unrelated pointers"
      | p, q => Res.ofOption "difference of unrelated pointers" (ctx.diff? σ.mem p q elemTy)
    pure (σ.set r (.int d))
  | .getGlobal r sym _ => do
    let p ← Res.ofOption "unknown global symbol" (ctx.symAddr? sym [])
    pure (σ.set r (.ptr p))
  | .blockAddress r fn lbl => pure (σ.set r (.ptr (.label fn lbl)))
  | .baseClassAddr r base off srcTy dstTy => do
    let p ← σ.getPtr base
    match p, recordName? srcTy, recordName? dstTy with
    | .loc b path, some d, some bn =>
      let ps ← Res.ofOption "unsupported base class layout" (ctx.basePath 16 d bn off)
      pure (σ.set r (.ptr (.loc b (path ++ ps.map PathElem.idx))))
    | .null, _, _ => pure (σ.set r (.ptr .null))
    | _, _, _ => .ub "unsupported base class conversion"
  | .derivedClassAddr r base off srcTy dstTy => do
    let p ← σ.getPtr base
    match p, recordName? dstTy, recordName? srcTy with
    | .loc b path, some d, some bn =>
      let ps ← Res.ofOption "unsupported base class layout" (ctx.basePath 16 d bn off)
      let k := path.length - ps.length
      if ps.length ≤ path.length && path.drop k == ps.map PathElem.idx then
        pure (σ.set r (.ptr (.loc b (path.take k))))
      else .ub "invalid downcast"
    | .null, _, _ => pure (σ.set r (.ptr .null))
    | _, _, _ => .ub "unsupported derived class conversion"
  | .vtableAddressPoint r vt idx off => do
    if (ctx.mod.findGlobal? vt).isNone then .ub "unknown vtable" else
    pure (σ.set r (.ptr (.vtable vt idx off)))
  | .vtableGetVptr r obj ty => do
    let p ← σ.getPtr obj
    match p, ctx.vptrClass? σ.mem p ty with
    | .loc b path, some n =>
      let vp ← Res.ofOption "class without a vptr" (ctx.vptrPath 16 n)
      pure (σ.set r (.ptr (.loc b (path ++ vp.map PathElem.idx))))
    | _, _ => .ub "vptr of a non-object"
  | .vtableGetVirtualFnAddr r vp slot => do
    match ← σ.getPtr vp with
    | .vtable vt i k => pure (σ.set r (.ptr (.vtable vt i (k + slot))))
    | _ => .ub "virtual call through an invalid vptr"
  | .vttGlobalAddr r vtt n => do
    let b ← Res.ofOption "unknown VTT" (ctx.gaddr vtt)
    let q ← Res.ofOption "VTT entry out of range" (ctx.stride? σ.mem (.loc b [.idx 0]) n (.ptr .void))
    pure (σ.set r (.ptr q))
  | .vttParamAddr r vtt n => do
    let p ← σ.getPtr vtt
    let q ← Res.ofOption "VTT entry out of range" (ctx.stride? σ.mem p n (.ptr .void))
    pure (σ.set r (.ptr q))
  | .extractMember r a i _ _ => do
    match ← σ.get a with
    | .agg fs => pure (σ.set r (← Res.ofOption "bad member index" fs[i]?))
    | _ => .ub "extract_member of a non-record"
  | .binop r k nsw nuw a b ty => do
    match ty with
    | .int s w =>
      let x ← σ.getInt a
      let y ← σ.getInt b
      let z ← evalBinop k nsw nuw s w x y
      pure (σ.set r (.int z))
    | .bool =>
      let x ← σ.getBool a
      let y ← σ.getBool b
      match k with
      | .and => pure (σ.set r (.bool (x && y)))
      | .or => pure (σ.set r (.bool (x || y)))
      | .xor => pure (σ.set r (.bool (x != y)))
      | _ => .ub "unsupported bool operation"
    | .array (.int s w) _ => do
      let zs ← vecZip (← σ.get a) (← σ.get b) fun x y => match x, y with
        | .int x, .int y => Val.int <$> evalBinop k nsw nuw s w x y
        | _, _ => .ub "vector arithmetic on an indeterminate element"
      pure (σ.set r (.arr zs))
    | _ => .ub "unsupported operand type"
  | .fbinop r k a b ty => do
    match ← σ.get a, ← σ.get b, ty with
    | .float x, .float y, _ => pure (σ.set r (.float (roundFloat ty (evalFBinop k x y))))
    | .arr xs, .arr ys, .array e _ => do
      let zs ← vecZip (.arr xs) (.arr ys) fun x y => match x, y with
        | .float x, .float y => pure (.float (roundFloat e (evalFBinop k x y)))
        | _, _ => .ub "vector arithmetic on an indeterminate element"
      pure (σ.set r (.arr zs))
    | _, _, _ => .ub "expected floats"
  | .fmuladd r a b c ty => do
    match ← σ.get a, ← σ.get b, ← σ.get c, ty with
    | .float x, .float y, .float z, _ =>
      pure (σ.set r (.float (roundFloat ty (roundFloat ty (x * y) + z))))
    | .arr xs, .arr ys, .arr zs, .array e _ => do
      let ps ← vecZip (.arr xs) (.arr ys) fun x y => pure (.arr [x, y])
      let vs ← vecZip (.arr ps) (.arr zs) fun p z => match p, z with
        | .arr [.float x, .float y], .float z => pure (.float (roundFloat e (roundFloat e (x * y) + z)))
        | _, _ => .ub "vector arithmetic on an indeterminate element"
      pure (σ.set r (.arr vs))
    | _, _, _, _ => .ub "expected floats"
  | .shift r left a amt ty _ => do
    match ty with
    | .int s w =>
      let x ← σ.getInt a
      let n ← σ.getInt amt
      let z ← evalShift left s w x n
      pure (σ.set r (.int z))
    | .array (.int s w) _ => do
      let zs ← vecZip (← σ.get a) (← σ.get amt) fun x n => match x, n with
        | .int x, .int n => Val.int <$> evalVecShift left s w x n
        | _, _ => .ub "vector shift of an indeterminate element"
      pure (σ.set r (.arr zs))
    | _ => .ub "unsupported shift type"
  | .unop r k nsw a ty => do
    match ty, k with
    | .int s w, _ =>
      let x ← σ.getInt a
      let z ← evalUnop k nsw s w x
      pure (σ.set r (.int z))
    | .bool, .not =>
      let x ← σ.getBool a
      pure (σ.set r (.bool !x))
    | .array (.int s w) _, _ => do
      match ← σ.get a with
      | .arr xs => do
        let zs ← xs.mapM fun x => match x with
          | .int x => Val.int <$> evalUnop k nsw s w x
          | _ => .ub "vector arithmetic on an indeterminate element"
        pure (σ.set r (.arr zs))
      | _ => .ub "expected a vector"
    | _, _ => .ub "unsupported unary operation"
  | .fneg r a _ => do
    match ← σ.get a with
    | .float x => pure (σ.set r (.float (-x)))
    | .arr xs => do
      let zs ← xs.mapM fun x => match x with
        | .float x => pure (.float (-x))
        | _ => .ub "vector arithmetic on an indeterminate element"
      pure (σ.set r (.arr zs))
    | _ => .ub "expected a float"
  | .fmath r fn a ty => do
    match ← σ.get a with
    | .float x =>
      match evalFMath fn x with
      | some y => pure (σ.set r (.float (roundFloat ty y)))
      | none => .ub s!"unsupported floating-point function {fn}"
    | _ => .ub "expected a float"
  | .isFpClass r a cls ty => do
    match ← σ.get a with
    | .float x =>
      match (cls.splitOn "|").mapM (fun c => fpClass ty (String.ofList (c.toList.filter (· != ' '))) x) with
      | some bs => pure (σ.set r (.bool (bs.any id)))
      | none => .ub s!"unsupported floating-point class {cls}"
    | _ => .ub "expected a float"
  | .bitCount r leading pz a ty => do
    match ty with
    | .int _ w =>
      let x ← σ.getInt a
      -- of 0 with `poison_zero`, an indeterminate value that only a use makes undefined:
      -- `__builtin_clzg(x, d)` and `std::countl_zero` compute it, then select `d` for 0
      pure (σ.set r (match evalBitCount leading pz w x with | some z => .int z | none => .undef))
    | _ => .ub "unsupported clz/ctz type"
  | .isConstant r _ => pure (σ.set r (.bool false))
  | .bitOp r fn a ty => do
    match ty with
    | .int s w =>
      let x ← σ.getInt a
      let z ← evalBitOp fn s w x
      pure (σ.set r (.int z))
    | _ => .ub s!"unsupported {fn} type"
  | .rotate r left a n ty => do
    match ty with
    | .int s w =>
      let x ← σ.getInt a
      let k ← σ.getInt n
      -- a rotation to the right by `k` is one to the left by `w - k`
      let u := (x % (2 : Int) ^ w).toNat
      let k := (k % (2 : Int) ^ w).toNat % w
      let k := if left then k else (w - k) % w
      pure (σ.set r (.int (wrap s w ((u * 2 ^ k + u / 2 ^ (w - k)) % 2 ^ w))))
    | _ => .ub "unsupported rotate type"
  | .copysign r a b _ => do
    match ← σ.get a, ← σ.get b with
    | .float x, .float y =>
      -- the bits of `x` with the sign bit of `y` (zeros included; a `float` is held as a double)
      let s : UInt64 := 0x8000000000000000
      pure (σ.set r (.float (Float.ofBits ((x.toBits &&& ~~~s) ||| (y.toBits &&& s)))))
    | _, _ => .ub "expected floats"
  | .fminmax r isMax a b _ => do
    match ← σ.get a, ← σ.get b with
    | .float x, .float y =>
      -- equal operands (zeros of either sign) give `b`, as glibc's `fmax` / `fmin` do
      let z := if Std.decodeF x == .nan then y else if Std.decodeF y == .nan then x
        else if cmpFloat (if isMax then .gt else .lt) x y then x else y
      pure (σ.set r (.float z))
    | _, _ => .ub "expected floats"
  | .prefetch _ => pure σ
  | .allocaN r ty name n => do
    let k ← σ.getInt n
    if k ≤ 0 then .ub "variable-length array of non-positive size (C11 6.7.6.2p5)" else
    -- the size arrives as a `size_t`: from 2^63 on it was a negative number
    if 2 ^ 63 ≤ k then .ub "variable-length array of negative size (C11 6.7.6.2p5)" else
    let aty : Ty := .array ty k.toNat
    let (b, m) := σ.mem.alloc .stack aty (ctx.initVal 32 aty)
    .ok ({ (σ.withMem m).set r (.ptr (.loc b [.idx 0])) with names := (name, b) :: σ.names })
  | .stackSave r => pure (σ.set r (.ptr (.loc σ.mem.next [])))
  | .stackRestore p => do
    match ← σ.getPtr p with
    | .loc b [] =>
      if b ≤ σ.mem.next then pure (σ.withMem (σ.mem.endScope b))
      else .ub "stackrestore: not a token of cir.stacksave"
    | _ => .ub "stackrestore: not a token of cir.stacksave"
  | .vaCopy src dst => do
    let ps ← σ.getPtr src
    let pd ← σ.getPtr dst
    if Std.vaLive (σ.mem.read? pd) then
      .ub "va_copy into a va_list already initialized, without va_end (C11 7.16.1.2p2)" else
    match σ.mem.read? ps with
    | some (.agg [.int t, f, area, s]) =>
      -- after another function's va_arg on it, its owner may only end it, and only that function
      -- may go on with it (C11 7.16p3)
      let mine : Bool := match f with
        | .int g => g == (frameId σ : Int)
        | _ => false
      if t == 1 || (t == 3 && !ownObject σ ps && mine) then
        let m ← Res.ofOption "va_copy: invalid destination" (σ.mem.write? pd (.agg [.int 1, .int 0, area, s]))
        pure (σ.withMem m)
      else if t == 3 then .ub "va_copy of a va_list after another function's va_arg on it (C11 7.16p3)"
      else if t == 4 then .ub "va_copy of a va_list after a v*printf call on it, which leaves its value indeterminate (C11 7.21.6.8p2)"
      else .ub "va_copy of a va_list not initialized, or ended (C11 7.16.1.2p2)"
    | _ => .ub "va_copy of a va_list not initialized, or ended (C11 7.16.1.2p2)"
  | .vaStart ap => do
    let p ← σ.getPtr ap
    if Std.vaLive (σ.mem.read? p) then
      .ub "va_start on a va_list already initialized, without va_end (C11 7.16.1.4p3)" else
    let area : Val := match σ.names.lookup "__va_args" with
      | some b => .ptr (.loc b [.idx 0])
      | none => .ptr .null
    let m ← Res.ofOption "va_start: invalid va_list" (σ.mem.write? p (.agg [.int 1, .int 0, area, .ptr .null]))
    pure (σ.withMem m)
  | .vaEnd ap => do
    let p ← σ.getPtr ap
    -- in the function whose va_start or va_copy initialized it (C11 7.16.1p1)
    if !ownObject σ p then
      .ub "va_end in another function than the one whose va_start or va_copy initialized the va_list (C11 7.16.1p1)" else
    match σ.mem.read? p with
    | some (.agg (.int t :: rest)) =>
      if t == 1 || t == 3 || t == 4 then
        let m ← Res.ofOption "va_end: invalid va_list" (σ.mem.write? p (.agg (.int 2 :: rest)))
        pure (σ.withMem m)
      else .ub "va_end on a va_list not initialized by va_start or va_copy (C11 7.16.1.3p2)"
    | _ => .ub "va_end on a va_list not initialized by va_start or va_copy (C11 7.16.1.3p2)"
  | .vaEndCheck =>
    -- before a return: every va_list of this function's objects that is initialized was ended
    if σ.names.any (fun (_, b) => vaLiveObject (σ.mem.live? b)) then
      .ub "return without va_end on a va_list this function initialized (C11 7.16.1.3p2)"
    else pure σ
  | .vaEndCheckOf aps =>
    -- where the block of the va_list objects `aps` ends: each one initialized was ended
    if aps.any (fun a => match σ.env a with
        | some (.ptr (.loc b _)) => vaLiveObject (σ.mem.live? b)
        | _ => false) then
      .ub "the block of a va_list this function initialized ends without va_end (C11 7.16.1p1, 7.16.1.3p2)"
    else pure σ
  | .sjNote p st v => pure (σ.withMem (sjNoteMem ctx σ p st v))
  | .vaBox r a ty => do
    let v ← σ.get a
    let (b, m) := σ.mem.alloc .stack (.func [ty] .void false) v
    pure ((σ.withMem m).set r (.ptr (.loc b [])))
  | .fail msg => .ub msg
  | .fitsCheck a ty msg => do
    match ty, ← σ.get a with
    | .int s w, .int x => if inRange s w x then pure σ else .ub msg
    | _, _ => .ub msg
  | .alignCheck a n => do
    match ← σ.get a with
    | .ptr (.loc b path) =>
      if ctx.posAligned σ.mem b path n then pure σ else .ub "misaligned vector access"
    | _ => pure σ
  | .vaArg r ap ty => vaArgOp σ r ap ty false
  | .vaArgP r ap ty => vaArgOp σ r ap ty true
  | .arithOverflow r o k a b _ dst => do
    match dst with
    | .int s w =>
      let x ← σ.getInt a
      let y ← σ.getInt b
      let z := match k with | .add => x + y | .sub => x - y | _ => x * y
      pure ((σ.set r (.int (wrap s w z))).set o (.bool !(inRange s w z)))
    | _ => .ub "unsupported overflow-checked type"
  | .iabs r mp a ty => do
    match ty with
    | .int s w =>
      let x ← σ.getInt a
      if mp && x == intMin s w then .ub "abs of the minimum value"
      else pure (σ.set r (.int (wrap s w x.natAbs)))
    | _ => .ub "unsupported abs type"
  | .atomicFetch r k ff p v ty => do
    match ty with
    | .int s w =>
      let ptr ← σ.getPtr p
      let y ← σ.getInt v
      match ← ctx.typedLoad σ.mem ty ptr with
      | .int x =>
        let z ← match k with
          | "add" => pure (x + y) | "sub" => pure (x - y)
          | "and" => pure (bitwise s w (· &&& ·) x y) | "or" => pure (bitwise s w (· ||| ·) x y)
          | "xor" => pure (bitwise s w (· ^^^ ·) x y)
          | "max" => pure (max x y) | "min" => pure (min x y)
          | _ => .ub s!"unsupported atomic operation {k}"
        let z := wrap s w z
        let m ← ctx.typedStore σ.mem ty ptr (.int z)
        pure ((σ.withMem m).set r (.int (if ff then x else z)))
      | _ => .ub "atomic operation on a non-integer"
    | _ => .ub "unsupported atomic type"
  | .atomicXchg r p v ty => do
    let ptr ← σ.getPtr p
    let x ← σ.get v
    let old ← ctx.typedLoad σ.mem ty ptr
    let m ← ctx.typedStore σ.mem ty ptr x
    pure ((σ.withMem m).set r old)
  | .atomicCmpXchg ro rk p e d ty succ fail => do
    -- C11 7.17.7.4p2: the failure order is neither release nor acq_rel (clang turns a constant
    -- one into relaxed, and a variable one reaches relaxed through its switch; C++
    -- [atomics.types.operations] has the same precondition) and, in C11 only, no stronger than
    -- the success order (C++17 dropped that, P0418R2, and C23 too)
    match memOrderRank succ, memOrderRank fail with
    | some s, some f =>
      if f == 3 || f == 4 then
        .ub "atomic compare-exchange: the failure order is release or acq_rel (C11 7.17.7.4p2)" else
      if s < f && !ctx.mod.cxx then
        .ub ("atomic compare-exchange: the failure order is stronger than the success order " ++
          "(C11 7.17.7.4p2; not in C23 or C++17)") else
      pure ()
    | _, _ => .ub "atomic compare-exchange: unknown memory order"
    let ptr ← σ.getPtr p
    let ev ← σ.get e
    let dv ← σ.get d
    let old ← ctx.typedLoad σ.mem ty ptr
    if ← ctx.cmpXchgEq σ.mem old ev then
      let m ← ctx.typedStore σ.mem ty ptr dv
      pure (((σ.withMem m).set ro old).set rk (.bool true))
    else
      pure ((σ.set ro old).set rk (.bool false))
  | .getBitfield r p st size off sg ty => do
    let ptr ← σ.getPtr p
    match ctx.bfPlaced? σ.mem ptr st with
    | some (b, q, nb) =>
      -- a storage unit placed over other objects: its bytes, read as an
      -- access of the bit-field's type (`Ctx.bfScalarAt`)
      let x ← ctx.bfLoadBytes σ.mem b ty q nb
      pure (σ.set r (bfVal ty (bfExtract x (8 * nb) size off sg)))
    | none =>
      match st with
      | .int _ sw =>
        match ← ctx.typedLoad σ.mem st ptr with
        | .int x => pure (σ.set r (bfVal ty (bfExtract x sw size off sg)))
        | _ => .ub "bit-field storage is not an integer"
      | .array (.int _ ew) n =>
        match ← ctx.typedLoad σ.mem st ptr with
        | .arr xs =>
          if xs.length = n then
            match bfJoin ew xs with
            | some x => pure (σ.set r (bfVal ty (bfExtract x (n * ew) size off sg)))
            | none => .ub "read of an indeterminate or ill-typed value"
          else .ub "bit-field storage is not an array of its type"
        | _ => .ub "bit-field storage is not an array of its type"
      | _ => .ub "unsupported bit-field storage"
  | .setBitfield r p v st size off sg ty => do
    let ptr ← σ.getPtr p
    let x ← match ← σ.get v with
      | .int i => pure i
      | .bool b => pure (if b then 1 else 0)
      | _ => .ub "expected an integer"
    let res := bfVal ty (bfExtract (bfInsert 0 size size 0 x) size size 0 sg)
    match ctx.bfPlaced? σ.mem ptr st with
    | some (b, q, nb) =>
      -- a storage unit placed over other objects: its bytes, written as an
      -- access of the bit-field's type
      let raw := ctx.bfLoadBytes0 σ.mem b ty q nb
      let m ← ctx.bfStoreBytes b ty σ.mem q nb (bfInsert raw (8 * nb) size off x)
      pure ((σ.withMem m).set r res)
    | none =>
      match st with
      | .int s sw =>
        -- the other bits of a storage unit that was never written read as 0; a unit
        -- in an inactive union member has the active member's bits (`Ctx.unionView?`)
        let raw : Int := match ((ctx.unionView? σ.mem ptr).getD σ.mem).read? ptr with
          | some (.int y) => y
          | _ => 0
        let m ← ctx.typedStore σ.mem st ptr (.int (wrap s sw (bfInsert raw sw size off x)))
        pure ((σ.withMem m).set r res)
      | .array (.int s ew) n =>
        match ((ctx.unionView? σ.mem ptr).getD σ.mem).read? ptr with
        | some (.arr ys) =>
          if ys.length = n then
            -- as for an integer unit: the bits of elements never written read as 0
            let m ← ctx.typedStore σ.mem st ptr (.arr (bfSplit s ew n (bfInsert (bfJoin0 ew ys) (n * ew) size off x)))
            pure ((σ.withMem m).set r res)
          else .ub "bit-field storage is not an array of its type"
        | _ => .ub "bit-field storage is not an array of its type"
      | _ => .ub "unsupported bit-field storage"
  | .cmp r k a b _ => do
    let x ← σ.get a
    let y ← σ.get b
    let c ← ctx.evalCmpB σ.mem k x y
    pure (σ.set r (.bool c))
  | .cast r k a src dst => do
    let x ← σ.get a
    -- the first typed view of heap storage (`operator new`, `malloc`,
    -- `calloc`) gives it the type `T`, or `T[n / sizeof T]` (then the
    -- pointer designates the first element)
    let (σ, x) ← match k, x, dst with
      | .bitcast, .ptr (.loc b []), .ptr t =>
        match σ.mem.blocks b with
        | some ⟨.heap, true, .array (.other tag) n, .undef⟩ =>
          match heapKind? tag, ctx.sizeAlign 32 t with
          | some zero, some (sz, _) =>
            let elem := if zero then (ctx.zeroVal 32 t).getD (ctx.initVal 32 t) else ctx.initVal 32 t
            if sz > 0 ∧ n % sz = 0 ∧ n / sz ≠ 1 ∧ n ≠ 0 then
              let cnt := n / sz
              pure (σ.withMem (σ.mem.setBlock b ⟨.heap, true, .array t cnt, .arr (List.replicate cnt elem)⟩),
                .ptr (.loc b [.idx 0]))
            else
              pure (σ.withMem (σ.mem.setBlock b ⟨.heap, true, t, elem⟩), x)
          | _, _ => pure (σ, x)
        | _ => pure (σ, x)
      | _, _, _ => pure (σ, x)
    let x := ctx.convertPtr σ.mem k x dst
    ctx.castCheck σ.mem k x dst
    let v ← castVal ctx σ.mem k x src dst
    pure (σ.set r v)
  | .select r c a b _ => do
    let bc ← σ.getBool c
    let x ← σ.get a
    let y ← σ.get b
    pure (σ.set r (if bc then x else y))
  | .complexCreate r a b _ => do
    let x ← σ.get a
    let y ← σ.get b
    pure (σ.set r (.arr [x, y]))
  | .complexPart r imag c _ => do
    match ← σ.get c with
    | .arr [x, y] => pure (σ.set r (if imag then y else x))
    -- `__real__` / `__imag__` of a real value: the value itself, and 0
    | .int x => pure (σ.set r (.int (if imag then 0 else x)))
    | .float x => pure (σ.set r (.float (if imag then 0 else x)))
    | _ => .ub "complex part of an indeterminate or ill-typed value"
  | .complexArith r sub a b ty => do
    match ← σ.get a, ← σ.get b, ty with
    | .arr [.int x, .int y], .arr [.int u, .int v], .int s w =>
      let k := if sub then BinOp.sub else BinOp.add
      let re ← evalBinop k false false s w x u
      let im ← evalBinop k false false s w y v
      pure (σ.set r (.arr [.int re, .int im]))
    | .arr [.float x, .float y], .arr [.float u, .float v], .float _ =>
      let k := if sub then FBinOp.fsub else FBinOp.fadd
      pure (σ.set r (.arr [.float (roundFloat ty (evalFBinop k x u)), .float (roundFloat ty (evalFBinop k y v))]))
    | _, _, _ => .ub "complex arithmetic on an indeterminate or ill-typed value"
  | .complexEq r ne a b _ => do
    match ← σ.get a, ← σ.get b with
    | .arr [x, y], .arr [u, v] =>
      let e ← ctx.evalCmpB σ.mem .eq x u
      let e' ← ctx.evalCmpB σ.mem .eq y v
      pure (σ.set r (.bool (if ne then !(e && e') else e && e')))
    | _, _ => .ub "complex comparison of a non-complex value"
  | .vecCreate r es _ => do
    let vs ← es.mapM σ.get
    pure (σ.set r (.arr vs))
  | .vecSplat r x n _ => do
    let v ← σ.get x
    pure (σ.set r (.arr (List.replicate n v)))
  | .vecExtract r v i _ => do
    match ← σ.get v with
    | .arr xs =>
      let k ← σ.getInt i
      match (if 0 ≤ k then xs[k.toNat]? else none) with
      | some x => pure (σ.set r x)
      | none => .ub "vector index out of range"
    | _ => .ub "expected a vector"
  | .vecInsert r v x i _ => do
    match ← σ.get v with
    | .arr xs =>
      let k ← σ.getInt i
      let y ← σ.get x
      if 0 ≤ k ∧ k.toNat < xs.length then pure (σ.set r (.arr (xs.set k.toNat y)))
      else .ub "vector index out of range"
    | _ => .ub "expected a vector"
  | .vecCmp r k a b _ rt => do
    let zs ← vecZip (← σ.get a) (← σ.get b) fun x y => do
      let c ← ctx.evalCmpB σ.mem k x y
      match rt with
      | .int s w => pure (.int (wrap s w (if c then -1 else 0)))
      | _ => .ub "vector comparison with an unsupported result type"
    pure (σ.set r (.arr zs))
  | .vecShuffle r a b idx => do
    match ← σ.get a, ← σ.get b with
    | .arr xs, .arr ys =>
      let vs ← idx.mapM fun i =>
        if i = -1 then pure Val.undef
        else match (if 0 ≤ i then (xs ++ ys)[i.toNat]? else none) with
          | some x => pure x
          | none => .ub "vector shuffle index out of range"
      pure (σ.set r (.arr vs))
    | _, _ => .ub "expected vectors"
  | .vecTernary r c a b => do
    let ps ← vecZip (← σ.get a) (← σ.get b) fun x y => pure (.arr [x, y])
    let zs ← vecZip (← σ.get c) (.arr ps) fun k p => match k, p with
      | .int k, .arr [x, y] => pure (if k != 0 then x else y)
      | _, _ => .ub "vector select on an indeterminate condition"
    pure (σ.set r (.arr zs))
  | .x86Intrinsic r name args ty => do
    let vs ← args.mapM σ.get
    match Std.x86Intrinsic name vs ty with
    | some v => pure (σ.set r v)
    | none => .ub ("x86 intrinsic " ++ name ++ " outside its model (operands of another shape, or the sign of a NaN)")
  | .allocException r _ ty =>
    let (b, m) := σ.mem.alloc .exn ty (ctx.initVal 32 ty)
    .ok ((σ.withMem m).set r (.ptr (.loc b [])))
  | .beginCatch tr er eh => do
    match ← σ.get eh with
    | .tok x => pure ((σ.set tr (.tok x)).set er (.ptr x.obj))
    | _ => .ub "begin_catch of a non-token"
  | .endCatch _ => .ok σ
  | .initCatchParam kind exn dst ty => do
    let pe ← σ.getPtr exn
    let pd ← σ.getPtr dst
    -- `pointer`: the exception object is a pointer that the handler's type takes unchanged
    -- (`findHandler`: its own type, a qualification, `void *` or function pointer conversion, a
    -- `std::nullptr_t` as the null pointer), copied as a scalar
    if kind = "scalar" || kind = "pointer" then
      let v ← ctx.typedLoad σ.mem ty pe
      let m ← ctx.typedStore σ.mem ty pd v
      pure (σ.withMem m)
    else if kind = "reference" then
      let m ← ctx.typedStore σ.mem ty pd (.ptr pe)
      pure (σ.withMem m)
    else .ub "unsupported catch parameter kind"
  | .assume c => do
    let b ← σ.getBool c
    if b then pure σ else .ub "assumption violated"
  | _ => .ub "not a simple operation"

/-! ### The interpreter -/

/-! ### Observation of loop heads (for `cirrun --trace`)

`loopHead` is the identity. Compiled code (the `cirrun` interpreter) replaces
it by `loopHeadImpl`, which, when the environment variable `CIR_TRACE` is
set, prints the values of the named local variables at every loop head: the
data from which loop invariants are mined. Proofs never see it: the loop
unfolding lemmas remove it. -/

/-- The value of a variable as trace text: integers; through a pointer, the
pointee (an integer, or the elements of a container); iterator positions. -/
def traceVal (m : Mem) (v : Val) : Option String :=
  let ints (xs : List Val) : String :=
    "[" ++ ",".intercalate (xs.filterMap fun x => match x with
      | .int i => some (toString i) | .bool b => some (if b then "1" else "0") | _ => none) ++ "]"
  match v with
  | .int i => some (toString i)
  | .bool b => some (if b then "1" else "0")
  | .ptr (.loc b path) =>
    match m.read? (.loc b path) with
    | some (.vec _ xs) => some (ints xs)
    | some (.arr xs) => some (ints xs)
    | some (.int i) => some ("*" ++ toString i)
    | _ => none
  | .agg [.ptr (.loc _ path)] =>
    match path.getLast? with
    | some e => some ("@" ++ toString e.index)
    | none => none
  | .vec _ xs => some (ints xs)
  | _ => none

/-- One trace line: `@LOOP name=value …` for the named variables of `σ`. -/
def traceLine (σ : State) : String :=
  let vars := σ.names.reverse.filterMap fun (n, b) =>
    match σ.mem.blocks b with
    | some blk => (traceVal σ.mem blk.val).map fun t => n ++ "=" ++ t
    | none => none
  "@LOOP " ++ " ".intercalate vars

/-- Whether loop heads are traced (`CIR_TRACE` set). -/
unsafe def traceOn : Bool := unsafeBaseIO do return (← IO.getEnv "CIR_TRACE").isSome

unsafe def loopHeadImpl (σ : State) : State :=
  if traceOn then dbgTrace (traceLine σ) fun _ => σ else σ

/-- A loop head (the identity, see above). -/
@[implemented_by loopHeadImpl] def loopHead (σ : State) : State := σ

/-- The memory once a region is left with `e`: the stack blocks allocated while it ran die
(`endScope lo`), except when the program ends (`exit`), which ends the lifetime of no
automatic object (C11 7.22.4.4; C++ `exit` destroys none): the exit sequence runs with the
objects of the exiting calls alive, and nothing runs after it. A `longjmp` ends the objects of
the regions it leaves, as the other exits do (C11 6.2.4p6). -/
def Exit.leaveMem : Exit → Mem → Nat → Mem
  | .halt _, m, _ => m
  | .yield _, m, lo | .cond _, m, lo | .brk, m, lo | .cont, m, lo | .ret _, m, lo | .exn _, m, lo
  | .goto _, m, lo | .longjmp _ _, m, lo => m.endScope lo

/-- The memory once a destructor with a body has returned, `args` its arguments: the lifetime of
the object `this` designates ended when the call started (C++ [basic.life]p1), so the object's
members are indeterminate again, as a fresh object's (`Ctx.initVal`), and reading them is
undefined ([basic.life]p7); its storage stays, for a reuse ([basic.life]p8: a placement new into
it, then the destructor at the end of its scope on the new object). A base or member subobject
that an enclosing destructor destroys ends in the same way. The end of a lifetime is no store by
the program: a const object's read-only block ends too. The rest of memory is unchanged. -/
def endLifetime (ctx : Ctx) (args : List Val) (m : Mem) : Mem :=
  match args with
  | .ptr (.loc b path) :: _ =>
    match m.blocks b with
    | some blk =>
      if !blk.alive then m else
      match ctx.typeAt blk.ty path with
      | some (.record n) =>
        match blk.val.set? path (ctx.initVal 32 (.record n)) with
        | some v => m.setBlock b { blk with val := v }
        | none => m
      | _ => m
    | none => m
  | _ => m

mutual

/-- Run the operations of a block until one of them leaves the block. A block
that ends without a terminator ends with the implicit `cir.yield` that MLIR's
printer elides in single-block `cir.scope` / `cir.if` / cleanup regions. -/
def evalOps (ctx : Ctx) (ops : List Op) (σ : State) : Res (Step × State) :=
  match ops with
  | [] => .ok (.exit (.yield []), σ)
  | op :: ops => do
    let (s, σ) ← evalOp ctx op σ
    match s with
    | .next => evalOps ctx ops σ
    | s => pure (s, σ)
partial_fixpoint

/-- Run a region from its entry block with the given block arguments. On exit
the stack blocks allocated meanwhile die (unless the program ends, `Exit.leaveMem`) and the
SSA scope is restored. -/
def evalRegion (ctx : Ctx) (r : Region) (args : List Val) (σ : State) : Res (Exit × State) :=
  match r with
  | .mk [] => .ok (.yield [], σ)
  | .mk (b :: bs) => do
    let (e, σ') ← evalBlock ctx (b :: bs) 0 args σ
    pure (e, { mem := e.leaveMem σ'.mem σ.mem.next, env := σ.env, names := σ.names })
partial_fixpoint

/-- Run block `i` of a region, following `cir.br` jumps. -/
def evalBlock (ctx : Ctx) (blocks : List Block) (i : BlockId) (args : List Val) (σ : State) :
    Res (Exit × State) :=
  match blocks[i]? with
  | none => .ub "branch to a missing block"
  | some (.mk params ops) => do
    let σ ← σ.bindArgs params args
    let (s, σ) ← evalOps ctx ops σ
    match s with
    | .exit (.goto l) =>
      -- a label of this region: continue there; otherwise leave the region
      match labelBlock? l blocks with
      | some j => evalBlock ctx blocks j [] σ
      | none => pure (.goto l, σ)
    | .exit e => pure (e, σ)
    | .jump j vs => evalBlock ctx blocks j vs σ
    | .next => .ub "fell off the end of a block"
partial_fixpoint

/-- Run one operation. -/
def evalOp (ctx : Ctx) (op : Op) (σ : State) : Res (Step × State) :=
  match op with
  | .const .. | .alloca .. | .load .. | .retLoad .. | .store .. | .copy .. | .getMember .. | .getElement ..
  | .ptrStride .. | .ptrDiff .. | .getGlobal .. | .blockAddress .. | .baseClassAddr .. | .derivedClassAddr ..
  | .vtableAddressPoint .. | .vtableGetVptr .. | .vtableGetVirtualFnAddr .. | .vttGlobalAddr .. | .vttParamAddr ..
  | .extractMember .. | .binop .. | .fbinop .. | .fmuladd .. | .shift .. | .unop .. | .fneg ..
  | .fmath .. | .isFpClass .. | .bitCount .. | .isConstant .. | .getBitfield .. | .setBitfield ..
  | .bitOp .. | .rotate .. | .copysign .. | .fminmax .. | .prefetch .. | .allocaN .. | .stackSave ..
  | .stackRestore .. | .vaCopy .. | .allocaConst ..
  | .arithOverflow .. | .iabs .. | .atomicFetch .. | .atomicXchg .. | .atomicCmpXchg .. | .vaStart ..
  | .vaEnd .. | .vaArg .. | .vaArgP .. | .vaBox .. | .vaEndCheck | .vaEndCheckOf .. | .sjNote ..
  | .fail .. | .fitsCheck .. | .alignCheck .. | .unionMember ..
  | .cmp .. | .cast .. | .select .. | .complexCreate .. | .complexPart .. | .complexArith ..
  | .complexEq .. | .vecCreate .. | .vecSplat .. | .vecExtract .. | .vecInsert .. | .vecCmp ..
  | .vecShuffle .. | .vecTernary .. | .x86Intrinsic .. | .allocException .. | .beginCatch .. | .endCatch ..
  | .initCatchParam .. | .assume .. => do
    let σ' ← evalSimple ctx op σ
    pure (.next, σ')
  | .call _ res callee args argTys _ _ => do
    let vs ← args.mapM σ.get
    let sym ← match callee with
      | .direct s => pure s
      | .indirect fv => do
        match ← σ.get fv with
        | .ptr (.fn s) => pure s
        | _ => .ub "indirect call through a non-function pointer"
    let vs ← adjustThis ctx callee sym argTys vs
    let (e, m) ← evalCall ctx sym vs σ.mem
    match e with
    | .ret v => do pure (.next, ← (σ.withMem m).setResults res v.toList)
    | .exn x => pure (.exit (.exn x), σ.withMem m)
    | .halt n => pure (.exit (.halt n), σ.withMem m)
    | .longjmp t v => pure (.exit (.longjmp t v), σ.withMem m)
    | _ => .ub "abnormal function exit"
  | .scope res body => do
    let (e, σ') ← evalRegion ctx body [] σ
    match e with
    | .yield vs => do pure (.next, ← σ'.setResults res vs)
    | .cond _ => .ub "cir.condition outside a loop condition"
    | e => pure (.exit e, σ')
  | .setjmp r env vol svol ok rest => do
    if !ok then .ub "setjmp outside the contexts of C11 7.13.1.1p4" else
    let p ← σ.getPtr env
    -- this invocation's token: a block of the setjmp's region, so live exactly while this op
    -- runs; the buffer holds its id + 1 (`Std.jmpTokenAt`)
    let tok := σ.mem.next
    let (q, tv) ← Res.ofOption "setjmp: invalid jmp_buf" (Std.jmpTokenAt ctx σ.mem p tok)
    let m ← Res.ofOption "setjmp: invalid jmp_buf" (σ.mem.write? q tv)
    -- the snapshot for C11 7.13.2.1p3 (`forgetWrites`): each automatic object of the function with
    -- its value, the volatility of its parts (`svol`; `vol`, the `volatile` accesses through other
    -- pointers known now), and the parts stored into since (none yet: `Op.sjNote` and the library
    -- models record them in each live invocation that the registry, `Std.sjRegister`, lists)
    let sv : List (Nat × List Nat × Bool) := svol.filterMap fun (a, path, isVol) => match σ.env a with
      | some (.ptr (.loc b _)) => some (b, path, isVol)
      | _ => none
    let dv : List (Nat × List Nat) := vol.filterMap fun v => match σ.env v with
      | some (.ptr (.loc b q)) => (Std.memberPath? q).map fun path => (b, path)
      | _ => none
    let snap := σ.names.filterMap fun (_, b) => (m.live? b).map fun blk =>
      Val.agg [.int b, blk.val,
        .arr (sv.filterMap fun (b', path, isVol) => if b' == b && isVol then some (Std.pathVal path) else none),
        .arr (sv.filterMap fun (b', path, isVol) => if b' == b && !isVol then some (Std.pathVal path) else none),
        .arr (dv.filterMap fun (b', path) => if b' == b then some (Std.pathVal path) else none), .arr []]
    let (_, m) := m.alloc .stack (.other "setjmp") (.agg snap)
    let m ← Std.sjRegisterR ctx m tok
    evalOp ctx (.setjmpRun r tok 0 rest) (σ.withMem m)
  | .setjmpRun r tok v rest => do
    let (e, σ') ← evalRegion ctx rest [] (σ.set r (.int v))
    match e with
    | .longjmp t w =>
      -- back to this invocation: `rest` again, `setjmp` returning `w` (1 for 0, C11 7.13.2.1p4)
      if t = tok then
        evalOp ctx (.setjmpRun r tok (if w = 0 then 1 else w) rest) (σ'.withMem (forgetChanged ctx tok σ'.mem))
      else pure (.exit (.longjmp t w), σ')
    | e => pure (.exit e, σ')
  | .cleanupScope k body cl => do
    let (e, σ1) ← evalRegion ctx body [] σ
    match e with
    -- program termination runs no cleanup
    | .halt n => pure (.exit (.halt n), σ1)
    -- neither does a `longjmp`; skipping a destructor that a throw would run is undefined in C++
    | .longjmp t v =>
      if runsCleanup k true && callsDestructor ctx cl then
        .ub "longjmp over the destructor of an automatic object (C++ [csetjmp.syn]p2)"
      else pure (.exit (.longjmp t v), σ1)
    | e =>
      let isEh := match e with | .exn _ => true | _ => false
      if runsCleanup k isEh then do
        let (e2, σ2) ← evalRegion ctx cl [] σ1
        match e2 with
        | .yield [] => finishRegion e σ2
        -- a destructor that calls `exit` ends the program
        | .halt n => pure (.exit (.halt n), σ2)
        | .longjmp t v => pure (.exit (.longjmp t v), σ2)
        | _ => .ub "cleanup region did not complete normally"
      else finishRegion e σ1
  | .ifOp c t el => do
    let b ← σ.getBool c
    let (e, σ') ← evalRegion ctx (if b then t else el) [] σ
    finishRegion e σ'
  | .ternary res c t el => do
    let b ← σ.getBool c
    let (e, σ') ← evalRegion ctx (if b then t else el) [] σ
    match e with
    | .yield vs => do pure (.next, ← σ'.setResults res vs)
    | .cond _ => .ub "cir.condition outside a loop condition"
    | e => pure (.exit e, σ')
  | .forOp _ c b s cl => evalFor ctx c b s cl σ
  | .whileOp _ c b cl => evalWhile ctx c b cl σ
  | .doWhileOp _ b c => evalDo ctx b c σ
  | .switch c _ body => do
    let x ← σ.getInt c
    match body with
    | .mk [.mk [] ops] =>
      match switchStart x ops with
      | none => pure (.next, σ)
      | some i => evalCases ctx (ops.drop i) σ
    | _ => .ub "unsupported switch form"
  | .tryOp body hs unw => do
    let (e, σ1) ← evalRegion ctx body [] σ
    match e with
    | .exn x =>
      match ← findHandler x.typeinfo hs with
      | some h => do
        let (e2, σ2) ← evalRegion ctx h [.tok x] σ1
        finishRegion e2 σ2
      | none =>
        match unw with
        | some u => do
          let (e2, σ2) ← evalRegion ctx u [.tok x] σ1
          finishRegion e2 σ2
        | none => pure (.exit (.exn x), σ1)
    | e => finishRegion e σ1
  | .yield vs => do pure (.exit (.yield (← vs.mapM σ.get)), σ)
  | .condition c => do pure (.exit (.cond (← σ.getBool c)), σ)
  | .brk => pure (.exit .brk, σ)
  | .cont => pure (.exit .cont, σ)
  | .goto l => pure (.exit (.goto l), σ)
  | .indirectGoto t fn => do
    match ← σ.getPtr t with
    | .label f l => if f = fn then pure (.exit (.goto l), σ) else .ub "indirect goto to a label of another function"
    | _ => .ub "indirect goto to a pointer that is not a label address"
  | .label _ => pure (.next, σ)
  | .asmBarrier => pure (.next, σ)
  | .asmTied res ins ties => do
    let vs ← ins.mapM σ.get
    let outs ← ties.mapM fun k => Res.ofOption "asm: tied input out of range" vs[k]?
    match res, outs with
    | none, [] => pure (.next, σ)
    | some r, [v] => pure (.next, σ.set r v)
    | some r, _ :: _ :: _ => pure (.next, σ.set r (.agg outs))
    | _, _ => .ub "asm: result count mismatch"
  | .libc fn args => do
    let vs ← args.mapM σ.get
    let mdl ← match fn with
      | "memcpy" => pure Model.memcpy
      | "memmove" => pure Model.memmove
      | "memset" => pure Model.memset
      -- in the C++ library's own code (`Frontend.tagStdMemCalls`)
      | "memcpy.std" => pure Model.memcpyStd
      | "memmove.std" => pure Model.memmoveStd
      | "memset.std" => pure Model.memsetStd
      | _ => .ub ("unsupported operation cir.libc." ++ fn)
    let (_, m) ← Std.runModel ctx mdl vs σ.mem
    pure (.next, σ.withMem m)
  | .ret none => pure (.exit (.ret none), σ)
  | .ret (some v) => do pure (.exit (.ret (some (← σ.get v))), σ)
  | .br d args => do pure (.jump d (← args.mapM σ.get), σ)
  | .brcond c t ta el ea => do
    if ← σ.getBool c then pure (.jump t (← ta.mapM σ.get), σ)
    else pure (.jump el (← ea.mapM σ.get), σ)
  | .throw obj _ ti =>
    match obj, ti with
    | some o, some t => do pure (.exit (.exn ⟨← σ.getPtr o, t⟩), σ)
    -- `throw;` in a catch handler is parsed as `.resume` of the handler's token
    | _, _ => .ub "rethrow outside a catch handler is not modelled"
  | .resume tok => do
    match ← σ.get tok with
    | .tok x => pure (.exit (.exn x), σ)
    | _ => .ub "resume of a non-token"
  | .trap => .ub "trap"
  | .unreachable => .ub "cir.unreachable executed"
  | .ehTerminate _ => .ub "std::terminate called"
  | .case .. => .ub "cir.case outside cir.switch"
  | .unknown name _ => .ub ("unsupported operation " ++ name)
partial_fixpoint

/-- The cases of a simple-form switch, from the selected one on, with
fallthrough on `cir.yield` and exit on `cir.break`. -/
def evalCases (ctx : Ctx) (ops : List Op) (σ : State) : Res (Step × State) :=
  match ops with
  | [] => .ok (.next, σ)
  | op :: ops =>
    match op with
    | .case _ _ r => do
      let (e, σ) ← evalRegion ctx r [] σ
      match e with
      | .yield [] => evalCases ctx ops σ
      | .brk => pure (.next, σ)
      | .yield _ => .ub "case region yields values"
      | .cond _ => .ub "cir.condition in a case region"
      | e => pure (.exit e, σ)
    | .yield [] => .ok (.next, σ)
    | _ => .ub "unsupported switch body"
partial_fixpoint

/-- The optional per-iteration cleanup region of a loop. -/
def evalIterCleanup (ctx : Ctx) (cl : Option (CleanupKind × Region)) (isEh : Bool) (σ : State) :
    Res State :=
  match cl with
  | none => .ok σ
  | some (k, r) =>
    if runsCleanup k isEh then do
      let (e, σ') ← evalRegion ctx r [] σ
      match e with
      | .yield [] => pure σ'
      | _ => .ub "loop cleanup did not complete normally"
    else .ok σ
partial_fixpoint

/-- `cir.for : cond {c} body {b} step {s} [cleanup]`. -/
def evalFor (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    Res (Step × State) := do
  let (ec, σ) ← evalRegion ctx c [] (loopHead σ)
  match ec with
  | .cond false => do pure (.next, ← evalIterCleanup ctx cl false σ)
  | .cond true => do
    let (eb, σ) ← evalRegion ctx b [] σ
    match eb with
    | .yield [] => evalForStep ctx c b s cl σ
    | .cont => evalForStep ctx c b s cl σ
    | .brk => do pure (.next, ← evalIterCleanup ctx cl false σ)
    | .goto l => do pure (.exit (.goto l), ← evalIterCleanup ctx cl false σ)
    | .ret v => do pure (.exit (.ret v), ← evalIterCleanup ctx cl false σ)
    | .exn x => do pure (.exit (.exn x), ← evalIterCleanup ctx cl true σ)
    | .halt n => pure (.exit (.halt n), σ)
    | .longjmp t v => pure (.exit (.longjmp t v), σ)
    | _ => .ub "abnormal exit from a loop body"
  | .exn x => if cl.isSome then .ub "exception in a loop condition with cleanup" else pure (.exit (.exn x), σ)
  | .halt n => pure (.exit (.halt n), σ)
  | .longjmp t v => pure (.exit (.longjmp t v), σ)
  | _ => .ub "loop condition region did not end with cir.condition"
partial_fixpoint

/-- End of an iteration of a `cir.for`: step region, cleanup, next iteration. -/
def evalForStep (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    Res (Step × State) := do
  let (es, σ) ← evalRegion ctx s [] σ
  match es with
  | .yield [] => do
    let σ ← evalIterCleanup ctx cl false σ
    evalFor ctx c b s cl σ
  | .exn x => do pure (.exit (.exn x), ← evalIterCleanup ctx cl true σ)
  | .halt n => pure (.exit (.halt n), σ)
  | .longjmp t v => pure (.exit (.longjmp t v), σ)
  | _ => .ub "abnormal exit from a loop step region"
partial_fixpoint

/-- `cir.while {c} do {b} [cleanup]`. -/
def evalWhile (ctx : Ctx) (c b : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    Res (Step × State) := do
  let (ec, σ) ← evalRegion ctx c [] (loopHead σ)
  match ec with
  | .cond false => do pure (.next, ← evalIterCleanup ctx cl false σ)
  | .cond true => do
    let (eb, σ) ← evalRegion ctx b [] σ
    match eb with
    | .yield [] => do evalWhile ctx c b cl (← evalIterCleanup ctx cl false σ)
    | .cont => do evalWhile ctx c b cl (← evalIterCleanup ctx cl false σ)
    | .brk => do pure (.next, ← evalIterCleanup ctx cl false σ)
    | .goto l => do pure (.exit (.goto l), ← evalIterCleanup ctx cl false σ)
    | .ret v => do pure (.exit (.ret v), ← evalIterCleanup ctx cl false σ)
    | .exn x => do pure (.exit (.exn x), ← evalIterCleanup ctx cl true σ)
    | .halt n => pure (.exit (.halt n), σ)
    | .longjmp t v => pure (.exit (.longjmp t v), σ)
    | _ => .ub "abnormal exit from a loop body"
  | .exn x => if cl.isSome then .ub "exception in a loop condition with cleanup" else pure (.exit (.exn x), σ)
  | .halt n => pure (.exit (.halt n), σ)
  | .longjmp t v => pure (.exit (.longjmp t v), σ)
  | _ => .ub "loop condition region did not end with cir.condition"
partial_fixpoint

/-- `cir.do {b} while {c}`. -/
def evalDo (ctx : Ctx) (b c : Region) (σ : State) : Res (Step × State) := do
  let (eb, σ) ← evalRegion ctx b [] (loopHead σ)
  match eb with
  | .yield [] => evalDoCond ctx b c σ
  | .cont => evalDoCond ctx b c σ
  | .goto l => pure (.exit (.goto l), σ)
  | .brk => pure (.next, σ)
  | .ret v => pure (.exit (.ret v), σ)
  | .exn x => pure (.exit (.exn x), σ)
  | .halt n => pure (.exit (.halt n), σ)
  | .longjmp t v => pure (.exit (.longjmp t v), σ)
  | _ => .ub "abnormal exit from a loop body"
partial_fixpoint

/-- Condition of a `cir.do` after an iteration. -/
def evalDoCond (ctx : Ctx) (b c : Region) (σ : State) : Res (Step × State) := do
  let (ec, σ) ← evalRegion ctx c [] σ
  match ec with
  | .cond true => evalDo ctx b c σ
  | .cond false => pure (.next, σ)
  | .exn x => pure (.exit (.exn x), σ)
  | .halt n => pure (.exit (.halt n), σ)
  | .longjmp t v => pure (.exit (.longjmp t v), σ)
  | _ => .ub "loop condition region did not end with cir.condition"
partial_fixpoint

/-- Call a function by symbol: its native model if it has one, else its body
in a fresh SSA environment. A destructor's return ends the lifetime of the object it ran on
(`endLifetime`). -/
def evalCall (ctx : Ctx) (sym : String) (args : List Val) (m : Mem) : Res (Exit × Mem) :=
  match ctx.mod.findFunc? sym with
  | none => .ub ("call to an unknown function " ++ sym)
  | some fd =>
    match fd.model with
    | some mdl => Std.runModel ctx mdl args m
    | none =>
      match fd.body with
      | none => .ub ("call to an external function without a model: " ++ sym)
      | some body => do
        let (e, σ) ← evalRegion ctx body args ⟨m, fun _ => none, []⟩
        match e with
        | .ret v =>
          if fd.special = .dtor then pure (.ret v, endLifetime ctx args σ.mem) else pure (.ret v, σ.mem)
        | .exn x =>
          if fd.nothrow then .ub "exception escaped a noexcept function"
          else pure (.exn x, σ.mem)
        | .halt n => pure (.halt n, σ.mem)
        | .longjmp t v => pure (.longjmp t v, σ.mem)
        | _ => .ub "function body exited without cir.return"
partial_fixpoint

end

end CIR
