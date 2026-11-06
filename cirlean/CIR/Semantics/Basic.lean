import CIR.Memory
import CIR.Std.Float

/-!
  Basic semantic objects shared by the interpreter and the library models.
-/

namespace CIR

/-- Result of running something: a value, undefined behaviour (with a
reason), or divergence. Unsupported operations are treated as undefined
behaviour, so a proof never covers an execution that reaches them. -/
inductive Res (α : Type) where
  | ok (a : α)
  | ub (msg : String)
  /-- Non-termination: the bottom element of the flat order used by
  `partial_fixpoint`. -/
  | div
  deriving Inhabited

namespace Res

@[inline] def bind {α β : Type} (x : Res α) (f : α → Res β) : Res β :=
  match x with
  | .ok a => f a
  | .ub m => .ub m
  | .div => .div

instance : Monad Res where
  pure := .ok
  bind := Res.bind

instance instOrderRes {α : Type} : Lean.Order.PartialOrder (Res α) :=
  inferInstanceAs (Lean.Order.PartialOrder (Lean.Order.FlatOrder (Res.div : Res α)))
instance instCCPORes {α : Type} : Lean.Order.CCPO (Res α) :=
  inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder (Res.div : Res α)))
instance instMonoBindRes : Lean.Order.MonoBind Res where
  bind_mono_left h := by
    cases h
    · exact Lean.Order.FlatOrder.rel.bot
    · exact Lean.Order.FlatOrder.rel.refl
  bind_mono_right h := by
    rename_i a _ _
    cases a
    · exact h _
    · exact Lean.Order.FlatOrder.rel.refl
    · exact Lean.Order.FlatOrder.rel.refl

instance : LawfulMonad Res := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl
/-- Not proved by `rfl` on purpose: simp then records the step with a proof
term instead of a definitional change. As a definitional step, the kernel
compares `Res.ok a >>= f` with `f a`, both binds when `f a` is one, by
unfolding both sides; its recursor reduction then evaluates the head of `f a`
(e.g. the range test of a store, `inRange false 64 v`), which for a symbolic
`v` of the form `n + 1` recurses on the literal `2^64` ("deep recursion"). -/
@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → Res β) : (Res.ok a >>= f) = f a := id rfl
@[simp] theorem ub_bind {α β : Type} (m : String) (f : α → Res β) : (Res.ub m >>= f) = .ub m := rfl
@[simp] theorem div_bind {α β : Type} (f : α → Res β) : (Res.div >>= f) = .div := rfl

/-- `x >>= f` succeeds iff `x` succeeds and `f` succeeds on its result. -/
theorem bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [ok_bind, ub_bind, div_bind]

def ofOption {α : Type} (msg : String) : Option α → Res α
  | some a => .ok a
  | none => .ub msg

@[simp] theorem ofOption_some {α : Type} (msg : String) (a : α) : ofOption msg (some a) = .ok a := rfl
@[simp] theorem ofOption_none {α : Type} (msg : String) : ofOption msg (none : Option α) = .ub msg := rfl

/-- A partial operation that is defined under a condition: the condition
becomes a branch of the computation (split by symbolic execution). -/
theorem ofOption_ite {α : Type} (msg : String) (c : Prop) [Decidable c] (a b : Option α) :
    ofOption msg (if c then a else b) = if c then ofOption msg a else ofOption msg b := by
  split <;> rfl

def check (b : Bool) (msg : String) : Res Unit :=
  if b then .ok () else .ub msg

end Res

/-- How a region was left. -/
inductive Exit where
  /-- `cir.yield` (normal completion; carries the yielded values). -/
  | yield (vs : List Val)
  /-- `cir.condition` of a loop condition region. -/
  | cond (b : Bool)
  | brk
  | cont
  /-- `cir.return` -/
  | ret (v : Option Val)
  /-- An exception propagating outwards. -/
  | exn (e : Exn)
  /-- `cir.goto "l"`: leaves regions (running their cleanups) up to the
  region with the block labelled `l`, where execution continues. -/
  | goto (lbl : String)
  /-- Program termination by `exit`, `_Exit` or `quick_exit` with this status
  (C11 7.22.4; a return from `main` ends the program the same way,
  5.1.2.2.3). It leaves every region, loop and call without running cleanups
  (C does not unwind; C++ `exit` destroys no automatic objects), and no
  handler catches it. -/
  | halt (code : Int)
  /-- `longjmp` back to the `setjmp` invocation whose token block is `tok`, which returns `val`
  (C11 7.13.2.1). Like `halt` it leaves regions, loops and calls without running cleanups and no
  handler catches it; the `setjmp` op of that invocation does (`Op.setjmp`). -/
  | longjmp (tok : Nat) (val : Int)
  deriving Inhabited

/-- Machine state: memory and the SSA environment of the current function.
`names` is ghost data (the C++ name and block of each live `cir.alloca`):
specifications and loop invariants use it to refer to local variables by name.
Only the variadic operations read it: `cir.va_start` finds the block of the
variadic arguments there, and whether a `va_list` is one of the function's
own objects decides what `va_arg`, `va_copy` and the check before a return
allow (C11 7.16). -/
structure State where
  mem   : Mem
  env   : VId → Option Val
  names : List (String × Nat) := []

instance : Inhabited State := ⟨⟨default, fun _ => none, []⟩⟩

/-- Read-only context: the module and the block of each global variable. -/
structure Ctx where
  mod   : Module
  gaddr : String → Option Nat

namespace State

def get (σ : State) (v : VId) : Res Val := Res.ofOption "use of undefined SSA value" (σ.env v)

def set (σ : State) (v : VId) (x : Val) : State :=
  { σ with env := upd σ.env v (some x) }

def getInt (σ : State) (v : VId) : Res Int := do
  match ← σ.get v with
  | .int i => pure i
  | _ => .ub "expected an integer"

def getBool (σ : State) (v : VId) : Res Bool := do
  match ← σ.get v with
  | .bool b => pure b
  | _ => .ub "expected a bool"

def getPtr (σ : State) (v : VId) : Res Ptr := do
  match ← σ.get v with
  | .ptr p => pure p
  | _ => .ub "expected a pointer"

/-- Bind block arguments. -/
def bindArgs (σ : State) : List VId → List Val → Res State
  | [], [] => .ok σ
  | v :: vs, x :: xs => (σ.set v x).bindArgs vs xs
  -- more arguments than parameters: the variadic arguments of a call (the
  -- entry block of a variadic function). They go to a fresh block that
  -- `cir.va_start` finds under the name `__va_args`; it is freed when the
  -- function returns.
  | [], x :: xs =>
    let (b, m) := σ.mem.alloc .stack (.array (.int true 64) (x :: xs).length) (.arr (x :: xs))
    .ok { σ with mem := m, names := ("__va_args", b) :: σ.names }
  | _, _ => .ub "block argument count mismatch"

/-- Bind the (optional) result of an op that yields a list of values. -/
def setResults (σ : State) : Option VId → List Val → Res State
  | none, [] => .ok σ
  | some r, [x] => .ok (σ.set r x)
  | _, _ => .ub "result count mismatch"

def withMem (σ : State) (m : Mem) : State := { σ with mem := m }

end State

/-! ### Types -/

def Ty.isScalar : Ty → Bool
  | .int .. | .bool | .float _ | .ptr _ | .vptr => true
  | _ => false

/-- The value is a defined value of the scalar type. -/
def fitsTy : Ty → Val → Bool
  | .int s w, .int v => inRange s w v
  | .bool, .bool _ => true
  | .float _, .float _ => true
  | .ptr _, .ptr _ => true
  | .vptr, .ptr _ => true
  | _, _ => false

/-- The type of the element a path designates in an object of type `t`, as
far as it is known without record declarations (through array elements). -/
def Ty.atPath : Ty → List PathElem → Option Ty
  | t, [] => some t
  | .array e _, .idx _ :: rest => Ty.atPath e rest
  | _, _ => none

/-- A scalar access of type `acc` to an element stored with type `t` reads
the same bits: the same type up to the signedness of an integer (C11 6.5p7:
`char` / `unsigned char`), pointers to anything, the same float kind. -/
def Ty.accessCompatible : Ty → Ty → Bool
  | .int _ w, .int _ w' => w == w'
  | .bool, .bool => true
  | .float k, .float k' => k == k'
  | .ptr _, .ptr _ | .ptr _, .vptr | .vptr, .ptr _ | .vptr, .vptr => true
  | _, _ => false

/-- A scalar access whose type does not match the scalar element it reaches
(as known from the block's type through array elements; record members, whose
types are in the record declarations, are checked by `Ctx.punnedMember` at the
loads and stores of `evalSimple`): memory holds typed elements, not bytes, so
a wider or narrower access (`*(uint32_t *)p` on a `char` array, GNU
`may_alias` word loops) has no meaning here and is undefined, as in the
`memcpy` model. -/
def Mem.punnedAccess (m : Mem) (ty : Ty) (p : Ptr) : Bool :=
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match Ty.atPath blk.ty path with
      | some t => ty.isScalar && t.isScalar && !t.accessCompatible ty
      | none => false
    | none => false
  | _ => false

/-- Typed load: scalars must be defined values of their type. -/
def loadTy (m : Mem) (ty : Ty) (p : Ptr) : Res Val :=
  if m.punnedAccess ty p then .ub "type-punned access (byte-level access not modelled)" else
  match m.read? p with
  | none => .ub "invalid memory read"
  | some v =>
    if ty.isScalar then
      if fitsTy ty v then .ok v
      else match ty, v with
        -- access through the signed or unsigned counterpart of the stored
        -- type (C11 6.5p7; `char` / `unsigned char`): the same bits
        | .int s w, .int x => if inRange (!s) w x then .ok (.int (wrap s w x))
          else .ub "read of an indeterminate or ill-typed value"
        -- bytes that are no value of the type, stored through a character
        -- lvalue (`setByteRepr`; C11 6.2.6.1p5)
        | .bool, .int _ => .ub "read of a bool whose byte is neither 0 nor 1"
        | .float _, .int _ => .ub "read of a floating object holding a NaN bit pattern (not modelled)"
        | _, _ => .ub "read of an indeterminate or ill-typed value"
    else .ok v

/-- Why `Mem.write?` refuses a write: the modification of a const object or a
string literal (C11 6.7.3p6, 6.4.5p7), or another invalid write. -/
def Mem.writeFail (m : Mem) : Ptr → Val → String
  | .loc b p, w => match m.live? b with
    | some blk =>
      if blk.kind = .readonly then
        if (blk.val.get? p).all (Val.initBy · w) then "invalid memory write"
        else "modification of a const object (C11 6.7.3p6, 6.4.5p7)"
      else "invalid memory write"
    | none => "invalid memory write"
  | _, _ => "invalid memory write"

/-- Typed store. -/
def storeTy (m : Mem) (ty : Ty) (p : Ptr) (v : Val) : Res Mem :=
  if m.punnedAccess ty p then .ub "type-punned access (byte-level access not modelled)" else
  if ty.isScalar && !fitsTy ty v then .ub "ill-typed store" else
  match m.write? p v with
  | none => .ub (m.writeFail p v)
  | some m' => .ok m'

/-! ### Integer addresses (C11 6.3.2.3p5, p6, 7.20.1.4p1)

A pointer converts to a flat address, as GCC and Clang have it. Block `b` starts
at `(b + 1) · 2^S` (`Ctx.segBits`: 32 for 8-byte pointers, 20 for 4-byte ones),
so blocks never touch and every start is aligned to `2^S`; a pointer into a block
adds the byte position of its path (`Ctx.absPos?`). A function's address is
`Ctx.fnBase` plus 16 times its position in the module. A pointer whose path has
no byte position (a container element) converts to an address of a range of its
own (`Ctx.otherAddr`), from which no conversion back designates anything. An
integer converts to the pointer into the live block whose range
`[start, start + size]` holds it, at the canonical path of that byte
(`Ctx.canonByte`; `start + size` is the pointer one past the block), or to the
function at it; otherwise to an `.addr` pointer, which compares by its address
and designates no object (GCC: a pointer converted to an integer and back must
reference the same object). Constants of integer type that are addresses
(`#cir.global_view<@f> : !s64i`, the `ptr` of a member function pointer) are
those addresses (`Ctx.symIntAddr?`). -/

/-- The width of a pointer in bits. -/
def Ctx.ptrBits (ctx : Ctx) : Nat := 8 * ctx.mod.ptrBytes

/-- `S`: block `b` starts at address `(b + 1) · 2^S`. -/
def Ctx.segBits (ctx : Ctx) : Nat := if ctx.mod.ptrBytes = 4 then 20 else 32

/-- The blocks `b` with `b + 1 < Ctx.segLimit` have flat addresses (below `Ctx.fnBase`
for 8-byte pointers, below `Ctx.otherAddr`'s range for 4-byte ones). -/
def Ctx.segLimit (ctx : Ctx) : Nat := if ctx.mod.ptrBytes = 4 then 0xE00 else 2 ^ 29

/-- The address of the first function of the module. -/
def Ctx.fnBase (ctx : Ctx) : Nat := if ctx.mod.ptrBytes = 4 then 0xF0000000 else 2 ^ 61

/-- The address of function `f`: `Ctx.fnBase` plus 16 times its position in the module. -/
def Ctx.fnAddr? (ctx : Ctx) (f : String) : Option Nat :=
  (ctx.mod.funcs.findIdx? (·.sym == f)).map (ctx.fnBase + 16 * ·)

/-- The integer of type `(s, w)` that the address `a` converts to: the pointer's bits,
truncated to a narrower type, sign-extended to a wider one (GCC). -/
def Ctx.intOfAddr (ctx : Ctx) (s : Bool) (w : Nat) (a : Int) : Int :=
  let p := wrap false ctx.ptrBits a
  wrap s w (if ctx.ptrBits < w then wrap true ctx.ptrBits p else p)

/-- The address of symbol `sym` as a constant of integer type: a function's
(`Ctx.fnAddr?`), or the start of a global's block (without indices). -/
def Ctx.symIntAddr? (ctx : Ctx) (sym : String) (indices : List Int) : Option Int :=
  match ctx.gaddr sym, indices with
  | some b, [] => if b + 1 < ctx.segLimit then some ((b + 1) * 2 ^ ctx.segBits) else none
  | some _, _ => none
  | none, [] => (ctx.fnAddr? sym).map fun a => (a : Int)
  | none, _ => none

namespace Ctx

def record? (ctx : Ctx) (name : String) : Option RecordDecl := ctx.mod.findRecord? name

/-- Value of a freshly allocated object: fields and elements present,
scalars indeterminate. (Every type constructor has its own equation, so the
unfolding lemmas only apply to known types.) -/
def initVal (ctx : Ctx) : Nat → Ty → Val
  | 0, _ => .undef
  | d + 1, .array e n => .arr (List.replicate n (ctx.initVal d e))
  | d + 1, .record name => match ctx.record? name with
    | some r => .agg (r.members.map fun mt => ctx.initVal d mt.2)
    | none => .undef
  | _ + 1, .int _ _ => .undef
  | _ + 1, .bool => .undef
  | _ + 1, .float _ => .undef
  | _ + 1, .void => .undef
  | _ + 1, .ptr _ => .undef
  | _ + 1, .func _ _ _ => .undef
  | _ + 1, .vptr => .undef
  | _ + 1, .ehToken => .undef
  | _ + 1, .catchToken => .undef
  | _ + 1, .cleanupToken => .undef
  | _ + 1, .other _ => .undef

/-- Zero-initialised value (`#cir.zero`). -/
def zeroVal (ctx : Ctx) : Nat → Ty → Option Val
  | 0, _ => none
  | _ + 1, .int _ _ => some (.int 0)
  | _ + 1, .bool => some (.bool false)
  | _ + 1, .float _ => some (.float 0)
  | _ + 1, .ptr _ => some (.ptr .null)
  | d + 1, .array e n => (ctx.zeroVal d e).map fun z => .arr (List.replicate n z)
  | d + 1, .record name => match ctx.record? name with
    | some r =>
      if r.kind = .union then
        -- zero-initialisation of a union: its first member, zeroed
        match r.members with
        | [] => some (.agg [])
        | (_, t0) :: rest => (ctx.zeroVal d t0).map fun z => .agg (z :: rest.map fun mt => ctx.initVal d mt.2)
      else (r.members.mapM fun mt => ctx.zeroVal d mt.2).map .agg
    | none => none
  | _ + 1, .void => none
  | _ + 1, .func _ _ _ => none
  -- a zero vptr (value-initialization zeroes a polymorphic object before its constructor
  -- stores the vptr): null, so that a dispatch through it is undefined
  | _ + 1, .vptr => some (.ptr .null)
  | _ + 1, .ehToken => none
  | _ + 1, .catchToken => none
  | _ + 1, .cleanupToken => none
  | _ + 1, .other _ => none

/-- Whether objects of the type hold a vptr (also in a member or an element). -/
def holdsVptr (ctx : Ctx) : Nat → Ty → Bool
  | 0, _ => false
  | _ + 1, .vptr => true
  | d + 1, .array e _ => ctx.holdsVptr d e
  | d + 1, .record name => match ctx.record? name with
    | some r => r.members.any fun mt => ctx.holdsVptr d mt.2
    | none => false
  | _ + 1, _ => false

/-- Address of a global or function symbol. -/
def symAddr? (ctx : Ctx) (sym : String) (indices : List Int) : Option Ptr :=
  match ctx.gaddr sym with
  | some b => if indices.all (0 ≤ ·) then some (.loc b (indices.map fun i => .idx i.toNat)) else none
  | none => if indices.isEmpty && (ctx.mod.findFunc? sym).isSome then some (.fn sym) else none

/-- Value of a constant attribute at a type. -/
def constVal (ctx : Ctx) : Nat → Ty → Const → Option Val
  | 0, _, _ => none
  | d + 1, ty, c => match c, ty with
    | .int v, .int s w => if inRange s w v then some (.int v) else none
    | .int v, .bool => some (.bool (v != 0))
    | .bool b, _ => some (.bool b)
    | .blockAddr fn lbl, .ptr _ => some (.ptr (.label fn lbl))
    | .float _ v, .float .single => some (.float (Std.roundSingle v))
    | .float _ v, _ => some (.float v)
    | .null, _ => some (.ptr .null)
    | .ptrInt v, _ => some (.ptr (if v == 0 then .null else .addr v))
    | .zero, t => ctx.zeroVal 32 t
    | .undef, _ => some .undef
    | .poison, _ => some .undef
    | .array cs, .array e _ => (cs.mapM (ctx.constVal d e)).map .arr
    | .str bytes tz, .array (.int s w) _ =>
      some (.arr (bytes.map (fun b => .int (wrap s w b)) ++ List.replicate tz (.int 0)))
    | .record cs, .record name => match ctx.record? name with
      | some r =>
        if r.members.length = cs.length then
          ((r.members.zip cs).mapM fun mc => ctx.constVal d mc.1.2 mc.2).map .agg
        else none
      | none => none
    | .globalAddr sym idx, .int s w =>
      -- of integer type (the `ptr` of a member function pointer): the address
      match ctx.symIntAddr? sym idx with
      | some a => some (.int (ctx.intOfAddr s w a))
      | none => (ctx.symAddr? sym idx).map .ptr
    | .globalAddr sym idx, ty =>
      -- `#cir.global_view<@arr> : !cir.ptr<T>` of an array global `T[n]`
      -- (string literals as `char *`): the address of its first element
      let gty : Option Ty := (ctx.mod.findGlobal? sym).map (·.ty)
      let decay : Bool := match idx, ty, gty with
        | [], Ty.ptr t, some (Ty.array e _) => Ty.beq t e
        | _, _, _ => false
      (ctx.symAddr? sym (if decay then [0] else idx)).map .ptr
    | .vtableAddr vt i k, _ =>
      if (ctx.mod.findGlobal? vt).isSome then some (.ptr (.vtable vt i k)) else none
    | _, _ => none

end Ctx

/-! ### Integer arithmetic -/

/-- Integer binary operation on values of type `int<s, w>`. Overflow is
undefined under `nsw` (signed) / `nuw` (unsigned) and wraps otherwise;
division truncates toward zero. -/
def evalBinop (k : BinOp) (nsw nuw s : Bool) (w : Nat) (x y : Int) : Res Int :=
  let chk (z : Int) : Res Int :=
    if inRange s w z then .ok z
    else if (s && nsw) || (!s && nuw) then .ub "integer overflow"
    else .ok (wrap s w z)
  match k with
  | .add => chk (x + y)
  | .sub => chk (x - y)
  | .mul => chk (x * y)
  | .div =>
    if y = 0 then .ub "division by zero"
    else if s && x = intMin s w && y = -1 then .ub "division overflow"
    else .ok (Int.tdiv x y)
  | .rem =>
    if y = 0 then .ub "remainder by zero"
    else if s && x = intMin s w && y = -1 then .ub "remainder overflow"
    else .ok (Int.tmod x y)
  | .and => .ok (bitwise s w (· &&& ·) x y)
  | .or => .ok (bitwise s w (· ||| ·) x y)
  | .xor => .ok (bitwise s w (· ^^^ ·) x y)
  | .max => .ok (max x y)
  | .min => .ok (min x y)

/-- Shifts. Left shifts follow C (a negative operand or an overflowing
result is undefined), which is stricter than C++20 and hence sound for both;
right shifts are arithmetic. -/
def evalShift (left s : Bool) (w : Nat) (x n : Int) : Res Int :=
  if n < 0 ∨ w ≤ n then .ub "shift amount out of range"
  else if left then
    let z := x * 2 ^ n.toNat
    if s then
      if x < 0 then .ub "left shift of a negative value"
      else if inRange s w z then .ok z else .ub "left shift overflow"
    else .ok (wrap false w z)
  else .ok (x / 2 ^ n.toNat)

def evalUnop (k : UnOp) (nsw s : Bool) (w : Nat) (x : Int) : Res Int :=
  match k with
  | .inc => evalBinop .add nsw false s w x 1
  | .dec => evalBinop .sub nsw false s w x 1
  | .minus => evalBinop .sub nsw false s w 0 x
  | .not => .ok (wrap s w (-x - 1))

def cmpInt (k : CmpKind) (x y : Int) : Option Bool :=
  match k with
  | .lt => some (decide (x < y))
  | .le => some (decide (x ≤ y))
  | .gt => some (decide (y < x))
  | .ge => some (decide (y ≤ x))
  | .eq => some (decide (x = y))
  | .ne => some (decide (x ≠ y))
  | _ => none

/-- IEEE comparison: of the exact values (`-0 = +0`); every comparison with
NaN is false except `ne` and `uno` (unordered). -/
def cmpFloat (k : CmpKind) (x y : Float) : Bool :=
  match Std.fkey (Std.decodeF x), Std.fkey (Std.decodeF y) with
  | some a, some b =>
    match k with
    | .lt => decide (a < b)
    | .le => decide (a ≤ b)
    | .gt => decide (b < a)
    | .ge => decide (b ≤ a)
    | .eq => a == b
    | .ne => a != b
    | .one => a != b
    | .uno => false
  | _, _ => k == .ne || k == .uno

/-- Size and alignment (x86-64; pointers as in the module's data layout,
`Module.ptrBytes`). Records are laid out from their member list, which already
contains explicit padding members. -/
-- one equation per type constructor, so that `simp` unfolds it only on
-- known types (an equation `sizeAlign (d+1) ty = match ty with …` would also
-- rewrite under the binder of `step` and blow up)
def Ctx.sizeAlign (ctx : Ctx) : Nat → Ty → Option (Nat × Nat)
  | 0, _ => none
  | _ + 1, .int _ w => let n := (w + 7) / 8; some (n, if n ≥ 16 then 16 else n)
  | _ + 1, .bool => some (1, 1)
  | _ + 1, .float .single => some (4, 4)
  | _ + 1, .float .double => some (8, 8)
  | _ + 1, .float .fp16 => some (2, 2)
  | _ + 1, .float .bf16 => some (2, 2)
  | _ + 1, .float .fp80 => some (16, 16)
  | _ + 1, .float .fp128 => some (16, 16)
  | _ + 1, .float .longDouble => some (16, 16)
  | _ + 1, .ptr _ => some (ctx.mod.ptrBytes, ctx.mod.ptrBytes)
  | _ + 1, .vptr => some (ctx.mod.ptrBytes, ctx.mod.ptrBytes)
  | d + 1, .array e n => (ctx.sizeAlign d e).map fun (s, a) => (n * s, a)
  | d + 1, .record name => match ctx.record? name with
    | some r =>
      match r.padding with
      | [] =>
        let step (acc : Option (Nat × Nat)) (t : Ty) : Option (Nat × Nat) :=
          match acc, ctx.sizeAlign d t with
          | some (off, al), some (s, a) =>
            if r.kind = .union then some (max off s, max al a)
            else if r.packed then some (off + s, 1)
            else let off' := (off + a - 1) / a * a; some (off' + s, max al a)
          | _, _ => none
        -- a vector member is aligned as `RecordDecl.vecAligns` gives
        let stepV (acc : Option (Nat × Nat)) (m : (MemberKind × Ty) × Nat) : Option (Nat × Nat) :=
          match acc, ctx.sizeAlign d m.1.2 with
          | some (off, al), some (s, a) =>
            let a := max a ((r.vecAligns.lookup m.2).getD 1)
            if r.kind = .union then some (max off s, max al a)
            else if r.packed then some (off + s, 1)
            else let off' := (off + a - 1) / a * a; some (off' + s, max al a)
          | _, _ => none
        let fold := if r.vecAligns.isEmpty then (r.members.map (·.2)).foldl step (some (0, 1))
          else r.members.zipIdx.foldl stepV (some (0, 1))
        fold.map fun (s, a) => if r.packed then (s, 1) else ((s + a - 1) / a * a, a)
      | pad =>
        -- a union with tail padding, as CIR lays it out: its most aligned
        -- member (the larger one of equal alignment), then the padding (a
        -- bit-field's storage unit can be less aligned than its declared type)
        let big (acc : Option (Nat × Nat)) (t : Ty) : Option (Nat × Nat) :=
          match acc, ctx.sizeAlign d t with
          | some (s, a), some (s', a') => some (if a < a' ∨ (a = a' ∧ s < s') then (s', a') else (s, a))
          | _, _ => none
        match (r.members.map (·.2)).foldl big (some (0, 1)), pad.mapM (ctx.sizeAlign d) with
        | some (s, a), some ps => some (s + (ps.map (·.1)).sum, if r.packed then 1 else a)
        | _, _ => none
    | none => none
  | _ + 1, .void => none
  | _ + 1, .func _ _ _ => none
  | _ + 1, .ehToken => none
  | _ + 1, .catchToken => none
  | _ + 1, .cleanupToken => none
  | _ + 1, .other _ => none

/-- The type of the subobject at `path` in an object of type `ty`: array
elements and record members (padding included). -/
def Ctx.typeAt (ctx : Ctx) : Ty → List PathElem → Option Ty
  | ty, [] => some ty
  | .array e _, .idx _ :: p => ctx.typeAt e p
  | .record name, .idx k :: p =>
    match ctx.record? name with
    | some r => match r.members[k]? with
      | some (_, t) => ctx.typeAt t p
      | none => none
    | none => none
  | _, _ => none

/-- Byte offsets of the members of a (non-union) record. -/
def Ctx.memberOffsets (ctx : Ctx) (name : String) : Option (List Nat) :=
  match ctx.record? name with
  | some r =>
    let step (acc : Option (Nat × List Nat)) (t : Ty) : Option (Nat × List Nat) :=
      match acc, ctx.sizeAlign 32 t with
      | some (off, offs), some (s, a) =>
        let off' := if r.packed then off else (off + a - 1) / a * a
        some (off' + s, offs ++ [off'])
      | _, _ => none
    -- a vector member is aligned as `RecordDecl.vecAligns` gives
    let stepV (acc : Option (Nat × List Nat)) (m : (MemberKind × Ty) × Nat) : Option (Nat × List Nat) :=
      match acc, ctx.sizeAlign 32 m.1.2 with
      | some (off, offs), some (s, a) =>
        let a := max a ((r.vecAligns.lookup m.2).getD 1)
        let off' := if r.packed then off else (off + a - 1) / a * a
        some (off' + s, offs ++ [off'])
      | _, _ => none
    if r.vecAligns.isEmpty then ((r.members.map (·.2)).foldl step (some (0, []))).map (·.2)
    else (r.members.zipIdx.foldl stepV (some (0, []))).map (·.2)
  | none => none

/-- `Mem.punnedAccess` for record members: a scalar access, along a path that
goes through a record, whose type does not match the scalar member (or
element of a member) it reaches, its type from the record declarations
(`Ctx.typeAt`). A path through array elements only is `Mem.punnedAccess`'s,
which `loadTy` / `storeTy` check (the same `Ty.atPath`, so symbolic execution
evaluates it once). A union member is a member: a read through its own
pointer has its type (the reinterpretation of another member's scalars is
`Ctx.unionView?`'s and `Ctx.unionActivate?`'s). -/
def Ctx.punnedMember (ctx : Ctx) (m : Mem) (ty : Ty) (p : Ptr) : Bool :=
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match Ty.atPath blk.ty path with
      | some _ => false
      | none =>
        match ctx.typeAt blk.ty path with
        | some t => ty.isScalar && t.isScalar && !t.accessCompatible ty
        | none => false
    | none => false
  | _ => false

/-! ### Bytes of objects, and the scalars aggregates start with (C11 6.5p7, 6.2.6.1p4, 6.7.2.1p15-16) -/

/-- A character type (`char`, `signed char`, `unsigned char`, `std::byte`):
its accesses may read and write the bytes of any object (C11 6.5p7). -/
def Ty.isChar : Ty → Bool
  | .int _ w => w == 8
  | _ => false

/-- `void`, whose pointers count bytes in arithmetic (GNU C: `sizeof (void)` is 1;
Clang adjusts `this` so for a call through a member function pointer). -/
def Ty.isVoid : Ty → Bool
  | .void => true
  | _ => false

/-- A scalar whose bytes a character access reads and writes: an integer
wider than a byte, a floating type, `bool`. -/
def Ty.hasBytes : Ty → Bool
  | .int _ w => 8 < w
  | .float _ => true
  | .bool => true
  | _ => false

/-- An array or a record (unions included). -/
def Ty.isAggregate : Ty → Bool
  | .array _ _ => true
  | .record _ => true
  | _ => false

/-- The member of a (non-union) record whose bytes contain byte `r`, from
member `j` (offsets `os`) on: its index, type and offset. -/
def Ctx.memberAt (ctx : Ctx) : Nat → List (MemberKind × Ty) → List Nat → Nat → Option (Nat × Ty × Nat)
  | j, (_, t) :: ms, o :: os, r =>
    match ctx.sizeAlign 32 t with
    | some (s, _) => if o ≤ r ∧ r < o + s then some (j, t, o) else ctx.memberAt (j + 1) ms os r
    | none => none
  | _, _, _, _ => none

/-- Record `n` is class `b`, or the `b.base` layout CIR uses for a base
subobject of class `b` (no tail padding). -/
def isClassOrBase (n b : String) : Bool := n == b || n == b ++ ".base"

/-- A record without data members (an empty class). -/
def Ctx.isEmptyRecord (ctx : Ctx) (n : String) : Bool :=
  match ctx.record? n with
  | some r => r.members.all fun mt => mt.1 == .pad || mt.1 == .empty
  | none => false

/-- The scalar that byte `k` of the object of type `t` and value `v` at `path`
falls in: array elements, record members by their offsets, and for a union its
active member (the first that holds a value, else member 0; C11 6.7.2.1p16).
`some (path', t', k')`: byte `k'` of the scalar of type `t'` at `path'`. For
`k = 0`, the scalar the object starts with (6.7.2.1p15: a pointer to a
structure points to its initial member; an array's to its first element). -/
def Ctx.scalarIn (ctx : Ctx) : Nat → Ty → Val → List PathElem → Nat → Option (List PathElem × Ty × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, t, v, path, k =>
    if t.isScalar then some (path, t, k) else
    match t, v with
    | .array e n, .arr xs =>
      match ctx.sizeAlign 32 e with
      | some (s, _) =>
        if s = 0 ∨ n ≤ k / s then none else
        match xs[k / s]? with
        | some x => ctx.scalarIn fuel e x (path ++ [.idx (k / s)]) (k % s)
        | none => none
      | none => none
    | .record name, .agg vs =>
      match ctx.record? name with
      | some rd =>
        if rd.kind = .union then
          let j := (vs.findIdx? Val.holds).getD 0
          match rd.members[j]?, vs[j]? with
          | some (_, tj), some x =>
            match ctx.sizeAlign 32 tj with
            | some (s, _) => if k < s then ctx.scalarIn fuel tj x (path ++ [.idx j]) k else none
            | none => none
          | _, _ => none
        else
          match ctx.memberOffsets name with
          | some offs =>
            match ctx.memberAt 0 rd.members offs k with
            | some (j, tj, o) =>
              match vs[j]? with
              | some x => ctx.scalarIn fuel tj x (path ++ [.idx j]) (k - o)
              | none => none
            | none => none
          | none => none
      | none => none
    | _, _ => none

/-- The path of the subobject of record type `n` that the object of type `t` at
`path` starts with (C11 6.7.2.1p15-16): the object itself, its first member, an
array's first element, a union's member. -/
def Ctx.recordAt (ctx : Ctx) : Nat → Ty → List PathElem → String → Option (List PathElem)
  | 0, _, _, _ => none
  | fuel + 1, t, path, n =>
    match t with
    | .record n' =>
      if isClassOrBase n' n || isClassOrBase n n' then some path else
      match ctx.record? n' with
      | some rd =>
        if rd.kind = .union then
          rd.members.zipIdx.findSome? fun ((_, tj), j) => ctx.recordAt fuel tj (path ++ [.idx j]) n
        else
          match rd.members.head? with
          | some (_, t0) => ctx.recordAt fuel t0 (path ++ [.idx 0]) n
          | none => none
      | none => none
    | .array e len => if 0 < len then ctx.recordAt fuel e (path ++ [.idx 0]) n else none
    | _ => none

/-- The nearest object of record type `n` that the object at `rest` below the
object of type `t` at `pre` starts, through initial members (a structure's
first member, an array's first element, a union's members); `cand`: the last
such object above, as the walk goes down. -/
def Ctx.enclosingIn (ctx : Ctx) (n : String) : Ty → List PathElem → List PathElem →
    Option (List PathElem) → Option (List PathElem)
  | _, [], _, cand => cand
  | .array e _, .idx i :: rest, pre, cand =>
    ctx.enclosingIn n e rest (pre ++ [.idx i]) (if i = 0 then cand else none)
  | .record n', .idx i :: rest, pre, cand =>
    let cand := if isClassOrBase n' n || isClassOrBase n n' then some pre else cand
    match ctx.record? n' with
    | some rd =>
      match rd.members[i]? with
      | some (_, ti) =>
        ctx.enclosingIn n ti rest (pre ++ [.idx i]) (if rd.kind = .union ∨ i = 0 then cand else none)
      | none => none
    | none => none
  | _, _, _, _ => none

/-- The object that a pointer to the object at `path` designates once converted
to a pointer to record type `n` (C11 6.7.2.1p15-16: a pointer to a structure,
suitably converted, points to its initial member, and conversely; a pointer to
a union to each of its members, and conversely): that object when it has the
type, else the subobject of the type it starts with (`Ctx.recordAt`), else the
nearest enclosing object of the type that it starts (`Ctx.enclosingIn`), else
the object at `path`. -/
def Ctx.convertPath (ctx : Ctx) (bty : Ty) (path : List PathElem) (n : String) : List PathElem :=
  match ctx.typeAt bty path with
  | some (.record n') =>
    if isClassOrBase n' n || isClassOrBase n n' then path
    else match ctx.recordAt 32 (.record n') path n with
      | some p => p
      | none => (ctx.enclosingIn n bty path [] none).getD path
  | some t =>
    match ctx.recordAt 32 t path n with
    | some p => p
    | none => (ctx.enclosingIn n bty path [] none).getD path
  | none => path

/-- The value has the structure of its type: an `agg` for a record, an `arr`
for an array, a scalar value for a scalar type (the library models keep other
values in some objects: `opt`, `vec`). -/
def Val.shaped : Ty → Val → Bool
  | .record _, .agg _ => true
  | .array _ _, .arr _ => true
  | t, _ => t.isScalar

/-- Where an access reaches memory when it is not the ordinary access at its
pointer's path (`Ctx.reachIn`). -/
inductive Reach where
  /-- Byte `k` of the scalar of type `t` at `path`: a character access
  (C11 6.5p7, 6.2.6.1p4). -/
  | byte (path : List PathElem) (t : Ty) (k : Nat)
  /-- The object at `path`: the scalar, or the record of the access's type,
  that the pointer's object starts with (6.7.2.1p15-16). -/
  | obj (path : List PathElem)
  /-- No object of the access's type there: type-punned (6.5p7). -/
  | punned
  /-- A value of type `t` read or written member by member, or element by element, over
  the object at `path`: a record over a scalar or an array that does not start with one
  (6.5p7: an aggregate type that includes the types of the objects among its members), a
  vector (an array type) over an object of another type, such as the elements of a larger
  array. -/
  | spread (path : List PathElem) (t : Ty)
  /-- An object the module only declares (defined in another translation unit
  or a library, `Module.initMem`): its value is not known, no access is
  defined. -/
  | external
  deriving Inhabited

/-- A scalar access of type `ty`, through a pointer that is a byte view at byte
`k0` (0: none), to byte `k` of the scalar of type `t` at `path`: a character
access to its byte; else, through no byte view, the scalar itself, of a
compatible type, at its first byte; else type-punned (a byte view is valid only
as a pointer for other types than the character types). -/
def reachScalar (ty : Ty) (k0 : Nat) : List PathElem × Ty × Nat → Reach
  | (path, t, k) =>
    if ty.isChar then
      if t.isChar then (if k = 0 then .obj path else .punned) else .byte path t k
    else if k0 = 0 && k = 0 && t.accessCompatible ty then .obj path else .punned

/-- `Ctx.reachIn` for a scalar access of type `ty` that is not the ordinary
access: byte `k` of the object of type `t` at `path` in the block `blk` falls in
the scalar `Ctx.scalarIn` finds (for an object whose value has its type's
structure, `Val.shaped`), which `reachScalar` classifies. -/
def Ctx.reachScalarAt (ctx : Ctx) (blk : MemBlock) (ty : Ty) (path : List PathElem) (k : Nat) (t : Ty) :
    Option Reach :=
  if t.isScalar || t.isAggregate then
    match (if blk.alive then blk.val.get? path else none) with
    | some v =>
      if Val.shaped t v then some ((ctx.scalarIn 32 t v path k).elim .punned (reachScalar ty k))
      else none
    | none => none
  else none

/-- `Ctx.reachIn` for an access of record type `n` to the object of type `t` at
`path` in the block `blk`, of another record type, an array or a scalar: the
subobject of type `n` it starts with (`Ctx.recordAt`); else, at a record,
type-punned (6.5p7), at an array or a scalar member by member (`Reach.spread`:
6.5p7's aggregate clause). -/
def Ctx.reachRecordAt (ctx : Ctx) (blk : MemBlock) (path : List PathElem) (n : String) (t : Ty) :
    Option Reach :=
  match t, (if blk.alive then blk.val.get? path else none) with
  | .record _, some (.agg _) => some ((ctx.recordAt 32 t path n).elim .punned .obj)
  | .array _ _, some (.arr _) => some ((ctx.recordAt 32 t path n).elim (.spread path (.record n)) .obj)
  | t, some _ => if t.isScalar then some (.spread path (.record n)) else none
  | _, _ => none

/-- The path of an access before byte `k` of a byte view (`k = 0` for no byte
view), and `k`. -/
def splitByte (path : List PathElem) : List PathElem × Nat :=
  match splitLast path with
  | some (pre, .byte k) => (pre, k)
  | _ => (path, 0)

/-- `Ctx.reachIn`'s ordinary access, from the type `t` of the object at the
path (before byte `k` of a byte view): a scalar access to a scalar (but a
character access to a wider scalar, a byte of it), a record access to a record
of a related type or to an empty record, an array access to an object of its
type, other accesses. -/
def Ctx.reachNone (ctx : Ctx) (ty : Ty) (k : Nat) (t : Ty) : Bool :=
  if ty.isScalar then t.isScalar && k == 0 && !(ty.isChar && t.hasBytes)
  else match ty, t with
    | .record n, .record n' => k != 0 || isClassOrBase n n' || isClassOrBase n' n || ctx.isEmptyRecord n
    | .record n, t => k != 0 || ctx.isEmptyRecord n || !(t.isScalar || t.isAggregate)
    | .array _ _, t => (k == 0 && t == ty) || !(t.isScalar || t.isAggregate)
    | _, _ => true

/-- `Ctx.reachIn` is the ordinary access, by the type of the object at the path
(`Ctx.reachNone`; at a path the block's type does not give, a scalar access):
not at a global the module only declares. -/
def Ctx.reachTypeNone (ctx : Ctx) (blk : MemBlock) (ty : Ty) (path : List PathElem) : Bool :=
  (blk.alive || blk.kind != .external) &&
  match ctx.typeAt blk.ty (splitByte path).1 with
  | some t => ctx.reachNone ty (splitByte path).2 t
  | none => !ty.isAggregate

/-- `Ctx.reachIn` when the access is not the ordinary one by the type alone: a
global the module only declares, the scalar, record or array access at the
object of type `t` at the path, an aggregate access over a value the block's
type does not give. -/
def Ctx.reachSlow (ctx : Ctx) (blk : MemBlock) (ty : Ty) (path : List PathElem) : Option Reach :=
  if !blk.alive && blk.kind == .external then some .external else
  match ctx.typeAt blk.ty (splitByte path).1 with
  | some t =>
    if ty.isScalar then ctx.reachScalarAt blk ty (splitByte path).1 (splitByte path).2 t
    else match ty with
      | .record n => ctx.reachRecordAt blk (splitByte path).1 n t
      | .array _ _ => some (.spread path ty)
      | _ => none
  | none =>
    if ty.isAggregate then
      match (if blk.alive then blk.val.get? (splitByte path).1 else none) with
      | some v => if (splitByte path).2 == 0 && Val.shaped ty v then none else some .punned
      | none => none
    else none

/-- How an access of type `ty` along `path` reaches the block `blk`. `none`:
the ordinary access at `path` (`loadTy` / `storeTy`, `Ctx.punnedMember`). A
scalar access through a byte view (`.byte k` last), a character access to a
`Ty.hasBytes` scalar, and a scalar access at the path of an array or a record
reach the scalar that the byte falls in (`Ctx.scalarIn`): an aggregate's
initial scalar (C11 6.7.2.1p15-16), so that a scalar is never stored over an
aggregate; through a byte view only a character access is defined
(`reachScalar`). An access of record type at an object of another record type
reaches the subobject of its type that the object starts with
(`Ctx.recordAt`), else it is type-punned (6.5p7; C++ [basic.lval]p11); at an
array whose first element (recursively) has its type, it reaches that element
(a pointer to an array object used as a pointer to its element type). An access
of an array type (a vector, `!cir.vector<N x T>` being `T[N]`) at an object of
another type, or through a byte view, reads or writes element by element the
objects at its bytes (`Reach.spread`): `*(v4sf *)&a[i]` for a `float` array `a`
is `a[i]` to `a[i + 3]`. At an object whose type the block's does not give (an
element of a library container), an access of an aggregate type is the ordinary
one only over a value of its shape. The values that library models keep in
objects (`opt`, `vec`: not `Val.shaped`) are accessed as they are. -/
def Ctx.reachIn (ctx : Ctx) (blk : MemBlock) (ty : Ty) (path : List PathElem) : Option Reach :=
  if ctx.reachTypeNone blk ty path then none else ctx.reachSlow blk ty path

/-- `Ctx.reachIn` is the ordinary access by the type of the object at the path. -/
theorem Ctx.reachIn_of_typeNone {ctx : Ctx} {blk : MemBlock} {ty : Ty} {path : List PathElem}
    (h : ctx.reachTypeNone blk ty path = true) : ctx.reachIn blk ty path = none := by
  simp only [Ctx.reachIn, h, if_true]

/-- `Ctx.reachIn` on the block a pointer designates. -/
def Ctx.reach? (ctx : Ctx) (m : Mem) (ty : Ty) : Ptr → Option (Nat × Reach)
  | .loc b path =>
    match m.blocks b with
    | some blk => (ctx.reachIn blk ty path).map fun r => (b, r)
    | none => none
  | _ => none

/-- Byte `k` (little-endian) of a value of scalar type `t`: integers in two's
complement, `bool` as 0 / 1, floats by their IEEE bit pattern, and the bytes a
`bool` or floating object keeps as an `.int` when they are no value of its
type (`setByteRepr`). `none` where the bytes are not modelled: a NaN `Float`
(`Float` keeps a single NaN, without sign or payload), an indeterminate value,
another kind of value, a byte outside the object. -/
def byteOf (t : Ty) (v : Val) (k : Nat) : Option Nat :=
  match t, v with
  | .int _ w, .int x => if 8 * k < w then some ((wrap false w x).toNat / 2 ^ (8 * k) % 256) else none
  | .bool, .bool c => if k = 0 then some (if c then 1 else 0) else none
  | .float .double, .float f =>
    if k < 8 ∧ Std.decodeF f ≠ .nan then some (f.toBits.toNat / 2 ^ (8 * k) % 256) else none
  | .float .single, .float f =>
    if k < 4 ∧ Std.decodeF f ≠ .nan then some (Std.singleToBits f / 2 ^ (8 * k) % 256) else none
  | .bool, .int u => if k = 0 then some (u.toNat % 256) else none
  | .float .double, .int u => if k < 8 then some (u.toNat / 2 ^ (8 * k) % 256) else none
  | .float .single, .int u => if k < 4 then some (u.toNat / 2 ^ (8 * k) % 256) else none
  | _, _ => none

/-- The value of scalar type `t` with byte `k` replaced by `c` (`c < 256`):
`none` where `byteOf` is, for a `bool` byte other than 0 / 1 (a trap
representation), and for a floating result whose bit pattern is a NaN. -/
def setByte (t : Ty) (v : Val) (k c : Nat) : Option Val :=
  match t, v with
  | .int s w, .int x =>
    if 8 * k < w then
      let u := (wrap false w x).toNat
      some (.int (wrap s w (u - u / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + c * 2 ^ (8 * k) : Nat)))
    else none
  | .bool, .bool _ => if k = 0 ∧ c ≤ 1 then some (.bool (c == 1)) else none
  | .float .double, .float f =>
    if k < 8 ∧ Std.decodeF f ≠ .nan then
      let u := f.toBits.toNat
      let u' := u - u / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + c * 2 ^ (8 * k)
      if Std.decodeBits u' = .nan then none else some (.float (Float.ofBits u'.toUInt64))
    else none
  | .float .single, .float f =>
    if k < 4 ∧ Std.decodeF f ≠ .nan then
      let u := Std.singleToBits f
      let g := Std.singleOfBits (u - u / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + c * 2 ^ (8 * k))
      if Std.decodeF g = .nan then none else some (.float g)
    else none
  | _, _ => none

/-- The value of an object of scalar type `t` after a character store of `c`
into its byte `k` (C11 6.2.6.1p4-5): `setByte`'s, but a `bool` or floating
object whose bytes are then no value of its type (a `bool` byte other than
0 / 1, a NaN's bit pattern) keeps them, as their unsigned number in an `.int`:
its character reads give them (`byteOf`), its reads as `t` are undefined, for
a NaN not modelled (`loadValOf`). -/
def setByteRepr (t : Ty) (v : Val) (k c : Nat) : Option Val :=
  let put (u : Nat) : Nat := u - u / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + c * 2 ^ (8 * k)
  let dbl (u : Nat) : Val :=
    if Std.decodeBits u = .nan then .int u else .float (Float.ofBits u.toUInt64)
  let sgl (u : Nat) : Val :=
    let g := Std.singleOfBits u
    if Std.decodeF g = .nan then .int u else .float g
  match t, v with
  | .bool, .bool _ | .bool, .int _ =>
    if k = 0 then some (if c ≤ 1 then .bool (c == 1) else .int c) else none
  | .float .double, .float f =>
    if k < 8 ∧ Std.decodeF f ≠ .nan then some (dbl (put f.toBits.toNat)) else none
  | .float .double, .int u => if k < 8 then some (dbl (put u.toNat)) else none
  | .float .single, .float f =>
    if k < 4 ∧ Std.decodeF f ≠ .nan then some (sgl (put (Std.singleToBits f))) else none
  | .float .single, .int u => if k < 4 then some (sgl (put u.toNat)) else none
  | _, _ => setByte t v k c

/-! ### Union members

The member of a union last stored is its active one, whichever pointer the
store went through (C11 6.5.2.3p3, footnote 95): its value holds the stored
bytes, and the other members are indeterminate (`.undef`). A member that is
read, or stored into, while indeterminate takes the scalars the active member
stores at the same offsets with the same sizes (the same value for the same
type, else `punScalar`): same-size members, the common initial sequence of
structs (6.5.2.3p6), a bit-field unit after a member of its width. Its other
scalars are composed from the active member's bytes (`Ctx.composeAt`,
little-endian as character accesses read them, 6.5p7: a narrower member or
array element, the halves of a wider scalar, a scalar over several bytes stored
through a character array member); a byte the active member does not hold stays
indeterminate. C++ modules read unions the same way, as GCC and Clang document
(ISO C++ leaves reading another member undefined, [class.union], [basic.life]p7,
the common initial sequence aside). -/

/-- A scalar stored as type `src`, read as type `dst` of the same size (C11
6.5.2.3, footnote 95: the stored bytes are reinterpreted): integers of the same
width (wrapped to the target's signedness), an integer and a binary64 or
binary32 float of its width (the bit pattern), floats of the same kind, a
`bool` and a character-sized integer (0 / 1; another byte read as `bool` is
kept as an `.int`, as `setByteRepr` keeps it, and reading it is undefined);
the bytes a `bool` or floating object keeps as an `.int` (`setByteRepr`: a
trap byte, a NaN's bit pattern) read as an integer of its size; also arrays of
one integer type and length, such as bit-field storage units
`!cir.array<!u8i x N>` (the same elements). `none` otherwise: pointers
(provenance), other sizes and formats, other non-scalars, and NaN bit patterns
from an integer or a `Float` (`Float` has a single NaN, without sign or
payload). -/
def punScalar (src dst : Ty) (v : Val) : Option Val :=
  match src, dst, v with
  | .int _ w, .int s w', .int x => if w = w' then some (.int (wrap s w x)) else none
  | .array (.int s w) n, .array (.int s' w') n', .arr xs =>
    if s = s' ∧ w = w' ∧ n = n' then some (.arr xs) else none
  | .int _ w, .float k, .int x =>
    match w, k with
    | 64, .double =>
      let b := (wrap false 64 x).toNat
      if Std.decodeBits b = .nan then none else some (.float (Float.ofBits b.toUInt64))
    | 32, .single =>
      let f := Std.singleOfBits (wrap false 32 x).toNat
      if Std.decodeF f = .nan then none else some (.float f)
    | _, _ => none
  | .float k, .int s w, .float f =>
    if Std.decodeF f = .nan then none else
    match k, w with
    | .double, 64 => some (.int (wrap s 64 f.toBits.toNat))
    | .single, 32 => some (.int (wrap s 32 (Std.singleToBits f)))
    | _, _ => none
  | .float k, .int s w, .int u =>
    match k, w with
    | .double, 64 => some (.int (wrap s 64 u))
    | .single, 32 => some (.int (wrap s 32 u))
    | _, _ => none
  | .bool, .int _ w, .bool c => if w = 8 then some (.int (if c then 1 else 0)) else none
  | .bool, .int s w, .int u => if w = 8 then some (.int (wrap s 8 u)) else none
  | .int _ w, .bool, .int x =>
    let b := (wrap false 8 x).toNat
    if w = 8 then some (if b ≤ 1 then .bool (b == 1) else .int (b : Int)) else none
  | .float k, .float k', .float f => if k = k' then some (.float f) else none
  | _, _, _ => none

/-- The scalar stored at byte offset `o` of a value `v` of type `t` (`d`:
fuel): its type and value. A record's members at their offsets (padding and
empty members hold none), array elements, a union's member holding a value.
(One equation per type constructor, so that `simp` unfolds it only on known
types.) -/
def Ctx.scalarAt (ctx : Ctx) : Nat → Ty → Val → Nat → Option (Ty × Val)
  | 0, _, _, _ => none
  | _ + 1, .int s w, v, o => if o = 0 then some (.int s w, v) else none
  | _ + 1, .bool, v, o => if o = 0 then some (.bool, v) else none
  | _ + 1, .float k, v, o => if o = 0 then some (.float k, v) else none
  | _ + 1, .ptr t, v, o => if o = 0 then some (.ptr t, v) else none
  | _ + 1, .vptr, v, o => if o = 0 then some (.vptr, v) else none
  | d + 1, .array e _, .arr xs, o =>
    match ctx.sizeAlign 32 e with
    | some (s, _) =>
      if s = 0 then none else
      match xs[o / s]? with
      | some x => ctx.scalarAt d e x (o % s)
      | none => none
    | none => none
  | d + 1, .record name, .agg vs, o =>
    match ctx.record? name with
    | some r =>
      if r.kind = .union then
        match (r.members.zip vs).find? (fun mv => match mv.2 with | .undef => false | _ => true) with
        | some ((_, tm), vm) => ctx.scalarAt d tm vm o
        | none => none
      else
        match ctx.memberOffsets name with
        | some offs =>
          match ((r.members.zip offs).zip vs).find? (fun ((mt, off), _) =>
              mt.1 != .pad && mt.1 != .empty && decide (off ≤ o) &&
              decide (o < off + ((ctx.sizeAlign 32 mt.2).map (·.1)).getD 0)) with
          | some (((_, tm), off), vm) => ctx.scalarAt d tm vm (o - off)
          | none => none
        | none => none
    | none => none
  | _ + 1, _, _, _ => none

/-- The byte at offset `o` of a value `v` of type `t` (`d`: fuel), as a
character access reads it (`byteOf`): a record's members at their offsets
(padding and empty members hold none), array elements, a union's member holding
a value; `none` where no byte is held (a pointer's, an indeterminate scalar's, a
NaN `Float`'s). (One equation per type constructor, so that `simp` unfolds it
only on known types.) -/
def Ctx.byteAt (ctx : Ctx) : Nat → Ty → Val → Nat → Option Nat
  | 0, _, _, _ => none
  | _ + 1, .int s w, v, o => byteOf (.int s w) v o
  | _ + 1, .bool, v, o => byteOf .bool v o
  | _ + 1, .float k, v, o => byteOf (.float k) v o
  | d + 1, .array e _, .arr xs, o =>
    match ctx.sizeAlign 32 e with
    | some (s, _) =>
      if s = 0 then none else
      match xs[o / s]? with
      | some x => ctx.byteAt d e x (o % s)
      | none => none
    | none => none
  | d + 1, .record name, .agg vs, o =>
    match ctx.record? name with
    | some r =>
      if r.kind = .union then
        match (r.members.zip vs).find? (fun mv => match mv.2 with | .undef => false | _ => true) with
        | some ((_, tm), vm) => ctx.byteAt d tm vm o
        | none => none
      else
        match ctx.memberOffsets name with
        | some offs =>
          match ((r.members.zip offs).zip vs).find? (fun ((mt, off), _) =>
              mt.1 != .pad && mt.1 != .empty && decide (off ≤ o) &&
              decide (o < off + ((ctx.sizeAlign 32 mt.2).map (·.1)).getD 0)) with
          | some (((_, tm), off), vm) => ctx.byteAt d tm vm (o - off)
          | none => none
        | none => none
    | none => none
  | _ + 1, _, _, _ => none

/-- The value of scalar type `t` with the bytes `bs` (little-endian): an
integer, a `bool`, a binary64 or binary32 float; bytes that are no value of
the type kept as a character store keeps them (`setByteRepr`: a `bool` byte
other than 0 / 1, a NaN's pattern, as their unsigned number in an `.int`); for
another number of bytes or another type, indeterminate. -/
def scalarOfBytes (t : Ty) (bs : List Nat) : Val :=
  let u : Nat := bs.foldr (fun c acc => c + 256 * acc) 0
  match t with
  | .int s w => if 8 * bs.length = w then .int (wrap s w (u : Int)) else .undef
  | .bool => if bs.length = 1 then (if u ≤ 1 then .bool (u == 1) else .int (u : Int)) else .undef
  | .float .double =>
    if bs.length = 8 then
      (if Std.decodeBits u = .nan then .int (u : Int) else .float (Float.ofBits u.toUInt64))
    else .undef
  | .float .single =>
    if bs.length = 4 then
      (let g := Std.singleOfBits u; if Std.decodeF g = .nan then .int (u : Int) else .float g)
    else .undef
  | _ => .undef

/-- The scalar of type `t` composed from the bytes that a value `sv` of type
`src` holds at offsets `base`, `base + 1`, … (`Ctx.byteAt`, `scalarOfBytes`);
indeterminate where one of them is not held. -/
def Ctx.composeAt (ctx : Ctx) (src : Ty) (sv : Val) (base : Nat) (t : Ty) : Val :=
  match ctx.sizeAlign 32 t with
  | some (n, _) =>
    match (List.range n).mapM (fun k => ctx.byteAt 32 src sv (base + k)) with
    | some bs => scalarOfBytes t bs
    | none => .undef
  | none => .undef

/-- The scalar of type `t` that the bytes at offset `base` of a value `sv` of
type `src` hold: the scalar stored there, itself for the same type, else
reinterpreted when it has `t`'s size (`punScalar`), else composed from the
bytes held there (`Ctx.composeAt`; C11 6.5.2.3p3, footnote 95, 6.5p7): a
narrower member or array element, a scalar across several stored scalars or
bytes. -/
def Ctx.reinterpScalar (ctx : Ctx) (src : Ty) (sv : Val) (base : Nat) (t : Ty) : Val :=
  match ctx.scalarAt 32 src sv base with
  | some (ts, w) =>
    if Ty.beq ts t then w
    else if (ctx.sizeAlign 32 ts).map (·.1) = (ctx.sizeAlign 32 t).map (·.1) then
      (punScalar ts t w).getD .undef
    else ctx.composeAt src sv base t
  | none => ctx.composeAt src sv base t

/-- The value of type `t` that the bytes at offset `base` of a value `sv` of
type `src` hold (`d`: fuel): scalars (`Ctx.reinterpScalar`), arrays element by
element, records member by member (a union by its first member, the others
indeterminate); anything else indeterminate. (One equation per type
constructor.) -/
def Ctx.reinterpAt (ctx : Ctx) (src : Ty) (sv : Val) : Nat → Nat → Ty → Val
  | 0, _, _ => .undef
  | _ + 1, base, .int s w => ctx.reinterpScalar src sv base (.int s w)
  | _ + 1, base, .bool => ctx.reinterpScalar src sv base .bool
  | _ + 1, base, .float k => ctx.reinterpScalar src sv base (.float k)
  | _ + 1, base, .ptr t => ctx.reinterpScalar src sv base (.ptr t)
  | _ + 1, base, .vptr => ctx.reinterpScalar src sv base .vptr
  | d + 1, base, .array e n =>
    match ctx.sizeAlign 32 e with
    | some (s, _) => .arr ((List.range n).map fun k => ctx.reinterpAt src sv d (base + k * s) e)
    | none => .undef
  | d + 1, base, .record name =>
    match ctx.record? name with
    | some r =>
      if r.kind = .union then
        match r.members with
        | [] => .agg []
        | (_, t0) :: rest => .agg (ctx.reinterpAt src sv d base t0 :: rest.map fun _ => .undef)
      else
        match ctx.memberOffsets name with
        | some offs => .agg ((r.members.zip offs).map fun (mt, off) => ctx.reinterpAt src sv d (base + off) mt.2)
        | none => .undef
    | none => .undef
  | _ + 1, _, _ => .undef

/-- The value member `k` (of type `tk`) of a union takes when it is read or
stored into while indeterminate: the bytes of the first other member holding a
value (`Ctx.reinterpAt`; `j` is the index of the head), else an indeterminate
`tk`. -/
def Ctx.fromActive (ctx : Ctx) (k : Nat) (tk : Ty) : Nat → List (MemberKind × Ty) → List Val → Val
  | j, (_, t) :: ms, v :: vs =>
    match v with
    | .undef => ctx.fromActive k tk (j + 1) ms vs
    | v => if k = j then ctx.fromActive k tk (j + 1) ms vs else ctx.reinterpAt t v 32 0 tk
  | _, _, _ => ctx.initVal 32 tk

/-- No member or element along `path` holds `.undef` in the value `v`. -/
def noUndefAlong : Val → List PathElem → Bool
  | _, [] => true
  | .agg vs, .idx k :: p => match vs[k]? with
    | some .undef => false
    | some v => noUndefAlong v p
    | none => true
  | .arr xs, .idx k :: p => match xs[k]? with
    | some v => noUndefAlong v p
    | none => true
  | _, _ :: _ => true

/-- The members of a union after member `i` becomes the active one (`j` is the
index of the head): the others are indeterminate; an inactive member that
becomes active starts as `init` (`Ctx.fromActive`: the bytes of the member that
held a value). -/
def activeMember (i j : Nat) (init : Val) : List Val → List Val
  | [] => []
  | v :: vs =>
    (if i = j then (match v with | .undef => init | v => v) else .undef) :: activeMember i (j + 1) init vs

/-- The value a read along `path` sees in a value `v` of type `t`, where it
differs from `v`: the union members on the path that are indeterminate, from
the member holding a value (`Ctx.fromActive`); `none` when nothing differs. An
array element or a struct member at the end of the path is read as it is (no
lookup, so an element at a symbolic index of an unknown list is no case). -/
def Ctx.viewValIn? (ctx : Ctx) : Ty → Val → List PathElem → Option Val
  | _, _, [] => none
  | .array e _, .arr xs, .idx k :: p =>
    match p with
    | [] => none
    | _ =>
      match xs[k]? with
      | some x => (ctx.viewValIn? e x p).map fun x' => .arr (xs.set k x')
      | none => none
  | .record name, .agg vs, .idx k :: p =>
    match ctx.record? name with
    | some r =>
      match r.kind with
      | .union =>
        match r.members[k]?, vs[k]? with
        | some (_, tk), some vk =>
          match vk with
          | .undef =>
            let vk' := ctx.fromActive k tk 0 r.members vs
            some (.agg (vs.set k ((ctx.viewValIn? tk vk' p).getD vk')))
          | _ => (ctx.viewValIn? tk vk p).map fun vk' => .agg (vs.set k vk')
        | _, _ => none
      | _ =>
        match p with
        | [] => none
        | _ =>
          match r.members[k]?, vs[k]? with
          | some (_, tk), some vk => (ctx.viewValIn? tk vk p).map fun vk' => .agg (vs.set k vk')
          | _, _ => none
    | none => none
  | _, _, _ => none

/-- The value of type `t` after a store along `path` has made the union members
on the path active, where it differs: an indeterminate member takes the bytes
of the member holding a value (`Ctx.fromActive`), and the union's other members
become indeterminate (`activeMember`); `none` when nothing changes (a member
holding a value is the active one, the others are indeterminate already). An
array element or a struct member at the end of the path changes nothing. -/
def Ctx.activateValIn? (ctx : Ctx) : Ty → Val → List PathElem → Option Val
  | _, _, [] => none
  | .array e _, .arr xs, .idx k :: p =>
    match p with
    | [] => none
    | _ =>
      match xs[k]? with
      | some x => (ctx.activateValIn? e x p).map fun x' => .arr (xs.set k x')
      | none => none
  | .record name, .agg vs, .idx k :: p =>
    match ctx.record? name with
    | some r =>
      match r.kind with
      | .union =>
        match r.members[k]?, vs[k]? with
        | some (_, tk), some vk =>
          match vk with
          | .undef =>
            let vk' := ctx.fromActive k tk 0 r.members vs
            some (.agg (activeMember k 0 ((ctx.activateValIn? tk vk' p).getD vk') vs))
          | _ => (ctx.activateValIn? tk vk p).map fun vk' => .agg (vs.set k vk')
        | _, _ => none
      | _ =>
        match p with
        | [] => none
        | _ =>
          match r.members[k]?, vs[k]? with
          | some (_, tk), some vk => (ctx.activateValIn? tk vk p).map fun vk' => .agg (vs.set k vk')
          | _, _ => none
    | none => none
  | _, _, _ => none

theorem Ctx.viewValIn?_eq_none_of_noUndefAlong {ctx : Ctx} :
    ∀ {t : Ty} {v : Val} {p : List PathElem}, noUndefAlong v p = true → ctx.viewValIn? t v p = none
  | _, _, [], _ => by simp [Ctx.viewValIn?]
  | t, v, e :: p, h => by
    cases e with
    | vel g i => cases t <;> cases v <;> simp [Ctx.viewValIn?]
    | byte _ => cases t <;> cases v <;> simp [Ctx.viewValIn?]
    | idx k =>
      cases t <;> cases v <;> simp only [Ctx.viewValIn?] <;> try rfl
      case array.arr e n xs =>
        split
        · rfl
        · simp only [noUndefAlong] at h
          cases hx : xs[k]? with
          | none => rfl
          | some x =>
            simp only [hx] at h
            simp [Ctx.viewValIn?_eq_none_of_noUndefAlong (t := e) h]
      case record.agg name vs =>
        simp only [noUndefAlong] at h
        cases hr : ctx.record? name with
        | none => rfl
        | some r =>
          simp only
          cases hv : vs[k]? with
          | none => cases r.kind <;> simp only <;> (try split) <;> simp_all
          | some vk =>
            simp only [hv] at h
            by_cases hu : vk = .undef
            · subst hu; simp at h
            · have h' : noUndefAlong vk p = true := by cases vk <;> simp_all
              cases hm : r.members[k]? with
              | none => cases r.kind <;> simp only <;> (try split) <;> simp_all
              | some mt =>
                obtain ⟨mk, tk⟩ := mt
                have ih := Ctx.viewValIn?_eq_none_of_noUndefAlong (ctx := ctx) (t := tk) h'
                cases r.kind <;> simp only <;> (try split) <;> simp_all

theorem Ctx.activateValIn?_eq_none_of_noUndefAlong {ctx : Ctx} :
    ∀ {t : Ty} {v : Val} {p : List PathElem}, noUndefAlong v p = true → ctx.activateValIn? t v p = none
  | _, _, [], _ => by simp [Ctx.activateValIn?]
  | t, v, e :: p, h => by
    cases e with
    | vel g i => cases t <;> cases v <;> simp [Ctx.activateValIn?]
    | byte _ => cases t <;> cases v <;> simp [Ctx.activateValIn?]
    | idx k =>
      cases t <;> cases v <;> simp only [Ctx.activateValIn?] <;> try rfl
      case array.arr e n xs =>
        split
        · rfl
        · simp only [noUndefAlong] at h
          cases hx : xs[k]? with
          | none => rfl
          | some x =>
            simp only [hx] at h
            simp [Ctx.activateValIn?_eq_none_of_noUndefAlong (t := e) h]
      case record.agg name vs =>
        simp only [noUndefAlong] at h
        cases hr : ctx.record? name with
        | none => rfl
        | some r =>
          simp only
          cases hv : vs[k]? with
          | none => cases r.kind <;> simp only <;> (try split) <;> simp_all
          | some vk =>
            simp only [hv] at h
            by_cases hu : vk = .undef
            · subst hu; simp at h
            · have h' : noUndefAlong vk p = true := by cases vk <;> simp_all
              cases hm : r.members[k]? with
              | none => cases r.kind <;> simp only <;> (try split) <;> simp_all
              | some mt =>
                obtain ⟨mk, tk⟩ := mt
                have ih := Ctx.activateValIn?_eq_none_of_noUndefAlong (ctx := ctx) (t := tk) h'
                cases r.kind <;> simp only <;> (try split) <;> simp_all

/-- Whether `path` enters a member of a union below an object of type `t` (`d`:
fuel), by the types alone: record members' types from the record declarations,
array elements by their type; a path element that is no index ends the walk.
Without one, a read or a store along the path meets no union member, whatever
the object's value (`Ctx.viewVal?`, `Ctx.activateVal?`). (One equation per type
constructor, so that `simp` decides it on known types.) -/
def Ctx.unionOnPath (ctx : Ctx) : Nat → Ty → List PathElem → Bool
  | 0, _, _ => true
  | _ + 1, _, [] => false
  | d + 1, .array e _, .idx _ :: p => ctx.unionOnPath d e p
  | d + 1, .record name, .idx k :: p =>
    match ctx.record? name with
    | some r =>
      match r.kind with
      | .union => true
      | _ =>
        match r.members[k]? with
        | some (_, tk) => ctx.unionOnPath d tk p
        | none => false
    | none => false
  | _ + 1, _, _ :: _ => false

/-- The value a read along `path` sees in a value `v` of type `t`, where it
differs from `v` (`Ctx.viewValIn?`); `none` by the types alone when the path
enters no union member (`Ctx.unionOnPath`), so that the value of a record
without unions, a symbolic one included, is no case. (A `match` on the
decision, not an `if`: simp reduces it once the decision is a constructor,
without simplifying the walk, where it would visit both branches of an `if`.) -/
def Ctx.viewVal? (ctx : Ctx) (t : Ty) (v : Val) (path : List PathElem) : Option Val :=
  match ctx.unionOnPath 32 t path with
  | true => ctx.viewValIn? t v path
  | false => none

/-- The value of type `t` after a store along `path` has made the union members
on the path active, where it differs (`Ctx.activateValIn?`); `none` by the
types alone when the path enters no union member (`Ctx.unionOnPath`; a `match`,
as in `Ctx.viewVal?`). -/
def Ctx.activateVal? (ctx : Ctx) (t : Ty) (v : Val) (path : List PathElem) : Option Val :=
  match ctx.unionOnPath 32 t path with
  | true => ctx.activateValIn? t v path
  | false => none

theorem Ctx.viewVal?_eq_none_of_noUndefAlong {ctx : Ctx} {t : Ty} {v : Val} {p : List PathElem}
    (h : noUndefAlong v p = true) : ctx.viewVal? t v p = none := by
  unfold Ctx.viewVal?
  split
  · exact Ctx.viewValIn?_eq_none_of_noUndefAlong h
  · rfl

theorem Ctx.activateVal?_eq_none_of_noUndefAlong {ctx : Ctx} {t : Ty} {v : Val} {p : List PathElem}
    (h : noUndefAlong v p = true) : ctx.activateVal? t v p = none := by
  unfold Ctx.activateVal?
  split
  · exact Ctx.activateValIn?_eq_none_of_noUndefAlong h
  · rfl

/-- The memory a read through `p` sees: its block with `Ctx.viewVal?` along
the path (nothing is written); `none` when the view changes nothing. -/
def Ctx.unionView? (ctx : Ctx) (m : Mem) : Ptr → Option Mem
  | .loc b path => match m.blocks b with
    | some blk => (ctx.viewVal? blk.ty blk.val path).map fun v => m.setBlock b { blk with val := v }
    | none => none
  | _ => none

/-- The memory before a store through `p`: the union members on its path
activated (`Ctx.activateVal?`); `none` when nothing changes. In a read-only
block the store then succeeds only as the initialization of a const object
(`Val.initBy`): over a member whose bytes another member holds, it fails. -/
def Ctx.unionActivate? (ctx : Ctx) (m : Mem) : Ptr → Option Mem
  | .loc b path => match m.blocks b with
    | some blk =>
      match ctx.activateVal? blk.ty blk.val path with
      | some v => some (m.setBlock b { blk with val := v })
      | none => none
    | none => none
  | _ => none

/-- A load of type `ty` of byte `k` of an object of type `t`, from the value
`r` read: a character type's value of that byte, else (another access type)
type-punned. -/
def byteLoadOf (ty : Ty) (r : Option Val) (t : Ty) (k : Nat) : Res Val :=
  match ty with
  | .int s 8 =>
    match r with
    | some v =>
      match byteOf t v k with
      | some c => .ok (.int (wrap s 8 c))
      | none => .ub "byte access not modelled (pointer, NaN, indeterminate value, or outside the object)"
    | none => .ub "invalid memory read"
  | _ => .ub "type-punned access (byte-level access not modelled)"

/-- A store of type `ty` of `v` into byte `k` of an object of type `t`, from
the value `r` read and with the write `wr` of the object's new value. Once the
value is read, the write fails only in a read-only block: a const object or a
string literal, whose determinate bytes no store may change (C11 6.7.3p6,
6.4.5p7). No byte is written into an indeterminate value, const or not. -/
def byteStoreOf (ty : Ty) (v : Val) (r : Option Val) (t : Ty) (k : Nat) (wr : Val → Option Mem) :
    Res Mem :=
  match ty, v with
  | .int s 8, .int c =>
    if inRange s 8 c then
      match r with
      | some old =>
        match setByteRepr t old k (wrap false 8 c).toNat with
        | some new => Res.ofOption "modification of a const object (C11 6.7.3p6, 6.4.5p7)" (wr new)
        | none => .ub "byte access not modelled (pointer, NaN, indeterminate value, or outside the object)"
      | none => .ub "invalid memory write"
    else .ub "ill-typed store"
  | .int _ 8, _ => .ub "ill-typed store"
  | _, _ => .ub "type-punned access (byte-level access not modelled)"

/-- A character load of byte `k` of the scalar at `path` (`Reach.byte`). -/
def byteLoad (m : Mem) (ty : Ty) (b : Nat) (path : List PathElem) (t : Ty) (k : Nat) : Res Val :=
  byteLoadOf ty (m.read? (.loc b path)) t k

/-- A character store into byte `k` of the scalar at `path` (`Reach.byte`):
the scalar's new value with that byte replaced. -/
def byteStore (m : Mem) (ty : Ty) (b : Nat) (path : List PathElem) (t : Ty) (k : Nat) (v : Val) :
    Res Mem :=
  byteStoreOf ty v (m.read? (.loc b path)) t k (fun w => m.write? (.loc b path) w)

/-- `loadTy`'s check of the value read. -/
def loadValOf (ty : Ty) : Option Val → Res Val
  | none => .ub "invalid memory read"
  | some v =>
    if ty.isScalar then
      if fitsTy ty v then .ok v
      else match ty, v with
        | .int s w, .int x => if inRange (!s) w x then .ok (.int (wrap s w x))
          else .ub "read of an indeterminate or ill-typed value"
        -- bytes that are no value of the type, stored through a character
        -- lvalue (`setByteRepr`; C11 6.2.6.1p5)
        | .bool, .int _ => .ub "read of a bool whose byte is neither 0 nor 1"
        | .float _, .int _ => .ub "read of a floating object holding a NaN bit pattern (not modelled)"
        | _, _ => .ub "read of an indeterminate or ill-typed value"
    else .ok v

/-- The write of `w` at `path` in block `b`, given its block `blk` (`Mem.write?`). -/
def writeIn (m : Mem) (b : Nat) (blk : MemBlock) (path : List PathElem) (w : Val) : Option Mem :=
  if blk.alive then
    if blk.kind = .readonly then
      if (blk.val.get? path).all (Val.initBy · w) then
        match blk.val.set? path w with
        | some v' => some (m.setBlock b { blk with val := v' })
        | none => none
      else none
    else match blk.val.set? path w with
      | some v' => some (m.setBlock b { blk with val := v' })
      | none => none
  else none

/-- `Mem.punnedAccess` in a block of type `bty`. -/
def punnedAt (bty ty : Ty) (path : List PathElem) : Bool :=
  match Ty.atPath bty path with
  | some t => ty.isScalar && t.isScalar && !t.accessCompatible ty
  | none => false

/-- `storeTy`'s write of `v` at `path` in block `b`, given its block `blk`. -/
def storeAt (m : Mem) (b : Nat) (blk : MemBlock) (ty : Ty) (path : List PathElem) (v : Val) : Res Mem :=
  if ty.isScalar && !fitsTy ty v then .ub "ill-typed store"
  else if blk.alive then
    if blk.kind = .readonly then
      if (blk.val.get? path).all (Val.initBy · v) then
        match blk.val.set? path v with
        | some v' => .ok (m.setBlock b { blk with val := v' })
        | none => .ub "invalid memory write"
      else .ub "modification of a const object (C11 6.7.3p6, 6.4.5p7)"
    else match blk.val.set? path v with
      | some v' => .ok (m.setBlock b { blk with val := v' })
      | none => .ub "invalid memory write"
  else .ub "invalid memory write"

/-- The byte offset of the subobject at `path` in an object of type `t`: array
elements by their size, record members by their offsets, union members at 0,
and `k` for a last step `.byte k`. -/
def Ctx.absPos? (ctx : Ctx) : Ty → List PathElem → Option Nat
  | _, [] => some 0
  | _, [.byte k] => some k
  | .array e _, .idx i :: rest =>
    match ctx.sizeAlign 32 e, ctx.absPos? e rest with
    | some (s, _), some q => some (i * s + q)
    | _, _ => none
  | .record name, .idx i :: rest =>
    match ctx.record? name with
    | some rd =>
      match rd.members[i]? with
      | some (_, ti) =>
        if rd.kind = .union then ctx.absPos? ti rest
        else
          match ctx.memberOffsets name, ctx.absPos? ti rest with
          | some offs, some q => (offs[i]?).map (· + q)
          | _, _ => none
      | none => none
    | none => none
  | _, _ => none

/-- Whether the byte position of the object at `path` in block `b`
(`Ctx.absPos?`) is a multiple of `a` (`Ctx.castAligned`); a position that is
not known counts as aligned. -/
def Ctx.posAligned (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (a : Nat) : Bool :=
  match m.blocks b with
  | some blk =>
    match ctx.absPos? blk.ty path with
    | some q => q % a == 0
    | none => true
  | none => true

/-- A pointer to the object at `path` in block `b`, converted to a pointer to
`t`, is correctly aligned for `t` (C11 6.3.2.3p7: otherwise the conversion is
undefined): its byte position in its complete object is a multiple of `t`'s
alignment. A complete object is taken to be aligned for every type, as
`malloc`'s storage is. `void`, a function type, a character type and `bool`
(no alignment, or 1), and the start of a complete object or its element 0,
need neither the module's layouts nor a position (`Ctx.posAligned`). -/
def Ctx.castAligned (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (t : Ty) : Bool :=
  match t, path with
  | .void, _ | .func .., _ | .int _ 8, _ | .bool, _ => true
  | _, [] | _, [.idx 0] => true
  | _, _ =>
    match ctx.sizeAlign 32 t with
    | some (_, a) => a ≤ 1 || ctx.posAligned m b path a
    | none => true

/-- The value of type `t` read member by member from byte `q` of the complete
object of block `b` (`Ctx.spreadLoad`): a scalar from the scalar there, as
`reachScalar` classifies it (`loadTy`, `byteLoad`), a structure's members at
their offsets (its padding indeterminate), an array's elements. -/
def Ctx.gatherAt (ctx : Ctx) : Nat → Mem → Nat → Ty → Nat → Res Val
  | 0, _, _, _, _ => .ub "aggregate access not modelled"
  | fuel + 1, m, b, t, q =>
    if t.isScalar then
      match m.blocks b with
      | some blk =>
        match ctx.scalarIn 32 blk.ty blk.val [] q with
        | some r =>
          match reachScalar t 0 r with
          | .obj p => loadTy m t (.loc b p)
          | .byte p t' k => byteLoad m t b p t' k
          | _ => .ub "type-punned access (byte-level access not modelled)"
        | none => .ub "type-punned access (byte-level access not modelled)"
      | none => .ub "invalid memory read"
    else
      match t with
      | .record n =>
        match ctx.record? n, ctx.memberOffsets n with
        | some rd, some offs =>
          if rd.kind = .union then .ub "aggregate access not modelled" else do
          let vs ← (rd.members.zip offs).mapM fun ((kd, tj), o) =>
            if kd = .pad then .ok (ctx.initVal 32 tj) else ctx.gatherAt fuel m b tj (q + o)
          pure (.agg vs)
        | _, _ => .ub "aggregate access not modelled"
      | .array e len =>
        match ctx.sizeAlign 32 e with
        | some (s, _) => do
          let xs ← (List.range len).mapM fun i => ctx.gatherAt fuel m b e (q + i * s)
          pure (.arr xs)
        | none => .ub "aggregate access not modelled"
      | _ => .ub "aggregate access not modelled"

/-- The write of `v`, of type `t`, member by member at byte `q` of the complete
object of block `b` (`Ctx.spreadStore`): a scalar into the scalar there, as
`reachScalar` classifies it (`storeTy`, `byteStore`; an indeterminate value as
it is), a structure's members at their offsets (not its padding), an array's
elements. -/
def Ctx.scatterAt (ctx : Ctx) : Nat → Mem → Nat → Ty → Nat → Val → Res Mem
  | 0, _, _, _, _, _ => .ub "aggregate access not modelled"
  | fuel + 1, m, b, t, q, v =>
    if t.isScalar then
      match m.blocks b with
      | some blk =>
        match ctx.scalarIn 32 blk.ty blk.val [] q with
        | some r =>
          match reachScalar t 0 r with
          | .obj p =>
            match v with
            | .undef => Res.ofOption "invalid memory write" (m.write? (.loc b p) .undef)
            | _ => storeTy m t (.loc b p) v
          | .byte p t' k => byteStore m t b p t' k v
          | _ => .ub "type-punned access (byte-level access not modelled)"
        | none => .ub "type-punned access (byte-level access not modelled)"
      | none => .ub "invalid memory write"
    else
      match t, v with
      | .record n, .agg vs =>
        match ctx.record? n, ctx.memberOffsets n with
        | some rd, some offs =>
          if rd.kind = .union then .ub "aggregate access not modelled" else
          ((rd.members.zip offs).zip vs).foldlM (fun m (((kd, tj), o), x) =>
            if kd = .pad then .ok m else ctx.scatterAt fuel m b tj (q + o) x) m
        | _, _ => .ub "aggregate access not modelled"
      | .array e _, .arr xs =>
        match ctx.sizeAlign 32 e with
        | some (s, _) => xs.zipIdx.foldlM (fun m (x, i) => ctx.scatterAt fuel m b e (q + i * s) x) m
        | none => .ub "aggregate access not modelled"
      | _, _ => .ub "ill-typed store"

/-- A load of type `t` member by member, or element by element, over the object at
`path` in block `b` (`Reach.spread`): a record over a scalar or an array that does not
start with one (C11 6.5p7: an aggregate type that includes the types of the objects
among its members), a vector over the objects at its bytes. -/
def Ctx.spreadLoad (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (t : Ty) : Res Val :=
  match m.blocks b with
  | some blk =>
    if blk.alive then
      match ctx.absPos? blk.ty path with
      | some q => ctx.gatherAt 32 m b t q
      | none => .ub "aggregate access not modelled"
    else .ub "invalid memory read"
  | none => .ub "invalid memory read"

/-- A store of `v`, of type `t`, member by member, or element by element, over the
object at `path` in block `b` (`Ctx.spreadLoad`). -/
def Ctx.spreadStore (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) (t : Ty) (v : Val) :
    Res Mem :=
  match m.blocks b with
  | some blk =>
    match ctx.absPos? blk.ty path with
    | some q => ctx.scatterAt 32 m b t q v
    | none => .ub "aggregate access not modelled"
  | none => .ub "invalid memory write"

/-- `loadTy` with record members checked (`Ctx.punnedMember`), the character
accesses to the bytes of objects and the scalars that aggregates start with
(`Ctx.reach?`), through the union members on the path as the stores left them
(`Ctx.unionView?`; also on the path that an access at an aggregate reaches). -/
def Ctx.typedLoad (ctx : Ctx) (m : Mem) (ty : Ty) (p : Ptr) : Res Val :=
  let m := (ctx.unionView? m p).getD m
  match ctx.reach? m ty p with
  | some (b, .byte path t k) => byteLoad m ty b path t k
  | some (b, .obj path) => loadTy ((ctx.unionView? m (.loc b path)).getD m) ty (.loc b path)
  | some (_, .punned) => .ub "type-punned access (byte-level access not modelled)"
  | some (b, .spread path t) => ctx.spreadLoad m b path t
  | some (_, .external) => .ub "external object without a model"
  | none =>
    if ctx.punnedMember m ty p then .ub "type-punned access (byte-level access not modelled)" else
    loadTy m ty p

/-- `storeTy` with record members checked (`Ctx.punnedMember`), the character
accesses to the bytes of objects and the scalars that aggregates start with
(`Ctx.reach?`), once the union members on the path are made active
(`Ctx.unionActivate?`; also on the path that an access at an aggregate
reaches). -/
def Ctx.typedStore (ctx : Ctx) (m : Mem) (ty : Ty) (p : Ptr) (v : Val) : Res Mem :=
  let m := (ctx.unionActivate? m p).getD m
  match ctx.reach? m ty p with
  | some (b, .byte path t k) => byteStore m ty b path t k v
  | some (b, .obj path) => storeTy ((ctx.unionActivate? m (.loc b path)).getD m) ty (.loc b path) v
  | some (_, .punned) => .ub "type-punned access (byte-level access not modelled)"
  | some (b, .spread path t) => ctx.spreadStore m b path t v
  | some (_, .external) => .ub "external object without a model"
  | none =>
    if ctx.punnedMember m ty p then .ub "type-punned access (byte-level access not modelled)" else
    storeTy m ty p v

/-- The ordinary load at its pointer, from the memory as the union view `o` leaves
it (`none`: unchanged). -/
theorem Ctx.typedLoad_eq_loadTy {ctx : Ctx} {m : Mem} {ty : Ty} {p : Ptr} {o : Option Mem}
    (hu : ctx.unionView? m p = o) (h0 : ctx.reach? (o.getD m) ty p = none)
    (h : ctx.punnedMember (o.getD m) ty p = false) :
    ctx.typedLoad m ty p = loadTy (o.getD m) ty p := by
  subst hu
  simp [Ctx.typedLoad, h0, h]

theorem Ctx.typedLoad_eq_ub {ctx : Ctx} {m : Mem} {ty : Ty} {p : Ptr} {o : Option Mem}
    (hu : ctx.unionView? m p = o) (h0 : ctx.reach? (o.getD m) ty p = none)
    (h : ctx.punnedMember (o.getD m) ty p = true) :
    ctx.typedLoad m ty p = .ub "type-punned access (byte-level access not modelled)" := by
  subst hu
  simp [Ctx.typedLoad, h0, h]

/-- The ordinary store at its pointer, into the memory as the activation `o`
leaves it (`none`: unchanged). -/
theorem Ctx.typedStore_eq_storeTy {ctx : Ctx} {m : Mem} {ty : Ty} {p : Ptr} {v : Val}
    {o : Option Mem} (hu : ctx.unionActivate? m p = o) (h0 : ctx.reach? (o.getD m) ty p = none)
    (h : ctx.punnedMember (o.getD m) ty p = false) :
    ctx.typedStore m ty p v = storeTy (o.getD m) ty p v := by
  subst hu
  simp [Ctx.typedStore, h0, h]

theorem Ctx.typedStore_eq_ub {ctx : Ctx} {m : Mem} {ty : Ty} {p : Ptr} {v : Val}
    {o : Option Mem} (hu : ctx.unionActivate? m p = o) (h0 : ctx.reach? (o.getD m) ty p = none)
    (h : ctx.punnedMember (o.getD m) ty p = true) :
    ctx.typedStore m ty p v = .ub "type-punned access (byte-level access not modelled)" := by
  subst hu
  simp [Ctx.typedStore, h0, h]

/-- The record member and array element punning checks of an access of type
`ty` along `path` in a block of type `bty` (`Ctx.punnedMember` and
`Mem.punnedAccess`, which both look the block up). -/
def Ctx.punnedIn (ctx : Ctx) (bty ty : Ty) (path : List PathElem) : Bool :=
  match Ty.atPath bty path with
  | some t => ty.isScalar && t.isScalar && !t.accessCompatible ty
  | none =>
    match ctx.typeAt bty path with
    | some t => ty.isScalar && t.isScalar && !t.accessCompatible ty
    | none => false

/-- Block `blk` as a load along `path` sees it: the union members on the path
as the stores left them (`Ctx.unionView?`). -/
def Ctx.viewBlk (ctx : Ctx) (blk : MemBlock) (path : List PathElem) : MemBlock :=
  { blk with val := (ctx.viewVal? blk.ty blk.val path).getD blk.val }

/-- Block `blk` once a store along `path` has made the union members on the
path active (`Ctx.unionActivate?`). -/
def Ctx.activateBlk (ctx : Ctx) (blk : MemBlock) (path : List PathElem) : MemBlock :=
  match ctx.activateVal? blk.ty blk.val path with
  | some v => { blk with val := v }
  | none => blk

/-- `Ctx.typedLoad` with one block lookup (the compiled code's, `@[csimp]`). -/
def Ctx.typedLoadFast (ctx : Ctx) (m : Mem) (ty : Ty) : Ptr → Res Val
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      let blk := ctx.viewBlk blk path
      match ctx.reachIn blk ty path with
      | some (.byte pre t k) => byteLoadOf ty (if blk.alive then blk.val.get? pre else none) t k
      | some (.obj p') =>
        let blk := ctx.viewBlk blk p'
        match punnedAt blk.ty ty p' with
        | true => .ub "type-punned access (byte-level access not modelled)"
        | false => loadValOf ty (if blk.alive then blk.val.get? p' else none)
      | some .punned => .ub "type-punned access (byte-level access not modelled)"
      | some (.spread p' t) => ctx.spreadLoad ((ctx.unionView? m (.loc b path)).getD m) b p' t
      | some .external => .ub "external object without a model"
      | none =>
        match ctx.punnedIn blk.ty ty path with
        | true => .ub "type-punned access (byte-level access not modelled)"
        | false => loadValOf ty (if blk.alive then blk.val.get? path else none)
    | none => .ub "invalid memory read"
  | p => loadTy m ty p

/-- `Ctx.typedStore` with one block lookup (the compiled code's, `@[csimp]`). -/
def Ctx.typedStoreFast (ctx : Ctx) (m : Mem) (ty : Ty) : Ptr → Val → Res Mem
  | .loc b path, v =>
    match m.blocks b with
    | some blk =>
      let blk := ctx.activateBlk blk path
      match ctx.reachIn blk ty path with
      | some (.byte pre t k) =>
        byteStoreOf ty v (if blk.alive then blk.val.get? pre else none) t k (writeIn m b blk pre)
      | some (.obj p') =>
        let blk := ctx.activateBlk blk p'
        match punnedAt blk.ty ty p' with
        | true => .ub "type-punned access (byte-level access not modelled)"
        | false => storeAt m b blk ty p' v
      | some .punned => .ub "type-punned access (byte-level access not modelled)"
      | some (.spread p' t) => ctx.spreadStore ((ctx.unionActivate? m (.loc b path)).getD m) b p' t v
      | some .external => .ub "external object without a model"
      | none =>
        match ctx.punnedIn blk.ty ty path with
        | true => .ub "type-punned access (byte-level access not modelled)"
        | false => storeAt m b blk ty path v
    | none => if ty.isScalar && !fitsTy ty v then .ub "ill-typed store" else .ub "invalid memory write"
  | p, v => storeTy m ty p v

theorem ite_true_eq_match {α : Type} (c : Bool) (x y : α) :
    (if c = true then x else y) = (match c with | true => x | false => y) := by
  cases c <;> rfl

theorem loadTy_eq_loadValOf (m : Mem) (ty : Ty) (p : Ptr) :
    loadTy m ty p = match m.punnedAccess ty p with
      | true => .ub "type-punned access (byte-level access not modelled)"
      | false => loadValOf ty (m.read? p) := by
  unfold loadTy
  cases m.punnedAccess ty p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · rfl

theorem read?_of_blocks {m : Mem} {b : Nat} {blk : MemBlock} (h : m.blocks b = some blk)
    (path : List PathElem) : m.read? (.loc b path) = if blk.alive then blk.val.get? path else none := by
  simp only [Mem.read?, Mem.live?, h]
  cases blk.alive <;> rfl

theorem write?_of_blocks {m : Mem} {b : Nat} {blk : MemBlock} (h : m.blocks b = some blk)
    (path : List PathElem) : (fun w => m.write? (.loc b path) w) = writeIn m b blk path := by
  funext w
  simp only [Mem.write?, Mem.live?, h, writeIn]
  by_cases hal : blk.alive = true
  · simp only [hal, ↓reduceIte]
    rfl
  · simp only [hal, Bool.false_eq_true, ↓reduceIte]

theorem loadTy_loc_eq {m : Mem} {b : Nat} {blk : MemBlock} (h : m.blocks b = some blk)
    (ty : Ty) (path : List PathElem) :
    loadTy m ty (.loc b path) = match punnedAt blk.ty ty path with
      | true => .ub "type-punned access (byte-level access not modelled)"
      | false => loadValOf ty (if blk.alive then blk.val.get? path else none) := by
  have hp : m.punnedAccess ty (.loc b path) = punnedAt blk.ty ty path := by
    simp only [Mem.punnedAccess, h, punnedAt]
  rw [loadTy_eq_loadValOf, read?_of_blocks h, hp]

theorem Mem.setBlock_blocks_same (m : Mem) (b : Nat) (blk : MemBlock) :
    (m.setBlock b blk).blocks b = some blk := by
  simp [Mem.setBlock, upd]

theorem Mem.setBlock_setBlock (m : Mem) (b : Nat) (x y : MemBlock) :
    (m.setBlock b x).setBlock b y = m.setBlock b y := by
  simp only [Mem.setBlock, Mem.mk.injEq, and_true]
  funext a
  simp only [upd]
  split <;> rfl

/-- The memory a typed load reads has block `b` as the view along the path sees
it. -/
theorem Ctx.unionView?_getD_blocks {ctx : Ctx} {m : Mem} {b : Nat} {blk : MemBlock}
    (h : m.blocks b = some blk) (path : List PathElem) :
    ((ctx.unionView? m (.loc b path)).getD m).blocks b = some (ctx.viewBlk blk path) := by
  simp only [Ctx.unionView?, h, Ctx.viewBlk]
  cases ctx.viewVal? blk.ty blk.val path with
  | none => simpa using h
  | some v => simp [Mem.setBlock_blocks_same]

@[csimp] theorem Ctx.typedLoad_eq_typedLoadFast : @Ctx.typedLoad = @Ctx.typedLoadFast := by
  funext ctx m ty p
  cases p
  case loc b path =>
    rcases h : m.blocks b with _ | blk
    · simp only [Ctx.typedLoad, Ctx.typedLoadFast, Ctx.unionView?, h, Option.getD_none, Ctx.reach?,
        Ctx.punnedMember, loadTy_eq_loadValOf, Mem.punnedAccess, Mem.read?, Mem.live?]
      all_goals rfl
    · have h' := Ctx.unionView?_getD_blocks (ctx := ctx) h path
      simp only [Ctx.typedLoad, Ctx.typedLoadFast, h]
      generalize (ctx.unionView? m (.loc b path)).getD m = m' at h' ⊢
      generalize ctx.viewBlk blk path = blk' at h' ⊢
      simp only [Ctx.reach?, h']
      rcases hr : ctx.reachIn blk' ty path with _ | r
      · simp only [Option.map_none, ite_true_eq_match, loadTy_loc_eq h', Ctx.punnedMember, h',
          Ctx.punnedIn, punnedAt]
        rcases ha : Ty.atPath blk'.ty path with _ | t
        · rcases ht : ctx.typeAt blk'.ty path with _ | t
          · rfl
          · cases (ty.isScalar && t.isScalar && !t.accessCompatible ty) <;> rfl
        · cases (ty.isScalar && t.isScalar && !t.accessCompatible ty) <;> rfl
      · cases r with
        | byte pre t k => simp only [Option.map_some, byteLoad, read?_of_blocks h']
        | obj p' => simp only [Option.map_some, loadTy_loc_eq (Ctx.unionView?_getD_blocks h' p')]
        | punned => simp only [Option.map_some]
        | spread p' t => simp only [Option.map_some]
        | external => simp only [Option.map_some]
  all_goals rfl

theorem storeTy_eq_match (m : Mem) (ty : Ty) (p : Ptr) (v : Val) :
    storeTy m ty p v = match m.punnedAccess ty p with
      | true => .ub "type-punned access (byte-level access not modelled)"
      | false => if ty.isScalar && !fitsTy ty v then .ub "ill-typed store" else
        match m.write? p v with
        | none => .ub (m.writeFail p v)
        | some m' => .ok m' := by
  unfold storeTy
  cases m.punnedAccess ty p <;> rfl

theorem storeAt_eq {m : Mem} {b : Nat} {blk : MemBlock} (h : m.blocks b = some blk)
    (ty : Ty) (path : List PathElem) (v : Val) :
    (if ty.isScalar && !fitsTy ty v then .ub "ill-typed store" else
      match m.write? (.loc b path) v with
      | none => .ub (m.writeFail (.loc b path) v)
      | some m' => .ok m') = storeAt m b blk ty path v := by
  simp only [Mem.write?, Mem.writeFail, Mem.live?, h, storeAt]
  by_cases hil : (ty.isScalar && !fitsTy ty v) = true
  · simp only [hil, ↓reduceIte]
  · simp only [hil]
    by_cases hal : blk.alive = true
    · simp only [hal, ↓reduceIte]
      by_cases hro : blk.kind = BlockKind.readonly
      · by_cases hin : (blk.val.get? path).all (Val.initBy · v) = true
        · simp only [hro, hin, ↓reduceIte]
          cases blk.val.set? path v <;> rfl
        · simp only [hro, hin, Bool.false_eq_true, ↓reduceIte]
      · simp only [hro, ↓reduceIte]
        cases blk.val.set? path v <;> rfl
    · simp only [hal, Bool.false_eq_true, ↓reduceIte]

theorem storeTy_loc_eq {m : Mem} {b : Nat} {blk : MemBlock} (h : m.blocks b = some blk)
    (ty : Ty) (path : List PathElem) (v : Val) :
    storeTy m ty (.loc b path) v = match punnedAt blk.ty ty path with
      | true => .ub "type-punned access (byte-level access not modelled)"
      | false => storeAt m b blk ty path v := by
  have hp : m.punnedAccess ty (.loc b path) = punnedAt blk.ty ty path := by
    simp only [Mem.punnedAccess, h, punnedAt]
  rw [storeTy_eq_match, storeAt_eq h, hp]

/-- The memory a typed store writes has block `b` as the activation along the
path left it. -/
theorem Ctx.unionActivate?_getD_blocks {ctx : Ctx} {m : Mem} {b : Nat} {blk : MemBlock}
    (h : m.blocks b = some blk) (path : List PathElem) :
    ((ctx.unionActivate? m (.loc b path)).getD m).blocks b = some (ctx.activateBlk blk path) := by
  simp only [Ctx.unionActivate?, h, Ctx.activateBlk]
  cases ctx.activateVal? blk.ty blk.val path with
  | none => simpa using h
  | some v => simp [Mem.setBlock_blocks_same]

/-- A store into block `b` after the activation along a path into `b` is the
store into the memory before it: the activation set block `b` only. -/
theorem Ctx.storeAt_unionActivate? {ctx : Ctx} {m : Mem} {b : Nat} (path : List PathElem)
    (blk' : MemBlock) (ty : Ty) (p' : List PathElem) (v : Val) :
    storeAt ((ctx.unionActivate? m (.loc b path)).getD m) b blk' ty p' v = storeAt m b blk' ty p' v := by
  rcases hb : m.blocks b with _ | blk
  · simp only [Ctx.unionActivate?, hb, Option.getD_none]
  · rcases hv : ctx.activateVal? blk.ty blk.val path with _ | va
    · simp only [Ctx.unionActivate?, hb, hv, Option.getD_none]
    · simp only [Ctx.unionActivate?, hb, hv, Option.getD_some, storeAt, Mem.setBlock_setBlock]

theorem Ctx.writeIn_unionActivate? {ctx : Ctx} {m : Mem} {b : Nat} (path : List PathElem)
    (blk' : MemBlock) (pre : List PathElem) :
    writeIn ((ctx.unionActivate? m (.loc b path)).getD m) b blk' pre = writeIn m b blk' pre := by
  funext w
  rcases hb : m.blocks b with _ | blk
  · simp only [Ctx.unionActivate?, hb, Option.getD_none]
  · rcases hv : ctx.activateVal? blk.ty blk.val path with _ | va
    · simp only [Ctx.unionActivate?, hb, hv, Option.getD_none]
    · simp only [Ctx.unionActivate?, hb, hv, Option.getD_some, writeIn, Mem.setBlock_setBlock]

@[csimp] theorem Ctx.typedStore_eq_typedStoreFast : @Ctx.typedStore = @Ctx.typedStoreFast := by
  funext ctx m ty p v
  cases p
  case loc b path =>
    rcases h : m.blocks b with _ | blk
    · simp only [Ctx.typedStore, Ctx.typedStoreFast, Ctx.unionActivate?, h, Option.getD_none,
        Ctx.reach?, Ctx.punnedMember, storeTy_eq_match, Mem.punnedAccess, Mem.write?, Mem.writeFail,
        Mem.live?]
      all_goals rfl
    · have h' := Ctx.unionActivate?_getD_blocks (ctx := ctx) h path
      have hs := Ctx.storeAt_unionActivate? (ctx := ctx) (m := m) (b := b) path
      have hw := Ctx.writeIn_unionActivate? (ctx := ctx) (m := m) (b := b) path
      simp only [Ctx.typedStore, Ctx.typedStoreFast, h]
      generalize (ctx.unionActivate? m (.loc b path)).getD m = m' at h' hs hw ⊢
      generalize ctx.activateBlk blk path = blk' at h' ⊢
      simp only [Ctx.reach?, h']
      rcases hr : ctx.reachIn blk' ty path with _ | r
      · simp only [Option.map_none, ite_true_eq_match, storeTy_loc_eq h', Ctx.punnedMember, h',
          Ctx.punnedIn, punnedAt, hs]
        rcases ha : Ty.atPath blk'.ty path with _ | t
        · rcases ht : ctx.typeAt blk'.ty path with _ | t
          · rfl
          · cases (ty.isScalar && t.isScalar && !t.accessCompatible ty) <;> rfl
        · cases (ty.isScalar && t.isScalar && !t.accessCompatible ty) <;> rfl
      · cases r with
        | byte pre t k =>
          simp only [Option.map_some, byteStore, read?_of_blocks h', write?_of_blocks h', hw]
        | obj p' =>
          simp only [Option.map_some, storeTy_loc_eq (Ctx.unionActivate?_getD_blocks h' p'),
            Ctx.storeAt_unionActivate?, hs]
        | punned => simp only [Option.map_some]
        | spread p' t => simp only [Option.map_some]
        | external => simp only [Option.map_some]
  all_goals rfl

/-! ### Pointer arithmetic in bytes (C11 6.5.6p8, 6.5.6p9) -/

/-- The canonical path of byte `r` of the object of type `t` and value `v` at
`path`: the outermost subobject that starts at that byte (record members by
their offsets, array elements; the end of an array is its one-past element, as
`Mem.stride?` gives it; in a union, its active member, the first that holds a
value as `Ctx.scalarIn` finds it, when the byte lies inside it), else a byte
view of the innermost scalar, or union, that contains it. -/
def Ctx.canonByte (ctx : Ctx) : Nat → Ty → Val → List PathElem → Nat → List PathElem
  | 0, _, _, path, r => if r = 0 then path else path ++ [.byte r]
  | fuel + 1, t, v, path, r =>
    if r = 0 then path else
    match t with
    | .array e n =>
      match ctx.sizeAlign 32 e with
      | some (s, _) =>
        if s ≠ 0 ∧ r = n * s then path ++ [.idx n]
        else if s = 0 ∨ n ≤ r / s then path ++ [.byte r]
        else
          let x := match v with
            | .arr xs => xs[r / s]?.getD .undef
            | _ => .undef
          ctx.canonByte fuel e x (path ++ [.idx (r / s)]) (r % s)
      | none => path ++ [.byte r]
    | .record name =>
      match ctx.record? name, ctx.memberOffsets name with
      | some rd, some offs =>
        if rd.kind = .union then
          match v with
          | .agg vs =>
            let j := (vs.findIdx? Val.holds).getD 0
            match rd.members[j]?, vs[j]? with
            | some (_, tj), some x =>
              match ctx.sizeAlign 32 tj with
              | some (sj, _) =>
                if r < sj then ctx.canonByte fuel tj x (path ++ [.idx j]) r else path ++ [.byte r]
              | none => path ++ [.byte r]
            | _, _ => path ++ [.byte r]
          | _ => path ++ [.byte r]
        else match ctx.memberAt 0 rd.members offs r with
          | some (j, tj, o) =>
            let x := match v with
              | .agg vs => vs[j]?.getD .undef
              | _ => .undef
            ctx.canonByte fuel tj x (path ++ [.idx j]) (r - o)
          | none => path ++ [.byte r]
      | _, _ => path ++ [.byte r]
    | _ => path ++ [.byte r]

/-! ### Integer addresses of pointers (the layout: `Ctx.segBits`) -/

/-- The address of a pointer into block `b` along `path` that has no flat address: in a
range of its own (from `2^62` for 8-byte pointers, from `0xE0000000` below `Ctx.fnBase`
for 4-byte ones), fixed by `b` and `path`. -/
def Ctx.otherAddr (ctx : Ctx) (b : Nat) (path : List PathElem) : Int :=
  let code : Int := ((b : Int) + 1) * 2 ^ 32 + path.foldl (fun acc e => acc * 1024 + (e.index : Int) + 1) 0
  if ctx.mod.ptrBytes = 4 then 0xE0000000 + code % 2 ^ 28 else 2 ^ 62 + code % 2 ^ 62

/-- The address a pointer converts to (`none` for a label or vtable address, not
modelled). -/
def Ctx.addrOf? (ctx : Ctx) (m : Mem) : Ptr → Option Int
  | .null => some 0
  | .addr a => some a
  | .loc b path =>
    match (m.blocks b).bind fun blk => ctx.absPos? blk.ty path with
    | some q =>
      if b + 1 < ctx.segLimit ∧ q < 2 ^ ctx.segBits then some ((b + 1) * 2 ^ ctx.segBits + q)
      else some (ctx.otherAddr b path)
    | none => some (ctx.otherAddr b path)
  | .fn f => (ctx.fnAddr? f).map fun a => (a : Int)
  | _ => none

/-- The pointer that the integer `c` converts to (its bits, truncated or extended to a
pointer's width, GCC): null for 0; in the range `[start, start + size]` of a live block,
the canonical pointer to that byte (`Ctx.canonByte`; `start + size` is one past the
block); at a function's address, the function; otherwise an `.addr` pointer. -/
def Ctx.ptrOfAddr (ctx : Ctx) (m : Mem) (c : Int) : Ptr :=
  let a := (wrap false ctx.ptrBits c).toNat
  let seg := 2 ^ ctx.segBits
  if a = 0 then .null
  else if seg ≤ a ∧ a / seg < ctx.segLimit then
    match m.live? (a / seg - 1) with
    | some blk =>
      match ctx.sizeAlign 32 blk.ty with
      | some (size, _) =>
        if a % seg ≤ size then .loc (a / seg - 1) (ctx.canonByte 32 blk.ty blk.val [] (a % seg))
        else .addr c
      | none => .addr c
    | none => .addr c
  else if ctx.fnBase ≤ a ∧ (a - ctx.fnBase) % 16 = 0 then
    match ctx.mod.funcs[(a - ctx.fnBase) / 16]? with
    | some f => .fn f.sym
    | none => .addr c
  else .addr c

/-- Whether two paths are elements of one array (the same parent path, of an
array type or of a type not known) or of one container: their structural
comparison is that of their positions. -/
def Ctx.sameArray (ctx : Ctx) (bty : Ty) (path path' : List PathElem) : Bool :=
  match splitLast path, splitLast path' with
  | some (pre, .idx _), some (pre', .idx _) =>
    pre == pre' &&
      (match ctx.typeAt bty pre with
       | some (.array _ _) => true
       | some _ => false
       | none => true)
  | some (pre, .vel _ _), some (pre', .vel _ _) => pre == pre'
  | _, _ => false

/-- Pointer equality (C11 6.5.9p6). Two pointers into the same block compare
by their byte positions in its complete object (`Ctx.absPos?`): a pointer to an
object and one to a subobject at its beginning compare equal (6.7.2.1p15, p16:
a structure and its first member, an array and its element 0, a union and its
members), and so do the pointer one past an object and one to the object that
follows it. Elements of one array compare by their paths (`Ctx.sameArray`, the
same result), as do paths without a byte position. A pointer converted from an
integer that designates no object (`.addr`) compares with an object or function
pointer by address (`Ctx.addrOf?`). Other pointers into different blocks, or not
into a block, compare as `Mem.ptrEq?` says. -/
def Ctx.ptrEq? (ctx : Ctx) (m : Mem) (p q : Ptr) : Option Bool :=
  match p, q with
  | .loc b path, .loc b' path' =>
    if b = b' then
      match m.blocks b with
      | some blk =>
        if ctx.sameArray blk.ty path path' then some (path == path')
        else
          match ctx.absPos? blk.ty path, ctx.absPos? blk.ty path' with
          | some i, some j => some (i == j)
          | _, _ => some (path == path')
      | none => m.ptrEq? p q
    else m.ptrEq? p q
  | .addr a, .loc b path | .loc b path, .addr a =>
    (ctx.addrOf? m (.loc b path)).map fun x => wrap false ctx.ptrBits x == wrap false ctx.ptrBits a
  | .addr a, .fn f | .fn f, .addr a =>
    some ((ctx.fnAddr? f).any fun x => wrap false ctx.ptrBits x == wrap false ctx.ptrBits a)
  | _, _ => m.ptrEq? p q

/-- Whether two pointers designate subobjects of the same parent object in the
same block (the paths but their last steps agree). -/
def Ptr.sameParent : Ptr → Ptr → Bool
  | .loc b path, .loc b' path' =>
    b == b' &&
      (match splitLast path, splitLast path' with
       | some (pre, _), some (pre', _) => pre == pre'
       | _, _ => false)
  | _, _ => false

/-- Slot `k` of array `i` of the vtable `vt` moved by `d` bytes: whole slots
of a pointer's size, in the array (the virtual base offsets and the offset to
the top that precede a vptr's address point, Itanium C++ ABI 2.5.2). -/
def Ctx.vtableStride? (ctx : Ctx) (vt : String) (i k : Nat) (d : Int) : Option Ptr :=
  let s : Int := ctx.mod.ptrBytes
  if s ≠ 0 ∧ d % s = 0 ∧ 0 ≤ k + d / s then some (.vtable vt i (k + d / s).toNat) else none

/-- `p + n` for a pointer to a character type that is no element of a
character array: byte positions in the block's complete object (C11 6.2.6.1p4,
6.3.2.3p7: the bytes of an object's representation), `0 ≤ q ≤` its size, the
result in canonical form (`Ctx.canonByte`), so that the pointer converted back
designates the subobject at that byte (`offsetof`, `container_of`); a vtable
slot by `Ctx.vtableStride?`; `p` itself for `n = 0` (as `Mem.stride?`). -/
def Ctx.charStride? (ctx : Ctx) (m : Mem) (p : Ptr) (n : Int) : Option Ptr :=
  if n = 0 then (match p with | .loc _ _ | .vtable .. => some p | _ => none) else
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match ctx.absPos? blk.ty path, ctx.sizeAlign 32 blk.ty with
      | some q0, some (s, _) =>
        let q : Int := q0 + n
        if 0 ≤ q ∧ q ≤ s then some (.loc b (ctx.canonByte 32 blk.ty blk.val [] q.toNat)) else none
      | _, _ => none
    | none => none
  | .vtable vt i k => ctx.vtableStride? vt i k n
  | _ => none

/-- `p - p'` for pointers to a character type: their byte positions in the
same block's complete object. -/
def Ctx.charDiff? (ctx : Ctx) (m : Mem) : Ptr → Ptr → Option Int
  | .loc b path, .loc b' path' =>
    if b = b' then
      match m.blocks b with
      | some blk =>
        match ctx.absPos? blk.ty path, ctx.absPos? blk.ty path' with
        | some q, some q' => some ((q : Int) - q')
        | _, _ => none
      | none => none
    else none
  | _, _ => none

/-- The object of `e` bytes that the object of type `t` at `path` starts with:
the object itself, else (recursively) its element 0, or the first member of a
structure (C11 6.7.2.1p15). -/
def Ctx.sizedAt (ctx : Ctx) : Nat → Ty → List PathElem → Nat → Option (List PathElem)
  | 0, _, _, _ => none
  | fuel + 1, t, path, e =>
    match ctx.sizeAlign 32 t with
    | some (s, _) =>
      if s = e then some path
      else match t with
        | .array et len => if 0 < len then ctx.sizedAt fuel et (path ++ [.idx 0]) e else none
        | .record name =>
          match ctx.record? name with
          | some rd =>
            if rd.kind = .union then none
            else match rd.members.head? with
              | some (_, t0) => ctx.sizedAt fuel t0 (path ++ [.idx 0]) e
              | none => none
          | none => none
        | _ => none
    | none => none

/-- The array whose element the subobject at `path` is: its path, element size
and count, and the element's index. -/
def Ctx.elemOf? (ctx : Ctx) (bty : Ty) (path : List PathElem) : Option (List PathElem × Nat × Nat × Nat) :=
  match splitLast path with
  | some (pre, .idx i) =>
    match ctx.typeAt bty pre with
    | some (.array et len) => (ctx.sizeAlign 32 et).map fun (s, _) => (pre, s, len, i)
    | _ => none
  | _ => none

/-- How a pointer moves as a pointer to a non-character type of `e` bytes
(C11 6.5.6p7, p8). -/
inductive Lens where
  /-- An element of an array of `e`-byte elements: `Mem.stride?` / `Mem.diff?`. -/
  | elem (path : List PathElem)
  /-- The object at `obj`, which is no array element, as an array of one, at
  index `j`: 0, or 1 for the pointer one past it (`obj ++ [.byte e]`). -/
  | one (obj : List PathElem) (j : Nat)
  /-- Byte `q` of the array at `base` of `len` elements of `s ≠ e` bytes: a
  stride in other units than the elements' (`*(int *)((short *)a + 2)`). -/
  | bytes (base : List PathElem) (s len q : Nat)
  deriving Inhabited

/-- The `Lens` of a pointer for a non-character type of `e` bytes. An object of
`e` bytes that the pointed-to object starts with (`Ctx.sizedAt`: a pointer to
an array object used as a pointer to its element type is one to element 0; a
pointer to a structure converted to a pointer to its first member's type is one
to that member) is an array element (`elem`) or a lone object (`one`); else an
array element of another size is a byte position in its array (`bytes`); else
the object is a lone object. A byte view is a byte position in its element's
array, or the pointer one past a lone object (`k = e`). -/
def Ctx.lens? (ctx : Ctx) (m : Mem) (e : Nat) : Ptr → Option (Nat × Lens)
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match splitLast path with
      | some (pre, .byte k) =>
        match ctx.elemOf? blk.ty pre with
        | some (base, s, len, i) => if s ≠ e ∧ k < s then some (b, .bytes base s len (i * s + k)) else none
        | none => if k = e then some (b, .one pre 1) else none
      | _ =>
        match ctx.typeAt blk.ty path with
        | some t =>
          match ctx.sizedAt 32 t path e with
          | some pT => if (ctx.elemOf? blk.ty pT).isSome then some (b, .elem pT) else some (b, .one pT 0)
          | none =>
            match ctx.elemOf? blk.ty path with
            | some (base, s, len, i) => some (b, .bytes base s len (i * s))
            | none => some (b, .one path 0)
        | none => none
    | none => none
  | _ => none

/-- `p + n` for a pointer to a non-character type of `e` bytes that is no
element of an array of its size, by its `Ctx.lens?`: an array element by
`Mem.stride?`; a lone object as an array of one (C11 6.5.6p7, p8: `n` in
`{0, 1}`, one past it a byte view `.byte e` through which no access is
defined); a byte position moved by `n * e` within its array (an element, or a
byte view of it); a vtable slot by `Ctx.vtableStride?`; `p` itself for
`n = 0`. -/
def Ctx.lensStride? (ctx : Ctx) (m : Mem) (p : Ptr) (n : Int) (e : Nat) : Option Ptr :=
  if n = 0 then (match p with | .loc _ _ | .vtable .. => some p | _ => none) else
  if let .vtable vt i k := p then ctx.vtableStride? vt i k (n * e) else
  match ctx.lens? m e p with
  | some (b, .elem pT) => m.stride? (.loc b pT) n
  | some (b, .one obj j) =>
    let j' : Int := j + n
    if j' = 0 then some (.loc b obj) else if j' = 1 then some (.loc b (obj ++ [.byte e])) else none
  | some (b, .bytes base s len q) =>
    let q' : Int := q + n * e
    if 0 ≤ q' ∧ q' ≤ len * s then
      let r := q'.toNat
      some (.loc b (base ++ (if r % s = 0 then [.idx (r / s)] else [.idx (r / s), .byte (r % s)])))
    else none
  | none => none

/-- `p - p'` for pointers to a non-character type of `e` bytes (C11 6.5.6p9):
elements of one array (`Mem.diff?`), the indices of one lone object, or byte
positions in one array that differ by a multiple of `e`. -/
def Ctx.lensDiff? (ctx : Ctx) (m : Mem) (p p' : Ptr) (e : Nat) : Option Int :=
  match ctx.lens? m e p, ctx.lens? m e p' with
  | some (b, .elem q), some (b', .elem q') => if b = b' then m.diff? (.loc b q) (.loc b' q') else none
  | some (b, .one o j), some (b', .one o' j') => if b = b' ∧ o = o' then some ((j : Int) - j') else none
  | some (b, .bytes base _ _ q), some (b', .bytes base' _ _ q') =>
    let d : Int := (q : Int) - q'
    if b = b' ∧ base = base' ∧ e ≠ 0 ∧ d % e = 0 then some (d / e) else none
  | _, _ => none

/-- The element type of the array whose element `p` designates (the elements
`Mem.stride?` moves it over): `some (some et)`; `some none` when it is not known
(a container element, a path of unknown type, a block of unknown size); `none`
for a byte view, a record member, the block's object or a vtable slot (whose
arithmetic is in bytes, `Ctx.vtableStride?`). -/
def Ctx.elemTyOf? (ctx : Ctx) (m : Mem) : Ptr → Option (Option Ty)
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match splitLast path with
      | some (pre, .idx _) =>
        match ctx.typeAt blk.ty pre with
        | some (.array et _) => some (some et)
        | some _ => none
        | none => some none
      | some (_, .vel _ _) => some none
      | some (_, .byte _) => none
      | none => if (ctx.sizeAlign 32 blk.ty).isSome then none else some none
    | none => some none
  | .vtable .. => none
  | _ => some none

/-- Whether `p`'s arithmetic as a pointer to `elemTy` is in its element's
units (today's `Mem.stride?` / `Mem.diff?`): `p` designates an array element
of the size of `elemTy` (or either size is not known). -/
def Ctx.sameUnits (ctx : Ctx) (m : Mem) (p : Ptr) (elemTy : Ty) : Bool :=
  match ctx.elemTyOf? m p with
  | some (some et) =>
    match ctx.sizeAlign 32 et, ctx.sizeAlign 32 elemTy with
    | some (s, _), some (e, _) => s == e
    | _, _ => true
  | some none => true
  | none => false

/-- `p + n` for a pointer to `elemTy` (`cir.ptr_stride`; C11 6.5.6p8: a stride
counts objects of the pointer's type): in its element's units (`Mem.stride?`)
when `p` is an element of an array of elements of `elemTy`'s size; else for a
character type in bytes over the complete object (`Ctx.charStride?`), for
another type by the pointer's `Ctx.lens?` (`Ctx.lensStride?`). `void *` counts
bytes, as `char *` (`Ty.isVoid`). -/
def Ctx.stride? (ctx : Ctx) (m : Mem) (p : Ptr) (n : Int) (elemTy : Ty) : Option Ptr :=
  let elemTy := if elemTy.isVoid then .int false 8 else elemTy
  if ctx.sameUnits m p elemTy then m.stride? p n
  else if elemTy.isChar then ctx.charStride? m p n
  else match ctx.sizeAlign 32 elemTy with
    | some (e, _) => ctx.lensStride? m p n e
    | none => none

/-- `p - p'` for pointers to `elemTy` (`cir.ptr_diff`; C11 6.5.6p9): in their
elements' units (`Mem.diff?`) when both are elements of arrays of elements of
`elemTy`'s size; else for a character type the difference of their byte
positions (`Ctx.charDiff?`), for another type by their `Ctx.lens?`
(`Ctx.lensDiff?`). `void *` counts bytes, as `char *`. -/
def Ctx.diff? (ctx : Ctx) (m : Mem) (p p' : Ptr) (elemTy : Ty) : Option Int :=
  let elemTy := if elemTy.isVoid then .int false 8 else elemTy
  if ctx.sameUnits m p elemTy && ctx.sameUnits m p' elemTy then m.diff? p p'
  else if elemTy.isChar then ctx.charDiff? m p p'
  else match ctx.sizeAlign 32 elemTy with
    | some (e, _) => ctx.lensDiff? m p p' e
    | none => none

/-- Whether a pointer is a byte view (`.byte k` last). -/
def Ptr.isByteView : Ptr → Bool
  | .loc _ path =>
    match splitLast path with
    | some (_, .byte _) => true
    | _ => false
  | _ => false

end CIR
