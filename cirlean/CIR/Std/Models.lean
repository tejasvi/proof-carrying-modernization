import CIR.Semantics.Basic
import CIR.Std.Complex
import CIR.Std.Libm
import CIR.Std.LibmCR
import CIR.Std.Hash

/-!
  Native Lean models of C++ standard library functions.

  Calling conventions are those of CIR before calling-convention lowering:
  `this` is the first argument (a pointer), references are pointers, small
  classes returned by value (iterators) are returned as `agg` values.

  Abstract representations:
  * `std::vector<T>`: `Val.vec g xs`, the elements in order;
  * `std::string`:    `Val.vec g (chars ++ [0])` (terminator kept);
  * `std::optional<T>`: `Val.opt (some v)` / `Val.opt none`;
  * `std::unique_ptr<T>`: `Val.agg [Val.ptr p]`;
  * contiguous iterators (`__wrap_iter<T*>`): `Val.agg [Val.ptr p]`.

  `g` is a generation number. Constructors and every operation that may
  reallocate (push_back, pop_back, clear, resize, reserve, assignment, swap)
  install a fresh generation, which invalidates all element pointers and
  iterators into the container. This is conservative (C++ keeps some of them
  valid), hence sound.
-/

namespace CIR.Std

open CIR

/-- `fresh` in compiled code: the memory's run-time cell keeps its map (`MemRT.withNext`). -/
unsafe def freshImpl (m : Mem) : Nat × Mem := (m.next, MemRT.withNext m (m.next + 1))

/-- A fresh generation number (shares the counter with block ids). -/
@[implemented_by freshImpl]
def fresh (m : Mem) : Nat × Mem := (m.next, { m with next := m.next + 1 })

def readVal (m : Mem) (p : Ptr) : Res Val := Res.ofOption "invalid read in library model" (m.read? p)

/-- The `long` of a `jmp_buf` at `p` (a `struct __jmp_buf_tag`) that holds a `setjmp` token: the
first element of its `__jmpbuf` array. -/
def jmpSlot : Ptr → Ptr
  | .loc b path => .loc b (path ++ [.idx 0, .idx 0])
  | p => p

/-- Where `setjmp` keeps the token of its invocation (token block `tok`) in the buffer at `p`, and
the value that holds it: in a `jmp_buf`, the block's id + 1 in its first `long` (`jmpSlot`); in the
buffer of `__builtin_setjmp`, an array of pointers or of 64-bit integers whose address CIR passes
as a `void **`, that number in its second word, where GCC keeps the resume address (in an array of
pointers as an integer address, `Ptr.addr`). That buffer must hold five words from `p` (GCC's
`intptr_t buf[5]`; CIR's code for the builtin writes words 0 and 2, `dropSetjmpWordOps`): `none`
for a shorter one, as for any other buffer. -/
def jmpTokenAt (ctx : Ctx) (m : Mem) (p : Ptr) (tok : Nat) : Option (Ptr × Val) :=
  match p with
  | .loc b path =>
    match (m.blocks b).bind fun blk => ctx.typeAt blk.ty path with
    | some (.ptr _) =>
      if (m.stride? p 5).isSome then (m.stride? p 1).map fun q => (q, .ptr (.addr (tok + 1))) else none
    | some (.int _ 64) =>
      if (m.stride? p 5).isSome then (m.stride? p 1).map fun q => (q, .int (tok + 1)) else none
    | _ => some (jmpSlot p, .int (tok + 1))
  | _ => none

/-- The number that the buffer at `p` holds where `setjmp` keeps its token (`jmpTokenAt`). -/
def jmpTokenWord? (ctx : Ctx) (m : Mem) (p : Ptr) : Option Int :=
  match jmpTokenAt ctx m p 0 with
  | some (q, _) =>
    match m.read? q with
    | some (.int t) | some (.ptr (.addr t)) => some t
    | _ => none
  | none => none

/-- `Model.longjmp`: `longjmp(env, v)`, or `__builtin_longjmp(buf)`, whose value is 1 (GCC requires
the constant 1): back to the `setjmp` invocation whose token the buffer holds (`Exit.longjmp`). -/
def longjmpModel (ctx : Ctx) (args : List Val) (m : Mem) : Res (Exit × Mem) :=
  match args with
  | .ptr env :: rest =>
    match (match rest with | [.int v] => some v | [] => some 1 | _ => none) with
    | none => .ub "longjmp: invalid arguments"
    | some v =>
      match jmpTokenWord? ctx m env with
      | some t =>
        match m.live? (t.toNat - 1) with
        | some ⟨.stack, _, .other "setjmp", _⟩ =>
          if 0 < t then .ok (.longjmp (t.toNat - 1) (if v = 0 then 1 else v), m)
          else .ub ("longjmp: the jmp_buf holds no setjmp (C11 7.13.2.1p2 when none was called; a " ++
            "setjmp in a block that branches is not modelled)")
        | _ => .ub ("longjmp to a setjmp that is no longer active (C11 7.13.2.1p2 when its function " ++
            "has returned; a block left meanwhile is not modelled)")
      | none => .ub ("longjmp: the jmp_buf holds no setjmp (C11 7.13.2.1p2 when none was called; a " ++
          "setjmp in a block that branches is not modelled)")
  | _ => .ub "longjmp: invalid arguments"

def writeVal (m : Mem) (p : Ptr) (v : Val) : Res Mem :=
  Res.ofOption "invalid write in library model" (m.write? p v)

/-! ### What a `longjmp` back finds changed (C11 7.13.2.1p3)

Each live `setjmp` invocation has a token block (`Op.setjmp`) holding its snapshot: an entry
`[b, v0, sv, snv, dv, mods]` per automatic object `b` of its function (`forgetWrites`). A store
anywhere, in the function of the `setjmp`, in a callee or in a library model, is recorded in the
snapshots that hold its object (`sjMarkMem`), found through a registry of the live invocations. -/

/-- A path of member indices, as a `setjmp` snapshot holds it. -/
def pathVal (p : List Nat) : Val := .arr (p.map fun (i : Nat) => .int i)

/-- The paths of a `setjmp` snapshot field (`pathVal`s). -/
def pathsOf : Val → List (List Nat)
  | .arr ps => ps.map fun p => match p with
    | .arr is => is.filterMap fun v => match v with
      | .int i => some i.toNat
      | _ => none
    | _ => []
  | _ => []

/-- The member path of a pointer path (`none` through a container element or a byte). -/
def memberPath? : List PathElem → Option (List Nat)
  | [] => some []
  | .idx i :: rest => (memberPath? rest).map (i :: ·)
  | _ => none

/-- `p` added to the paths `ps` (a snapshot field), once. -/
def addPath (ps : Val) (p : List Nat) : Val :=
  if (pathsOf ps).contains p then ps else match ps with
    | .arr xs => .arr (xs ++ [pathVal p])
    | _ => .arr [pathVal p]

/-- The symbol of the registry of the live `setjmp` invocations, a global that the frontend adds to
a module with a `setjmp` (`Frontend.sjNotes`): the ids of their token blocks. -/
def sjRegistrySym : String := "cirlean.setjmps"

/-- The token blocks of the live `setjmp` invocations (`sjRegistrySym`); none in a module without
the registry. -/
def sjTokens (ctx : Ctx) (m : Mem) : List Nat :=
  match ctx.gaddr sjRegistrySym with
  | some r => match m.read? (.loc r []) with
    | some (.arr ts) => ts.filterMap fun v => match v with
      | .int t => if (m.live? t.toNat).isSome then some t.toNat else none
      | _ => none
    | _ => []
  | none => []

/-- The registry with the token block `tok` of a new `setjmp` invocation added (and the ended ones
dropped); memory as it is in a module without the registry. -/
def sjRegister (ctx : Ctx) (m : Mem) (tok : Nat) : Mem :=
  match ctx.gaddr sjRegistrySym with
  | some r => (m.write? (.loc r []) (.arr ((sjTokens ctx m ++ [tok]).map fun (t : Nat) => .int t))).getD m
  | none => m

/-- The snapshot of token block `tok` recording, when it holds object `b`, a store into it
(`store`, at the member path of `q`; the whole object through a container element or a byte) and
a `volatile` access (`vol`, at that member path; none through a container element or a byte). -/
def sjMarkOne (b : Nat) (q : List PathElem) (store vol : Bool) (m : Mem) (tok : Nat) : Mem :=
  match m.live? tok with
  | some ⟨.stack, _, .other "setjmp", .agg snap⟩ =>
    if !snap.any (fun en => match en with | .agg (.int b' :: _) => b'.toNat == b | _ => false) then m else
    let snap' := snap.map fun en => match en with
      | .agg [.int b', v0, sv, snv, dv, mods] =>
        if b'.toNat == b then
          .agg [.int b', v0, sv, snv,
            (if vol then (match memberPath? q with | some p => addPath dv p | none => dv) else dv),
            (if store then addPath mods ((memberPath? q).getD []) else mods)]
        else en
      | en => en
    (m.write? (.loc tok []) (.agg snap')).getD m
  | _ => m

/-- A store into the object `p` points into (`store`) and a `volatile` access through `p` (`vol`),
recorded in the snapshot of every live `setjmp` invocation that holds the object (`sjMarkOne`):
`Op.sjNote`, and the library models' stores into the program's objects. -/
def sjMarkMem (ctx : Ctx) (m : Mem) (p : Ptr) (store vol : Bool) : Mem :=
  match p with
  | .loc b q => (sjTokens ctx m).foldl (sjMarkOne b q store vol) m
  | _ => m

/-- `v` stored at `p` as by a store of the program (`Ctx.typedStore`), noted for the live `setjmp`
invocations (`sjMarkMem`): a library model's store into a program's object. -/
def storeMarked (ctx : Ctx) (m : Mem) (ty : Ty) (p : Ptr) (v : Val) : Res Mem := do
  return sjMarkMem ctx (← ctx.typedStore m ty p v) p true false

/-- `v` written at `p` (`msg` if it cannot be), noted for the live `setjmp` invocations. -/
def writeMarked (ctx : Ctx) (m : Mem) (p : Ptr) (v : Val) (msg : String) : Res Mem := do
  return sjMarkMem ctx (← Res.ofOption msg (m.write? p v)) p true false

/-- `sjRegister`, as a step of `Op.setjmp`. -/
def sjRegisterR (ctx : Ctx) (m : Mem) (tok : Nat) : Res Mem := pure (sjRegister ctx m tok)

/-- `*end = p` for the `strto*` models: a `char *` stored through the end
pointer, typed and checked as a store of the program (`Ctx.typedStore`: the
object must hold a pointer, also as a record member or array element, C11
6.5p7), and noted for the live `setjmp` invocations (`sjMarkMem`). A null end
pointer stores nothing. -/
def storeEnd (ctx : Ctx) (m : Mem) (e p : Val) : Res Mem :=
  match e with
  | .ptr .null => pure m
  | .ptr q => storeMarked ctx m (.ptr (.int true 8)) q p
  | _ => .ub "the end pointer argument is not a pointer"

/-- `__cxa_guard_release` / `__cxa_guard_abort`: `x` stored into the guard
variable at `g`, an integer object, as a typed store. -/
def storeGuard (ctx : Ctx) (m : Mem) (g : Ptr) (x : Int) (what : String) : Res Mem :=
  match g with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      match ctx.typeAt blk.ty path with
      | some (.int s w) => ctx.typedStore m (.int s w) g (.int x)
      | _ => .ub s!"{what}: not a guard variable"
    | none => .ub s!"{what}: not a guard variable"
  | _ => .ub s!"{what}: not a guard variable"

/-- The path from a value to its first container: the value itself, or the first
element of an array, recursively. -/
def firstVec : Val → Option (List PathElem)
  | .vec _ _ => some []
  | .arr (x :: _) => (firstVec x).map (.idx 0 :: ·)
  | _ => none

/-- The container at the address of a pointer that designates none. CIR stores
the address of an `initializer_list`'s backing array object (`T(*)[N]`, through
a bitcast) as its `const T*` begin (`initListCtor`); for containers `T` whose
list the program's own code walks (the elements of a vector of vectors or of
strings), that pointer designates the array, and its strides are byte views of
the array object (`Ctx.stride?`). The container is then the first element of
the array, or the element at a byte view of it at a multiple of the element
size. -/
def containerAt? (ctx : Ctx) (m : Mem) : Ptr → Option Ptr
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      let elem : Option (List PathElem) := match splitLast path with
        | some (pre, .byte k) =>
          match ctx.typeAt blk.ty pre with
          | some (.array e n) =>
            match ctx.sizeAlign 32 e with
            | some (s, _) => if 0 < s ∧ k % s = 0 ∧ k / s < n then some (pre ++ [.idx (k / s)]) else none
            | none => none
          | _ => none
        | _ => some path
      match elem with
      | some q =>
        match blk.val.get? q with
        | some v => (firstVec v).map fun r => .loc b (q ++ r)
        | none => none
      | none => none
    | none => none
  | _ => none

/-- The container a container model's object pointer designates: the pointer
itself, or (when it designates no container) the container at its address
(`containerAt?`), for the element pointers a model returns. -/
def contPtr (ctx : Ctx) (m : Mem) (p : Ptr) : Ptr :=
  match m.read? p with
  | some (.vec _ _) => p
  | _ => (containerAt? ctx m p).getD p

mutual
/-- libc++'s members of an empty `std::vector` where no constructor of the model ran: every
member a null pointer (or zero), recursively. `std::vector`'s default constructor is `constexpr`,
so a global is constant-initialized (no dynamic initialization calls it), and CIR may spell a
defaulted constructor as the member stores. -/
def isEmptyVecLayout : Val → Bool
  | .agg fs => isEmptyVecLayoutList fs
  | .ptr .null => true
  | .int 0 => true
  | _ => false
def isEmptyVecLayoutList : List Val → Bool
  | [] => true
  | v :: vs => isEmptyVecLayout v && isEmptyVecLayoutList vs
end

/-- Whether `p` designates an object of type `std::vector<…>` (libc++'s or libstdc++'s record). -/
def isVecObject (ctx : Ctx) (m : Mem) : Ptr → Bool
  | .loc b path => match m.blocks b with
    | some blk => match ctx.typeAt blk.ty path with
      | some (.record n) => n.startsWith "std::__1::vector<" || n.startsWith "std::vector<"
      | _ => false
    | none => false
  | _ => false

/-- Read a container value `vec g xs`; through a pointer that designates no
container, the container at its address (`containerAt?`); a `std::vector` object
holding libc++'s members of an empty vector (`isEmptyVecLayout`) is an empty
vector (generation 0: no element pointer of it exists, `ensureVec` gives it a
container before one is formed). -/
def readVec (ctx : Ctx) (m : Mem) (p : Ptr) : Res (Nat × List Val) :=
  match m.read? p with
  | some (.vec g xs) => pure (g, xs)
  | r =>
    match (containerAt? ctx m p).bind m.read? with
    | some (.vec g xs) => pure (g, xs)
    | _ => match r with
      | none => .ub "invalid read in library model"
      | some v =>
        if isEmptyVecLayout v && isVecObject ctx m p then pure (0, [])
        else .ub "object is not a live std::vector / std::string"

/-- Store a container value under a fresh generation. -/
def writeVec (m : Mem) (p : Ptr) (xs : List Val) : Res Mem :=
  let (g, m) := fresh m
  writeVal m p (.vec g xs)

/-- The memory where the `std::vector` object at `p` holds a container: an object
`readVec` reads as an empty vector from libc++'s members (`isEmptyVecLayout`) gets the
empty container, before an element pointer (`begin`, `end`, `data`) into it is formed. -/
def ensureVec (ctx : Ctx) (m : Mem) (p : Ptr) : Res Mem :=
  match m.read? p, (containerAt? ctx m p).bind m.read? with
  | some (.vec _ _), _ => .ok m
  | _, some (.vec _ _) => .ok m
  | some v, _ => if isEmptyVecLayout v && isVecObject ctx m p then writeVec m p [] else .ok m
  | none, _ => .ok m

/-- Pointer to element `i` of the container at `p` (generation `g`). -/
def elemPtr (p : Ptr) (g i : Nat) : Res Ptr :=
  match p with
  | .loc b path => .ok (.loc b (path ++ [.vel g i]))
  | _ => .ub "bad container pointer"

def fieldPtr (p : Ptr) (i : Nat) : Res Ptr :=
  match p with
  | .loc b path => .ok (.loc b (path ++ [.idx i]))
  | _ => .ub "bad object pointer"

/-- Throw a library exception (object contents are not modelled). -/
def throwLib (m : Mem) (typeinfo : String) : Res (Exit × Mem) :=
  let (b, m) := m.alloc .exn (.other typeinfo) (.agg [])
  .ok (.exn ⟨.loc b [], typeinfo⟩, m)

def retv (v : Val) (m : Mem) : Res (Exit × Mem) := .ok (.ret (some v), m)
def retVoid (m : Mem) : Res (Exit × Mem) := .ok (.ret none, m)

/-- `size_t` result. -/
def sizeVal (n : Nat) : Res Val :=
  if inRange false 64 n then .ok (.int n) else .ub "size overflow"

/-- Read the pointer held by an iterator / unique_ptr object. -/
def readBoxedPtr (m : Mem) (p : Ptr) : Res Ptr := do
  match ← readVal m p with
  | .agg [.ptr q] => pure q
  | _ => .ub "object does not hold a pointer"

/-- The element a `std::vector<bool>` reference proxy at `p` designates (`vecBoolModel`). -/
def bitRefElem (m : Mem) (p : Ptr) : Res Ptr := do
  match ← readVal m p with
  | .agg [.ptr q, _] => pure q
  | _ => .ub "std::vector<bool>: the reference was not formed by operator[] or at"

/-- A `std::vector<bool>` element's value. -/
def boolElem : Val → Res Bool
  | .bool b => pure b
  | _ => .ub "std::vector<bool>: an element is no bool"

/-- A C string's terminator. -/
def isNulVal (x : Val) : Bool := match x with | .int c => c == 0 | _ => false

/-- A character of a C string (not indeterminate). -/
def isIntVal (x : Val) : Bool := match x with | .int _ => true | _ => false

/-- The value of the character object `p` designates, when its type (as far as `Ty.atPath` knows
it from the block's type) is a character type: a pointer to an object that is no array element
acts as a pointer to the first element of an array of length one (C11 6.5.6p7). -/
def charObject? (m : Mem) (p : Ptr) : Option Val :=
  match p with
  | .loc b path => match m.blocks b with
    | some blk => match Ty.atPath blk.ty path, m.read? p with
      | some (.int _ 8), some v => some v
      | _, _ => none
    | none => none
  | _ => none

/-- A pointer to a nonempty array object as a pointer to its element 0, as bytes' rule makes a
pointer to an array object converted to a pointer to its element type (`CHANGES_bytes.md`, 2 and
3): the name of a typeinfo constant points to its `_ZTS` array object. `none` for other pointers. -/
def arrayObjStart? (m : Mem) : Ptr → Option Ptr
  | .loc b path => match m.read? (.loc b path) with
    | some (.arr (_ :: _)) => some (.loc b (path ++ [.idx 0]))
    | _ => none
  | _ => none

/-- Read a C string (pointer into a char array) up to its terminator. -/
def readCStr (m : Mem) (p : Ptr) : Res (List Val) :=
  match m.elemPos? p with
  | some (b, pre, .idx i, _) => do
    match ← readVal m (.loc b pre) with
    | .arr xs =>
      let rest := xs.drop i
      match rest.findIdx? isNulVal with
      | some k =>
        let cs := rest.take k
        if cs.all isIntVal then pure cs
        else .ub "indeterminate character in C string"
      | none => .ub "unterminated C string"
    | _ => .ub "C string does not point into a char array"
  | _ =>
    -- a character object that is no array element: an array of one (C11 6.5.6p7)
    match charObject? m p with
    | some v => if isNulVal v then pure [] else .ub "unterminated C string"
    | none =>
      -- a pointer to an array object: its element 0
      match arrayObjStart? m p, m.read? p with
      | some _, some (.arr xs) =>
        match xs.findIdx? isNulVal with
        | some k =>
          let cs := xs.take k
          if cs.all isIntVal then pure cs
          else .ub "indeterminate character in C string"
        | none => .ub "unterminated C string"
      | _, _ => .ub "C string pointer is not an array element pointer"

/-- The characters `%s` with precision `n` writes (C11 7.21.6.1p8): those of
the array at `p` up to its terminator or the `n`th, whichever comes first;
the array needs no terminator within its first `n` elements. -/
def readCStrN (m : Mem) (p : Ptr) (n : Nat) : Res (List Val) :=
  match m.elemPos? p with
  | some (b, pre, .idx i, _) => do
    match ← readVal m (.loc b pre) with
    | .arr xs =>
      let rest := (xs.drop i).take n
      let cs := match rest.findIdx? isNulVal with
        | some k => rest.take k
        | none => rest
      if cs.length < n && (rest.findIdx? isNulVal).isNone then .ub "unterminated C string"
      else if cs.all isIntVal then pure cs
      else .ub "indeterminate character in C string"
    | _ => .ub "C string does not point into a char array"
  | _ =>
    -- a character object that is no array element: an array of one (C11 6.5.6p7)
    match charObject? m p with
    | some v =>
      if n == 0 || isNulVal v then pure []
      else if 1 < n then .ub "unterminated C string"
      else if isIntVal v then pure [v]
      else .ub "indeterminate character in C string"
    | none =>
      -- a pointer to an array object: its element 0
      match arrayObjStart? m p, m.read? p with
      | some _, some (.arr xs) =>
        let rest := xs.take n
        let cs := match rest.findIdx? isNulVal with
          | some k => rest.take k
          | none => rest
        if cs.length < n && (rest.findIdx? isNulVal).isNone then .ub "unterminated C string"
        else if cs.all isIntVal then pure cs
        else .ub "indeterminate character in C string"
      | _, _ => .ub "C string pointer is not an array element pointer"

/-- The elements of the array that `p` points into, from `p` to its end. -/
def arrTail (m : Mem) (p : Ptr) : Res (List Val) :=
  match m.elemPos? p with
  | some (b, pre, .idx i, _) => do
    match ← readVal m (.loc b pre) with
    | .arr xs => pure (xs.drop i)
    | _ => .ub "string does not point into a char array"
  | _ =>
    -- a pointer to an array object: its element 0
    match arrayObjStart? m p, m.read? p with
    | some _, some (.arr xs) => pure xs
    | _, _ => .ub "string pointer is not an array element pointer"

/-- The element pointers of `[first, last)` when both point into one array (or
container) with `first <= last`; `none` otherwise. -/
def rangePtrs (m : Mem) (first last : Ptr) : Option (List Ptr) :=
  match m.elemPos? first, m.elemPos? last with
  | some (b, pre, e, n), some (b', pre', e', _) =>
    if b = b' ∧ pre = pre' ∧ e.withIndex 0 = e'.withIndex 0 ∧ e.index ≤ e'.index ∧ e'.index ≤ n then
      some ((List.range (e'.index - e.index)).map fun k => .loc b (pre ++ [e.withIndex (e.index + k)]))
    else none
  | _, _ => none

/-- `strncmp` over the remaining characters, at most `n` of them: the
difference of the first differing characters (as `unsigned char`), 0 if
none differ before a terminator. Reading past an array is undefined. -/
def strncmpVals : Nat → List Val → List Val → Res Int
  | 0, _, _ => pure 0
  | n + 1, .int x :: xs, .int y :: ys =>
    let ux := x % 256
    let uy := y % 256
    if ux != uy then pure (ux - uy)
    else if ux == 0 then pure 0
    else strncmpVals n xs ys
  | _ + 1, _, _ => .ub "string comparison outside the strings or of an indeterminate character"

/-- Leading decimal digits of a character list: their value and count. -/
def takeDigits : List Int → Nat × Nat
  | c :: cs =>
    if 48 ≤ c && c ≤ 57 then
      let (v, k) := takeDigits cs
      -- value of the digits, most significant first: recombined below
      (v, k + 1)
    else (0, 0)
  | [] => (0, 0)

/-- Value of the first `k` digits of `cs`. -/
def digitsVal (cs : List Int) (k : Nat) : Nat :=
  (cs.take k).foldl (fun acc c => acc * 10 + (c - 48).toNat) 0

/-- Decimal digits of `n` (most significant first). -/
def natDigits (fuel n : Nat) : List Int :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n < 10 then [(n : Int) + 48] else natDigits fuel (n / 10) ++ [((n % 10 : Nat) : Int) + 48]

/-- Hexadecimal digits of `n`. -/
def hexDigits (upper : Bool) (fuel n : Nat) : List Int :=
  let d (k : Nat) : Int := if k < 10 then (k : Int) + 48 else (k : Int) - 10 + (if upper then 65 else 97)
  match fuel with
  | 0 => []
  | fuel + 1 => if n < 16 then [d n] else hexDigits upper fuel (n / 16) ++ [d (n % 16)]

/-- The flags of a conversion specification (`-+ #0`). -/
structure Flags where
  left : Bool := false
  plus : Bool := false
  space : Bool := false
  alt : Bool := false
  zero : Bool := false

def parseFlags (f : Flags) : List Int → Flags × List Int
  | 45 :: fmt => parseFlags { f with left := true } fmt
  | 43 :: fmt => parseFlags { f with plus := true } fmt
  | 32 :: fmt => parseFlags { f with space := true } fmt
  | 35 :: fmt => parseFlags { f with alt := true } fmt
  | 48 :: fmt => parseFlags { f with zero := true } fmt
  | fmt => (f, fmt)

/-- `sign ++ body` padded to `width`: spaces before, spaces after (`-`), or
zeros between the sign (or `0x`) and the body. -/
def padField (f : Flags) (width : Nat) (zeroPad : Bool) (sign body : List Int) : List Int :=
  let n := sign.length + body.length
  if f.left then sign ++ body ++ List.replicate (width - n) 32
  else if zeroPad then sign ++ List.replicate (width - n) 48 ++ body
  else List.replicate (width - n) 32 ++ sign ++ body

/-- Octal digits of `n`. -/
def octDigits (fuel n : Nat) : List Int :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n < 8 then [(n : Int) + 48] else octDigits fuel (n / 8) ++ [((n % 8 : Nat) : Int) + 48]

/-- A wide character the C locale has a multibyte character for: those of ASCII (glibc's C
locale); `%lc` of another is an encoding error (C11 7.21.6.1p8, as by wcrtomb). -/
def lcInLocale (x : Int) : Bool := 0 ≤ x && x < 128

/-- The text of one conversion `c` with flags `f`, field width `width`,
precision `prec` and length modifier `lm` (`h`, `hh`, `l`, `ll`, `j`, `z`,
`t`, `L` as character lists) of the argument `a`; `none` outside the modelled
subset. Integer arguments are converted to the type the conversion and its
length modifier name (C11 7.21.6.1p7). -/
def fmtConv (m : Mem) (f : Flags) (width : Nat) (prec : Option Nat) (lm : List Int) (c : Int)
    (a : Val) : Option (List Int) :=
  let bits : Nat := if lm == [104, 104] then 8 else if lm == [104] then 16 else if lm.isEmpty then 32 else 64
  let sgn (neg : Bool) : List Int := if neg then [45] else if f.plus then [43] else if f.space then [32] else []
  -- integer digits with the precision as a minimum count (`%.0d` of 0 prints nothing)
  let minDigits (ds : List Int) (zero : Bool) : List Int := match prec with
    | some p => if zero && p == 0 then [] else List.replicate (p - ds.length) 48 ++ ds
    | none => ds
  let intPad := f.zero && prec.isNone
  -- combinations C11 leaves undefined are refused (undefined behaviour): `#`
  -- other than with o x X and the floating conversions (7.21.6.1p6), a
  -- precision with c (p4), a length modifier the conversion does not take
  -- (p7: hh h l ll j z t with the integer conversions, l also with c and s,
  -- and before a floating conversion, where it has no effect); `0` with c or
  -- s is refused below
  let intC := c == 100 || c == 105 || c == 117 || c == 111 || c == 120 || c == 88
  let fltC := c == 102 || c == 70 || c == 101 || c == 69 || c == 103 || c == 71
  let lmOk :=
    if intC then
      lm.isEmpty || lm == [104, 104] || lm == [104] || lm == [108] || lm == [108, 108] || lm == [106] ||
        lm == [122] || lm == [116]
    else lm.isEmpty || lm == [108]
  if lm == [76] then none
  else if !lmOk || (f.alt && !(c == 111 || c == 120 || c == 88 || fltC)) || (prec.isSome && c == 99) then none
  else if c == 100 || c == 105 then
    match a with
    | .int x =>
      let v := wrap true bits x
      some (padField f width intPad (sgn (v < 0)) (minDigits (natDigits 64 v.natAbs) (v == 0)))
    | _ => none
  else if c == 117 || c == 120 || c == 88 || c == 111 then
    match a with
    | .int x =>
      let v := (wrap false bits x).toNat
      let ds := if c == 117 then natDigits 64 v else if c == 111 then octDigits 64 v else hexDigits (c == 88) 64 v
      let ds := minDigits ds (v == 0)
      -- `#`: `0x` before a nonzero hexadecimal number; a leading 0 in octal
      let pre : List Int := if f.alt && v != 0 && c == 120 then [48, 120]
        else if f.alt && v != 0 && c == 88 then [48, 88] else []
      let ds := if f.alt && c == 111 && ds.head? != some 48 then 48 :: ds else ds
      some (padField f width intPad pre ds)
    | _ => none
  else if c == 99 then
    match a with
    | .int x =>
      if f.zero then none
      -- `%lc`: the multibyte sequence wcrtomb gives for the wide character (p8); one outside the
      -- C locale is an encoding error (`sprintfBeforeLcError`)
      else if lm == [108] && !lcInLocale x then none
      else some (padField f width false [] [wrap false 8 x])
    | _ => none
  else if c == 115 then
    match a with
    -- with a precision `n`, at most `n` characters are read (no terminator needed among them)
    | .ptr p => match (match prec with | some n => readCStrN m p n | none => readCStr m p) with
      | .ok cs =>
        let cs := cs.filterMap fun v => match v with | .int x => some x | _ => none
        if f.zero then none else some (padField f width false [] cs)
      | _ => none
    | _ => none
  else if c == 102 || c == 70 || c == 101 || c == 69 || c == 103 || c == 71 then
    match a with
    | .float x => match fmtFloat c f.alt f.plus f.space prec x with
      | some (sign, body) =>
        let finite := match decodeF x with | .finite .. => true | _ => false
        some (padField f width (f.zero && finite) sign body)
      | none => none
    | _ => none
  else none

/-- The text of `sprintf(fmt, args)`, or `none` outside the modelled subset:
conversions `d i u o x X c s f F e E g G %` with flags, field width and
precision (digits or `*`), length modifiers `hh h l ll j z t`. Floating-point
conversions are exact (`CIR/Std/Float.lean`); a NaN is not modelled (glibc
prints its sign). -/
def sprintfChars (m : Mem) : Nat → List Int → List Val → Option (List Int)
  | _, [], _ => some []
  -- `fuel`: the length of the format (each step consumes a character)
  | 0, _ :: _, _ => none
  | fuel + 1, 37 :: 37 :: fmt, args => (sprintfChars m fuel fmt args).map (37 :: ·)
  | fuel + 1, 37 :: fmt, args =>
    let (f, fmt) := parseFlags {} fmt
    -- field width: digits, or `*` (an `int` argument; negative means `-`)
    let wa : Option (Flags × Nat × List Int × List Val) := match fmt, args with
      | 42 :: fmt, .int w :: args => some (if w < 0 then { f with left := true } else f, w.natAbs, fmt, args)
      | 42 :: _, _ => none
      | _, _ => some (f, digitsVal fmt (takeDigits fmt).2, fmt.drop (takeDigits fmt).2, args)
    match wa with
    | none => none
    | some (f, width, fmt, args) =>
    -- precision: `.` then digits (none: 0), or `.*` (a negative one is omitted)
    let pa : Option (Option Nat × List Int × List Val) := match fmt, args with
      | 46 :: 42 :: fmt, .int p :: args => some (if p < 0 then none else some p.toNat, fmt, args)
      | 46 :: 42 :: _, _ => none
      | 46 :: rest, _ => some (some (digitsVal rest (takeDigits rest).2), rest.drop (takeDigits rest).2, args)
      | _, _ => some (none, fmt, args)
    match pa with
    | none => none
    | some (prec, fmt, args) =>
    let lm := fmt.takeWhile fun c => c == 104 || c == 108 || c == 106 || c == 122 || c == 116 || c == 76
    let fmt := fmt.drop lm.length
    match fmt, args with
    | c :: fmt, a :: args =>
      match fmtConv m f width prec lm c a with
      | some out => (sprintfChars m fuel fmt args).map (out ++ ·)
      | none => none
    | _, _ => none
  | fuel + 1, c :: fmt, args => (sprintfChars m fuel fmt args).map (c :: ·)

/-- The text `sprintf(fmt, args)` writes before an encoding error, a `%lc` of a wide character
outside the C locale (`lcInLocale`), at which the call fails (C11 7.21.6.1p14, 7.21.6.6p3: a
negative result); `none` without such a `%lc`, or when the format is outside the modelled subset
before it (`sprintfChars` is `none` in both cases). -/
def sprintfBeforeLcError (m : Mem) : Nat → List Int → List Val → Option (List Int)
  | _, [], _ => none
  | 0, _ :: _, _ => none
  | fuel + 1, 37 :: 37 :: fmt, args => (sprintfBeforeLcError m fuel fmt args).map (37 :: ·)
  | fuel + 1, 37 :: fmt, args =>
    let (f, fmt) := parseFlags {} fmt
    let wa : Option (Flags × Nat × List Int × List Val) := match fmt, args with
      | 42 :: fmt, .int w :: args => some (if w < 0 then { f with left := true } else f, w.natAbs, fmt, args)
      | 42 :: _, _ => none
      | _, _ => some (f, digitsVal fmt (takeDigits fmt).2, fmt.drop (takeDigits fmt).2, args)
    match wa with
    | none => none
    | some (f, width, fmt, args) =>
    let pa : Option (Option Nat × List Int × List Val) := match fmt, args with
      | 46 :: 42 :: fmt, .int p :: args => some (if p < 0 then none else some p.toNat, fmt, args)
      | 46 :: 42 :: _, _ => none
      | 46 :: rest, _ => some (some (digitsVal rest (takeDigits rest).2), rest.drop (takeDigits rest).2, args)
      | _, _ => some (none, fmt, args)
    match pa with
    | none => none
    | some (prec, fmt, args) =>
    let lm := fmt.takeWhile fun c => c == 104 || c == 108 || c == 106 || c == 122 || c == 116 || c == 76
    let fmt := fmt.drop lm.length
    match fmt, args with
    | c :: fmt, a :: args =>
      if c == 99 && lm == [108] && !f.zero && prec.isNone &&
          (match a with | .int x => !lcInLocale x | _ => false) then
        some []
      else match fmtConv m f width prec lm c a with
        | some out => (sprintfBeforeLcError m fuel fmt args).map (out ++ ·)
        | none => none
    | _, _ => none
  | fuel + 1, c :: fmt, args => (sprintfBeforeLcError m fuel fmt args).map (c :: ·)

/-- The arguments of the `%s` conversions of a format with their precisions,
consumed as `sprintfChars` consumes the arguments. -/
def sprintfStrArgs : Nat → List Int → List Val → List (Ptr × Option Nat)
  | _, [], _ => []
  | 0, _ :: _, _ => []
  | fuel + 1, 37 :: 37 :: fmt, args => sprintfStrArgs fuel fmt args
  | fuel + 1, 37 :: fmt, args =>
    let (_, fmt) := parseFlags {} fmt
    let wa : Option (List Int × List Val) := match fmt, args with
      | 42 :: fmt, .int _ :: args => some (fmt, args)
      | 42 :: _, _ => none
      | _, _ => some (fmt.drop (takeDigits fmt).2, args)
    match wa with
    | none => []
    | some (fmt, args) =>
    let pa : Option (Option Nat × List Int × List Val) := match fmt, args with
      | 46 :: 42 :: fmt, .int p :: args => some (if p < 0 then none else some p.toNat, fmt, args)
      | 46 :: 42 :: _, _ => none
      | 46 :: rest, _ => some (some (digitsVal rest (takeDigits rest).2), rest.drop (takeDigits rest).2, args)
      | _, _ => some (none, fmt, args)
    match pa with
    | none => []
    | some (prec, fmt, args) =>
    let lm := fmt.takeWhile fun c => c == 104 || c == 108 || c == 106 || c == 122 || c == 116 || c == 76
    let fmt := fmt.drop lm.length
    match fmt, args with
    | 115 :: fmt, .ptr p :: args => (p, prec) :: sprintfStrArgs fuel fmt args
    | _ :: fmt, _ :: args => sprintfStrArgs fuel fmt args
    | _, _ => []
  | fuel + 1, _ :: fmt, args => sprintfStrArgs fuel fmt args

/-! ### Variadic arguments and `va_list` (C11 7.16, 7.21.6.8-13) -/

/-- A variadic argument as its call site passed it (`Op.vaBox`): a pointer to a stack block of type
`!cir.func<(t)>` holding the value; the type and the value. -/
def vaBoxed? (m : Mem) : Val → Option (Ty × Val)
  | .ptr (.loc b []) => match m.live? b with
    | some ⟨.stack, _, .func [t] .void false, x⟩ => some (t, x)
    | _ => none
  | _ => none

/-- `va_arg(ap, req)` may read a variadic argument passed with type `t` and value `x` (C11
7.16.1.1p2; the call site's types are already promoted): the same type, the signed and the unsigned
type of one width when `x` fits both, or `void *` and a pointer to a character type. -/
def vaCompatible (t req : Ty) (x : Val) : Bool :=
  t == req ||
  match t, req, x with
  | .int _ w, .int s w', .int v => w == w' && inRange s w' v
  | .ptr .void, .ptr (.int _ 8), _ | .ptr (.int _ 8), .ptr .void, _ => true
  | _, _, _ => false

/-- A `va_list`'s state, kept in its first member (`gp_offset`, unused otherwise): 1 initialized by
`va_start` or `va_copy`, 3 initialized and advanced by a `va_arg` in another function than the one
whose object it is (C11 7.16p3), 4 indeterminate after a `v*printf` call on it (7.21.6.8p2 and its
footnote: only `va_end` may follow), 2 ended by `va_end`; anything else: never initialized. Live
(to be ended before it is initialized again): 1, 3 or 4. -/
def vaLive : Option Val → Bool
  | some (.agg (.int t :: _)) => t == 1 || t == 3 || t == 4
  | _ => false

/-- The type the conversion `c` with length modifier `lm` needs of its argument after the
promotions (C11 7.21.6.1p7-8): `int` / `unsigned` for the integer conversions, `int` with `h`,
`hh` (a promoted `short` or `char` of either signedness), `long` / `unsigned long` with `l`,
`ll`, `j`, `z`, `t`; `int` for `c`, `wint_t` for `lc`; a pointer to a character type for `s`
(written `char *`), to `wchar_t` for `ls`; `double` for the floating conversions. `none` for the
conversions outside the modelled subset. -/
def convArgTy (lm : List Int) (c : Int) : Option Ty :=
  let short := lm == [104] || lm == [104, 104]
  let long := lm == [108] || lm == [108, 108] || lm == [106] || lm == [122] || lm == [116]
  if c == 100 || c == 105 then
    if lm.isEmpty || short then some (.int true 32) else if long then some (.int true 64) else none
  else if c == 117 || c == 111 || c == 120 || c == 88 then
    if lm.isEmpty then some (.int false 32) else if short then some (.int true 32)
    else if long then some (.int false 64) else none
  else if c == 99 then
    if lm.isEmpty then some (.int true 32) else if lm == [108] then some (.int false 32) else none
  else if c == 115 then
    if lm.isEmpty then some (.ptr (.int true 8)) else if lm == [108] then some (.ptr (.int true 32)) else none
  else if c == 102 || c == 70 || c == 101 || c == 69 || c == 103 || c == 71 then
    if lm.isEmpty || lm == [108] then some (.float .double) else none
  else none

/-- The argument (by index after the format) each conversion of `fmt` reads, with the type it
needs: a `*` field width or precision reads an `int` (7.21.6.1p5). -/
partial def fmtNeeds : List Int → Nat → List (Nat × Option Ty)
  | [], _ => []
  | 37 :: 37 :: fmt, i => fmtNeeds fmt i
  | 37 :: fmt, i =>
    let fmt := (parseFlags {} fmt).2
    let (w, fmt, i) : List (Nat × Option Ty) × List Int × Nat := match fmt with
      | 42 :: fmt => ([(i, some (.int true 32))], fmt, i + 1)
      | _ => ([], fmt.drop (takeDigits fmt).2, i)
    let (p, fmt, i) : List (Nat × Option Ty) × List Int × Nat := match fmt with
      | 46 :: 42 :: fmt => ([(i, some (.int true 32))], fmt, i + 1)
      | 46 :: rest => ([], rest.drop (takeDigits rest).2, i)
      | _ => ([], fmt, i)
    let lm := fmt.takeWhile fun c => c == 104 || c == 108 || c == 106 || c == 122 || c == 116 || c == 76
    match fmt.drop lm.length with
    | c :: fmt => w ++ p ++ [(i, convArgTy lm c)] ++ fmtNeeds fmt (i + 1)
    | [] => w ++ p
  | _ :: fmt, i => fmtNeeds fmt i

/-- The variadic arguments that the `va_list` at `ap` has not given to `va_arg` yet, each with its
type when its call site boxed it (`vaBoxed?`; a call through a function pointer passes values
only); `none` unless the `va_list` is initialized and its value determinate (state 1 or 3, see
`vaLive`). -/
def vaRemaining (m : Mem) (ap : Ptr) : Option (List (Option Ty × Val)) :=
  match m.read? ap with
  | some (.agg [.int t, _, .ptr area, _]) =>
    if !(t == 1 || t == 3) then none else
    match area with
    -- a call without variadic arguments
    | .null => some []
    | .loc b path =>
      match path.getLast?, m.read? (.loc b path.dropLast) with
      | some (.idx k), some (.arr xs) =>
        some ((xs.drop k).map fun v => match vaBoxed? m v with
          | some (t, x) => (some t, x)
          | none => (none, v))
      | _, _ => none
    | _ => none
  | _ => none

/-- Whether the arguments `args` (with their types where boxed) suit the conversions of `fmt`, as
the frontend checks a `printf` call with a literal format (`CIR.Frontend.checkFormats`): `some msg`
when one has another type than its conversion needs (C11 7.21.6.1p9), or else when one has the
other signedness and a value outside the type needed (read as it only when the value fits both, as
`va_arg` would, 7.16.1.1p2). An argument without its type is not checked here; its conversion
checks its kind. -/
def fmtArgsBad (fmt : List Int) (args : List (Option Ty × Val)) : Option String :=
  -- `false`: another type; `true`: the other signedness and a value that does not fit
  let verdicts := (fmtNeeds fmt 0).filterMap fun (i, need) =>
    match need, args[i]? with
    | some e, some (some t, x) =>
      match e, t with
      | .ptr (.int _ 8), .ptr (.int _ 8) => none
      | .int s w, .int s' w' =>
        if w != w' then some false
        else if s == s' || (match x with | .int v => inRange s w v | _ => false) then none
        else some true
      | e, t => if e == t then none else some false
    | _, _ => none
  if verdicts.contains false then
    some "an argument of another type than its conversion needs (C11 7.21.6.1p9)"
  else if verdicts.contains true then
    some "an argument of the other signedness that does not fit the type its conversion needs (C11 7.21.6.1p9, 7.16.1.1p2)"
  else none

/-- A `va_list` after a `v*printf` call on it: its value is indeterminate (state 4, `vaLive`). -/
def vaIndeterminate : Val → Val
  | .agg (_ :: rest) => .agg (.int 4 :: rest)
  | v => v

def isSpaceC (c : Int) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- The value of `strtol(s, NULL, 10)`'s subject sequence in the characters
`cs`: white space, an optional sign and the longest run of decimal digits;
0 when there are no digits. -/
def atoiVal (cs : List Int) : Int :=
  let (neg, ds) : Bool × List Int := match cs.dropWhile isSpaceC with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let mag : Int := decDigitsVal (ds.takeWhile isDigitC)
  if neg then -mag else mag

/-- The integer type a `scanf` length modifier names. -/
def scanIntTy (signed : Bool) (lm : List Int) : Ty :=
  .int signed (if lm == [104, 104] then 8 else if lm == [104] then 16 else if lm.isEmpty then 32 else 64)

/-- One `scanf` conversion `c` (length modifier `lm`) on the input item
`item` (at most the field width, after the skipped white space): the number
of characters converted, the value and the type of the object it is stored
in; `some none` for a matching failure; `none` outside the modelled subset
or for an integer that does not fit its object (C11 7.21.6.2p10, undefined).
Floating-point input items follow glibc: the longest prefix of a subject
sequence is read, and it must be a complete one (`1e+` fails). -/
def scanConv (c : Int) (lm : List Int) (item : List Int) : Option (Option (Nat × Val × Ty)) :=
  let (neg, s) : Bool × Nat := match item with
    | 45 :: _ => (true, 1)
    | 43 :: _ => (false, 1)
    | _ => (false, 0)
  let body := item.drop s
  if c == 102 || c == 70 || c == 101 || c == 69 || c == 103 || c == 71 || c == 97 || c == 65 then
    if lm == [76] then none else
    let (valid, longest) := fpSubject body
    if longest == 0 || valid != longest then some none
    else
      let single := lm.isEmpty
      let round : Bool → Nat → Nat → Float := if single then ratToSingle else ratToFloat
      some (some (s + valid, .float (subjectValue round neg (body.take valid)),
        .float (if single then .single else .double)))
  else if c == 100 || c == 117 || c == 120 || c == 88 then
    if lm == [76] then none else
    let dig := if c == 100 || c == 117 then isDigitC else isHexC
    -- `%x`: an optional `0x`/`0X` after the sign, as in the subject sequence of
    -- strtoul in base 16 (C11 7.21.6.2p12); `0x` without a hex digit is only a
    -- prefix of a number, a matching failure (p9-10)
    let pre : Nat :=
      if (c == 120 || c == 88) && body.head? == some 48 && (body.drop 1).head? ∈ [some 120, some 88] then 2 else 0
    let ds := (body.drop pre).takeWhile dig
    if ds.isEmpty then some none
    else
      let mag : Nat := if c == 100 || c == 117 then decDigitsVal ds else hexDigitsVal ds
      -- `u`, `x`, `X`: strtoul's value (p12), a negative number negated in unsigned long:
      -- `-1` is ULONG_MAX, which only an unsigned long (`l`, `ll`) holds
      let v : Int := if !neg then mag else if c == 100 || mag == 0 then -(mag : Int) else 2 ^ 64 - mag
      let ty := scanIntTy (c == 100) lm
      match ty with
      | .int sg w => if inRange sg w v then some (some (s + pre + ds.length, .int v, ty)) else none
      | _ => none
  else if c == 105 then
    if lm == [76] then none else
    -- `%i`: the subject sequence of strtol in base 0 (p12): `0x`/`0X` and hex digits, a
    -- leading 0 and octal digits, else decimal digits, the sign before them; `0x` without a
    -- hex digit is a matching failure, as for `%x`. After a 0, `b`/`B` starts a binary number
    -- for glibc's C23 `__isoc23_sscanf` (which C++ and `_GNU_SOURCE` programs call) and ends
    -- the number for `__isoc99_sscanf`, which the model does not tell apart: not modelled
    if body.head? == some 48 && (body.drop 1).head? ∈ [some 98, some 66] then none else
    let base : Nat :=
      if body.head? == some 48 && (body.drop 1).head? ∈ [some 120, some 88] then 16
      else if body.head? == some 48 then 8 else 10
    let pre : Nat := if base == 16 then 2 else 0
    let ds := (body.drop pre).takeWhile fun d =>
      if base == 16 then isHexC d else if base == 8 then 48 ≤ d && d ≤ 55 else isDigitC d
    if ds.isEmpty then some none
    else
      let mag : Nat :=
        if base == 16 then hexDigitsVal ds
        else if base == 8 then ds.foldl (fun acc d => acc * 8 + (d - 48).toNat) 0
        else decDigitsVal ds
      let v : Int := if neg then -(mag : Int) else mag
      let ty := scanIntTy true lm
      match ty with
      | .int sg w => if inRange sg w v then some (some (s + pre + ds.length, .int v, ty)) else none
      | _ => none
  else none

/-- `sscanf` on the input `inp` (the characters before the terminator) with
the format `fmt`: the objects to store (pointer, value, type) and the result,
the number of assignments, or EOF (-1) if the input ends before the first
conversion has completed; `none` outside the modelled subset (conversions
`d i u x X f F e E g G a A n %`, with `*`, field width, length modifiers
`hh h l ll j z t`). `done`: a conversion has completed; `n`: assignments so
far; `pos`: characters consumed (`%n`); `fuel`: the length of the format. -/
def scanChars : Nat → List Int → List Int → List Val → Bool → Nat → Nat →
    Option (List (Ptr × Val × Ty) × Int)
  | _, _, [], _, _, n, _ => some ([], n)
  | 0, _, _ :: _, _, _, _, _ => none
  | fuel + 1, inp, c :: fmt, args, done, n, pos =>
    -- an input failure: the count, or EOF before the first conversion
    let eof : Option (List (Ptr × Val × Ty) × Int) := some ([], if done then n else -1)
    if isSpaceC c then
      let k := (inp.takeWhile isSpaceC).length
      scanChars fuel (inp.drop k) fmt args done n (pos + k)
    else if c != 37 then
      match inp with
      | x :: inp' => if x == c then scanChars fuel inp' fmt args done n (pos + 1) else some ([], n)
      | [] => eof
    else
      match fmt with
      | 37 :: fmt' =>
        let k := (inp.takeWhile isSpaceC).length
        match inp.drop k with
        | 37 :: inp' => scanChars fuel inp' fmt' args done n (pos + k + 1)
        | _ :: _ => some ([], n)
        | [] => eof
      | _ =>
        let (suppress, fmt) : Bool × List Int := match fmt with
          | 42 :: f => (true, f)
          | f => (false, f)
        let width := digitsVal fmt (takeDigits fmt).2
        let fmt := fmt.drop (takeDigits fmt).2
        let lm := fmt.takeWhile fun c => c == 104 || c == 108 || c == 106 || c == 122 || c == 116 || c == 76
        let fmt := fmt.drop lm.length
        match fmt with
        | [] => none
        | conv :: fmt =>
          if conv == 110 then
            -- `%n`: the characters consumed so far; not a conversion
            if suppress then scanChars fuel inp fmt args done n pos else
            match args with
            | .ptr p :: args =>
              (scanChars fuel inp fmt args done n pos).map fun (st, r) => ((p, .int pos, scanIntTy true lm) :: st, r)
            | _ => none
          else
            let k := (inp.takeWhile isSpaceC).length
            let inp := inp.drop k
            if inp.isEmpty then eof else
            match scanConv conv lm (if width == 0 then inp else inp.take width) with
            | none => none
            | some none => some ([], n)
            | some (some (used, v, ty)) =>
              if suppress then scanChars fuel (inp.drop used) fmt args true n (pos + k + used) else
              match args with
              | .ptr p :: args =>
                (scanChars fuel (inp.drop used) fmt args true (n + 1) (pos + k + used)).map fun (st, r) =>
                  ((p, v, ty) :: st, r)
              | _ => none

/-- `strtol` and its siblings on the characters `cs` of a C string (C11
7.22.1.4) in base `base` (0 or 2..36): the value of the subject sequence, its
sign applied, and the number of characters up to its end; `(0, 0)` when there
is none. The subject sequence: white space (`isspace`), an optional sign, in
base 16 an optional `0x`/`0X` before a hexadecimal digit, in base 0 the base
from the prefix (`0x`: 16, `0`: 8, else 10), then the longest run of digits
below the base (`a`-`z`, `A`-`Z` are 10 to 35). `c23`: glibc's
`__isoc23_strtol` and siblings, which also take `0b`/`0B` before a binary
digit in bases 0 and 2 (C23). -/
def strtolWith (c23 : Bool) (base : Nat) (cs : List Int) : Int × Nat :=
  let ws := (cs.takeWhile isSpaceC).length
  let s1 := cs.drop ws
  let (neg, sg) : Bool × Nat := match s1 with
    | 45 :: _ => (true, 1)
    | 43 :: _ => (false, 1)
    | _ => (false, 0)
  let s2 := s1.drop sg
  let dval (c : Int) : Nat :=
    if 48 ≤ c && c ≤ 57 then (c - 48).toNat
    else if 97 ≤ c && c ≤ 122 then (c - 87).toNat
    else if 65 ≤ c && c ≤ 90 then (c - 55).toNat
    else 36
  let (b, pre) : Nat × Nat := match s2 with
    | 48 :: x :: d :: _ =>
      if (x == 120 || x == 88) && (base == 0 || base == 16) && dval d < 16 then (16, 2)
      else if c23 && (x == 98 || x == 66) && (base == 0 || base == 2) && dval d < 2 then (2, 2)
      else (if base == 0 then 8 else base, 0)
    | 48 :: _ => (if base == 0 then 8 else base, 0)
    | _ => (if base == 0 then 10 else base, 0)
  let ds := (s2.drop pre).takeWhile fun c => dval c < b
  if ds.isEmpty then (0, 0)
  else
    let mag : Nat := ds.foldl (fun acc c => acc * b + dval c) 0
    (if neg then -(mag : Int) else mag, ws + sg + pre + ds.length)

/-- glibc's class bits of a character in the C locale (`_ISupper` = 0x100, ...,
`_ISalnum` = 0x8, as the `_ISbit` macro lays them out on a little-endian
machine). -/
def ctypeBits (c : Int) : Int :=
  let up := 65 ≤ c && c ≤ 90
  let lo := 97 ≤ c && c ≤ 122
  let dig := 48 ≤ c && c ≤ 57
  let xd := dig || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
  let sp := c == 32 || (9 ≤ c && c ≤ 13)
  let prt := 32 ≤ c && c ≤ 126
  let graph := 33 ≤ c && c ≤ 126
  let blank := c == 32 || c == 9
  let cntrl := (0 ≤ c && c ≤ 31) || c == 127
  let alpha := up || lo
  let punct := graph && !(alpha || dig)
  let b (x : Bool) (v : Int) : Int := if x then v else 0
  b up 0x100 + b lo 0x200 + b alpha 0x400 + b dig 0x800 + b xd 0x1000 + b sp 0x2000 +
    b prt 0x4000 + b graph 0x8000 + b blank 0x1 + b cntrl 0x2 + b punct 0x4 + b (alpha || dig) 0x8

/-- Entry `c + 128` of glibc's table `which` (0: class bits, 1: toupper,
2: tolower), for `c` from -128 to 255. -/
def ctypeEntry (which : Nat) (c : Int) : Int :=
  if c < 0 || 127 < c then (if which == 0 then 0 else c)
  else match which with
    | 0 => ctypeBits c
    | 1 => if 97 ≤ c && c ≤ 122 then c - 32 else c
    | _ => if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- The characters of a string value (without terminator). -/
def strChars (xs : List Val) : Res (List Val) :=
  match xs.getLast? with
  | some (.int c) => if c == 0 then .ok xs.dropLast else .ub "malformed string value"
  | _ => .ub "malformed string value"

/-- The `std::optional` object designated by `p`: `p` itself, or, for a pointer
to one of its base-class subobjects (libc++ calls `has_value` on
`__optional_storage_base`), the enclosing object holding the optional value.
Only leading-subobject steps (`idx 0`) are stripped. -/
def optRoot (m : Mem) (p : Ptr) : Res (Ptr × Option Val) :=
  match p with
  | .loc b path =>
    let isOpt (pre : List PathElem) : Bool :=
      (path.drop pre.length).all (· == .idx 0) &&
        (match m.read? (.loc b pre) with
         | some (.opt _) => true
         | _ => false)
    match ((List.range (path.length + 1)).reverse.map path.take).find? isOpt with
    | some pre =>
      match m.read? (.loc b pre) with
      | some (.opt o) => .ok (.loc b pre, o)
      | _ => .ub "object is not a live std::optional"
    | none => .ub "object is not a live std::optional"
  | _ => .ub "object is not a live std::optional"

/-- An iterator position that is valid for comparisons and arithmetic: an
element or past-the-end position of a live container of the current
generation (comparing an invalidated iterator is undefined). -/
def validIter (m : Mem) (p : Ptr) : Bool := (m.elemPos? p).isSome

/-- The elements of a `std::initializer_list<T>` `{const T* first; size_t n}`. -/
def initListVals (e : Ty) (first : Ptr) (n : Int) (m : Mem) : Res (List Val) := do
  if n < 0 then .ub "bad initializer_list" else
  -- CIR stores the address of the backing array object (`T(*)[N]`, through a
  -- bitcast) into the `const T*` field: same address as its first element
  let first := match first, m.read? first with
    | .loc b path, some (.arr _) => .loc b (path ++ [.idx 0])
    | p, _ => p
  (List.range n.toNat).mapM fun (i : Nat) => do
    let p ← Res.ofOption "initializer_list out of range" (m.stride? first (i : Int))
    loadTy m e p

/-- `vector(std::initializer_list<T>)`. -/
def initListCtor (e : Ty) (this first : Ptr) (n : Int) (m : Mem) : Res (Exit × Mem) := do
  retVoid (← writeVec m this (← initListVals e first n m))

/-- A container value returned by value (a string a model makes), under a fresh generation. -/
def retVec (m : Mem) (xs : List Val) : Res (Exit × Mem) :=
  retv (.vec (fresh m).1 xs) (fresh m).2

/-- Does `p` point into the storage of the container at `c` (to an element, a part of one, or
the end)? -/
def intoCont (c p : Ptr) : Bool :=
  match c, p with
  | .loc b pre, .loc b' path => b == b' && pre.length < path.length && pre.isPrefixOf path
  | _, _ => false

/-- The position an iterator argument holds: a pointer, or a contiguous iterator (`__wrap_iter`,
`__normal_iterator`) holding one. -/
def iterPos? : Val → Option Ptr
  | .ptr p => some p
  | .agg [.ptr p] => some p
  | _ => none

/-- The position a `std::reverse_iterator` argument holds: that of its last member (`current`;
libc++ keeps the unused `__t_` before it). -/
def revPos? : Val → Option Ptr
  | .agg xs => xs.getLast?.bind iterPos?
  | _ => none

/-- The element pointers of the iterator range `[first, last)`: within one array or container
(`rangePtrs`), or empty between two null pointers. -/
def rangeOf? (m : Mem) (first last : Ptr) : Option (List Ptr) :=
  match first, last with
  | .null, .null => some []
  | _, _ => rangePtrs m first last

/-- The `n` characters from `p` (a string's characters or a `char` array; one character may be a
lone object), each read as a `char`: `char_traits<char>::copy` and `compare` read them (C++
[char.traits.require]). -/
def readChars (m : Mem) (p : Ptr) (n : Int) : Res (List Val) :=
  if n = 0 then pure [] else
  if n = 1 then do pure [← loadTy m (.int true 8) p] else do
  let q ← Res.ofOption "character range out of bounds" (m.stride? p n)
  let ps ← Res.ofOption "character range out of bounds" (rangePtrs m p q)
  ps.mapM (loadTy m (.int true 8))

/-- The characters of a `basic_string(first, last)` range: positions held by `char` pointers or
contiguous iterators, or (`rev`) by `std::reverse_iterator`s over them, whose range
`[last.current, first.current)` is read backwards; each character read as a `char`. -/
def rangeArgChars (m : Mem) (rev : Bool) (a b : Val) : Res (List Val) := do
  let pos := if rev then revPos? else iterPos?
  let some p := pos a | .ub "std::string: bad iterator argument"
  let some q := pos b | .ub "std::string: bad iterator argument"
  let (first, last) := if rev then (q, p) else (p, q)
  let ps ← Res.ofOption "std::string: iterator range not within one array" (rangeOf? m first last)
  let cs ← ps.mapM (loadTy m (.int true 8))
  pure (if rev then cs.reverse else cs)

/-- `basic_string::compare`'s result for characters `xs` against `ys`: `char_traits<char>::compare`
over the first `min` of their lengths (the first difference as `unsigned char`s, C++
[char.traits.specializations.char]), then the lengths; -1, 0 or 1, as the `memcmp` model. -/
def compareChars : List Val → List Val → Res Int
  | [], [] => pure 0
  | [], _ :: _ => pure (-1)
  | _ :: _, [] => pure 1
  | .int x :: xs, .int y :: ys =>
    if x % 256 < y % 256 then pure (-1)
    else if y % 256 < x % 256 then pure 1
    else compareChars xs ys
  | _, _ => .ub "string comparison of an indeterminate character"

/-- `compare(pos1, n1, s, n2)` on the characters `cs` of a string: its characters from `pos1`
(at most `n1`) against `s[0, n2)`, of which only the first `min` of both lengths are read
(`[s, s + n2)` must be a valid range, C++ [string.view.cons]); the string's length after `pos1`
first (`pos1 <= size()`, checked by the caller). -/
def compareSub (m : Mem) (cs : List Val) (pos1 n1 : Nat) (s : Ptr) (n2 : Int) : Res Int := do
  let xs := (cs.drop pos1).take n1
  if n2 < 0 then .ub "std::string::compare: bad length" else
  if 0 < n2 ∧ ((m.stride? s (n2 - 1)).bind m.read?).isNone = true then
    .ub "std::string::compare: character range out of bounds" else
  let ys ← readChars m s (min (xs.length : Int) n2)
  let r ← compareChars xs ys
  pure (if r ≠ 0 then r else if (xs.length : Int) < n2 then -1 else if n2 < xs.length then 1 else 0)

/-- The C locale's `struct lconv` value for the record `r`, with its strings
in the block `sb` holding ".": the first pointer member is `decimal_point`
(element 0), the other pointer members are "" (the terminator, element 1),
the `char` members are `CHAR_MAX`. -/
def lconvVal (ctx : Ctx) (r : RecordDecl) (sb : Nat) : Val :=
  .agg (r.members.foldl (fun (acc : Bool × List Val) mt =>
    match mt with
    | (.data, .ptr _) => (false, acc.2 ++ [Val.ptr (.loc sb [.idx (if acc.1 then 0 else 1)])])
    | (.data, .int _ 8) => (acc.1, acc.2 ++ [Val.int 127])
    | (_, t) => (acc.1, acc.2 ++ [ctx.initVal 32 t])) (true, [])).2

/-- Heap storage of `n` bytes (`operator new`, `malloc`, `calloc`): untyped
until its first cast to `T*`, which gives it the type `T` (or `T[n / sizeof T]`),
zero-initialised for `calloc`. Allocation is assumed to succeed. -/
def allocHeap (m : Mem) (n : Int) (zero : Bool) : Res (Exit × Mem) :=
  -- untyped storage of `n` bytes: `.array (.other "heap") n` (`"heap0"`:
  -- zero-filled), typed at its first cast
  let (b, m) := m.alloc .heap (.array (.other (if zero then "heap0" else "heap")) n.toNat) .undef
  retv (.ptr (.loc b [])) m

/-- Free heap storage: the pointer returned by the allocation, or (for an
array) a pointer to its first element. -/
def freeHeap (m : Mem) (p : Ptr) : Res (Exit × Mem) :=
  match p with
  | .null => retVoid m
  | .loc b [] | .loc b [.idx 0] => do
    retVoid (← Res.ofOption "freeing a pointer not from the allocator" (m.free? b))
  | _ => .ub "freeing a pointer not from the allocator"

/-- The element type of a `std::vector<T>` or `std::basic_string<T>` record (the
type of the object holding a container value `vec g xs`), from its first
template argument, for the scalar types the container models take; `ptrBits`:
the width of `long`. -/
def containerElemTy? (ptrBits : Nat) : Ty → Option Ty
  -- the string typedefs, as clang names their records
  | .record "std::__1::string" | .record "std::string" | .record "std::__cxx11::string" => some (.int true 8)
  | .record "std::__1::wstring" | .record "std::wstring" | .record "std::__cxx11::wstring" => some (.int true 32)
  | .record "std::__1::u8string" | .record "std::u8string" => some (.int false 8)
  | .record "std::__1::u16string" | .record "std::u16string" => some (.int false 16)
  | .record "std::__1::u32string" | .record "std::u32string" => some (.int false 32)
  | .record n =>
    let isCont := ["std::__1::vector<", "std::vector<", "std::__1::basic_string<", "std::basic_string<",
      "std::__cxx11::basic_string<"].any fun p => n.startsWith p
    if !isCont then none else
    let cs := (n.toList.dropWhile (· != '<')).drop 1 |>.takeWhile fun c => c != ',' && c != '>'
    let unpad (l : List Char) : List Char := l.dropWhile (· == ' ')
    match String.ofList (unpad (unpad cs).reverse).reverse with
    | "char" | "signed char" => some (.int true 8)
    | "unsigned char" => some (.int false 8)
    | "short" => some (.int true 16)
    | "unsigned short" | "char16_t" => some (.int false 16)
    | "int" | "wchar_t" => some (.int true 32)
    | "unsigned int" | "char32_t" => some (.int false 32)
    | "long" => some (.int true ptrBits)
    | "unsigned long" => some (.int false ptrBits)
    | "long long" => some (.int true 64)
    | "unsigned long long" => some (.int false 64)
    | "float" => some (.float .single)
    | "double" => some (.float .double)
    | "bool" => some .bool
    | _ => none
  | _ => none

/-- The byte range `[p, p + n)` as typed values: a range of whole elements of
an array, or of the live elements of a container (`std::vector`,
`std::string`: their storage `vec g xs`, the element type from the
container's record type), as block, parent path, first index, count, element
type; or a whole object (count 1, no index). Byte ranges inside an object, or
across objects of different types, are not modelled (`none`). -/
def typedRange? (ctx : Ctx) (m : Mem) (p : Ptr) (n : Int) : Option (Nat × List PathElem × Option Nat × Nat × Ty) :=
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      let whole : Option (Nat × List PathElem × Option Nat × Nat × Ty) :=
        match ctx.typeAt blk.ty path with
        | some t => match ctx.sizeAlign 32 t with
          | some (sz, _) => if (sz : Int) = n then some (b, path, none, 1, t) else none
          | none => none
        | none => none
      match splitLast path with
      | some (pre, .idx i) =>
        match ctx.typeAt blk.ty pre, m.read? (.loc b pre) with
        | some (.array e _), some (.arr xs) =>
          match ctx.sizeAlign 32 e with
          | some (sz, _) =>
            if sz > 0 ∧ n ≥ 0 ∧ n % sz = 0 ∧ i + (n / sz).toNat ≤ xs.length then
              some (b, pre, some i, (n / sz).toNat, e)
            else whole
          | none => whole
        | _, _ => whole
      | some (pre, .vel g i) =>
        match m.read? (.loc b pre), (ctx.typeAt blk.ty pre).bind (containerElemTy? (8 * ctx.mod.ptrBytes)) with
        | some (.vec g' xs), some e =>
          match ctx.sizeAlign 32 e with
          | some (sz, _) =>
            if g = g' ∧ sz > 0 ∧ n ≥ 0 ∧ n % sz = 0 ∧ i + (n / sz).toNat ≤ xs.length then
              some (b, pre, some i, (n / sz).toNat, e)
            else none
          | none => none
        | _, _ => none
      | _ => whole
    | none => none
  | _ => none

/-- The values of a typed range. -/
def rangeVals (m : Mem) (r : Nat × List PathElem × Option Nat × Nat × Ty) : Option (List Val) :=
  match r with
  | (b, path, none, _, _) => (m.read? (.loc b path)).map ([·])
  | (b, pre, some i, k, _) => match m.read? (.loc b pre) with
    | some (.arr xs) | some (.vec _ xs) => some ((xs.drop i).take k)
    | _ => none

/-- Write the values of a typed range. -/
def rangeWrite (m : Mem) (r : Nat × List PathElem × Option Nat × Nat × Ty) (vs : List Val) : Option Mem :=
  match r, vs with
  | (b, path, none, _, _), [v] => m.write? (.loc b path) v
  | (b, pre, some i, _, _), vs => match m.read? (.loc b pre) with
    | some (.arr xs) => m.write? (.loc b pre) (.arr (xs.take i ++ vs ++ xs.drop (i + vs.length)))
    -- a container keeps its generation: its storage is not reallocated
    | some (.vec g xs) => m.write? (.loc b pre) (.vec g (xs.take i ++ vs ++ xs.drop (i + vs.length)))
    | _ => none
  | _, _ => none

/-! ### Bytes of objects

`memcpy`, `memmove` and `memset` copy and set bytes (C11 7.24.2.1p2, 7.24.2.2p2,
7.24.6.1p2; an object's representation is its bytes, 6.2.6.1p4). Whole objects
of one type are copied as values (`typedRange?`); between objects of different
types, or over part of an object, the bytes of the range are moved. A range is
taken in the smallest object along the pointer's path that contains it
(`byteRange?`), whose scalars are read as bytes (`scalarBytes`) and rebuilt from
bytes (`scalarOfBytes`). Unions are not covered: a member's slot can hold a stale
value of that member. -/

/-- A byte of an object's representation. -/
inductive MByte where
  /-- A byte of known value (`< 256`). -/
  | val (c : Nat)
  /-- An indeterminate byte. -/
  | undef
  /-- Byte `k` of the pointer `p`, which has no byte values here: a pointer is
  rebuilt only from all its bytes, in order. -/
  | ptr (p : Ptr) (k : Nat)
  deriving DecidableEq, Inhabited

/-- The byte offsets of the members of a record laid out as a struct (as
`Ctx.sizeAlign` lays it out). -/
def structOffsets? (ctx : Ctx) (r : RecordDecl) : Option (List Nat) :=
  let step (acc : Option (Nat × List Nat)) (t : Ty) : Option (Nat × List Nat) :=
    match acc, ctx.sizeAlign 32 t with
    | some (off, offs), some (s, a) =>
      let off' := if r.packed then off else (off + a - 1) / a * a
      some (off' + s, offs ++ [off'])
    | _, _ => none
  ((r.members.map (·.2)).foldl step (some (0, []))).map (·.2)

/-- A record laid out as a union (`Ctx.sizeAlign`): its members share their storage. -/
def unionLayout (r : RecordDecl) : Bool := decide (r.kind = .union) || !r.padding.isEmpty

/-- The byte offset of the subobject at `path` in an object of type `t`: array
elements, record members (a union's at 0), and a byte view's `.byte k` last. -/
def pathOffset? (ctx : Ctx) : Ty → List PathElem → Option Nat
  | _, [] => some 0
  | _, [.byte k] => some k
  | .array e _, .idx i :: p =>
    match ctx.sizeAlign 32 e, pathOffset? ctx e p with
    | some (s, _), some o => some (i * s + o)
    | _, _ => none
  | .record name, .idx k :: p =>
    match ctx.record? name with
    | some r =>
      match r.members[k]? with
      | some (_, t) =>
        let off : Option Nat := if unionLayout r then some 0 else (structOffsets? ctx r).bind (·[k]?)
        match off, pathOffset? ctx t p with
        | some a, some o => some (a + o)
        | _, _ => none
      | none => none
    | none => none
  | _, _ => none

/-- The path goes into a member of a union. -/
def throughUnion (ctx : Ctx) : Ty → List PathElem → Bool
  | .array e _, .idx _ :: p => throughUnion ctx e p
  | .record name, .idx k :: p =>
    match ctx.record? name with
    | some r =>
      unionLayout r || match r.members[k]? with
        | some (_, t) => throughUnion ctx t p
        | none => false
    | none => false
  | _, _ => false

/-- The `n` bytes from the pointer `p`, in the smallest object along its path
that contains them: its block and path, its type, and the offset of `p` in it.
`none` for a path into a union member or without byte offsets (container
elements), and for bytes outside the block's object. -/
def byteRange? (ctx : Ctx) (m : Mem) (p : Ptr) (n : Nat) : Option (Nat × List PathElem × Ty × Nat) :=
  match p with
  | .loc b path =>
    match m.blocks b with
    | some blk =>
      let (path0, k) : List PathElem × Nat := match splitLast path with
        | some (pre, .byte k) => (pre, k)
        | _ => (path, 0)
      if throughUnion ctx blk.ty path0 then none else
      (List.range (path0.length + 1)).reverse.findSome? fun j =>
        match ctx.typeAt blk.ty (path0.take j) with
        | some t =>
          match pathOffset? ctx t (path0.drop j), ctx.sizeAlign 32 t with
          | some o, some (sz, _) => if o + k + n ≤ sz then some (b, path0.take j, t, o + k) else none
          | _, _ => none
        | none => none
    | none => none
  | _ => none

/-- The bytes of a scalar value `v` of type `t` of `sz` bytes: `byteOf`'s
(indeterminate where it has none: a NaN `Float`, a floating type it does not
cover), a pointer's, an indeterminate value's. `none`: not a scalar. -/
def scalarBytes (t : Ty) (v : Val) (sz : Nat) : Option (List MByte) :=
  if !t.isScalar then none else
  match t, v with
  | .ptr _, .ptr p | .vptr, .ptr p => some ((List.range sz).map (MByte.ptr p))
  | _, .undef => some (List.replicate sz .undef)
  | _, .int _ | _, .bool _ | _, .float _ =>
    some ((List.range sz).map fun k => match byteOf t v k with
      | some c => .val c
      | none => .undef)
  | _, _ => none

/-- The value of scalar type `t` from its bytes `bs` (little-endian): an integer
(re-wrapped to its type, as `setByte`), a `bool` from 0 or 1, a float from a bit
pattern that is not a NaN, the null pointer from zero bytes, a pointer from all
its bytes in order. Bytes that are no value of a `bool` or floating type (a
`bool` byte other than 0 / 1, a NaN's bit pattern) stay, as their unsigned
number in an `.int`, as after a character store (`setByteRepr`). Otherwise
indeterminate (`.undef`, whose reads are undefined): an indeterminate byte,
other bytes for a pointer, a pointer's bytes for another type. -/
def scalarOfBytes (t : Ty) (bs : List MByte) : Val :=
  let known : Option (List Nat) := bs.mapM fun b => match b with
    | .val c => some c
    | _ => none
  let num (cs : List Nat) : Nat := cs.foldr (fun c acc => c + 256 * acc) 0
  match t, known with
  | .int s w, some cs => .int (wrap s w (num cs))
  | .bool, some [c] => if c = 0 then .bool false else if c = 1 then .bool true else .int c
  | .float .double, some cs =>
    if decodeBits (num cs) = .nan then .int (num cs) else .float (Float.ofBits (num cs).toUInt64)
  | .float .single, some cs =>
    let g := singleOfBits (num cs)
    if decodeF g = .nan then .int (num cs) else .float g
  | .ptr _, some cs | .vptr, some cs => if cs.all (· == 0) then .ptr .null else .undef
  | .ptr _, none | .vptr, none =>
    match bs with
    | .ptr p 0 :: _ => if bs == (List.range bs.length).map (MByte.ptr p) then .ptr p else .undef
    | _ => .undef
  | _, _ => .undef

/-- Indeterminate bytes: those of `[a, b)` in `[lo, hi)`. -/
def undefSpan (a b lo hi : Nat) : List MByte := List.replicate (min b hi - max a lo) .undef

/-- The bytes of `[lo, hi)` (offsets in the object a range is taken in) that lie
in the object of type `t` at offset `o`, of value `v`, in order: its scalars'
(`scalarBytes`), its implicit padding's (indeterminate). `none`: a union, a
type without a size, a value of another shape. -/
def objBytes (ctx : Ctx) : Nat → Ty → Nat → Val → Nat → Nat → Option (List MByte)
  | 0, _, _, _, _, _ => none
  | d + 1, t, o, v, lo, hi =>
    match ctx.sizeAlign 32 t with
    | none => none
    | some (sz, _) =>
      if o + sz ≤ lo ∨ hi ≤ o then some [] else
      match t, v with
      | .array e _, .arr xs =>
        match ctx.sizeAlign 32 e with
        | some (es, _) =>
          if es = 0 then some [] else
          let i0 := (lo - o) / es
          -- the elements from the one holding byte `lo`
          let elem (x : Val × Nat) : Option (List MByte) := objBytes ctx d e (o + x.2 * es) x.1 lo hi
          ((((xs.drop i0).take ((hi - o + es - 1) / es - i0)).zipIdx i0).mapM elem).map List.flatten
        | none => none
      | .record name, .agg fs =>
        match ctx.record? name with
        | some r =>
          match structOffsets? ctx r, r.members.mapM (fun mt => (ctx.sizeAlign 32 mt.2).map (·.1)) with
          | some offs, some sizes =>
            if unionLayout r || fs.length != r.members.length then none else
            let ends := (offs.zip sizes).map fun (a, s) => a + s
            -- each member (value, member, offset, end of the member before it) after the
            -- implicit padding before it, then the tail padding
            let mem (x : (Val × MemberKind × Ty) × Nat × Nat) : Option (List MByte) :=
              (objBytes ctx d x.1.2.2 (o + x.2.1) x.1.1 lo hi).map (undefSpan (o + x.2.2) (o + x.2.1) lo hi ++ ·)
            (((fs.zip r.members).zip (offs.zip (0 :: ends))).mapM mem).map fun bss =>
              bss.flatten ++ undefSpan (o + ends.getLastD 0) (o + sz) lo hi
          | _, _ => none
        | none => none
      | t, v => (scalarBytes t v sz).map fun bs => (bs.drop (lo - o)).take (min hi (o + sz) - max lo o)

/-- The object of type `t` at offset `o`, of value `v`, with the bytes
`[lo, lo + bs.size)` (offsets in the object a range is taken in) replaced by
`bs`: each scalar they reach is rebuilt from its bytes (`scalarOfBytes`), the
others are kept; bytes of implicit padding are not stored. `none` as
`objBytes`. -/
def putBytes (ctx : Ctx) : Nat → Ty → Nat → Val → Nat → Array MByte → Option Val
  | 0, _, _, _, _, _ => none
  | d + 1, t, o, v, lo, bs =>
    match ctx.sizeAlign 32 t with
    | none => none
    | some (sz, _) =>
      if o + sz ≤ lo ∨ lo + bs.size ≤ o then some v else
      match t, v with
      | .array e _, .arr xs =>
        match ctx.sizeAlign 32 e with
        | some (es, _) =>
          if es = 0 then some v else
          let i0 := (lo - o) / es
          -- the elements from the one holding byte `lo`
          let elem (x : Val × Nat) : Option Val := putBytes ctx d e (o + x.2 * es) x.1 lo bs
          ((((xs.drop i0).take ((lo + bs.size - o + es - 1) / es - i0)).zipIdx i0).mapM elem).map
            fun (ys : List Val) => .arr (xs.take i0 ++ ys ++ xs.drop (i0 + ys.length))
        | none => none
      | .record name, .agg fs =>
        match ctx.record? name with
        | some r =>
          match structOffsets? ctx r with
          | some offs =>
            if unionLayout r || fs.length != r.members.length then none else
            let mem (x : (Val × MemberKind × Ty) × Nat) : Option Val := putBytes ctx d x.1.2.2 (o + x.2) x.1.1 lo bs
            (((fs.zip r.members).zip offs).mapM mem).map Val.agg
          | none => none
        | none => none
      | t, v =>
        (scalarBytes t v sz).map fun old => scalarOfBytes t (old.zipIdx.map fun (b, k) =>
          if lo ≤ o + k ∧ o + k < lo + bs.size then bs.getD (o + k - lo) .undef else b)

/-! ### Overlapping ranges

C makes copying between overlapping objects undefined for `memcpy`, `strcpy`,
`sprintf` and `snprintf` (C11 7.24.2.1p2, 7.24.2.3p2, 7.21.6.6p2, 7.21.6.5p2);
`memmove` copies them. -/

/-- The index `j` of a path `pre ++ .idx j :: _`. -/
def idxAfter? (pre p : List PathElem) : Option Nat :=
  if pre.isPrefixOf p then
    match p.drop pre.length with
    | .idx j :: _ => some j
    | _ => none
  else none

/-- The path `p` lies in the elements `[i, i + k)` of the array at `pre`. -/
def inSlice (pre : List PathElem) (i k : Nat) (p : List PathElem) : Bool :=
  match idxAfter? pre p with
  | some j => decide (i ≤ j) && decide (j < i + k)
  | none => false

/-- The longest common prefix of two paths. -/
def commonPath : List PathElem → List PathElem → List PathElem
  | a :: as, b :: bs => if a = b then a :: commonPath as bs else []
  | _, _ => []

/-- Paths `p` and `q` of a block of type `ty` part inside a union, into two of
its members, whose storage overlaps. -/
def unionSplit (ctx : Ctx) (ty : Ty) (p q : List PathElem) : Bool :=
  let c := commonPath p q
  decide (c.length < p.length) && decide (c.length < q.length) &&
    match ctx.typeAt ty c with
    | some (.record name) => match ctx.record? name with
      | some r => decide (r.kind = .union)
      | none => false
    | _ => false

/-- Two typed ranges (`typedRange?`) overlap: they are in the same block, and a
path one covers is a prefix of a path the other covers (the object at a path
covers its subobjects; the slice `[i, i + k)` of the array at `pre` covers
these elements), or they lie in different members of one union. -/
def rangesOverlap (ctx : Ctx) (m : Mem) (r r' : Nat × List PathElem × Option Nat × Nat × Ty) : Bool :=
  let (b, p, ip, k, _) := r
  let (b', q, iq, k', _) := r'
  if b = b' then
    (match ip, iq with
     | none, none => p.isPrefixOf q || q.isPrefixOf p
     | none, some j => p.isPrefixOf q || inSlice q j k' p
     | some i, none => q.isPrefixOf p || inSlice p i k q
     | some i, some j =>
       if p = q then decide (i < j + k') && decide (j < i + k) else inSlice p i k q || inSlice q j k' p) ||
    match m.blocks b with
    | some blk => unionSplit ctx blk.ty p q
    | none => false
  else false

/-- The block of a pointer and its byte offset in the block's object (`pathOffset?`). -/
def blockOffset? (ctx : Ctx) (m : Mem) : Ptr → Option (Nat × Nat)
  | .loc b path =>
    match m.blocks b with
    | some blk => (pathOffset? ctx blk.ty path).map ((b, ·))
    | none => none
  | _ => none

/-- The `n` bytes from `d` and the `n` bytes from `s` overlap: the same block,
intersecting byte offsets (`blockOffset?`). -/
def bytesOverlap (ctx : Ctx) (m : Mem) (d s : Ptr) (n : Nat) : Bool :=
  match blockOffset? ctx m d, blockOffset? ctx m s with
  | some (b, x), some (b', y) => b == b' && decide (x < y + n) && decide (y < x + n)
  | _, _ => false

/-- `memcpy(d, s, n)`, `n ≠ 0`, between overlapping objects: typed ranges
(`rangesOverlap`), else ranges of bytes (`bytesOverlap`). -/
def memcpyOverlap (ctx : Ctx) (m : Mem) (d s : Ptr) (n : Int) : Bool :=
  if n = 0 then false else
    match typedRange? ctx m s n, typedRange? ctx m d n with
    | some rs, some rd => rangesOverlap ctx m rs rd
    | _, _ => bytesOverlap ctx m d s n.toNat

/-- One of the strings `ps` overlaps the range `r` that the text is written to:
the characters read, which for a precision `n` (`%.ns`) are those before the
terminator or the `n`th, the terminator included when it is reached first
(`readCStrN`), else the string and its terminator (the format string, a `%s`
without a precision). -/
def strArgsOverlap (ctx : Ctx) (m : Mem) (r : Nat × List PathElem × Option Nat × Nat × Ty)
    (ps : List (Ptr × Option Nat)) : Bool :=
  ps.any fun (p, prec) =>
    let len? : Option Nat := match prec with
      | some n => match readCStrN m p n with
        | .ok cs => some (if cs.length < n then cs.length + 1 else n)
        | _ => none
      | none => match readCStr m p with
        | .ok cs => some (cs.length + 1)
        | _ => none
    match len? with
    | some len =>
      if len = 0 then false else
      match typedRange? ctx m p len with
      | some rs => rangesOverlap ctx m rs r
      | none => false
    | none => false

/-- A pointer argument of a `<string.h>` function with a length: valid even when
the length is 0 (C11 7.24.1p2, 7.1.4p1): it points into a live object or just
past its end, not null, and for a destination (`dst`) not into read-only
storage. -/
def validMemArg (m : Mem) (dst : Bool) (p : Ptr) : Bool :=
  match p with
  | .loc b _ => match m.live? b with
    | some blk => !(dst && decide (blk.kind = .readonly))
    | none => false
  | _ => false

/-- The position of the first of the characters `xs` equal to `c` converted to `unsigned char`,
reading one by one, at most `n` of them (`none`: `n` read, none equal); reading past `xs` or an
indeterminate character is undefined. -/
def memchrIdx (c : Int) : Nat → List Val → Res (Option Nat)
  | 0, _ => .ok none
  | _ + 1, [] => .ub "memchr: read past the end of the object"
  | k + 1, x :: xs =>
    match x with
    | .int v => if wrap false 8 v == wrap false 8 c then .ok (some 0) else do
      let r ← memchrIdx c k xs
      pure (r.map (· + 1))
    | _ => .ub "memchr: indeterminate character"

/-- The offset of the first of the bytes `bs` (the bytes of an object from offset `j` on, `n` of
them at most) that is `c` converted to `unsigned char`; `none` if no byte of the first `n` is.
Reading past the object, an indeterminate byte or a pointer's byte is undefined. -/
def memchrByteIdx (c : Int) : Nat → List MByte → Nat → Res (Option Nat)
  | 0, _, _ => .ok none
  | _ + 1, [], _ => .ub "memchr: read past the end of the object"
  | k + 1, x :: bs, j =>
    match x with
    | .val v => if (v : Int) == wrap false 8 c then .ok (some j) else memchrByteIdx c k bs (j + 1)
    | .undef => .ub "memchr: indeterminate byte"
    | _ => .ub "memchr: a pointer's byte (byte-level access not modelled)"

/-- `memchr(s, c, n)` over the bytes of an object that is no character array or object, as
`unsigned char` (C11 7.24.5.1; the bytes of its representation, 6.2.6.1p4): from the byte `s`
points to, in its block's complete object (`objBytes`), to the first one equal to `c`, at most
`n` of them; the result points to that byte (`Ctx.canonByte`). Bytes of a union member are not
modelled. -/
def memchrBytes (ctx : Ctx) (m : Mem) (s : Ptr) (c n : Int) : Res (Exit × Mem) :=
  match s with
  | .loc b path =>
    match m.live? b with
    | some blk =>
      let path0 := match splitLast path with
        | some (pre, .byte _) => pre
        | _ => path
      if throughUnion ctx blk.ty path0 then .ub "memchr: byte-level access not modelled" else
      match ctx.absPos? blk.ty path, ctx.sizeAlign 32 blk.ty with
      | some q, some (sz, _) =>
        match objBytes ctx 32 blk.ty 0 blk.val q sz with
        | some bs => do
          match ← memchrByteIdx c n.toNat bs q with
          | some j => retv (.ptr (.loc b (ctx.canonByte 32 blk.ty blk.val [] j))) m
          | none => retv (.ptr .null) m
        | none => .ub "memchr: byte-level access not modelled"
      | _, _ => .ub "memchr: byte-level access not modelled"
    | none => .ub "memchr: an invalid pointer"
  | _ => .ub "memchr: an invalid pointer"

/-- The `n` bytes from `p` as `unsigned char`s (`Model.hashMemory`): from the byte `p` points to, in
its block's complete object (`objBytes`: the characters of a char array, the bytes of any other
object's representation); `none` past the end of the object, for an indeterminate byte or a
pointer's byte, through a union, and in a container (the characters of a `std::string` are not
read). -/
def readBytes? (ctx : Ctx) (m : Mem) (p : Ptr) (n : Nat) : Option (List UInt8) :=
  match p with
  | .loc b path =>
    match m.live? b with
    | some blk =>
      let path0 := match splitLast path with
        | some (pre, .byte _) => pre
        | _ => path
      if throughUnion ctx blk.ty path0 then none else
      match ctx.absPos? blk.ty path, ctx.sizeAlign 32 blk.ty with
      | some q, some (sz, _) =>
        if sz < q + n then none else
        match objBytes ctx 32 blk.ty 0 blk.val q (q + n) with
        | some bs =>
          if bs.length = n then bs.mapM fun x => match x with | .val v => some v.toUInt8 | _ => none
          else none
        | none => none
      | _, _ => none
    | none => none
  | _ => if n = 0 then some [] else none

/-- The `n` bytes from `p` lie in the object `p` points into (its block's complete object), whatever
their values (`fwrite` writes indeterminate ones as `unsigned char`s). -/
def bytesInObject (ctx : Ctx) (m : Mem) (p : Ptr) (n : Nat) : Bool :=
  match p with
  | .loc b path =>
    match m.live? b with
    | some blk =>
      match ctx.absPos? blk.ty path, ctx.sizeAlign 32 blk.ty with
      | some q, some (sz, _) => q + n ≤ sz
      | _, _ => false
    | none => false
  | _ => false

/-- `ffs` of `x` taken as `w` bits: the position, from 1, of its least significant bit set; 0 for 0. -/
def ffsOf (w : Nat) (x : Int) : Int :=
  let u := (x % 2 ^ w).toNat
  ((List.range w).find? fun i => u / 2 ^ i % 2 = 1).map (fun i => (i + 1 : Int)) |>.getD 0

/-- `memchr(s, c, n)` (`Model.memchr`): the characters of the char array `s` points into (or the
character object, an array of one), read one by one up to the first one equal to `c` converted to
`unsigned char`, at most `n` of them (C11 7.24.5.1); `s` must be valid even for `n` = 0
(`validMemArg`, 7.24.1p2). Any other object's bytes are read through a byte view
(`memchrBytes`). -/
def memchrModel (ctx : Ctx) (m : Mem) (s : Ptr) (c n : Int) : Res (Exit × Mem) :=
  if n ≤ 0 then
    if validMemArg m false s then retv (.ptr .null) m
    else .ub "memchr: an invalid pointer (C11 7.24.1p2)"
  else
  match m.elemPos? s with
  | some (b, pre, .idx i, _) =>
    match m.blocks b, m.read? (.loc b pre) with
    | some blk, some (.arr xs) =>
      match ctx.typeAt blk.ty pre with
      | some (.array (.int _ 8) _) => do
        match ← memchrIdx c n.toNat (xs.drop i) with
        | some k => retv (.ptr (.loc b (pre ++ [.idx (i + k)]))) m
        | none => retv (.ptr .null) m
      | _ => memchrBytes ctx m s c n
    | _, _ => .ub "memchr: an invalid pointer"
  | _ =>
    match charObject? m s with
    | some v => do
      match ← memchrIdx c n.toNat [v] with
      | some _ => retv (.ptr s) m
      | none => retv (.ptr .null) m
    | none => memchrBytes ctx m s c n

/-- `memset(d, c, n)` byte by byte (`n > 0`): the `n` bytes from `d`, in the
smallest object along its path that contains them (`byteRange?`), set to `c`
converted to `unsigned char`. -/
def memsetBytes (ctx : Ctx) (m : Mem) (d : Ptr) (c n : Int) : Res (Exit × Mem) := do
  let some (b, path, t, o) := byteRange? ctx m d n.toNat | .ub "memset: byte-level access not modelled"
  let v ← Res.ofOption "memset: invalid write" (m.read? (.loc b path))
  let some v' := putBytes ctx 32 t 0 v o (Array.replicate n.toNat (.val (wrap false 8 c).toNat))
    | .ub "memset: byte-level access not modelled"
  retv (.ptr d) (← Res.ofOption "memset: invalid write" (m.write? (.loc b path) v'))

/-- `memcpy(d, s, n)` / `memmove(d, s, n)` byte by byte (`n > 0`): the `n` bytes
from `s` (`objBytes`), all read before any is written, into the `n` bytes from
`d` (`putBytes`), each range in the smallest object along its pointer's path
that contains it (`byteRange?`). -/
def memcpyBytes (ctx : Ctx) (m : Mem) (d s : Ptr) (n : Int) : Res (Exit × Mem) := do
  let some (bs, ps, ts, os) := byteRange? ctx m s n.toNat | .ub "memcpy: byte-level access not modelled"
  let some (bd, pd, td, od) := byteRange? ctx m d n.toNat | .ub "memcpy: byte-level access not modelled"
  let vs ← Res.ofOption "memcpy: invalid read" (m.read? (.loc bs ps))
  let some bytes := objBytes ctx 32 ts 0 vs os (os + n.toNat) | .ub "memcpy: byte-level access not modelled"
  if bytes.length ≠ n.toNat then .ub "memcpy: byte-level access not modelled" else
  let vd ← Res.ofOption "memcpy: invalid write" (m.read? (.loc bd pd))
  let some vd' := putBytes ctx 32 td 0 vd od bytes.toArray | .ub "memcpy: byte-level access not modelled"
  retv (.ptr d) (← Res.ofOption "memcpy: invalid write" (m.write? (.loc bd pd) vd'))

/-- `memset(d, c, n)`: zero, or any byte into a range of bytes (`char`s); other
values, and ranges that are no typed range, byte by byte (`memsetBytes`). -/
def memsetModel (ctx : Ctx) (m : Mem) (d : Ptr) (c n : Int) : Res (Exit × Mem) := do
  if n = 0 then
    if validMemArg m true d then retv (.ptr d) m
    else .ub "memset: invalid pointer argument, also with length 0 (C11 7.24.1p2)" else
  let some r := typedRange? ctx m d n | memsetBytes ctx m d c n
  let (_, _, _, k, t) := r
  if c != 0 && !t.isChar then memsetBytes ctx m d c n else
  let v ← match t with
    | .int s 8 => pure (Val.int (wrap s 8 c))
    | t => Res.ofOption "memset: no zero value for the type" (ctx.zeroVal 32 t)
  retv (.ptr d) (← Res.ofOption "memset: invalid write" (rangeWrite m r (List.replicate k v)))

/-- `memcpy(d, s, n)` / `memmove(d, s, n)`: values of the same type (the source
values are read before the destination is written, as `memmove` does; for
`memcpy`, `runModel` first makes overlapping objects undefined, `memcpyOverlap`);
objects of different types, and ranges that are no typed range, byte by byte
(`memcpyBytes`). -/
def memcpyModel (ctx : Ctx) (m : Mem) (d s : Ptr) (n : Int) : Res (Exit × Mem) := do
  if n = 0 then
    if validMemArg m true d && validMemArg m false s then retv (.ptr d) m
    else .ub "memcpy: invalid pointer argument, also with length 0 (C11 7.24.1p2)" else
  let some rs := typedRange? ctx m s n | memcpyBytes ctx m d s n
  let some rd := typedRange? ctx m d n | memcpyBytes ctx m d s n
  if rs.2.2.2.1 != rd.2.2.2.1 then memcpyBytes ctx m d s n else
  let vs ← Res.ofOption "memcpy: invalid read" (rangeVals m rs)
  -- same element type; or integers of the same width (`char` / `unsigned
  -- char`): the bytes are reinterpreted in the destination's type
  let some vs := (match rs.2.2.2.2, rd.2.2.2.2 with
    | .int _ w, .int s' w' =>
      if w == w' then some (vs.map fun v => match v with | .int x => Val.int (wrap s' w' x) | v => v)
      else none
    | ts, td => if ts == td then some vs else none) | memcpyBytes ctx m d s n
  retv (.ptr d) (← Res.ofOption "memcpy: invalid write" (rangeWrite m rd vs))

/-- `memcmp(a, b, n)` on two typed ranges of one scalar type (`char`s of either
signedness; the elements of arrays or containers, whole objects): their bytes
(`scalarBytes`, little-endian), the sign of the first difference as unsigned
bytes. An indeterminate byte in either range is undefined; a pointer's bytes
are not modelled. -/
def memcmpModel (ctx : Ctx) (m : Mem) (a b : Ptr) (n : Int) : Res (Exit × Mem) := do
  if n = 0 then
    if validMemArg m false a && validMemArg m false b then retv (.int 0) m
    else .ub "memcmp: invalid pointer argument, also with length 0 (C11 7.24.1p2)" else
  match typedRange? ctx m a n, typedRange? ctx m b n with
  | some ra, some rb =>
    let ta := ra.2.2.2.2
    let tb := rb.2.2.2.2
    let some (sz, _) := ctx.sizeAlign 32 ta | .ub "memcmp: byte-level access not modelled"
    if !(ta == tb || ta.isChar && tb.isChar) then .ub "memcmp: byte-level access not modelled" else
    let xs ← Res.ofOption "memcmp: invalid read" (rangeVals m ra)
    let ys ← Res.ofOption "memcmp: invalid read" (rangeVals m rb)
    let bytes (t : Ty) (vs : List Val) : Option (List MByte) :=
      (vs.mapM fun v => scalarBytes t v sz).map List.flatten
    let some bx := bytes ta xs | .ub "memcmp: byte-level access not modelled"
    let some by_ := bytes tb ys | .ub "memcmp: byte-level access not modelled"
    if (bx ++ by_).any (fun c => c matches .ptr ..) then .ub "memcmp: byte-level access not modelled" else
    let known (bs : List MByte) : Option (List Nat) := bs.mapM fun c => match c with
      | .val c => some c
      | _ => none
    let some cx := known bx | .ub "memcmp: read of an indeterminate byte"
    let some cy := known by_ | .ub "memcmp: read of an indeterminate byte"
    -- only the sign is specified (C11 7.24.4.1p2); glibc returns the difference of the first
    -- differing bytes (as unsigned char), as the strcmp model does
    let r : Int := match (cx.zip cy).find? (fun (x, y) => x != y) with
      | some (x, y) => (x : Int) - y
      | none => 0
    retv (.int r) m
  | _, _ => .ub "memcmp: byte-level access not modelled"

/-- The block holding the registrations of `kind`, `atexit` (`atexit` / `__cxa_atexit`) or
`at_quick_exit`, with their list in registration order: the first live block of type `kind` from
block `b` (the first one after the globals) on. The first registration allocates it, mostly during
static initialization, so the search is short; looking at every block would cost a walk through
all memory updates for each block. -/
def handlerRegistry (kind : String) (m : Mem) (b : Nat) : Option (Nat × List Val) :=
  go (m.next - b) b
where
  go : Nat → Nat → Option (Nat × List Val)
    | 0, _ => none
    | n + 1, b =>
      match m.blocks b with
      | some ⟨.global, true, .other k, .arr es⟩ => if k == kind then some (b, es) else go n (b + 1)
      | _ => go n (b + 1)

/-- `lrint(x)` / `llrint(x)` (`fn`): `x` rounded to nearest, half to even (the default rounding
mode), as a `long` / `long long`; out of their range, and for an infinity or NaN, the value is
unspecified (C11 7.12.9.5), undefined here. -/
def lrintModel (fn : String) (x : Float) (m : Mem) : Res (Exit × Mem) :=
  match decodeF (roundIntF 4 x) with
  | .finite neg mg e =>
    let t := truncVal neg mg e
    if inRange true 64 t then retv (.int t) m else .ub s!"{fn}: the rounded value is out of range"
  | _ => .ub s!"{fn} of an infinity or NaN"

/-- `signal(sig, f)` (`Model.signal`): `f` registered for `sig` in the registry block `signal`
(`handlerRegistry`; 65 entries, `SIG_DFL`, a null pointer, until registered), the function
registered before returned; `SIG_ERR` (`(void (*)(int)) -1`, the address with all bits set, as
the program's `int_to_ptr` of it gives) for a signal a program may not handle in glibc.
Registering only: no signal is ever delivered. -/
def signalModel (ctx : Ctx) (m : Mem) (sig : Int) (f : Ptr) : Res (Exit × Mem) :=
  if sig < 1 || 64 < sig || sig == 9 || sig == 19 || sig == 32 || sig == 33 then
    retv (.ptr (.addr (2 ^ (8 * ctx.mod.ptrBytes) - 1))) m
  else
    match handlerRegistry "signal" m ctx.mod.globals.length with
    | some (b, es) => do
      retv (es.getD sig.toNat (.ptr .null)) (← writeVal m (.loc b []) (.arr (es.set sig.toNat (.ptr f))))
    | none =>
      let (_, m) := m.alloc .global (.other "signal")
        (.arr ((List.replicate 65 (Val.ptr .null)).set sig.toNat (.ptr f)))
      retv (.ptr .null) m

/-- `posix_memalign(mp, a, size)` (`Model.posixMemalign`): `EINVAL` (22) unless `a` is a power of
two and a multiple of `sizeof(void *)`; else `*mp` = fresh heap storage of `size` bytes (as
`allocHeap`), and 0. -/
def posixMemalignModel (ctx : Ctx) (m : Mem) (mp : Ptr) (a size : Int) : Res (Exit × Mem) :=
  if a ≤ 0 || a % (ctx.mod.ptrBytes : Int) != 0 || (a.toNat &&& (a.toNat - 1)) != 0 then
    retv (.int 22) m
  else do
    let (b, m) := m.alloc .heap (.array (.other "heap") size.toNat) .undef
    retv (.int 0) (← ctx.typedStore m (.ptr .void) mp (.ptr (.loc b [])))

/-! ### `rand` / `srand`: glibc's `random_r` for `TYPE_3` -/

/-- One output: `st[f] += st[r]` (mod 2^32), the result is that word shifted right by one, and
`f`, `r` advance cyclically over the 31 words. -/
def randStep (st : List Nat) (f r : Nat) : Nat × List Nat × Nat × Nat :=
  let v := (st.getD f 0 + st.getD r 0) % 2 ^ 32
  (v / 2, st.set f v, (f + 1) % 31, (r + 1) % 31)

/-- `srandom_r(seed)`: word 0 is the seed (1 for 0), word `i` is `16807 * word (i-1)` modulo
2^31 - 1 by Schrage's method on 32-bit words (as glibc computes it, also for a seed above
2^31 - 1), then 310 outputs are discarded. The 31 words (unsigned) and the positions of `fptr`
and `rptr`. -/
def randSeed (seed : Nat) : List Nat × Nat × Nat :=
  let s : Nat := seed % 2 ^ 32
  let w0 : Int := wrap true 32 (if s = 0 then 1 else (s : Int))
  let (ws, _) := (List.range 30).foldl (fun (acc : Array Int × Int) _ =>
    let w := acc.2
    let w' := wrap true 32 (16807 * Int.tmod w 127773 - 2836 * Int.tdiv w 127773)
    let w' := if w' < 0 then w' + 2147483647 else w'
    (acc.1.push w', w')) (#[w0], w0)
  let st := ws.toList.map fun w => (w % 2 ^ 32).toNat
  (List.range 310).foldl (fun (acc : List Nat × Nat × Nat) _ =>
    let (_, st, f, r) := randStep acc.1 acc.2.1 acc.2.2
    (st, f, r)) (st, 3, 0)

/-- The generator's state as stored: the 31 words, then the positions of `fptr` and `rptr`. -/
def randVal (st : List Nat) (f r : Nat) : Val := .arr ((st ++ [f, r]).map fun (n : Nat) => .int n)

/-- The block holding the generator's state: the first one after the globals, which
`CIR.runCtors` allocates for a module that calls `rand` or `srand`. -/
def randBlock (ctx : Ctx) (m : Mem) : Res (Nat × List Nat × Nat × Nat) :=
  let b := ctx.mod.globals.length
  match m.blocks b with
  | some ⟨.global, true, .other "rand", .arr vs⟩ =>
    let ns := vs.filterMap fun v => match v with | .int n => some n.toNat | _ => none
    if ns.length = 33 then .ok (b, ns.take 31, ns.getD 31 0, ns.getD 32 0)
    else .ub "rand: invalid generator state"
  | _ => .ub "rand: no generator state (the program did not start with runCtors)"

/-! ### Libraries outside the C and C++ standards: libevent 2.1, POSIX

These follow the libraries' documentation and, where it is silent, their source (libevent
2.1.12-stable) and what glibc and Linux do. Where a result depends on the environment of the run
rather than on the arguments, the models read it from `World.current`. -/

/-- The environment of a run, where library results depend on it: whether the allocations
libevent makes succeed (`alloc`: in `evhttp_add_header`, `evbuffer_new`, `evbuffer_add`), the
id of the only thread (`threadId`, what `pthread_self` returns; glibc's ids are the addresses of
the threads' descriptors, never 0), whether that thread may use the real-time scheduling policies
(`rtPrivileged`: Linux's `CAP_SYS_NICE`, else `pthread_setschedparam` gives EPERM), the clock
(`now`, what `time` returns, in seconds since the Epoch), and the local time zone (`tzOffset`, its
offset from UTC in seconds east, a fixed one: `ctime_r`). -/
structure World where
  alloc : Bool := true
  threadId : Nat := 1
  rtPrivileged : Bool := true
  now : Int := 0
  tzOffset : Int := 0

/-- The environment the models assume, the same in every run (README, trust base): allocations
succeed, the thread's id is 1 and it may use the real-time policies, the clock reads the Epoch
(1970-01-01 00:00:00 UTC), and local time is UTC. -/
def World.current : World := {}

/-- The symbol of the program's `errno`: an `int` global that the frontend adds to a module that
declares `__errno_location` (`Frontend.errnoGlobal`; not internal, so linked units share it). -/
def errnoSym : String := "cirlean.errno"

/-- `errno = e`: a typed store into the program's `errno` (`errnoSym`); nothing in a module without
it, which cannot read `errno`. -/
def setErrno (ctx : Ctx) (m : Mem) (e : Int) : Res Mem :=
  match ctx.gaddr errnoSym with
  | some b => ctx.typedStore m (.int true 32) (.loc b []) (.int e)
  | none => pure m

/-- An update of `errno` that only a module with one computes (`errnoSym`): `u ()` is `none` for no
change, `some (some e)` to store `e`, `some none` to make it indeterminate (glibc's rule varies, so
a later read is undefined). The standard library's models whose glibc versions set `errno` use it:
`strtod` and `strtol` and their siblings, `sscanf`, the `<math.h>` functions. -/
def updErrno (ctx : Ctx) (m : Mem) (u : Unit → Option (Option Int)) : Res Mem :=
  match ctx.gaddr errnoSym with
  | none => pure m
  | some b =>
    match u () with
    | none => pure m
    | some (some e) => ctx.typedStore m (.int true 32) (.loc b []) (.int e)
    | some none => Res.ofOption "errno: invalid write" (m.write? (.loc b []) .undef)

/-- Whether glibc's `strtod` (`single`: `strtof`) of the characters `cs` stores ERANGE in `errno`
(C11 7.22.1.3p10): when the value overflows (it rounds to an infinity), and when it underflows, a
nonzero value tiny after rounding (below the least normal number when rounded to the format's
precision with no bound on the exponent, x86's tininess) and inexact (glibc's `round_and_return`);
not for an infinity, a NaN or a zero written as such. -/
def strtodErange (single : Bool) (cs : List Int) : Bool :=
  let cs := cs.dropWhile fun c => c == 32 || (9 ≤ c && c ≤ 13)
  let cs := match cs with
    | 45 :: r | 43 :: r => r
    | r => r
  let cs := cs.take (fpSubject cs).1
  match cs with
  | [] => false
  | c :: _ =>
    if lowerC c == 105 || lowerC c == 110 then false else
    let hex := hexPrefix cs
    let dig := if hex then isHexC else isDigitC
    let rest := if hex then cs.drop 2 else cs
    let ip := rest.takeWhile dig
    let (fp, after) : List Int × List Int := match rest.drop ip.length with
      | 46 :: r => (r.takeWhile dig, r.drop (r.takeWhile dig).length)
      | r => ([], r)
    let mant := if hex then hexDigitsVal (ip ++ fp) else decDigitsVal (ip ++ fp)
    let x : Int := match after with
      | p :: r => if lowerC p == (if hex then 112 else 101) then expVal r else 0
      | [] => 0
    let (base, x) : Nat × Int := if hex then (2, x - 4 * fp.length) else (10, x - fp.length)
    -- `scaleRound`'s bounds: beyond them an infinity, or a zero
    if mant = 0 then false
    else if 5000 < x || x < -(5000 + 4 * (Nat.log2 mant + 1) : Int) then true
    else
      let (num, den) := if 0 ≤ x then (mant * base ^ x.toNat, 1) else (mant, base ^ (-x).toNat)
      -- precision `p`; tiny: below `2^emin · (1 - 2^-(p+1))`, i.e. `num · 2^t < (2^(p+1) - 1) · den`
      let (p, emin, emax, t) : Nat × Int × Int × Nat :=
        if single then (24, -149, 104, 151) else (53, -1074, 971, 1076)
      match roundBin p emin emax num den with
      | none => true
      | some (m, e) =>
        let exact := if 0 ≤ e then m * 2 ^ e.toNat * den == num else m * den == num * 2 ^ (-e).toNat
        num * 2 ^ t < (2 ^ (p + 1) - 1) * den && !exact

/-- glibc's `errno` after the `<math.h>` function `fn` (`single`: its `float` version) gave `y` for
the arguments `xs` (C11 7.12.1; glibc's `math_errhandling` has `MATH_ERRNO`), as an `updErrno`
update: EDOM for a NaN from arguments that are not NaNs (a domain error), ERANGE for an infinity
from finite ones (a pole or an overflow); indeterminate after a possible underflow, a subnormal
result of a function that is not exact or a 0 from `exp`, `exp2`, `pow`, `atan2`, `erfc` or
`tgamma` of a nonzero first argument, all arguments finite (whether glibc stores ERANGE then
differs between functions). -/
def libmErrno (fn : String) (single : Bool) (xs : List Float) (y : Float) : Option (Option Int) :=
  let key (f : Float) : Option Int := fkey (decodeF f)
  let finite (f : Float) : Bool := match decodeF f with
    | .finite .. => true
    | _ => false
  let exact := fn == "floor" || fn == "ceil" || fn == "trunc" || fn == "round" || fn == "fabs" ||
    fn == "fmin" || fn == "fmax" || fn == "fmod"
  if xs.any (fun x => (key x).isNone) then none
  else if (key y).isNone then some (some 33)
  else if !finite y then (if xs.all finite then some (some 34) else none)
  else
    let k := (key y).getD 0
    let tiny := k.natAbs < (if single then 2 ^ 948 else 2 ^ 52)
    let firstNonzero := match xs with
      | x :: _ => (key x).getD 0 != 0
      | [] => false
    if exact || !tiny || !xs.all finite then none
    else if k != 0 then some none
    else if (fn == "exp" || fn == "exp2" || fn == "pow" || fn == "atan2" || fn == "erfc" || fn == "tgamma") &&
      firstNonzero then some none
    else none

/-- `y`, the result of the `<math.h>` function `fn` (`single`: its `float` version) for the
arguments `xs`, returned with `errno` as glibc leaves it (`libmErrno`). -/
def libmRet (ctx : Ctx) (fn : String) (single : Bool) (xs : List Float) (y : Float) (m : Mem) :
    Res (Exit × Mem) := do
  retv (.float y) (← updErrno ctx m fun _ => libmErrno fn single xs y)

/-- The arguments and the result of `fn` (`Model.libm`; `single`: its `float` version) for `args`,
`none` for arguments it does not take. A transcendental function's `float` version is the C
library's `float` function (`sinf`, ...: Lean's `Float32` calls it), not the double function
rounded to `float`; the conversions between a `float` held as a double and `Float32` are exact. -/
def libmResult (fn : String) (single : Bool) (args : List Val) : Option (List Float × Float) :=
  let r : Float → Float := fun f => if single then roundSingle f else f
  let u (d : Float → Float) (s : Float32 → Float32) (x : Float) : Float :=
    if single then (s x.toFloat32).toFloat else d x
  let b (d : Float → Float → Float) (s : Float32 → Float32 → Float32) (x y : Float) : Float :=
    if single then (s x.toFloat32 y.toFloat32).toFloat else d x y
  match fn, args with
  | "sqrt", [.float x] => some ([x], r x.sqrt)
  | "exp", [.float x] => some ([x], u Float.exp Float32.exp x)
  | "log", [.float x] => some ([x], u Float.log Float32.log x)
  | "log2", [.float x] => some ([x], u Float.log2 Float32.log2 x)
  | "log10", [.float x] => some ([x], u Float.log10 Float32.log10 x)
  | "sin", [.float x] => some ([x], u Float.sin Float32.sin x)
  | "cos", [.float x] => some ([x], u Float.cos Float32.cos x)
  | "tan", [.float x] => some ([x], u Float.tan Float32.tan x)
  | "atan", [.float x] => some ([x], u Float.atan Float32.atan x)
  | "asin", [.float x] => some ([x], u Float.asin Float32.asin x)
  | "acos", [.float x] => some ([x], u Float.acos Float32.acos x)
  | "sinh", [.float x] => some ([x], u Float.sinh Float32.sinh x)
  | "cosh", [.float x] => some ([x], u Float.cosh Float32.cosh x)
  | "tanh", [.float x] => some ([x], u Float.tanh Float32.tanh x)
  | "asinh", [.float x] => some ([x], u Float.asinh Float32.asinh x)
  | "acosh", [.float x] => some ([x], u Float.acosh Float32.acosh x)
  | "atanh", [.float x] => some ([x], u Float.atanh Float32.atanh x)
  | "exp2", [.float x] => some ([x], u Float.exp2 Float32.exp2 x)
  | "floor", [.float x] => some ([x], r (roundIntF 0 x))
  | "ceil", [.float x] => some ([x], r (roundIntF 1 x))
  | "trunc", [.float x] => some ([x], r (roundIntF 2 x))
  | "round", [.float x] => some ([x], r (roundIntF 3 x))
  | "fabs", [.float x] => some ([x], r x.abs)
  | "fmod", [.float x, .float y] => some ([x, y], r (fmodF x y))
  | "cbrt", [.float x] => some ([x], u Float.cbrt Float32.cbrt x)
  | "pow", [.float x, .float y] => some ([x, y], b Float.pow Float32.pow x y)
  | "atan2", [.float x, .float y] => some ([x, y], b Float.atan2 Float32.atan2 x y)
  | "fmin", [.float x, .float y] =>
    some ([x, y], if cmpFloat .uno x x then y else if cmpFloat .uno y y then x else if cmpFloat .lt y x then y else x)
  | "fmax", [.float x, .float y] =>
    some ([x, y], if cmpFloat .uno x x then y else if cmpFloat .uno y y then x else if cmpFloat .lt x y then y else x)
  | _, _ => none

/-- The correctly rounded result `r` of `fn` (`Std.CR`) of `x`, with `errno` as glibc's
(`libmRet`); undefined when its rounding is not decided at 2048 bits. -/
def crModel (ctx : Ctx) (fn : String) (x : Float) (r : Option Float) (m : Mem) : Res (Exit × Mem) :=
  match r with
  | some v => libmRet ctx fn false [x] v m
  | none => .ub s!"{fn}: the rounding is not decided at 2048 bits (not modelled)"

/-- Linux's scheduling policies (`<sched.h>`): `SCHED_OTHER` 0, `SCHED_FIFO` 1, `SCHED_RR` 2,
`SCHED_BATCH` 3, `SCHED_IDLE` 5, `SCHED_DEADLINE` 6, `SCHED_EXT` 7 (Linux 6.12; 4 is reserved). -/
def schedPolicy (p : Int) : Bool := p == 0 || p == 1 || p == 2 || p == 3 || p == 5 || p == 6 || p == 7

/-- `sched_get_priority_max(p)` (`max`) or `sched_get_priority_min(p)`: Linux's values, none for a
policy that is not one (here the `SCHED_RESET_ON_FORK` flag makes it none). -/
def schedPriorityOf (max : Bool) (p : Int) : Option Int :=
  if p == 1 || p == 2 then some (if max then 99 else 1)
  else if schedPolicy p then some 0
  else none

/-- The error of `pthread_setschedparam` with policy `p` and priority `prio`, which glibc gets from
Linux's `sched_setscheduler`, or 0: with the `SCHED_RESET_ON_FORK` flag (2^30) set aside, EINVAL (22)
for a policy that is not one, for `SCHED_DEADLINE` (whose parameters a `struct sched_param` does not
hold), for a priority outside 0..99, for 0 with `SCHED_FIFO` and `SCHED_RR` and for another one with
the others; then EPERM (1) for a real-time policy without the privilege (`World.rtPrivileged`).
Linux also asks for it to leave `SCHED_IDLE`, which is not modelled (the policy is not kept). -/
def schedParamError (p prio : Int) : Int :=
  let p := if 0 ≤ p && p / 2 ^ 30 % 2 == 1 then p - 2 ^ 30 else p
  let rt := p == 1 || p == 2
  if !schedPolicy p || p == 6 || prio < 0 || 99 < prio || rt != (prio != 0) then 22
  else if rt && !World.current.rtPrivileged then 1
  else 0

/-- glibc's messages for the error numbers 0 to 133 (x86-64 Linux), "" for the two it has none for
(41, 58): `strerror_r`'s. -/
def glibcErrorTexts : List String := [
  "Success", "Operation not permitted", "No such file or directory", "No such process",
  "Interrupted system call", "Input/output error", "No such device or address",
  "Argument list too long", "Exec format error", "Bad file descriptor", "No child processes",
  "Resource temporarily unavailable", "Cannot allocate memory", "Permission denied", "Bad address",
  "Block device required", "Device or resource busy", "File exists", "Invalid cross-device link",
  "No such device", "Not a directory", "Is a directory", "Invalid argument",
  "Too many open files in system", "Too many open files", "Inappropriate ioctl for device",
  "Text file busy", "File too large", "No space left on device", "Illegal seek",
  "Read-only file system", "Too many links", "Broken pipe", "Numerical argument out of domain",
  "Numerical result out of range", "Resource deadlock avoided", "File name too long",
  "No locks available", "Function not implemented", "Directory not empty",
  "Too many levels of symbolic links", "", "No message of desired type", "Identifier removed",
  "Channel number out of range", "Level 2 not synchronized", "Level 3 halted", "Level 3 reset",
  "Link number out of range", "Protocol driver not attached", "No CSI structure available",
  "Level 2 halted", "Invalid exchange", "Invalid request descriptor", "Exchange full", "No anode",
  "Invalid request code", "Invalid slot", "", "Bad font file format", "Device not a stream",
  "No data available", "Timer expired", "Out of streams resources", "Machine is not on the network",
  "Package not installed", "Object is remote", "Link has been severed", "Advertise error",
  "Srmount error", "Communication error on send", "Protocol error", "Multihop attempted",
  "RFS specific error", "Bad message", "Value too large for defined data type",
  "Name not unique on network", "File descriptor in bad state", "Remote address changed",
  "Can not access a needed shared library", "Accessing a corrupted shared library",
  ".lib section in a.out corrupted", "Attempting to link in too many shared libraries",
  "Cannot exec a shared library directly", "Invalid or incomplete multibyte or wide character",
  "Interrupted system call should be restarted", "Streams pipe error", "Too many users",
  "Socket operation on non-socket", "Destination address required", "Message too long",
  "Protocol wrong type for socket", "Protocol not available", "Protocol not supported",
  "Socket type not supported", "Operation not supported", "Protocol family not supported",
  "Address family not supported by protocol", "Address already in use",
  "Cannot assign requested address", "Network is down", "Network is unreachable",
  "Network dropped connection on reset", "Software caused connection abort",
  "Connection reset by peer", "No buffer space available",
  "Transport endpoint is already connected", "Transport endpoint is not connected",
  "Cannot send after transport endpoint shutdown", "Too many references: cannot splice",
  "Connection timed out", "Connection refused", "Host is down", "No route to host",
  "Operation already in progress", "Operation now in progress", "Stale file handle",
  "Structure needs cleaning", "Not a XENIX named type file", "No XENIX semaphores available",
  "Is a named type file", "Remote I/O error", "Disk quota exceeded", "No medium found",
  "Wrong medium type", "Operation canceled", "Required key not available", "Key has expired",
  "Key has been revoked", "Key was rejected by service", "Owner died", "State not recoverable",
  "Operation not possible due to RF-kill", "Memory page has hardware error"]

/-- glibc's message for the error number `e`, if it has one. -/
def glibcErrorText (e : Int) : Option String :=
  if e < 0 then none
  else match glibcErrorTexts[e.toNat]? with
    | some s => if s.isEmpty then none else some s
    | none => none

/-- The date of the day `z` days after 1970-01-01 in the proleptic Gregorian calendar: the year, the
month (1..12) and the day of the month (1..31) (H. Hinnant's `civil_from_days`). -/
def civilOfDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let mo := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if mo ≤ 2 then 1 else 0), mo.toNat, d.toNat)

/-- `ctime_r`'s text for the local time `s` (seconds since the Epoch), in `asctime`'s form
`"%.3s %.3s%3d %.2d:%.2d:%.2d %d\n"` (C11 7.27.3.1, glibc's `asctime_r`), or the error that glibc
gives: EINVAL (22) for a year that `struct tm` cannot hold (`localtime_r` fails, and `asctime_r` of
a null pointer is EINVAL), EOVERFLOW (75) for one above `INT_MAX` (`asctime_r`'s own check). -/
def ctimeText (s : Int) : Except Int (List Int) :=
  let days := s / 86400
  let sec := (s % 86400).toNat
  let (y, mo, d) := civilOfDays days
  if y - 1900 < -2 ^ 31 || 2 ^ 31 - 1 < y - 1900 then .error 22
  else if 2 ^ 31 - 1 < y then .error 75
  else
    let two (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n
    let wday := ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"].getD ((days + 4) % 7).toNat ""
    let mon := ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov",
      "Dec"].getD (mo - 1) ""
    let mday := (if d < 10 then "  " else " ") ++ toString d
    let hms := two (sec / 3600) ++ ":" ++ two (sec / 60 % 60) ++ ":" ++ two (sec % 60)
    .ok ((wday ++ " " ++ mon ++ mday ++ " " ++ hms ++ " " ++ toString y ++ "\n").toList.map
      fun c => (c.toNat : Int))

/-- `pthread_setschedparam(t, p, sp)` (`Model.pthreadSetschedparam`): `t` must be the thread's
id; the error of policy `p` with `sp->sched_priority` (`schedParamError`), which glibc also
stores in `errno`. -/
def setschedparamModel (ctx : Ctx) (m : Mem) (t p : Int) (sp : Ptr) : Res (Exit × Mem) := do
  if t != World.current.threadId then
    .ub "pthread_setschedparam: not the id of a thread (the only one is pthread_self()'s)" else
  let prio ← ctx.typedLoad m (.int true 32) (← fieldPtr sp 0)
  match prio with
  | .int prio =>
    -- glibc returns the error that `sched_setscheduler` left in `errno`
    let e := schedParamError p prio
    if e == 0 then retv (.int 0) m else retv (.int e) (← setErrno ctx m e)
  | _ => .ub "pthread_setschedparam: the priority is not an int"

/-- `strerror_r(e, buf, n)`, GNU's (`Model.strerrorR`): glibc's message for `e`, or
"Unknown error e" written to `buf` as `snprintf(buf, n, …)` would, and `buf`. -/
def strerrorRModel (ctx : Ctx) (m : Mem) (e : Int) (buf : Ptr) (n : Int) : Res (Exit × Mem) :=
  match glibcErrorText e with
  | some s =>
    -- glibc's own string, in read-only storage; `buf` is not used
    let cs : List Val := s.toList.map fun c => .int c.toNat
    let (b, m) := m.alloc .readonly (.array (.int true 8) (cs.length + 1)) (.arr (cs ++ [.int 0]))
    retv (.ptr (.loc b [.idx 0])) m
  | none => do
    -- `snprintf(buf, n, "Unknown error %d", e)`, and `buf`
    if n ≤ 0 then retv (.ptr buf) m else
    let txt := ("Unknown error " ++ toString e).toList.map fun c => (c.toNat : Int)
    let kept := txt.take (n.toNat - 1)
    let some r := typedRange? ctx m buf (kept.length + 1)
      | .ub "strerror_r: the buffer is not a char range of the length needed"
    match r.2.2.2.2 with
    | .int sg 8 => do
      let vs := (kept ++ [0]).map fun x => Val.int (wrap sg 8 x)
      retv (.ptr buf) (← Res.ofOption "strerror_r: invalid write" (rangeWrite m r vs))
    | _ => .ub "strerror_r: the buffer is not a char range"

/-- `time(t)` (`Model.time`): `World.now`, also stored into `*t` when `t` is not null. -/
def timeModel (ctx : Ctx) (m : Mem) (t : Ptr) : Res (Exit × Mem) := do
  match t with
  | .null => retv (.int World.current.now) m
  | _ => retv (.int World.current.now) (← ctx.typedStore m (.int true 64) t (.int World.current.now))

/-- `ctime_r(t, buf)` (`Model.ctimeR`): `ctimeText` of `*t` at `World.tzOffset` into `buf`, and
`buf`; null with glibc's `errno` when it fails. -/
def ctimeRModel (ctx : Ctx) (m : Mem) (t buf : Ptr) : Res (Exit × Mem) := do
  match ← ctx.typedLoad m (.int true 64) t with
  | .int s =>
    match ctimeText (s + World.current.tzOffset) with
    | .error e => retv (.ptr .null) (← setErrno ctx m e)
    | .ok txt =>
      -- `snprintf(buf, 26, …)`: a longer text is cut, and the result is null (EOVERFLOW)
      let kept := txt.take 25
      let some r := typedRange? ctx m buf (kept.length + 1)
        | .ub "ctime_r: the buffer is not a char range of the length needed"
      match r.2.2.2.2 with
      | .int sg 8 =>
        let vs := (kept ++ [0]).map fun x => Val.int (wrap sg 8 x)
        let m ← Res.ofOption "ctime_r: invalid write" (rangeWrite m r vs)
        if txt.length < 26 then retv (.ptr buf) m else retv (.ptr .null) (← setErrno ctx m 75)
      | _ => .ub "ctime_r: the buffer is not a char range"
  | _ => .ub "ctime_r: the time is not a time_t"

/-- `sscanf(s, fmt, ...)` (`Model.sscanf`): the conversions of the characters of `s` (`scanChars`),
each value stored as a store of the program would be into the object it reaches, and noted for the
live `setjmp` invocations (`storeMarked`); `errno` indeterminate after a floating conversion that
may have overflowed or underflowed. -/
def sscanfModel (ctx : Ctx) (m : Mem) (s f : Ptr) (rest : List Val) : Res (Exit × Mem) := do
  let inp ← readCStr m s
  let fmt ← readCStr m f
  let ints (xs : List Val) : List Int := xs.filterMap fun v => match v with | .int c => some c | _ => none
  match scanChars (fmt.length + 1) (ints inp) (ints fmt) rest false 0 0 with
  | none => .ub "sscanf: format outside the modelled subset, or a value out of the range of its object"
  | some (stores, r) =>
    let m ← stores.foldlM (init := m) fun m (p, v, ty) => do
      -- the object must have exactly the conversion's type (C11 7.21.6.2p10-12:
      -- `%d` an int, `%u`/`%x` an unsigned int, `%hhu` an unsigned char, `%lf` a
      -- double, ...; the signedness counts), and the value is stored as by a
      -- store of the program (`Ctx.typedStore`). The object is the one that store
      -- reaches (`Ctx.reachIn`): through a pointer to a structure, union or array
      -- converted to the conversion's type, the scalar the aggregate starts with
      -- (6.7.2.1p15-16); through a character conversion (`%hhd`, `%hhu`), a byte of
      -- another scalar (6.5p7)
      let ok := match p with
        | .loc b path => match m.blocks b with
          | some blk =>
            ctx.typeAt blk.ty path == some ty ||
              match ctx.reachIn blk ty path with
              | some (.obj path') => ctx.typeAt blk.ty path' == some ty
              | some (.byte _ _ _) => true
              | _ => false
          | none => false
        | _ => false
      unless ok do .ub "sscanf: the object does not have the type of the conversion (C11 7.21.6.2p10)"
      -- noted for the live `setjmp` invocations, as a store of the program is (`storeMarked`)
      storeMarked ctx m ty p v
    -- a floating conversion that may have overflowed or underflowed (an infinity, a zero or a
    -- subnormal: glibc stores `strtod`'s ERANGE): `errno` indeterminate
    let m ← updErrno ctx m fun _ =>
      if stores.any (fun (_, v, ty) => match v with
        | .float x => match fkey (decodeF x) with
          | some k => k.natAbs < (if ty == .float .single then 2 ^ 948 else 2 ^ 52) || 2 ^ 2100 ≤ k.natAbs
          | none => false
        | _ => false) then some none else none
    retv (.int r) m

/-- `strtod(s, end)` (`Model.strtod`; `single`: `strtof`; `atof(s)`, which has no `end`): the
value of the subject sequence, `*end` after it, and ERANGE in `errno` for an overflow or an
underflow (`strtodErange`). `atof` of a value that overflows cannot be represented, which is
undefined (C11 7.22.1p1; glibc gives HUGE_VAL and ERANGE). -/
def strtodModel (ctx : Ctx) (single : Bool) (s : Ptr) (rest : List Val) (m : Mem) : Res (Exit × Mem) := do
  let cs ← readCStr m s
  let ints := cs.filterMap fun v => match v with | .int c => some c | _ => none
  let (f, k) := strtodWith (if single then ratToSingle else ratToFloat) ints
  if rest.isEmpty && !(match decodeF f with | .finite .. => true | _ => false) && strtodErange single ints then
    .ub "atof: the value cannot be represented (C11 7.22.1p1)" else
  let endp : Val := match s with
    | .loc b path => match splitLast path with
      | some (pre, .idx i) => .ptr (.loc b (pre ++ [.idx (i + k)]))
      | _ => .ptr s
    | _ => .ptr s
  let m ← match rest with
    | [] => pure m
    | [e] => storeEnd ctx m e endp
    | _ => .ub "strtod: unexpected arguments"
  -- an overflow or an underflow: ERANGE
  let m ← updErrno ctx m fun _ => if strtodErange single ints then some (some 34) else none
  retv (.float f) m

/-- The end of a printf-family call that met an encoding error (`sprintfBeforeLcError`, after the
text before it is written): the result -1, and `errno` EILSEQ, as wcrtomb stores it (C11
7.29.6.3.3p4). -/
def retEilseq (ctx : Ctx) (m : Mem) : Res (Exit × Mem) := do
  retv (.int (-1)) (← setErrno ctx m 84)

/-- `perror(s)` (`Model.perror`): the message goes to `stderr`, which is not modelled; afterwards
`errno` is indeterminate: C11 7.5p3 lets perror set it to any nonzero value, and glibc's leaves
EINVAL when `stderr` is not open for reading too (its `fdopen` of a duplicate of the descriptor
fails). -/
def perrorModel (ctx : Ctx) (m : Mem) (s : Ptr) : Res (Exit × Mem) := do
  let m ← match s with
    | .null => pure m
    | _ => do
      let _ ← readCStr m s
      pure m
  retVoid (← updErrno ctx m fun _ => some none)

/-- A libevent object that the program only holds a pointer to (`struct evbuffer`,
`struct event_base`, `struct evhttp_connection`, `struct evhttp_uri`: incomplete types in
libevent's headers): a live heap block of type `.other ("libevent." ++ tag)`, the pointer to its
start, and the block's value, the model's state (an evbuffer: its bytes). No member is visible,
so the program cannot read or write it; it only hands the pointer back to the library. -/
def libObj? (m : Mem) (tag : String) : Ptr → Option (Nat × Val)
  | .loc b [] =>
    match m.live? b with
    | some blk =>
      if blk.kind == .heap && blk.ty == .other ("libevent." ++ tag) then some (b, blk.val) else none
    | none => none
  | _ => none

/-- A fresh heap block allocated by a library (`Mem.alloc`; a function of its own, which the
well-formedness automation keeps folded, `WF_allocLib`). -/
def allocLib (m : Mem) (ty : Ty) (v : Val) : Nat × Mem := m.alloc .heap ty v

/-- The characters of a C string and its terminator, as a copy in a `char` array holds them
(libevent's `mm_strdup`, as `strdup`). -/
def cstrVals (cs : List Val) : List Val :=
  (cs ++ [Val.int 0]).map fun v => match v with | Val.int x => Val.int (wrap true 8 x) | v => v

/-- Member `i` of the object `p` points to (another pointer stays as it is, and an access through
it is undefined). -/
def fld : Ptr → Nat → Ptr
  | .loc b path, i => .loc b (path ++ [.idx i])
  | p, _ => p

/-- The pointer held by member `i`, of type `ty`, of the object at `p` (a typed load). -/
def loadPtrAt (ctx : Ctx) (m : Mem) (ty : Ty) (p : Ptr) (i : Nat) : Res Ptr := do
  match ← ctx.typedLoad m ty (fld p i) with
  | .ptr q => pure q
  | _ => .ub "library model: a pointer member is indeterminate"

/-- `evhttp_add_header(headers, key, value)` (libevent 2.1.12 `http.c`): -1 when the key or the
value holds a CR or LF (a folded value too: libevent 2.1.12's library refuses it,
`libev_cases.txt`). Else a `struct evkeyval` (zeroed, as `mm_calloc` makes it) holding heap copies
of both strings goes to the end of the list `headers`, a `struct evkeyvalq` (`TAILQ_HEAD`, which
the program can walk), by `TAILQ_INSERT_TAIL` through typed stores, and the result is 0.
Allocation is assumed to succeed (`World.current`). -/
def evAddHeader (ctx : Ctx) (m : Mem) (h k v : Ptr) : Res (Exit × Mem) := do
  let ks ← readCStr m k
  let vs ← readCStr m v
  let nl (x : Val) : Bool := match x with | .int c => c == 13 || c == 10 | _ => false
  if ks.any nl || vs.any nl then retv (.int (-1)) m
  else if !World.current.alloc then retv (.int (-1)) m
  else
    let isList : Bool := match h with
      | .loc b path => match m.live? b with
        | some blk => ctx.typeAt blk.ty path == some (.record "evkeyvalq")
        | none => false
      | _ => false
    if !isList then .ub "evhttp_add_header: the list is not a live struct evkeyvalq"
    else
      let z ← Res.ofOption "evhttp_add_header: struct evkeyval is not declared"
        (ctx.zeroVal 32 (.record "evkeyval"))
      let e := allocLib m (.record "evkeyval") z
      let kc := cstrVals ks
      let kb := allocLib e.2 (.array (.int true 8) kc.length) (.arr kc)
      let vc := cstrVals vs
      let vb := allocLib kb.2 (.array (.int true 8) vc.length) (.arr vc)
      let ent : Ty := .ptr (.record "evkeyval")
      let str : Ty := .ptr (.int true 8)
      -- TAILQ_INSERT_TAIL(headers, e, next): e's tqe_next is null already
      let last ← loadPtrAt ctx vb.2 (.ptr ent) h 1
      let m ← ctx.typedStore vb.2 (.ptr ent) (.loc e.1 [.idx 0, .idx 1]) (.ptr last)
      let m ← ctx.typedStore m str (.loc e.1 [.idx 1]) (.ptr (.loc kb.1 [.idx 0]))
      let m ← ctx.typedStore m str (.loc e.1 [.idx 2]) (.ptr (.loc vb.1 [.idx 0]))
      let m ← ctx.typedStore m ent last (.ptr (.loc e.1 []))
      let m ← ctx.typedStore m (.ptr ent) (fld h 1) (.ptr (.loc e.1 [.idx 0, .idx 0]))
      retv (.int 0) m

/-- `evbuffer_add(buf, data, n)` (libevent 2.1.12 `buffer.c`): the `n` bytes at `data` appended,
and 0. `data` must be valid also when `n` is 0 (libevent copies with `memcpy(dst, data, n)`, C11
7.1.4p1); the bytes are read as a `char` range (other byte-level reads are not modelled, as for
`memcpy`); -1 when the length would overflow `size_t`. Allocation is assumed to succeed. -/
def evbufferAdd (ctx : Ctx) (m : Mem) (p d : Ptr) (n : Int) : Res (Exit × Mem) :=
  match libObj? m "evbuffer" p with
  | some (b, .arr bs) =>
    if (bs.length : Int) + n > 2 ^ 64 - 1 then retv (.int (-1)) m
    else if !World.current.alloc then retv (.int (-1)) m
    else if n = 0 then
      if validMemArg m false d then retv (.int 0) m
      else .ub "evbuffer_add: invalid data pointer, also with length 0 (C11 7.1.4p1)"
    else
      match typedRange? ctx m d n with
      | some r =>
        match r.2.2.2.2, rangeVals m r with
        | .int _ 8, some xs => do
          let xs := xs.map fun v => match v with | .int x => Val.int (wrap false 8 x) | v => v
          retv (.int 0) (← writeVal m (.loc b []) (.arr (bs ++ xs)))
        | _, _ => .ub "evbuffer_add: the data is not a char range (byte-level access not modelled)"
      | none => .ub "evbuffer_add: the data is not a char range (byte-level access not modelled)"
  | _ => .ub "evbuffer_add: not a live evbuffer"

/-- `*_free(p)` of the libevent object `p` of kind `tag`, when `p` is not null (as
`evhttp_request_free` calls `evbuffer_free` and `evhttp_uri_free`). -/
def freeLibObj (m : Mem) (tag : String) (p : Ptr) : Res Mem :=
  match p with
  | .null => pure m
  | p =>
    match libObj? m tag p with
    | some (b, _) => Res.ofOption s!"{tag}: invalid object" (m.free? b)
    | none => .ub s!"libevent: not a live {tag}"

/-- One step of `evhttp_clear_headers(headers)` (libevent 2.1.12 `http.c`): the first entry, if
any, leaves the list by `TAILQ_REMOVE` (typed stores), then its key, its value and the entry are
freed. -/
def evRemoveFirst (ctx : Ctx) (m : Mem) (h : Ptr) : Res Mem := do
  let ent : Ty := .ptr (.record "evkeyval")
  let str : Ty := .ptr (.int true 8)
  match ← loadPtrAt ctx m ent h 0 with
  | .null => pure m
  | e =>
    let nx ← loadPtrAt ctx m ent (fld e 0) 0
    let pv ← loadPtrAt ctx m (.ptr ent) (fld e 0) 1
    let m ← match nx with
      | .null => ctx.typedStore m (.ptr ent) (fld h 1) (.ptr pv)
      | nx => ctx.typedStore m (.ptr ent) (fld (fld nx 0) 1) (.ptr pv)
    let m ← ctx.typedStore m ent pv (.ptr nx)
    let k ← loadPtrAt ctx m str e 1
    let v ← loadPtrAt ctx m str e 2
    let m := (← freeHeap m k).2
    let m := (← freeHeap m v).2
    pure (← freeHeap m e).2

/-- `evhttp_clear_headers(headers)`, then `mm_free(headers)`: the list emptied, and its head freed.
Each step frees a heap block, so a list ends within `m.next` steps (a cyclic one reaches an entry
already freed, which is undefined). A null list is undefined (libevent reads it). -/
def evFreeHeaders (ctx : Ctx) (m : Mem) (h : Ptr) : Res Mem := do
  match h with
  | .null => .ub "evhttp_request_free: a header list is null"
  | h =>
    let m ← (List.range m.next).foldlM (init := m) fun m _ => evRemoveFirst ctx m h
    pure (← freeHeap m h).2

/-- `struct evhttp_request` has libevent 2.1's layout (`<event2/http_struct.h>`), whose members
the models use by position: 1 `evcon`, 2 `flags`, 3 and 4 the header lists, 5 `remote_host`, 7
`host_cache`, 12 `uri`, 13 `uri_elems`, 17 `response_code_line`, 18 and 21 the buffers. -/
def evreqLayout (ctx : Ctx) : Bool :=
  match ctx.record? "evhttp_request" with
  | some r =>
    let t (i : Nat) : Option Ty := r.members[i]?.map (·.2)
    let str : Option Ty := some (.ptr (.int true 8))
    r.members.length == 29 && t 1 == some (.ptr (.record "evhttp_connection")) &&
      t 2 == some (.int true 32) && t 3 == some (.ptr (.record "evkeyvalq")) &&
      t 4 == some (.ptr (.record "evkeyvalq")) && t 5 == str && t 7 == str && t 12 == str &&
      t 13 == some (.ptr (.record "evhttp_uri")) && t 17 == str &&
      t 18 == some (.ptr (.record "evbuffer")) && t 21 == some (.ptr (.record "evbuffer"))
  | none => false

/-- `evhttp_request_free(req)` (libevent 2.1.12 `http.c`, the freeing not deferred):
`remote_host`, `uri`, `uri_elems`, `response_code_line` and `host_cache` freed when not null, both
header lists emptied and freed (`evFreeHeaders`), both buffers freed when not null, then the
request itself. -/
def evFreeRequest (ctx : Ctx) (m : Mem) (req : Ptr) : Res Mem := do
  let str : Ty := .ptr (.int true 8)
  let hdr : Ty := .ptr (.record "evkeyvalq")
  let buf : Ty := .ptr (.record "evbuffer")
  let m := (← freeHeap m (← loadPtrAt ctx m str req 5)).2
  let m := (← freeHeap m (← loadPtrAt ctx m str req 12)).2
  let m ← freeLibObj m "evhttp_uri" (← loadPtrAt ctx m (.ptr (.record "evhttp_uri")) req 13)
  let m := (← freeHeap m (← loadPtrAt ctx m str req 17)).2
  let m := (← freeHeap m (← loadPtrAt ctx m str req 7)).2
  let m ← evFreeHeaders ctx m (← loadPtrAt ctx m hdr req 3)
  let m ← evFreeHeaders ctx m (← loadPtrAt ctx m hdr req 4)
  let m ← freeLibObj m "evbuffer" (← loadPtrAt ctx m buf req 18)
  let m ← freeLibObj m "evbuffer" (← loadPtrAt ctx m buf req 21)
  pure (← freeHeap m req).2

/-- `evhttp_send_reply(req, code, reason, databuf)` (libevent 2.1.12 `http.c`:
`evhttp_response_code_`, then `evhttp_send`). `req` must be a live heap `struct evhttp_request` of
libevent 2.1's layout (`evreqLayout`), `reason` a C string or null, `databuf` a live evbuffer or
null. The previous response line is freed (the new one, a copy of `reason`, is freed with the
request). Without a connection (`evcon` null) the request is freed at once (`evFreeRequest`), and
`databuf` is left as it is; a request whose freeing is deferred (`EVHTTP_REQ_DEFER_FREE`) is not
modelled. With one (a live `evhttp_connection`), `databuf`'s bytes move into the request's output
buffer, and the request is libevent's from then on: it is sent and freed later, so to the program
it is freed now. -/
def evSendReply (ctx : Ctx) (m : Mem) (req reason buf : Ptr) : Res (Exit × Mem) := do
  let isReq : Bool := match req with
    | .loc b [] => match m.live? b with
      | some blk => blk.kind == .heap && blk.ty == .record "evhttp_request"
      | none => false
    | _ => false
  if !(evreqLayout ctx && isReq) then
    .ub "evhttp_send_reply: not a live heap struct evhttp_request of libevent 2.1's layout"
  else
    match reason with
    | .null => pure ()
    | r => discard (readCStr m r)
    let bufOk : Bool := match buf with
      | .null => true
      | b => (libObj? m "evbuffer" b).isSome
    if !bufOk then .ub "evhttp_send_reply: databuf is not a live evbuffer"
    else
      let str : Ty := .ptr (.int true 8)
      -- evhttp_response_code_: the previous response line freed
      let m := (← freeHeap m (← loadPtrAt ctx m str req 17)).2
      let m ← ctx.typedStore m str (fld req 17) (.ptr .null)
      match ← loadPtrAt ctx m (.ptr (.record "evhttp_connection")) req 1 with
      | .null =>
        match ← ctx.typedLoad m (.int true 32) (fld req 2) with
        | .int f =>
          if (wrap false 32 f).toNat &&& 8 != 0 then
            .ub "evhttp_send_reply: a request whose freeing is deferred (EVHTTP_REQ_DEFER_FREE) is not modelled"
          else retVoid (← evFreeRequest ctx m req)
        | _ => .ub "evhttp_send_reply: the request's flags are indeterminate"
      | evc =>
        if (libObj? m "evhttp_connection" evc).isNone then
          .ub "evhttp_send_reply: the request's connection is not a live evhttp_connection"
        else
          let m ← match buf with
            | .null => pure m
            | b => do
              let ob ← loadPtrAt ctx m (.ptr (.record "evbuffer")) req 21
              match libObj? m "evbuffer" b, libObj? m "evbuffer" ob with
              | some (bb, .arr xs), some (obb, .arr ys) =>
                if bb = obb then pure m
                else do
                  let m ← writeVal m (.loc obb []) (.arr (ys ++ xs))
                  writeVal m (.loc bb []) (.arr [])
              | _, _ => .ub "evhttp_send_reply: the request's output buffer is not a live evbuffer"
          retVoid (← evFreeRequest ctx m req)

/-- The members of `std::vector<bool>` and of its reference proxy whose models differ from
`std::vector<T>`'s (`Model.vecBool`). The proxy is the record `{element pointer, 1}`: a proxy
into a container whose generation changed no longer designates an element, as a reference into
it, and the proxy's members read and write only `bool` elements. -/
def vecBoolModel (ctx : Ctx) (op : VecBoolOp) (args : List Val) (m : Mem) : Res (Exit × Mem) :=
  match op, args with
  | .index, [.ptr this, .int i] => do
    let (g, xs) ← readVec ctx m this
    if 0 ≤ i ∧ i < xs.length then retv (.agg [.ptr (← elemPtr (contPtr ctx m this) g i.toNat), .int 1]) m
    else .ub "std::vector<bool>::operator[] out of range"
  | .checkedIndex, [.ptr this, .int i] => do
    let (g, xs) ← readVec ctx m this
    if 0 ≤ i ∧ i < xs.length then retv (.agg [.ptr (← elemPtr (contPtr ctx m this) g i.toNat), .int 1]) m
    else throwLib m "_ZTISt12out_of_range"
  | .resize, [.ptr this, .int n, .bool x] => do
    let (_, xs) ← readVec ctx m this
    retVoid (← writeVec m this (xs.take n.toNat ++ List.replicate (n.toNat - xs.length) (.bool x)))
  | .get, [.ptr this] => do retv (← loadTy m .bool (← bitRefElem m this)) m
  | .set, [.ptr this, .bool x] => do
    let p ← bitRefElem m this
    let _ ← loadTy m .bool p
    retv (.ptr this) (← writeVal m p (.bool x))
  | .assign, [.ptr this, .ptr other] => do
    let v ← loadTy m .bool (← bitRefElem m other)
    let p ← bitRefElem m this
    let _ ← loadTy m .bool p
    retv (.ptr this) (← writeVal m p v)
  | .flip, [.ptr this] => do
    let p ← bitRefElem m this
    match ← loadTy m .bool p with
    | .bool b => retVoid (← writeVal m p (.bool !b))
    | _ => .ub "std::vector<bool>: the reference does not designate an element"
  | .eq, [.ptr a, .ptr b] => do
    let (_, xs) ← readVec ctx m a
    let (_, ys) ← readVec ctx m b
    retv (.bool ((← xs.mapM boolElem) == (← ys.mapM boolElem))) m
  | _, _ => .ub "library model called with unexpected arguments"

/-- `scanf(fmt, ...)` (`Model.scanf`; `fscanf` on `stdin`, `LibOp.fscanf`): standard input is at
its end, so as `sscanf` on an empty string (only a `%n` stores). -/
def scanfStdin (ctx : Ctx) (m : Mem) (f : Ptr) (rest : List Val) : Res (Exit × Mem) := do
  let fmt ← readCStr m f
  let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
  match scanChars (fmt.length + 1) [] ints rest false 0 0 with
  | none => .ub "scanf: format outside the modelled subset"
  | some (stores, r) =>
    let m ← stores.foldlM (init := m) fun m (p, v, ty) => do
      -- as `sscanf`'s: the object has exactly the conversion's type, a typed store
      let ok := match p with
        | .loc b path => match m.blocks b with
          | some blk => ctx.typeAt blk.ty path == some ty
          | none => false
        | _ => false
      unless ok do .ub "scanf: the object does not have the type of the conversion (C11 7.21.6.2p10)"
      storeMarked ctx m ty p v
    retv (.int r) m

/-- The state of glibc's `drand48` generators (`LibOp.lrand48`, `LibOp.seed48`). -/
structure Drand48 where
  /-- the block that holds `[x, a, c, old]` (`Drand48.val`) -/
  blk : Nat
  x : Nat
  a : Nat
  c : Nat
  /-- the block of `seed48`'s copy of the previous `x`, three `unsigned short`s -/
  old : Nat

/-- The value of the state's block. -/
def Drand48.val (s : Drand48) : Val := .arr [.int s.x, .int s.a, .int s.c, .int s.old]

/-- The `drand48` state and the memory: its two blocks are allocated at the first use (`x` = 0,
`a` = 0x5DEECE66D, `c` = 0xB: glibc's zeroed data once its first call has initialized it), then
found as the registrations of `atexit` are (`handlerRegistry`, from block `b0` on). -/
def drand48State (m : Mem) (b0 : Nat) : Drand48 × Mem :=
  match handlerRegistry "drand48" m b0 with
  | some (b, [.int x, .int a, .int c, .int ob]) => (⟨b, x.toNat, a.toNat, c.toNat, ob.toNat⟩, m)
  | _ =>
    let r1 := m.alloc .global (.array (.int false 16) 3) (.arr [.int 0, .int 0, .int 0])
    let r2 := r1.2.alloc .global (.other "drand48") (.arr [.int 0, .int 0x5DEECE66D, .int 0xB, .int r1.1])
    (⟨r2.1, 0, 0x5DEECE66D, 0xB, r1.1⟩, r2.2)

/-- The models of `LibOp` (`Model.lib`), each documented at its operation; the streams are the
handles of `stdStreams` (`stdin` `Ptr.addr 1`, `stdout` 2, `stderr` 3). -/
def libModel (ctx : Ctx) (op : LibOp) (args : List Val) (m : Mem) : Res (Exit × Mem) :=
  match op, args with
  | .hashMemory, [.ptr p, .int n] =>
    match readBytes? ctx m p n.toNat with
    | some bs => retv (.int (City.hash64 bs.toArray).toNat) m
    | none => .ub ("__hash_memory: bytes past the object, indeterminate or of a pointer (byte-level " ++
        "access not modelled)")
  | .nextPrime, [.int n] =>
    if 0xFFFFFFFFFFFFFFC5 < n then .ub "__next_prime: its overflow_error is not modelled"
    else retv (.int (nextPrime n.toNat)) m
  | .fread, [.ptr p, .int _, .int _, .ptr s] =>
    if s = .addr 1 then
      if validMemArg m true p then retv (.int 0) m
      else .ub "fread: an invalid pointer argument (C11 7.1.4p1)"
    else .ub "fread: only stdin, which is at its end, is modelled"
  | .fputs, [.ptr p, .ptr s] => do
    if s = .addr 2 ∨ s = .addr 3 then
      let _ ← readCStr m p
      retv (.int 1) m
    else .ub "fputs: only stdout and stderr are modelled"
  | .fwrite, [.ptr p, .int size, .int n, .ptr s] =>
    if s = .addr 2 ∨ s = .addr 3 then
      if size * n = 0 then retv (.int 0) m
      else if bytesInObject ctx m p (size * n).toNat then retv (.int n) m
      else .ub "fwrite: bytes past the object (C11 7.21.8.2p2)"
    else .ub "fwrite: only stdout and stderr are modelled"
  | .ffs w, [.int x] => retv (.int (ffsOf w x)) m
  | .ungetc, [.int c, .ptr s] =>
    if s = .addr 1 then
      if c = -1 then retv (.int (-1)) m
      else .ub "ungetc: a character pushed back onto stdin is not modelled"
    else .ub "ungetc: only stdin is modelled"
  | .fscanf, .ptr s :: .ptr f :: rest =>
    if s = .addr 1 then scanfStdin ctx m f rest
    else .ub "fscanf: only stdin, which is at its end, is modelled"
  | .lrand48, [] => do
    let st := drand48State m ctx.mod.globals.length
    let x : Nat := (st.1.a * st.1.x + st.1.c) % 2 ^ 48
    retv (.int (x / 2 ^ 17 : Nat)) (← writeVal st.2 (.loc st.1.blk []) { st.1 with x := x }.val)
  | .seed48, [.ptr p] => do
    let st := drand48State m ctx.mod.globals.length
    let word (k : Nat) : Res Int := do
      let q ← Res.ofOption "seed48: the argument is not an array of three unsigned shorts" (st.2.stride? p k)
      match ← readVal st.2 q with
      | .int v => pure v
      | _ => .ub "seed48: an indeterminate seed"
    let s0 ← word 0
    let s1 ← word 1
    let s2 ← word 2
    let x : Nat := st.1.x
    let m1 ← writeVal st.2 (.loc st.1.old [])
      (.arr [.int (x % 2 ^ 16 : Nat), .int (x / 2 ^ 16 % 2 ^ 16 : Nat), .int (x / 2 ^ 32 : Nat)])
    let x' : Nat := (s2 % 2 ^ 16).toNat * 2 ^ 32 + (s1 % 2 ^ 16).toNat * 2 ^ 16 + (s0 % 2 ^ 16).toNat
    let m2 ← writeVal m1 (.loc st.1.blk []) { st.1 with x := x', a := 0x5DEECE66D, c := 0xB }.val
    retv (.ptr (.loc st.1.old [.idx 0])) m2
  | _, _ => .ub "library model: invalid arguments"

/-- Run a library model. -/
def runModel (ctx : Ctx) (mdl : Model) (args : List Val) (m : Mem) : Res (Exit × Mem) :=
  match mdl, args with
  -- std::vector<T>
  | .vecCtor _, [.ptr this] => do retVoid (← writeVec m this [])
  | .vecCopyCtor _, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    retVoid (← writeVec m this xs)
  | .vecMoveCtor _, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    let m ← writeVec m this xs
    retVoid (← writeVec m other [])
  | .vecInitListCtor e, [.ptr this, .agg [.ptr first, .int n], _] => initListCtor e this first n m
  | .vecInitListCtor e, [.ptr this, .agg [.ptr first, .int n]] => initListCtor e this first n m
  | .vecSizeCtor e, [.ptr this, .int n] => do
    let z ← Res.ofOption "element type cannot be value-initialised" (ctx.zeroVal 32 e)
    retVoid (← writeVec m this (List.replicate n.toNat z))
  | .vecSizeCtor e, [.ptr this, .int n, _] => do
    let z ← Res.ofOption "element type cannot be value-initialised" (ctx.zeroVal 32 e)
    retVoid (← writeVec m this (List.replicate n.toNat z))
  | .vecFillCtor e, [.ptr this, .int n, .ptr x] => do
    let v ← loadTy m e x
    retVoid (← writeVec m this (List.replicate n.toNat v))
  | .vecFillCtor e, [.ptr this, .int n, .ptr x, _] => do
    let v ← loadTy m e x
    retVoid (← writeVec m this (List.replicate n.toNat v))
  | .vecDtor _, [.ptr this] => do
    let _ ← readVec ctx m this
    retVoid (← writeVal m this .undef)
  | .vecCopyAssign _, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    let _ ← readVec ctx m this
    retv (.ptr this) (← writeVec m this xs)
  | .vecMoveAssign _, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    let _ ← readVec ctx m this
    let m ← writeVec m this xs
    retv (.ptr this) (← writeVec m other [])
  | .vecAssignInitList e, [.ptr this, .agg [.ptr first, .int n]] => do
    let xs ← initListVals e first n m
    let _ ← readVec ctx m this
    retv (.ptr this) (← writeVec m this xs)
  | .vecAssignFill e, [.ptr this, .int n, .ptr x] => do
    let v ← loadTy m e x
    let _ ← readVec ctx m this
    -- `x` is no reference into the vector (C++ [sequence.reqmts], `a.assign(n, t)`)
    if intoCont (contPtr ctx m this) x then .ub "std::vector::assign: the value is an element of the vector" else
    retVoid (← writeVec m this (List.replicate n.toNat v))
  | .vecRangeCtor e, .ptr this :: a :: b :: _ => do
    let some p := iterPos? a | .ub "std::vector(first, last): bad iterator argument"
    let some q := iterPos? b | .ub "std::vector(first, last): bad iterator argument"
    let ps ← Res.ofOption "std::vector(first, last): iterator range not within one array" (rangeOf? m p q)
    let xs ← ps.mapM (loadTy m e)
    retVoid (← writeVec m this xs)
  | .vecAssignRange e, [.ptr this, a, b] => do
    let _ ← readVec ctx m this
    let some p := iterPos? a | .ub "std::vector::assign: bad iterator argument"
    let some q := iterPos? b | .ub "std::vector::assign: bad iterator argument"
    -- neither iterator points into the vector (C++ [sequence.reqmts], `a.assign(i, j)`)
    if intoCont (contPtr ctx m this) p || intoCont (contPtr ctx m this) q then
      .ub "std::vector::assign: the range is in the vector" else
    let ps ← Res.ofOption "std::vector::assign: iterator range not within one array" (rangeOf? m p q)
    let xs ← ps.mapM (loadTy m e)
    retVoid (← writeVec m this xs)
  | .vecSize _, [.ptr this] => do
    let (_, xs) ← readVec ctx m this
    retv (← sizeVal xs.length) m
  | .vecEmpty _, [.ptr this] => do
    let (_, xs) ← readVec ctx m this
    retv (.bool xs.isEmpty) m
  | .vecIndex _, [.ptr this, .int i] => do
    let (g, xs) ← readVec ctx m this
    if 0 ≤ i ∧ i < xs.length then retv (.ptr (← elemPtr (contPtr ctx m this) g i.toNat)) m
    else .ub "std::vector::operator[] out of range"
  | .vecAt _, [.ptr this, .int i] => do
    let (g, xs) ← readVec ctx m this
    if 0 ≤ i ∧ i < xs.length then retv (.ptr (← elemPtr (contPtr ctx m this) g i.toNat)) m
    else throwLib m "_ZTISt12out_of_range"
  | .vecFront _, [.ptr this] => do
    let (g, xs) ← readVec ctx m this
    if xs.isEmpty then .ub "front() of empty vector" else retv (.ptr (← elemPtr (contPtr ctx m this) g 0)) m
  | .vecBack _, [.ptr this] => do
    let (g, xs) ← readVec ctx m this
    if xs.isEmpty then .ub "back() of empty vector" else retv (.ptr (← elemPtr (contPtr ctx m this) g (xs.length - 1))) m
  | .vecData _, [.ptr this] => do
    let m ← ensureVec ctx m this
    let (g, _) ← readVec ctx m this
    retv (.ptr (← elemPtr (contPtr ctx m this) g 0)) m
  | .vecBegin _, [.ptr this] => do
    let m ← ensureVec ctx m this
    let (g, _) ← readVec ctx m this
    retv (.agg [.ptr (← elemPtr (contPtr ctx m this) g 0)]) m
  | .vecEnd _, [.ptr this] => do
    let m ← ensureVec ctx m this
    let (g, xs) ← readVec ctx m this
    retv (.agg [.ptr (← elemPtr (contPtr ctx m this) g xs.length)]) m
  | .vecPushBack e, [.ptr this, .ptr x] => do
    let v ← loadTy m e x
    let (_, xs) ← readVec ctx m this
    retVoid (← writeVec m this (xs ++ [v]))
  | .vecEmplaceBack e, [.ptr this, .ptr x] => do
    let v ← loadTy m e x
    let (_, xs) ← readVec ctx m this
    let m ← writeVec m this (xs ++ [v])
    let (g, _) ← readVec ctx m this
    retv (.ptr (← elemPtr (contPtr ctx m this) g xs.length)) m
  | .vecEmplaceOther _, _ => .ub "std::vector::emplace_back: constructor arguments other than one element are not modelled"
  | .vecPopBack _, [.ptr this] => do
    let (_, xs) ← readVec ctx m this
    if xs.isEmpty then .ub "pop_back() of empty vector" else retVoid (← writeVec m this xs.dropLast)
  | .vecClear _, [.ptr this] => do
    let _ ← readVec ctx m this
    retVoid (← writeVec m this [])
  | .vecResize e, [.ptr this, .int n] => do
    let (_, xs) ← readVec ctx m this
    let z ← Res.ofOption "element type cannot be value-initialised" (ctx.zeroVal 32 e)
    retVoid (← writeVec m this (xs.take n.toNat ++ List.replicate (n.toNat - xs.length) z))
  | .vecResize e, [.ptr this, .int n, .ptr x] => do
    let (_, xs) ← readVec ctx m this
    let v ← loadTy m e x
    retVoid (← writeVec m this (xs.take n.toNat ++ List.replicate (n.toNat - xs.length) v))
  | .vecReserve _, [.ptr this, .int _] => do
    let (_, xs) ← readVec ctx m this
    retVoid (← writeVec m this xs)
  | .vecSwap _, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m this
    let (_, ys) ← readVec ctx m other
    let m ← writeVec m this ys
    retVoid (← writeVec m other xs)
  | .vecBool op, xs => vecBoolModel ctx op xs m
  -- contiguous iterators
  | .iterDeref _, [.ptr it] => do
    let p ← readBoxedPtr m it
    match m.read? p with
    | some _ => retv (.ptr p) m
    | none => .ub "dereferencing an invalid iterator"
  | .iterInc _, [.ptr it] => do
    let p ← readBoxedPtr m it
    let q ← Res.ofOption "iterator incremented out of range" (m.stride? p 1)
    retv (.ptr it) (← writeVal m it (.agg [.ptr q]))
  | .iterDec _, [.ptr it] => do
    let p ← readBoxedPtr m it
    let q ← Res.ofOption "iterator decremented out of range" (m.stride? p (-1))
    retv (.ptr it) (← writeVal m it (.agg [.ptr q]))
  | .iterEq _, [.ptr a, .ptr b] => do
    let p ← readBoxedPtr m a
    let q ← readBoxedPtr m b
    if !(validIter m p && validIter m q) then .ub "comparing an invalid iterator" else
    retv (.bool (← Res.ofOption "comparing unrelated iterators" (m.ptrEq? p q))) m
  | .iterNe _, [.ptr a, .ptr b] => do
    let p ← readBoxedPtr m a
    let q ← readBoxedPtr m b
    if !(validIter m p && validIter m q) then .ub "comparing an invalid iterator" else
    retv (.bool !(← Res.ofOption "comparing unrelated iterators" (m.ptrEq? p q))) m
  | .iterLt _, [.ptr a, .ptr b] => do
    let p ← readBoxedPtr m a
    let q ← readBoxedPtr m b
    if !(validIter m p && validIter m q) then .ub "comparing an invalid iterator" else
    retv (.bool (← Res.ofOption "comparing unrelated iterators" (m.ptrLt? p q))) m
  | .iterDiff _, [.ptr a, .ptr b] => do
    let p ← readBoxedPtr m a
    let q ← readBoxedPtr m b
    retv (.int (← Res.ofOption "subtracting unrelated iterators" (m.diff? p q))) m
  | .iterAdd _, [.ptr it, .int n] => do
    let p ← readBoxedPtr m it
    let q ← Res.ofOption "iterator advanced out of range" (m.stride? p n)
    retv (.agg [.ptr q]) m
  | .iterBase _, [.ptr it] => do
    retv (.ptr (← readBoxedPtr m it)) m
  -- std::string
  | .strCtorDefault, [.ptr this] => do retVoid (← writeVec m this [.int 0])
  | .strCtorCStr, [.ptr this, .ptr s] => do
    let cs ← readCStr m s
    retVoid (← writeVec m this (cs ++ [.int 0]))
  | .strCtorCStr, [.ptr this, .ptr s, _] => do
    let cs ← readCStr m s
    retVoid (← writeVec m this (cs ++ [.int 0]))
  | .strCopyCtor, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    retVoid (← writeVec m this xs)
  | .strMoveCtor, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    let m ← writeVec m this xs
    retVoid (← writeVec m other [.int 0])
  | .strDtor, [.ptr this] => do
    let _ ← readVec ctx m this
    retVoid (← writeVal m this .undef)
  | .strSize, [.ptr this] => do
    let (_, xs) ← readVec ctx m this
    let cs ← strChars xs
    retv (← sizeVal cs.length) m
  | .strEmpty, [.ptr this] => do
    let (_, xs) ← readVec ctx m this
    let cs ← strChars xs
    retv (.bool cs.isEmpty) m
  | .strIndex, [.ptr this, .int i] => do
    let (g, xs) ← readVec ctx m this
    let cs ← strChars xs
    if 0 ≤ i ∧ i ≤ cs.length then retv (.ptr (← elemPtr (contPtr ctx m this) g i.toNat)) m
    else .ub "std::string::operator[] out of range"
  | .strAt, [.ptr this, .int i] => do
    let (g, xs) ← readVec ctx m this
    let cs ← strChars xs
    if 0 ≤ i ∧ i < cs.length then retv (.ptr (← elemPtr (contPtr ctx m this) g i.toNat)) m
    else throwLib m "_ZTISt12out_of_range"
  | .strPushBack, [.ptr this, .int c] => do
    let (_, xs) ← readVec ctx m this
    let cs ← strChars xs
    retVoid (← writeVec m this (cs ++ [.int c, .int 0]))
  | .strAppend, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m this
    let (_, ys) ← readVec ctx m other
    let cs ← strChars xs
    let ds ← strChars ys
    retv (.ptr this) (← writeVec m this (cs ++ ds ++ [.int 0]))
  | .strAppendCStr, [.ptr this, .ptr s] => do
    let (_, xs) ← readVec ctx m this
    let cs ← strChars xs
    let ds ← readCStr m s
    retv (.ptr this) (← writeVec m this (cs ++ ds ++ [.int 0]))
  | .strCStr, [.ptr this] => do
    let (g, _) ← readVec ctx m this
    retv (.ptr (← elemPtr (contPtr ctx m this) g 0)) m
  | .strEq, [.ptr a, .ptr b] => do
    let (_, xs) ← readVec ctx m a
    let (_, ys) ← readVec ctx m b
    let cs ← strChars xs
    let ds ← strChars ys
    let eqv := cs.length == ds.length && (cs.zip ds).all fun (x, y) =>
      match x, y with
      | .int i, .int j => i == j
      | _, _ => false
    retv (.bool eqv) m
  | .strBegin, [.ptr this] => do
    let (g, _) ← readVec ctx m this
    retv (.agg [.ptr (← elemPtr (contPtr ctx m this) g 0)]) m
  | .strEnd, [.ptr this] => do
    let (g, xs) ← readVec ctx m this
    let cs ← strChars xs
    retv (.agg [.ptr (← elemPtr (contPtr ctx m this) g cs.length)]) m
  | .strCopyAssign, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    let _ ← readVec ctx m this
    retv (.ptr this) (← writeVec m this xs)
  | .strMoveAssign, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m other
    let _ ← readVec ctx m this
    let m ← writeVec m this xs
    retv (.ptr this) (← writeVec m other [.int 0])
  | .strSwap, [.ptr this, .ptr other] => do
    let (_, xs) ← readVec ctx m this
    let (_, ys) ← readVec ctx m other
    let m ← writeVec m this ys
    retVoid (← writeVec m other xs)
  | .strCtorRange rev, [.ptr this, a, b] => do
    let cs ← rangeArgChars m rev a b
    retVoid (← writeVec m this (cs ++ [.int 0]))
  | .strCtorRange rev, [.ptr this, a, b, _] => do
    let cs ← rangeArgChars m rev a b
    retVoid (← writeVec m this (cs ++ [.int 0]))
  | .strCtorFill, [.ptr this, .int n, .int c] => do
    retVoid (← writeVec m this (List.replicate n.toNat (.int c) ++ [.int 0]))
  | .strCtorFill, [.ptr this, .int n, .int c, _] => do
    retVoid (← writeVec m this (List.replicate n.toNat (.int c) ++ [.int 0]))
  | .strConcat, [_, .agg [.ptr p, .int n], .agg [.ptr q, .int k]] => do
    let cs ← readChars m p n
    let ds ← readChars m q k
    retVec m (cs ++ ds ++ [.int 0])
  | .strConcatCStr, [.ptr s, .ptr other] => do
    let cs ← readCStr m s
    let (_, ys) ← readVec ctx m other
    let ds ← strChars ys
    retVec m (cs ++ ds ++ [.int 0])
  | .strCompareCStr, [.ptr this, .ptr s] => do
    let (_, xs) ← readVec ctx m this
    let cs ← strChars xs
    let ds ← readCStr m s
    retv (.int (← compareChars cs ds)) m
  | .strCompareSub, [.ptr this, .int pos1, .int n1, .ptr s, .int n2] => do
    let (_, xs) ← readVec ctx m this
    let cs ← strChars xs
    if pos1 < 0 ∨ cs.length < pos1 then throwLib m "_ZTISt12out_of_range" else
    retv (.int (← compareSub m cs pos1.toNat n1.toNat s n2)) m
  -- std::optional<T>
  | .optCtorNull _, [.ptr this, _] => do retVoid (← writeVal m this (.opt none))
  | .optCtorNull _, [.ptr this] => do retVoid (← writeVal m this (.opt none))
  | .optCtorValue e, [.ptr this, .ptr x] => do
    let v ← loadTy m e x
    retVoid (← writeVal m this (.opt (some v)))
  | .optCopyCtor _, [.ptr this, .ptr other] => do
    let (_, o) ← optRoot m other
    retVoid (← writeVal m this (.opt o))
  | .optHasValue _, [.ptr this] => do
    let (_, o) ← optRoot m this
    retv (.bool o.isSome) m
  | .optDeref _, [.ptr this] => do
    match ← optRoot m this with
    | (root, some _) => retv (.ptr (← fieldPtr root 0)) m
    | (_, none) => .ub "dereferencing an empty std::optional"
  | .optValue _, [.ptr this] => do
    match ← optRoot m this with
    | (root, some _) => retv (.ptr (← fieldPtr root 0)) m
    | (_, none) => throwLib m "bad_optional_access"
  | .optValueOr e, [.ptr this, .ptr d] => do
    match ← optRoot m this with
    | (_, some v) => retv v m
    | (_, none) => retv (← loadTy m e d) m
  -- std::unique_ptr<T>
  | .uptrCtorNull _, [.ptr this] => do retVoid (← writeVal m this (.agg [.ptr .null]))
  | .uptrCtorNull _, [.ptr this, _] => do retVoid (← writeVal m this (.agg [.ptr .null]))
  | .uptrCtorPtr _, [.ptr this, .ptr p] => do retVoid (← writeVal m this (.agg [.ptr p]))
  | .uptrMoveCtor _, [.ptr this, .ptr other] => do
    let p ← readBoxedPtr m other
    let m ← writeVal m this (.agg [.ptr p])
    retVoid (← writeVal m other (.agg [.ptr .null]))
  | .uptrDtor _, [.ptr this] => do
    let p ← readBoxedPtr m this
    let m ← match p with
      | .null => pure m
      | .loc b [] => Res.ofOption "deleting a pointer not owned by unique_ptr" (m.free? b)
      | _ => .ub "deleting an interior pointer"
    retVoid (← writeVal m this .undef)
  | .uptrGet _, [.ptr this] => do retv (.ptr (← readBoxedPtr m this)) m
  | .uptrDeref _, [.ptr this] => do
    let p ← readBoxedPtr m this
    if p = .null then .ub "dereferencing a null unique_ptr" else retv (.ptr p) m
  | .uptrBool _, [.ptr this] => do
    let p ← readBoxedPtr m this
    retv (.bool (p != .null)) m
  | .uptrRelease _, [.ptr this] => do
    let p ← readBoxedPtr m this
    retv (.ptr p) (← writeVal m this (.agg [.ptr .null]))
  | .uptrReset _, [.ptr this, .ptr q] => do
    let p ← readBoxedPtr m this
    let m ← writeVal m this (.agg [.ptr q])
    match p with
    | .null => retVoid m
    | .loc b [] => retVoid (← Res.ofOption "bad delete in reset" (m.free? b))
    | _ => .ub "deleting an interior pointer"
  -- <algorithm>, <utility>
  | .stdMin ty, [.ptr a, .ptr b] => do
    match ← loadTy m ty a, ← loadTy m ty b with
    | .int x, .int y => retv (.ptr (if y < x then b else a)) m
    | _, _ => .ub "std::min on unsupported type"
  | .stdMax ty, [.ptr a, .ptr b] => do
    match ← loadTy m ty a, ← loadTy m ty b with
    | .int x, .int y => retv (.ptr (if x < y then b else a)) m
    | _, _ => .ub "std::max on unsupported type"
  | .stdSwap ty, [.ptr a, .ptr b] => do
    let x ← loadTy m ty a
    let y ← loadTy m ty b
    let m ← storeTy m ty a y
    retVoid (← storeTy m ty b x)
  | .stdMove _, [.ptr p] => retv (.ptr p) m
  -- runtime
  | .abort, _ => .ub "abort() called"
  | .assertFail, _ => .ub "assertion failure"
  -- `exit` / `_Exit` / `quick_exit`: the program ends with the status
  | .exit, [.int n] => .ok (.halt n, m)
  | .exit, _ => .ub "exit: the status is not an integer"
  | .exitNow quick, [.int n] =>
    let (_, m) := m.alloc .readonly (.other (if quick then "quick_exit" else "_Exit")) .undef
    .ok (.halt n, m)
  | .exitNow _, _ => .ub "exit: the status is not an integer"
  | .libThrow ti, _ => throwLib m ti
  -- single-object `operator new`: a fresh heap block, contents indeterminate
  -- (allocation is assumed to succeed); typed by the first store into it
  | .operatorNew, [.int n] => allocHeap m n false
  | .operatorNew, [.int n, .int _] => allocHeap m n false
  | .operatorDelete, [.ptr p] => freeHeap m p
  | .operatorDelete, [.ptr p, .int _] => freeHeap m p
  | .operatorDelete, [.ptr p, .int _, .int _] => freeHeap m p
  -- C library
  | .malloc, [.int n] => allocHeap m n false
  | .calloc, [.int c, .int sz] => allocHeap m (c * sz) true
  | .free, [.ptr p] => freeHeap m p
  | .strlen, [.ptr s] => do
    let cs ← readCStr m s
    retv (.int cs.length) m
  | .memset, [.ptr d, .int c, .int n] => memsetModel ctx m d c n
  | .memcpy, [.ptr d, .ptr s, .int n] =>
    if memcpyOverlap ctx m d s n then .ub "memcpy: overlapping objects" else memcpyModel ctx m d s n
  | .memmove, [.ptr d, .ptr s, .int n] => memcpyModel ctx m d s n
  | .memcmp, [.ptr a, .ptr b, .int n] => memcmpModel ctx m a b n
  -- the C++ library's own calls: with length 0 its platform's functions touch nothing
  | .memsetStd, [.ptr d, .int c, .int n] => if n = 0 then retv (.ptr d) m else memsetModel ctx m d c n
  | .memcpyStd, [.ptr d, .ptr s, .int n] =>
    if n = 0 then retv (.ptr d) m else
    if memcpyOverlap ctx m d s n then .ub "memcpy: overlapping objects" else memcpyModel ctx m d s n
  | .memmoveStd, [.ptr d, .ptr s, .int n] => if n = 0 then retv (.ptr d) m else memcpyModel ctx m d s n
  | .memcmpStd, [.ptr a, .ptr b, .int n] => if n = 0 then retv (.int 0) m else memcmpModel ctx m a b n
  | .sortLess ty, [.ptr first, .ptr last, _] => do
    let some ps := rangePtrs m first last | .ub "sort: the range is not within one array"
    let vs ← ps.mapM (ctx.typedLoad m ty)
    let sorted ← match ty with
      | .float _ =>
        let fs := vs.filterMap fun v => match v with | .float f => some f | _ => none
        if fs.length != vs.length then .ub "sort: an element is not a floating-point value"
        else if fs.any (fun f => decodeF f == .nan) then
          .ub "sort: a NaN in the range (no strict weak order, C++ [alg.sorting]p3)"
        else if fs.any (·.toBits == 0) && fs.any (·.toBits == 0x8000000000000000) then
          .ub "sort: -0.0 and +0.0 in one range: their order after libc++'s sort is not modelled"
        else pure ((fs.mergeSort fun a b => !cmpFloat .lt b a).map Val.float)
      | _ =>
        let xs := vs.filterMap fun v => match v with | .int x => some x | _ => none
        if xs.length != vs.length then .ub "sort: an element is not an integer"
        else pure ((xs.mergeSort fun a b => decide (a ≤ b)).map Val.int)
    let m ← (ps.zip sorted).foldlM (fun m (p, v) => ctx.typedStore m ty p v) m
    retVoid m
  | .lib op, args => libModel ctx op args m
  | .strncmp, [.ptr a, .ptr b, .int n] => do
    let xs ← arrTail m a
    let ys ← arrTail m b
    retv (.int (← strncmpVals n.toNat xs ys)) m
  | .strcmp, [.ptr a, .ptr b] => do
    let xs ← arrTail m a
    let ys ← arrTail m b
    retv (.int (← strncmpVals (xs.length + 1) xs ys)) m
  | .excNoop, _ => retVoid m
  | .excWhat msg, [.ptr _] =>
    -- the one string per message the frontend adds (`whatSym`), as the libraries return a literal
    match ctx.symAddr? (whatSym msg) [0] with
    | some p => retv (.ptr p) m
    | none =>
      -- a fresh read-only copy
      let cs : List Val := msg.toList.map fun c => .int c.toNat
      let (b, m) := m.alloc .readonly (.array (.int true 8) (cs.length + 1)) (.arr (cs ++ [.int 0]))
      retv (.ptr (.loc b [.idx 0])) m
  | .printf stream, args => do
    -- `fprintf`'s stream must be a valid `FILE *` (C11 7.21.6.1p2, 7.1.4p1): not
    -- null (stdin, stdout and stderr are non-null handles, `stdStreams`)
    let streamOk : Bool := stream == 0 || match args with
      | .ptr (.loc b _) :: _ => (m.live? b).isSome
      | .ptr (.addr _) :: _ => true
      | _ => false
    unless streamOk do .ub "fprintf: the stream is not a valid FILE * (C11 7.1.4p1)"
    let args := args.drop stream
    match args with
    | .ptr f :: rest =>
      let fmt ← readCStr m f
      let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
      match sprintfChars m ints.length ints rest with
      | some out => retv (.int out.length) m
      | none =>
        -- an encoding error (`sprintfBeforeLcError`) makes the result negative (C11 7.21.6.1p14)
        -- and `errno` EILSEQ (`retEilseq`)
        if (sprintfBeforeLcError m ints.length ints rest).isSome then retEilseq ctx m
        else .ub "printf: format outside the modelled subset or not matching the arguments"
    | _ => .ub "printf: no format string"
  -- the buffer then holds no invocation (an earlier one's is replaced): a `longjmp` with it is
  -- undefined
  | .setjmp, .ptr env :: _ =>
    match jmpTokenAt ctx m env 0 with
    | some (q, tv) => do
      retv (.int 0) (← writeVal m q (match tv with | .ptr _ => .ptr .null | _ => .int 0))
    | none => .ub "setjmp: invalid jmp_buf"
  | .setjmp, _ => .ub "setjmp: invalid jmp_buf"
  | .longjmp, args => longjmpModel ctx args m
  | .strtod single, .ptr s :: rest => strtodModel ctx single s rest m
  | .strtol signed c23, [.ptr s, e, .int base] => do
    if base != 0 && (base < 2 || 36 < base) then .ub "strtol: base outside 0 and 2..36"
    else
      let cs ← readCStr m s
      let ints := cs.filterMap fun v => match v with | .int c => some c | _ => none
      let (v, k) := strtolWith c23 base.toNat ints
      -- out of range: the bound in the direction of the sign (C11 7.22.1.4p8);
      -- unsigned: a minus sign negates in the return type (p5), a magnitude
      -- above ULONG_MAX is out of range
      let r : Int :=
        if signed then max (-(2 ^ 63)) (min (2 ^ 63 - 1) v)
        else if v.natAbs ≥ 2 ^ 64 then 2 ^ 64 - 1 else v % 2 ^ 64
      let endp : Val := match s with
        | .loc b path => match splitLast path with
          | some (pre, .idx i) => .ptr (.loc b (pre ++ [.idx (i + k)]))
          | _ => .ptr s
        | _ => .ptr s
      let m ← storeEnd ctx m e endp
      -- out of range: ERANGE (p8)
      let m ← updErrno ctx m fun _ =>
        if (if signed then v < -(2 ^ 63) || 2 ^ 63 - 1 < v else 2 ^ 64 ≤ v.natAbs) then some (some 34)
        else none
      retv (.int r) m
  | .atoi w, [.ptr s] => do
    let cs ← readCStr m s
    let v := atoiVal (cs.filterMap fun v => match v with | .int c => some c | _ => none)
    if inRange true w v then retv (.int v) m
    else .ub "atoi: the value is out of the range of the result type"
  | .realloc, [.ptr .null, .int n] => allocHeap m n false
  | .realloc, [.ptr (.loc b path), .int n] => do
    unless path == [] || path == [.idx 0] do .ub "realloc: not a pointer from the allocator"
    match m.blocks b with
    | some ⟨.heap, true, .array t c, .arr xs⟩ =>
      match ctx.sizeAlign 32 t with
      | some (sz, _) =>
        if sz == 0 || n.toNat % sz != 0 then .ub "realloc: size not a multiple of the element size" else
        let c' := n.toNat / sz
        let vs := xs.take c' ++ List.replicate (c' - c) (ctx.initVal 32 t)
        let (b', m) := m.alloc .heap (.array t c') (.arr vs)
        let m ← Res.ofOption "realloc: invalid block" (m.free? b)
        retv (.ptr (.loc b' (if path == [] then [] else [.idx 0]))) m
      | none => .ub "realloc: element type without a size"
    | some ⟨.heap, true, .array (.other _) _, .undef⟩ => do
      let (_, m) ← (do let r ← freeHeap m (.loc b []); pure r)
      allocHeap m n false
    -- a single object (`malloc(sizeof (T))`, `malloc(1)`: typed `T` by its
    -- first cast): the array of that one element
    | some ⟨.heap, true, t, v⟩ =>
      match t with
      | .array _ _ => .ub "realloc: not a live heap block"
      | _ =>
        if path != [] then .ub "realloc: not a pointer from the allocator" else
        match ctx.sizeAlign 32 t with
        | some (sz, _) =>
          if sz == 0 || n.toNat % sz != 0 then .ub "realloc: size not a multiple of the element size" else
          let c' := n.toNat / sz
          let vs := [v].take c' ++ List.replicate (c' - 1) (ctx.initVal 32 t)
          let (b', m) := m.alloc .heap (.array t c') (.arr vs)
          let m ← Res.ofOption "realloc: invalid block" (m.free? b)
          retv (.ptr (.loc b' [.idx 0])) m
        | none => .ub "realloc: element type without a size"
    | _ => .ub "realloc: not a live heap block"
  | .sprintf, .ptr d :: .ptr f :: rest => do
    let fmt ← readCStr m f
    let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
    match sprintfChars m ints.length ints rest with
    | none =>
      match sprintfBeforeLcError m ints.length ints rest with
      | some pre =>
        -- an encoding error: the characters before it and a terminator are written, as glibc
        -- does, the result is negative (C11 7.21.6.6p3) and `errno` EILSEQ (7.29.6.3.3p4)
        let some r := typedRange? ctx m d (pre.length + 1)
          | .ub "sprintf: destination is not a char range of the length needed"
        if strArgsOverlap ctx m r ((f, none) :: (if ints.contains 115 then sprintfStrArgs ints.length ints rest else [])) then
          .ub "sprintf: overlapping objects" else
        match r.2.2.2.2 with
        | .int sg 8 =>
          let vs := (pre ++ [0]).map fun x => Val.int (wrap sg 8 x)
          retEilseq ctx (← Res.ofOption "sprintf: invalid write" (rangeWrite m r vs))
        | _ => .ub "sprintf: destination is not a char range"
      | none => .ub "sprintf: format outside the modelled subset or not matching the arguments"
    | some out =>
      let n : Int := out.length + 1
      let some r := typedRange? ctx m d n | .ub "sprintf: destination is not a char range of the length needed"
      -- the format string and the `%s` arguments must not overlap the text written
      if strArgsOverlap ctx m r ((f, none) :: (if ints.contains 115 then sprintfStrArgs ints.length ints rest else [])) then
        .ub "sprintf: overlapping objects" else
      match r.2.2.2.2 with
      | .int sg 8 =>
        let vs := (out ++ [0]).map fun x => Val.int (wrap sg 8 x)
        retv (.int out.length) (← Res.ofOption "sprintf: invalid write" (rangeWrite m r vs))
      | _ => .ub "sprintf: destination is not a char range"
  | .snprintf, .ptr d :: .int size :: .ptr f :: rest => do
    let fmt ← readCStr m f
    let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
    match sprintfChars m ints.length ints rest with
    | none =>
      match sprintfBeforeLcError m ints.length ints rest with
      | some pre =>
        -- an encoding error: as `sprintf`, within `size`
        if size ≤ 0 then retEilseq ctx m else
        let kept := pre.take (size.toNat - 1)
        let some r := typedRange? ctx m d (kept.length + 1)
          | .ub "snprintf: destination is not a char range of the length needed"
        if strArgsOverlap ctx m r ((f, none) :: (if ints.contains 115 then sprintfStrArgs ints.length ints rest else [])) then
          .ub "snprintf: overlapping objects" else
        match r.2.2.2.2 with
        | .int sg 8 =>
          let vs := (kept ++ [0]).map fun x => Val.int (wrap sg 8 x)
          retEilseq ctx (← Res.ofOption "snprintf: invalid write" (rangeWrite m r vs))
        | _ => .ub "snprintf: destination is not a char range"
      | none => .ub "snprintf: format outside the modelled subset or not matching the arguments"
    | some out =>
      -- at most `size - 1` characters and the terminator; the result is the full length
      if size ≤ 0 then retv (.int out.length) m else
      let kept := out.take (size.toNat - 1)
      let some r := typedRange? ctx m d (kept.length + 1) | .ub "snprintf: destination is not a char range of the length needed"
      if strArgsOverlap ctx m r ((f, none) :: (if ints.contains 115 then sprintfStrArgs ints.length ints rest else [])) then
        .ub "snprintf: overlapping objects" else
      match r.2.2.2.2 with
      | .int sg 8 =>
        let vs := (kept ++ [0]).map fun x => Val.int (wrap sg 8 x)
        retv (.int out.length) (← Res.ofOption "snprintf: invalid write" (rangeWrite m r vs))
      | _ => .ub "snprintf: destination is not a char range"
  -- the v*printf functions: the arguments `ap` has not given to `va_arg` yet; afterwards its
  -- value is indeterminate
  | .vprintf stream, args => do
    let fname := if stream == 0 then "vprintf" else "vfprintf"
    -- `vfprintf`'s stream must be a valid `FILE *`, as `fprintf`'s (C11 7.21.6.8p2, 7.1.4p1)
    let streamOk : Bool := stream == 0 || match args with
      | .ptr (.loc b _) :: _ => (m.live? b).isSome
      | .ptr (.addr _) :: _ => true
      | _ => false
    unless streamOk do .ub "vfprintf: the stream is not a valid FILE * (C11 7.1.4p1)"
    match args.drop stream with
    | [.ptr f, .ptr ap] =>
      let fmt ← readCStr m f
      let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
      let some rest := vaRemaining m ap
        | .ub (fname ++ ": a va_list not initialized, ended, or indeterminate after another v*printf call (C11 " ++
            (if stream == 0 then "7.21.6.10p2)" else "7.21.6.8p2)"))
      match fmtArgsBad ints rest with
      | some msg => .ub (fname ++ ": " ++ msg)
      | none =>
      match sprintfChars m ints.length ints (rest.map (·.2)) with
      | some out => retv (.int out.length) (← writeVal m ap (vaIndeterminate (← readVal m ap)))
      | none => .ub (fname ++ ": format outside the modelled subset or not matching the arguments")
    | _ => .ub (fname ++ ": no format string and va_list")
  | .vsprintf, [.ptr d, .ptr f, .ptr ap] => do
    let fmt ← readCStr m f
    let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
    let some rest := vaRemaining m ap
      | .ub "vsprintf: a va_list not initialized, ended, or indeterminate after another v*printf call (C11 7.21.6.13p2)"
    match fmtArgsBad ints rest with
    | some msg => .ub ("vsprintf: " ++ msg)
    | none =>
    let args := rest.map (·.2)
    match sprintfChars m ints.length ints args with
    | none => .ub "vsprintf: format outside the modelled subset or not matching the arguments"
    | some out =>
      let n : Int := out.length + 1
      let some r := typedRange? ctx m d n | .ub "vsprintf: destination is not a char range of the length needed"
      if ints.contains 115 && strArgsOverlap ctx m r (sprintfStrArgs ints.length ints args) then
        .ub "vsprintf: overlapping objects" else
      match r.2.2.2.2 with
      | .int sg 8 =>
        let vs := (out ++ [0]).map fun x => Val.int (wrap sg 8 x)
        let m ← Res.ofOption "vsprintf: invalid write" (rangeWrite m r vs)
        retv (.int out.length) (← writeVal m ap (vaIndeterminate (← readVal m ap)))
      | _ => .ub "vsprintf: destination is not a char range"
  | .vsnprintf, [.ptr d, .int size, .ptr f, .ptr ap] => do
    let fmt ← readCStr m f
    let ints := fmt.filterMap fun v => match v with | .int c => some c | _ => none
    let some rest := vaRemaining m ap
      | .ub "vsnprintf: a va_list not initialized, ended, or indeterminate after another v*printf call (C11 7.21.6.12p2)"
    match fmtArgsBad ints rest with
    | some msg => .ub ("vsnprintf: " ++ msg)
    | none =>
    let args := rest.map (·.2)
    match sprintfChars m ints.length ints args with
    | none => .ub "vsnprintf: format outside the modelled subset or not matching the arguments"
    | some out =>
      -- at most `size - 1` characters and the terminator; the result is the full length
      if size ≤ 0 then retv (.int out.length) (← writeVal m ap (vaIndeterminate (← readVal m ap))) else
      let kept := out.take (size.toNat - 1)
      let some r := typedRange? ctx m d (kept.length + 1) | .ub "vsnprintf: destination is not a char range of the length needed"
      if ints.contains 115 && strArgsOverlap ctx m r (sprintfStrArgs ints.length ints args) then
        .ub "vsnprintf: overlapping objects" else
      match r.2.2.2.2 with
      | .int sg 8 =>
        let vs := (kept ++ [0]).map fun x => Val.int (wrap sg 8 x)
        let m ← Res.ofOption "vsnprintf: invalid write" (rangeWrite m r vs)
        retv (.int out.length) (← writeVal m ap (vaIndeterminate (← readVal m ap)))
      | _ => .ub "vsnprintf: destination is not a char range"
  | .sscanf, .ptr s :: .ptr f :: rest => sscanfModel ctx m s f rest
  | .scanf, .ptr f :: rest => scanfStdin ctx m f rest

  | .strcpy, [.ptr d, .ptr s] => do
    let cs ← readCStr m s
    let n : Int := cs.length + 1
    let some r := typedRange? ctx m d n | .ub "strcpy: destination is not a char range of the length needed"
    if (match typedRange? ctx m s n with | some rs => rangesOverlap ctx m rs r | none => false) then
      .ub "strcpy: overlapping objects" else
    match r.2.2.2.2 with
    | .int sg 8 =>
      let vs := (cs ++ [Val.int 0]).map fun v => match v with | Val.int x => Val.int (wrap sg 8 x) | v => v
      retv (.ptr d) (← Res.ofOption "strcpy: invalid write" (rangeWrite m r vs))
    | _ => .ub "strcpy: destination is not a char range"
  | .strncpy, [.ptr d, .ptr s, .int n] => do
    -- valid pointers also for n = 0 (C11 7.24.1p2)
    if n ≤ 0 then
      if validMemArg m true d && validMemArg m false s then retv (.ptr d) m
      else .ub "strncpy: invalid pointer argument, also with length 0 (C11 7.24.1p2)" else
    let cs ← readCStrN m s n.toNat
    let some r := typedRange? ctx m d n | .ub "strncpy: destination is not a char range of the length given"
    let read : Int := if cs.length < n.toNat then cs.length + 1 else cs.length
    if (match typedRange? ctx m s read with | some rs => rangesOverlap ctx m rs r | none => false) then
      .ub "strncpy: overlapping objects" else
    match r.2.2.2.2 with
    | .int sg 8 =>
      let vs := (cs ++ List.replicate (n.toNat - cs.length) (Val.int 0)).map fun v => match v with
        | Val.int x => Val.int (wrap sg 8 x)
        | v => v
      retv (.ptr d) (← Res.ofOption "strncpy: invalid write" (rangeWrite m r vs))
    | _ => .ub "strncpy: destination is not a char range"
  | .strcat, [.ptr d, .ptr s] => do
    let ds ← readCStr m d
    let cs ← readCStr m s
    -- from the terminator of the string at `d`
    let some e := m.stride? d ds.length | .ub "strcat: invalid destination"
    let n : Int := cs.length + 1
    let some r := typedRange? ctx m e n | .ub "strcat: destination is not a char range of the length needed"
    if (match typedRange? ctx m s n, typedRange? ctx m d (ds.length + n) with
        | some rs, some rd => rangesOverlap ctx m rs rd
        | _, _ => false) then
      .ub "strcat: overlapping objects" else
    match r.2.2.2.2 with
    | .int sg 8 =>
      let vs := (cs ++ [Val.int 0]).map fun v => match v with | Val.int x => Val.int (wrap sg 8 x) | v => v
      retv (.ptr d) (← Res.ofOption "strcat: invalid write" (rangeWrite m r vs))
    | _ => .ub "strcat: destination is not a char range"
  | .strchr, [.ptr s, .int c] => do
    -- a pointer to an array object: its element 0
    let s := (arrayObjStart? m s).getD s
    let cs ← readCStr m s
    -- bytes compared as `unsigned char` (the array may hold signed chars)
    let byte (v : Val) : Int := match v with | .int x => wrap false 8 x | _ => -1
    let k? := if wrap false 8 c = 0 then some cs.length else (cs.map byte).findIdx? (· == wrap false 8 c)
    match k? with
    | none => retv (.ptr .null) m
    | some k => match s with
      | .loc b path => match splitLast path with
        | some (pre, .idx i) => retv (.ptr (.loc b (pre ++ [.idx (i + k)]))) m
        | _ => .ub "strchr: the string pointer is not an array element pointer"
      | _ => .ub "strchr: the string pointer is not an array element pointer"
  | .strrchr, [.ptr s, .int c] => do
    let s := (arrayObjStart? m s).getD s
    let cs ← readCStr m s
    let byte (v : Val) : Int := match v with | .int x => wrap false 8 x | _ => -1
    -- the last character equal to `c` (C11 7.24.5.5), the terminator for 0
    let k? := if wrap false 8 c = 0 then some cs.length
      else ((cs.map byte).zipIdx.filter (·.1 == wrap false 8 c)).getLast?.map (·.2)
    match k? with
    | none => retv (.ptr .null) m
    | some k => match s with
      | .loc b path => match splitLast path with
        | some (pre, .idx i) => retv (.ptr (.loc b (pre ++ [.idx (i + k)]))) m
        | _ => .ub "strrchr: the string pointer is not an array element pointer"
      | _ => .ub "strrchr: the string pointer is not an array element pointer"
  | .localeconv, [] =>
    match ctx.record? "lconv" with
    | some r =>
      -- one string block ".": `decimal_point` is its element 0, every
      -- empty string its terminator (element 1)
      let (sb, m) := m.alloc .readonly (.array (.int true 8) 2) (.arr [.int 46, .int 0])
      let (lb, m) := m.alloc .readonly (.record "lconv") (lconvVal ctx r sb)
      retv (.ptr (.loc lb [])) m
    | none => .ub "localeconv: struct lconv is not declared"
  | .strdup, [.ptr s] => do
    let cs ← readCStr m s
    let vs := (cs ++ [Val.int 0]).map fun v => match v with | Val.int x => Val.int (wrap true 8 x) | v => v
    let (b, m) := m.alloc .heap (.array (.int true 8) vs.length) (.arr vs)
    retv (.ptr (.loc b [.idx 0])) m
  | .getchar, [] => retv (.int (-1)) m
  | .fflush, [.ptr p] =>
    -- a null pointer flushes every output stream, `stdout` and `stderr` have nothing pending
    -- (output is not modelled): 0; `stdin` is an input stream (C11 7.21.5.2p2) and any other
    -- pointer designates no stream (7.1.4p1): undefined (the handles are `stdStreams`')
    match p with
    | .null | .addr 2 | .addr 3 => retv (.int 0) m
    | .addr 1 => .ub "fflush of an input stream (C11 7.21.5.2p2)"
    | _ => .ub "fflush: the argument is not a stream (C11 7.1.4p1)"
  | .perror, [.ptr s] => perrorModel ctx m s
  | .signal, [.int sig, .ptr f] => signalModel ctx m sig f
  | .memchr, [.ptr s, .int c, .int n] => memchrModel ctx m s c n
  -- `errno` as after the other `<math.h>` functions (`libmRet`)
  | .hypot single, [.float x, .float y] =>
    libmRet ctx "hypot" single [x, y] (if single then hypotfF x y else hypotF x y) m
  | .expm1, [.float x] => libmRet ctx "expm1" false [x] (expm1F x) m
  | .log1p, [.float x] => libmRet ctx "log1p" false [x] (log1pF x) m
  | .erf, [.float x] => crModel ctx "erf" x (CR.erfCR x) m
  | .erfc, [.float x] => crModel ctx "erfc" x (CR.erfcCR x) m
  | .tgamma, [.float x] => crModel ctx "tgamma" x (CR.tgammaCR x) m
  -- glibc's lgamma also stores the sign of `Γ(x)` in `signgam` (POSIX), which a module that names
  -- it has as a global (`Frontend.libcGlobals`)
  | .lgamma, [.float x] =>
    match CR.lgammaCR x, ctx.gaddr "signgam" with
    | some v, some b => do libmRet ctx "lgamma" false [x] v (← writeVal m (.loc b []) (.int (CR.lgammaSign x)))
    | r, _ => crModel ctx "lgamma" x r m
  -- the default rounding mode, to nearest, half to even (C11 7.12.9.3-5)
  | .rint single, [.float x] => retv (.float (if single then roundSingle (roundIntF 4 x) else roundIntF 4 x)) m
  | .lrint fn, [.float x] => lrintModel fn x m
  | .posixMemalign, [.ptr mp, .int a, .int size] => posixMemalignModel ctx m mp a size
  | .pureVirtual, _ => .ub "pure virtual call"
  | .rand false, [] => do
    let (b, st, f, r) ← randBlock ctx m
    let (x, st, f, r) := randStep st f r
    retv (.int x) (← writeVal m (.loc b []) (randVal st f r))
  | .rand true, [.int s] => do
    let (b, _, _, _) ← randBlock ctx m
    let (st, f, r) := randSeed s.toNat
    retVoid (← writeVal m (.loc b []) (randVal st f r))
  | .atexit cxa, .ptr (.fn f) :: rest => do
    -- appended to the registrations' block (`handlerRegistry`), which only the exit sequence
    -- reads, taking the last one each time (`popHandler`)
    let entry : Val := .agg (.ptr (.fn f) :: (if cxa then rest.take 1 else []))
    match handlerRegistry "atexit" m ctx.mod.globals.length with
    | some (b, es) => retv (.int 0) (← writeVal m (.loc b []) (.arr (es ++ [entry])))
    | none =>
      let (_, m) := m.alloc .global (.other "atexit") (.arr [entry])
      retv (.int 0) m
  | .atQuickExit, [.ptr (.fn f)] => do
    -- the same for `quick_exit`, which runs them (C11 7.22.4.3, 7.22.4.7)
    let entry : Val := .agg [.ptr (.fn f)]
    match handlerRegistry "at_quick_exit" m ctx.mod.globals.length with
    | some (b, es) => retv (.int 0) (← writeVal m (.loc b []) (.arr (es ++ [entry])))
    | none =>
      let (_, m) := m.alloc .global (.other "at_quick_exit") (.arr [entry])
      retv (.int 0) m
  | .guardAcquire, [.ptr g] => do
    match ← readVal m g with
    | .int 0 => retv (.int 1) m
    | .int _ => retv (.int 0) m
    | _ => .ub "__cxa_guard_acquire: not a guard variable"
  | .guardRelease, [.ptr g] => do retVoid (← storeGuard ctx m g 1 "__cxa_guard_release")
  | .guardAbort, [.ptr g] => do retVoid (← storeGuard ctx m g 0 "__cxa_guard_abort")
  | .puts, [.ptr s] => do
    let cs ← readCStr m s
    retv (.int (cs.length + 1)) m
  | .putchar, [.int c] => retv (.int (wrap false 8 c)) m
  | .ctypeTable which, [] =>
    let ety : Ty := if which == 0 then .int false 16 else .int true 32
    let entries := (List.range 384).map fun (i : Nat) => Val.int (ctypeEntry which (Int.ofNat i - 128))
    let (tb, m) := m.alloc .readonly (.array ety 384) (.arr entries)
    let (pb, m) := m.alloc .readonly (.ptr ety) (.ptr (.loc tb [.idx 128]))
    retv (.ptr (.loc pb [])) m
  | .ctype fn, [.int c] =>
    if c < -1 || 255 < c then .ub s!"{fn}: argument out of the range of unsigned char"
    else
      let up := 65 ≤ c && c ≤ 90
      let lo := 97 ≤ c && c ≤ 122
      let dig := 48 ≤ c && c ≤ 57
      let sp := c == 32 || (9 ≤ c && c ≤ 13)
      let prt := 32 ≤ c && c ≤ 126
      let b2i (b : Bool) : Int := if b then 1 else 0
      match fn with
      | "isdigit" => retv (.int (b2i dig)) m
      | "isalpha" => retv (.int (b2i (up || lo))) m
      | "isalnum" => retv (.int (b2i (up || lo || dig))) m
      | "isspace" => retv (.int (b2i sp)) m
      | "isupper" => retv (.int (b2i up)) m
      | "islower" => retv (.int (b2i lo)) m
      | "isxdigit" => retv (.int (b2i (dig || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)))) m
      | "ispunct" => retv (.int (b2i (prt && c != 32 && !(up || lo || dig)))) m
      | "isprint" => retv (.int (b2i prt)) m
      | "toupper" => retv (.int (if lo then c - 32 else c)) m
      | "tolower" => retv (.int (if up then c + 32 else c)) m
      | _ => .ub s!"unsupported ctype function {fn}"
  | .ostreamOut chk, .ptr os :: rest => do
    -- the stream is an object (a null `std::ostream &` is undefined)
    unless (match os with | .loc b _ => (m.live? b).isSome | _ => false) do
      .ub "operator<<: the stream is not an object"
    match chk, rest with
    | 1, [.ptr s] => let _ ← readCStr m s
    | 2, [.ptr s] => let _ ← readVec ctx m s
    | _, _ => pure ()
    retv (.ptr os) m
  | .libm fn single, args =>
    match libmResult fn single args with
    | some (xs, y) => libmRet ctx fn single xs y m
    | none => .ub s!"unsupported arguments for {fn}"
  | .mulc3 single, [.float a, .float b, .float c, .float d] =>
    let (x, y) := mulc3 single a b c d
    retv (.arr [.float x, .float y]) m
  | .divc3 single, [.float a, .float b, .float c, .float d] =>
    let (x, y) := if single then divsc3 a b c d else divdc3 a b c d
    retv (.arr [.float x, .float y]) m
  -- libevent 2.1 and POSIX threads (`World.current`: allocation succeeds, thread id 1)
  | .evbufferNew, [] =>
    if World.current.alloc then
      let b := allocLib m (.other "libevent.evbuffer") (.arr [])
      retv (.ptr (.loc b.1 [])) b.2
    else retv (.ptr .null) m
  | .evbufferFree, [.ptr p] =>
    match libObj? m "evbuffer" p with
    | some (b, _) => do retVoid (← Res.ofOption "evbuffer_free: invalid buffer" (m.free? b))
    | none => .ub "evbuffer_free: not a live evbuffer"
  | .evbufferAdd, [.ptr p, .ptr d, .int n] => evbufferAdd ctx m p d n
  | .evbufferLength, [.ptr p] =>
    match libObj? m "evbuffer" p with
    | some (_, .arr bs) => retv (.int bs.length) m
    | _ => .ub "evbuffer_get_length: not a live evbuffer"
  | .evhttpAddHeader, [.ptr h, .ptr k, .ptr v] => evAddHeader ctx m h k v
  | .evhttpSendReply, [.ptr req, .int _, .ptr reason, .ptr buf] => evSendReply ctx m req reason buf
  | .eventBaseLoopbreak, [.ptr .null] => retv (.int (-1)) m
  | .eventBaseLoopbreak, [.ptr p] =>
    if (libObj? m "event_base" p).isSome then retv (.int 0) m
    else .ub "event_base_loopbreak: not a live event_base"
  | .pthreadSelf, [] => retv (.int World.current.threadId) m
  | .pthreadEqual, [.int a, .int b] => retv (.int (if a = b then 1 else 0)) m
  | .pthreadSetschedparam, [.int t, .int p, .ptr sp] => setschedparamModel ctx m t p sp
  | .schedPriority max, [.int p] =>
    match schedPriorityOf max p with
    | some v => retv (.int v) m
    | none => do retv (.int (-1)) (← setErrno ctx m 22)
  | .errnoLocation, [] =>
    match ctx.gaddr errnoSym with
    | some b => retv (.ptr (.loc b [])) m
    | none => .ub "__errno_location: the module has no errno object"
  | .strerrorR, [.int e, .ptr buf, .int n] => strerrorRModel ctx m e buf n
  | .time, [.ptr t] => timeModel ctx m t
  | .ctimeR, [.ptr t, .ptr buf] => ctimeRModel ctx m t buf
  | _, _ => .ub "library model called with unexpected arguments"

end CIR.Std
