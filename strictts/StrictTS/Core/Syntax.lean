/-
StrictTS core: the intrinsically typed IR.

`Expr TT Γ t` is an expression of type `t` in variable context `Γ`; only well-typed terms
exist, so evaluation never meets a type error. Statements are indexed by the return type
`ρ` of the enclosing function body. Blocks carry their declarations in continuation style,
which gives block scoping for free.
-/
import StrictTS.Core.Ty

namespace StrictTS

/-- Literal constants. -/
inductive Lit : Ty → Type where
  | num : F64 → Lit .num
  | bigint : Int → Lit .bigint
  | bool : Bool → Lit .bool
  | str : JSStr → Lit .str
  | undef : Lit .undef
  | null : Lit .null

/-- Binary `number` operators and binary `Math` functions. `pow`, `atan2` and `hypot` are
implementation-approximated in ECMA-262 and come from the `Impl` parameter. -/
inductive NumBin where
  | add | sub | mul | div | rem | pow
  | band | bor | bxor | shl | sar | shr
  | min | max | imul | atan2 | hypot
  deriving DecidableEq, Repr

/-- Unary `number` operators and unary `Math` functions (the transcendental ones come from `Impl`). -/
inductive NumUn where
  | neg | bnot | abs | floor | ceil | trunc | round | sign | sqrt | fround | clz32
  | cbrt | exp | expm1 | log | log1p | log2 | log10
  | sin | cos | tan | asin | acos | atan | sinh | cosh | tanh | asinh | acosh | atanh
  deriving DecidableEq, Repr

/-- Relational operators (`===` is `eq`; `!==` is `not ∘ eq`). -/
inductive Cmp where
  | lt | le | gt | ge | eq
  deriving DecidableEq, Repr

inductive NumPred where
  | isInteger | isSafeInteger | isFinite | isNaN
  deriving DecidableEq, Repr

inductive BigBin where
  | add | sub | mul | div | rem | pow | band | bor | bxor | shl | sar
  deriving DecidableEq, Repr

inductive ErrKind where
  | error | typeError | rangeError | syntaxError | referenceError
  deriving DecidableEq, Repr

/-- Pure primitive operations. Each takes exactly its declared argument types: there are no
implicit conversions (`+` on strings is `strConcat`, on numbers `numBin .add`). -/
inductive PrimOp : List Ty → Ty → Type where
  | numBin (op : NumBin) : PrimOp [.num, .num] .num
  | numUn (op : NumUn) : PrimOp [.num] .num
  | numCmp (op : Cmp) : PrimOp [.num, .num] .bool
  | numPred (op : NumPred) : PrimOp [.num] .bool
  | bigBin (op : BigBin) : PrimOp [.bigint, .bigint] .bigint
  | bigNeg : PrimOp [.bigint] .bigint
  | bigNot : PrimOp [.bigint] .bigint
  | bigCmp (op : Cmp) : PrimOp [.bigint, .bigint] .bool
  | bigAsIntN : PrimOp [.num, .bigint] .bigint
  | bigAsUintN : PrimOp [.num, .bigint] .bigint
  | bigOfNum : PrimOp [.num] .bigint
  | numOfBig : PrimOp [.bigint] .num
  | not : PrimOp [.bool] .bool
  | seq (t : Ty) (h : t.eqable = true) : PrimOp [t, t] .bool
  | strCmp (op : Cmp) : PrimOp [.str, .str] .bool
  | strConcat : PrimOp [.str, .str] .str
  | numToStr : PrimOp [.num] .str
  | numToStrRadix : PrimOp [.num, .num] .str
  | bigToStr : PrimOp [.bigint] .str
  | boolToStr : PrimOp [.bool] .str
  | enumToStr (cs : List String) : PrimOp [.enum cs] .str
  | strToNum : PrimOp [.str] .num
  | strToBig : PrimOp [.str] .bigint
  | parseFloat : PrimOp [.str] .num
  | parseInt : PrimOp [.str, .num] .num
  | toFixed : PrimOp [.num, .num] .str
  | toPrecision : PrimOp [.num, .num] .str
  | toExponential : PrimOp [.num, .opt .num] .str
  | strLength : PrimOp [.str] .num
  | charCodeAt : PrimOp [.str, .num] .num
  | codePointAt : PrimOp [.str, .num] (.opt .num)
  | charAt : PrimOp [.str, .num] .str
  | strAt : PrimOp [.str, .num] (.opt .str)
  | strSlice : PrimOp [.str, .num, .opt .num] .str
  | substring : PrimOp [.str, .num, .opt .num] .str
  | indexOf : PrimOp [.str, .str, .num] .num
  | lastIndexOf : PrimOp [.str, .str, .num] .num
  | strIncludes : PrimOp [.str, .str, .num] .bool
  | startsWith : PrimOp [.str, .str, .num] .bool
  | endsWith : PrimOp [.str, .str, .opt .num] .bool
  | trim : PrimOp [.str] .str
  | trimStart : PrimOp [.str] .str
  | trimEnd : PrimOp [.str] .str
  | padStart : PrimOp [.str, .num, .str] .str
  | padEnd : PrimOp [.str, .num, .str] .str
  | strRepeat : PrimOp [.str, .num] .str
  | replace : PrimOp [.str, .str, .str] .str
  | replaceAll : PrimOp [.str, .str, .str] .str
  | toUpper : PrimOp [.str] .str
  | toLower : PrimOp [.str] .str
  | fromCharCode : PrimOp [.num] .str
  | localeCompare : PrimOp [.str, .str] .num
  | errNew (k : ErrKind) : PrimOp [.str] .err
  | errMessage : PrimOp [.err] .str
  | errName : PrimOp [.err] .str
  -- values of type `unknown` (`dyn`), see StrictTS/Lib/Dyn.lean
  /-- a value as `unknown` (with its type) -/
  | toDyn (t : Ty) : PrimOp [t] .dyn
  /-- `typeof x` -/
  | dynTypeof : PrimOp [.dyn] .str
  /-- `Array.isArray(x)` -/
  | dynIsArray : PrimOp [.dyn] .bool
  /-- ToBoolean (truthiness) -/
  | dynTruthy : PrimOp [.dyn] .bool
  /-- the value at type `t` if it is one (`none` otherwise): checked casts and narrowing -/
  | dynCast (t : Ty) : PrimOp [.dyn] (.opt t)
  /-- `x === y` -/
  | dynEq : PrimOp [.dyn, .dyn] .bool

/-- Element type of a typed array as seen from TypeScript. -/
def TAKind.elem : TAKind → Ty
  | .bi64 | .bu64 => .bigint
  | _ => .num

/-- Effectful library operations: they read or write the heap, call callbacks, print, or
touch the job queue. Callbacks always receive every argument JavaScript passes (the
translator eta-expands shorter TypeScript callbacks). -/
inductive Builtin : List Ty → Ty → Type where
  -- arrays
  | arrOf (t : Ty) (n : Nat) : Builtin (List.replicate n t) (.arr t)
  | arrLength (t : Ty) : Builtin [.arr t] .num
  | arrGet (t : Ty) : Builtin [.arr t, .num] t
  | arrGetOpt (t : Ty) : Builtin [.arr t, .num] (.opt t)
  | arrAt (t : Ty) : Builtin [.arr t, .num] (.opt t)
  | arrSet (t : Ty) : Builtin [.arr t, .num, t] .undef
  | arrSetLength (t : Ty) : Builtin [.arr t, .num] .undef
  | arrPush (t : Ty) : Builtin [.arr t, t] .num
  | arrPop (t : Ty) : Builtin [.arr t] (.opt t)
  | arrShift (t : Ty) : Builtin [.arr t] (.opt t)
  | arrUnshift (t : Ty) : Builtin [.arr t, t] .num
  | arrSlice (t : Ty) : Builtin [.arr t, .num, .opt .num] (.arr t)
  | arrSplice (t : Ty) : Builtin [.arr t, .num, .num, .arr t] (.arr t)
  | arrConcat (t : Ty) : Builtin [.arr t, .arr t] (.arr t)
  | arrCopy (t : Ty) : Builtin [.arr t] (.arr t)
  | arrIndexOf (t : Ty) : Builtin [.arr t, t, .num] .num
  | arrLastIndexOf (t : Ty) : Builtin [.arr t, t, .num] .num
  | arrIncludes (t : Ty) : Builtin [.arr t, t] .bool
  | arrJoin : Builtin [.arr .str, .str] .str
  | arrReverse (t : Ty) : Builtin [.arr t] (.arr t)
  | arrFill (t : Ty) : Builtin [.arr t, t, .num, .opt .num] (.arr t)
  | arrMakeFill (t : Ty) : Builtin [.num, t] (.arr t)
  | arrSort (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons t .nil)) .num] (.arr t)
  | arrSortStr : Builtin [.arr .str] (.arr .str)
  | arrMap (t u : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) u] (.arr u)
  | arrFilter (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] (.arr t)
  | arrForEach (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .undef] .undef
  | arrFind (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] (.opt t)
  | arrFindIndex (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] .num
  | arrFindLast (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] (.opt t)
  | arrFindLastIndex (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] .num
  | arrSome (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] .bool
  | arrEvery (t : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool] .bool
  | arrFlatMap (t u : Ty) : Builtin [.arr t, .fn (.cons t (.cons .num (.cons (.arr t) .nil))) (.arr u)] (.arr u)
  | arrReduce (t u : Ty) :
      Builtin [.arr t, .fn (.cons u (.cons t (.cons .num (.cons (.arr t) .nil)))) u, u] u
  | arrReduce1 (t : Ty) :
      Builtin [.arr t, .fn (.cons t (.cons t (.cons .num (.cons (.arr t) .nil)))) t] t
  | arrReduceRight (t u : Ty) :
      Builtin [.arr t, .fn (.cons u (.cons t (.cons .num (.cons (.arr t) .nil)))) u, u] u
  | arrFromFn (t : Ty) : Builtin [.num, .fn (.cons .undef (.cons .num .nil)) t] (.arr t)
  -- typed arrays
  | taNew (k : TAKind) : Builtin [.num] (.tarr k)
  | taOfArr (k : TAKind) : Builtin [.arr k.elem] (.tarr k)
  | taLength (k : TAKind) : Builtin [.tarr k] .num
  | taGet (k : TAKind) : Builtin [.tarr k, .num] k.elem
  | taSet (k : TAKind) : Builtin [.tarr k, .num, k.elem] .undef
  | taFill (k : TAKind) : Builtin [.tarr k, k.elem] (.tarr k)
  | taSlice (k : TAKind) : Builtin [.tarr k, .num, .opt .num] (.tarr k)
  -- maps (SameValueZero keys, insertion order)
  | mapNew (k v : Ty) : Builtin [] (.map k v)
  | mapOfEntries (k v : Ty) : Builtin [.arr (.tup (.cons k (.cons v .nil)))] (.map k v)
  | mapGet (k v : Ty) : Builtin [.map k v, k] (.opt v)
  | mapSet (k v : Ty) : Builtin [.map k v, k, v] (.map k v)
  | mapHas (k v : Ty) : Builtin [.map k v, k] .bool
  | mapDelete (k v : Ty) : Builtin [.map k v, k] .bool
  | mapSize (k v : Ty) : Builtin [.map k v] .num
  | mapClear (k v : Ty) : Builtin [.map k v] .undef
  | mapKeys (k v : Ty) : Builtin [.map k v] (.arr k)
  | mapValues (k v : Ty) : Builtin [.map k v] (.arr v)
  | mapEntries (k v : Ty) : Builtin [.map k v] (.arr (.tup (.cons k (.cons v .nil))))
  | mapForEach (k v : Ty) : Builtin [.map k v, .fn (.cons v (.cons k (.cons (.map k v) .nil))) .undef] .undef
  -- objects used as dictionaries (own string keys; see `Dict` in Sem.lean)
  | dictNew (t : Ty) : Builtin [] (.dict t)
  | dictGet (t : Ty) : Builtin [.dict t, .str] (.opt t)
  | dictSet (t : Ty) : Builtin [.dict t, .str, t] .undef
  | dictHas (t : Ty) : Builtin [.dict t, .str] .bool
  | dictHasOwn (t : Ty) : Builtin [.dict t, .str] .bool
  | dictDelete (t : Ty) : Builtin [.dict t, .str] .bool
  | dictKeys (t : Ty) : Builtin [.dict t] (.arr .str)
  | dictValues (t : Ty) : Builtin [.dict t] (.arr t)
  | dictEntries (t : Ty) : Builtin [.dict t] (.arr (.tup (.cons .str (.cons t .nil))))
  -- values of type `unknown` that need the heap (see StrictTS/Lib/Dyn.lean)
  /-- the property read `x[k]` -/
  | dynGet : Builtin [.dyn, .str] .dyn
  /-- `k in x` -/
  | dynHas : Builtin [.dyn, .str] .bool
  /-- `String(x)` -/
  | dynToStr : Builtin [.dyn] .str
  -- sets
  | setNew (t : Ty) : Builtin [] (.set t)
  | setOfArr (t : Ty) : Builtin [.arr t] (.set t)
  | setAdd (t : Ty) : Builtin [.set t, t] (.set t)
  | setHas (t : Ty) : Builtin [.set t, t] .bool
  | setDelete (t : Ty) : Builtin [.set t, t] .bool
  | setSize (t : Ty) : Builtin [.set t] .num
  | setClear (t : Ty) : Builtin [.set t] .undef
  | setValues (t : Ty) : Builtin [.set t] (.arr t)
  | setForEach (t : Ty) : Builtin [.set t, .fn (.cons t (.cons t (.cons (.set t) .nil))) .undef] .undef
  -- mutable cells for captured `let` variables
  | boxNew (t : Ty) : Builtin [t] (.box t)
  | boxGet (t : Ty) : Builtin [.box t] t
  | boxSet (t : Ty) : Builtin [.box t, t] .undef
  -- environment
  | log : Builtin [.str] .undef
  | random : Builtin [] .num
  | now : Builtin [] .num
  -- promises and jobs
  | promResolve (t : Ty) : Builtin [t] (.promise t)
  | promReject (t : Ty) : Builtin [.err] (.promise t)
  | promThen (t u : Ty) : Builtin [.promise t, .fn (.cons t .nil) u] (.promise u)
  | promThenP (t u : Ty) : Builtin [.promise t, .fn (.cons t .nil) (.promise u)] (.promise u)
  | promCatch (t : Ty) : Builtin [.promise t, .fn (.cons .err .nil) t] (.promise t)
  | promFinally (t : Ty) : Builtin [.promise t, .fn .nil .undef] (.promise t)
  | promAll (t : Ty) : Builtin [.arr (.promise t)] (.promise (.arr t))
  /-- `Promise.all` over a tuple of promises of different types -/
  | promAllTup (ts : Tys) : Builtin [.tup (ts.map .promise)] (.promise (.tup ts))
  | promAllSettled (t : Ty) : Builtin [.arr (.promise t)] (.promise (.arr t.settled))
  | promAllSettledTup (ts : Tys) : Builtin [.tup (ts.map .promise)] (.promise (.tup (ts.map Ty.settled)))
  | promRace (t : Ty) : Builtin [.arr (.promise t)] (.promise t)
  | promNew (t : Ty) : Builtin [.fn (.cons (.fn (.cons t .nil) .undef) (.cons (.fn (.cons .err .nil) .undef) .nil)) .undef] (.promise t)
  | queueMicrotask : Builtin [.fn .nil .undef] .undef
  | setTimeout : Builtin [.fn .nil .undef, .num] .num

/-- A reference to a top-level function: its index in `Program.funs` and its name (for
messages only). The signature is part of the type, so calls are checked statically. -/
structure FunRef (args : Tys) (ret : Ty) where
  idx : Nat
  name : String
  deriving Repr

/-- A module-level variable: a mutable cell at heap address `idx` (allocated at start-up). -/
structure GRef (t : Ty) where
  idx : Nat
  name : String
  deriving Repr

mutual
/-- Expressions. -/
inductive Expr (TT : TypeTable) : Ctx → Ty → Type where
  | lit {Γ t} : Lit t → Expr TT Γ t
  | var {Γ t} : Var Γ t → Expr TT Γ t
  | gget {Γ t} : GRef t → Expr TT Γ t
  | prim {Γ args t} : PrimOp args t → Args TT Γ args → Expr TT Γ t
  | builtin {Γ args t} : Builtin args t → Args TT Γ args → Expr TT Γ t
  | and {Γ} : Expr TT Γ .bool → Expr TT Γ .bool → Expr TT Γ .bool
  | or {Γ} : Expr TT Γ .bool → Expr TT Γ .bool → Expr TT Γ .bool
  | cond {Γ t} : Expr TT Γ .bool → Expr TT Γ t → Expr TT Γ t → Expr TT Γ t
  | letE {Γ u} (t : Ty) : Expr TT Γ t → Expr TT (⟨t, false⟩ :: Γ) u → Expr TT Γ u
  | call {Γ args t} : FunRef args t → Args TT Γ args.toList → Expr TT Γ t
  | app {Γ args t} : Expr TT Γ (.fn args t) → Args TT Γ args.toList → Expr TT Γ t
  | lam {Γ args t} (Δ : Ctx) : Caps Γ Δ → Lam TT args t Δ → Expr TT Γ (.fn args t)
  | funVal {Γ args t} : FunRef args t → Expr TT Γ (.fn args t)
  | mkTup {Γ ts} : Args TT Γ ts.toList → Expr TT Γ (.tup ts)
  | getTup {Γ ts t} : Expr TT Γ (.tup ts) → Mem t ts.toList → Expr TT Γ t
  | mkRec {Γ fs} : Args TT Γ fs.types → Expr TT Γ (.record fs)
  | getRec {Γ fs t} : Expr TT Γ (.record fs) → Mem t fs.types → Expr TT Γ t
  /-- Allocation of an instance of class `c` with field list `fs` (= `TT.fields c`); fields
  start uninitialised. The field list is explicit so that no type of the IR mentions `TT`. -/
  | newObj {Γ} (c : String) (fs : Fields) : Expr TT Γ (.obj c)
  | getField {Γ c t} {fs : Fields} : Expr TT Γ (.obj c) → Mem t fs.types → Expr TT Γ t
  | fold {Γ n} : Expr TT Γ (TT.alias n) → Expr TT Γ (.named n)
  | unfold {Γ n} : Expr TT Γ (.named n) → Expr TT Γ (TT.alias n)
  | none {Γ t} : Expr TT Γ (.opt t)
  | some {Γ t} : Expr TT Γ t → Expr TT Γ (.opt t)
  | unwrap {Γ t} : Expr TT Γ (.opt t) → Expr TT Γ t
  | caseOpt {Γ t u} : Expr TT Γ (.opt t) → Expr TT Γ u → Expr TT (⟨t, false⟩ :: Γ) u → Expr TT Γ u
  | inj {Γ t ts} : Mem t ts.toList → Expr TT Γ t → Expr TT Γ (.union ts)
  | caseU {Γ ts u} : Expr TT Γ (.union ts) → Alts TT Γ ts.toList u → Expr TT Γ u
  | enumLit {Γ cs} : Fin cs.length → Expr TT Γ (.enum cs)
  /-- A call of an external (library or host) function, typed by its TypeScript signature: the
  world's oracle gives its result or the error it throws. -/
  | extern {Γ args t} (name : String) : Args TT Γ args → Expr TT Γ t
  /-- An external function returning `Promise<t>`: the oracle's outcome settles a fresh promise. -/
  | externAsync {Γ args t} (name : String) : Args TT Γ args → Expr TT Γ (.promise t)

/-- Argument lists. -/
inductive Args (TT : TypeTable) : Ctx → List Ty → Type where
  | nil {Γ} : Args TT Γ []
  | cons {Γ t ts} : Expr TT Γ t → Args TT Γ ts → Args TT Γ (t :: ts)

/-- Branches of a union case analysis, one per member type. -/
inductive Alts (TT : TypeTable) : Ctx → List Ty → Ty → Type where
  | nil {Γ u} : Alts TT Γ [] u
  | cons {Γ t ts u} : Expr TT (⟨t, false⟩ :: Γ) u → Alts TT Γ ts u → Alts TT Γ (t :: ts) u

/-- Function literals over a capture context `Δ`. An `async` function's body returns `ret`
and the function returns `Promise<ret>`. Parameters are slots (mutable if reassigned). -/
inductive Lam (TT : TypeTable) : Tys → Ty → Ctx → Type where
  | sync {args ret Δ} (params : Ctx) (h : params.map Slot.ty = args.toList)
      (body : Block TT (params ++ Δ) ret) : Lam TT args ret Δ
  | async {args ret Δ} (params : Ctx) (h : params.map Slot.ty = args.toList)
      (body : Block TT (params ++ Δ) ret) : Lam TT args (.promise ret) Δ

/-- Statements; `ρ` is the return type of the enclosing function body. -/
inductive Stmt (TT : TypeTable) : Ctx → Ty → Type where
  | expr {Γ ρ t} : Expr TT Γ t → Stmt TT Γ ρ
  | assign {Γ ρ t} : MVar Γ t → Expr TT Γ t → Stmt TT Γ ρ
  | gset {Γ ρ t} : GRef t → Expr TT Γ t → Stmt TT Γ ρ
  | setField {Γ ρ c t} {fs : Fields} : Expr TT Γ (.obj c) → Mem t fs.types → Expr TT Γ t → Stmt TT Γ ρ
  | ite {Γ ρ} : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Stmt TT Γ ρ
  | while {Γ ρ} : Expr TT Γ .bool → Block TT Γ ρ → Stmt TT Γ ρ
  | doWhile {Γ ρ} : Block TT Γ ρ → Expr TT Γ .bool → Stmt TT Γ ρ
  /-- `for (; cond; step) body` (the initialiser is a declaration in an enclosing block). -/
  | forLoop {Γ ρ} : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → Stmt TT Γ ρ
  | forOf {Γ ρ t} : Expr TT Γ (.arr t) → Block TT (⟨t, false⟩ :: Γ) ρ → Stmt TT Γ ρ
  | forOfMap {Γ ρ k v} : Expr TT Γ (.map k v) →
      Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → Stmt TT Γ ρ
  | forOfSet {Γ ρ t} : Expr TT Γ (.set t) → Block TT (⟨t, false⟩ :: Γ) ρ → Stmt TT Γ ρ
  | forOfStr {Γ ρ} : Expr TT Γ .str → Block TT (⟨.str, false⟩ :: Γ) ρ → Stmt TT Γ ρ
  /-- `break`: `n` counts enclosing breakable constructs (loops and `breakable` blocks). -/
  | brk {Γ ρ} (n : Nat) : Stmt TT Γ ρ
  /-- `continue`: `n` counts enclosing loops only. -/
  | cont {Γ ρ} (n : Nat) : Stmt TT Γ ρ
  | ret {Γ ρ} : Expr TT Γ ρ → Stmt TT Γ ρ
  /-- `return p` of a promise inside an async body (resolution with a thenable). -/
  | retP {Γ ρ} : Expr TT Γ (.promise ρ) → Stmt TT Γ ρ
  | throw {Γ ρ} : Expr TT Γ .err → Stmt TT Γ ρ
  /-- `try body catch (e) handler finally fin` (an absent `finally` is the empty block). -/
  | try {Γ ρ} : Block TT Γ ρ → Block TT (⟨.err, false⟩ :: Γ) ρ → Block TT Γ ρ → Stmt TT Γ ρ
  /-- `try body finally fin` (no catch clause). -/
  | tryFin {Γ ρ} : Block TT Γ ρ → Block TT Γ ρ → Stmt TT Γ ρ
  | caseOptS {Γ ρ t} : Expr TT Γ (.opt t) → Block TT Γ ρ → Block TT (⟨t, false⟩ :: Γ) ρ → Stmt TT Γ ρ
  | caseUS {Γ ρ ts} : Expr TT Γ (.union ts) → AltsS TT Γ ts.toList ρ → Stmt TT Γ ρ
  | block {Γ ρ} : Block TT Γ ρ → Stmt TT Γ ρ
  /-- A block that `break` can leave (`switch`, labelled blocks). -/
  | breakable {Γ ρ} : Block TT Γ ρ → Stmt TT Γ ρ

/-- Blocks: a sequence of statements and scoped declarations. -/
inductive Block (TT : TypeTable) : Ctx → Ty → Type where
  | nil {Γ ρ} : Block TT Γ ρ
  | seq {Γ ρ} : Stmt TT Γ ρ → Block TT Γ ρ → Block TT Γ ρ
  | decl {Γ ρ} (s : Slot) : Expr TT Γ s.ty → Block TT (s :: Γ) ρ → Block TT Γ ρ
  /-- `const x = await e; rest` (async function bodies only). -/
  | await {Γ ρ} (s : Slot) : Expr TT Γ (.promise s.ty) → Block TT (s :: Γ) ρ → Block TT Γ ρ

/-- Statement-level union case analysis branches. -/
inductive AltsS (TT : TypeTable) : Ctx → List Ty → Ty → Type where
  | nil {Γ ρ} : AltsS TT Γ [] ρ
  | cons {Γ t ts ρ} : Block TT (⟨t, false⟩ :: Γ) ρ → AltsS TT Γ ts ρ → AltsS TT Γ (t :: ts) ρ
end

/-- A top-level function. -/
structure FunDef (TT : TypeTable) where
  name : String
  args : Tys
  ret : Ty
  lam : Lam TT args ret []

/-- A whole program: its functions, the types of its module-level variables (heap cells
`0 .. globals.length - 1`), and the module body. -/
structure Program (TT : TypeTable) where
  funs : List (FunDef TT)
  globals : List Ty
  main : Block TT [] .undef

end StrictTS
