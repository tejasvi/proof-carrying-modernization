/-
StrictTS core: the definitional interpreter.

All evaluation functions form one `partial_fixpoint` definition in the monad
`JS TT = ExceptT Exc (StateT (World TT) Option)`: a diverging program denotes `none`, and
the meaning of a program is the least fixpoint — no fuel. Lean derives the unfolding
equations (`evalE.eq_def`, …) and a fixpoint-induction principle from this definition.

Statements return completion records together with the updated environment, so that a
`throw` inside `try` keeps the assignments made before it.
-/
import StrictTS.Lib.Prim

set_option maxHeartbeats 0

namespace StrictTS
open Lean.Order

variable {TT : TypeTable}

/-! ### Monotonicity of the exception combinators (needed by `partial_fixpoint`) -/

@[partial_fixpoint_monotone]
theorem JS.monotone_catchThrown {α : Type} {γ : Sort _} [PartialOrder γ]
    (f : γ → JS TT α) (hf : monotone f) : monotone (fun x => JS.catchThrown (f x)) := by
  unfold JS.catchThrown
  apply monotone_bind (m := StateT (World TT) Option)
  · exact monotone_exceptTRun f hf
  · exact monotone_const _

/-! ### Auxiliary definitions -/

/-- The value of a function body that ends without `return` (only for `undefined`). -/
def defaultRet : (ρ : Ty) → Option (Val TT ρ)
  | .undef => some .undef
  | _ => none

/-- Fresh field storage of a class instance (all fields uninitialised). -/
def OVals.empty : (ts : List Ty) → OVals TT ts
  | [] => .nil
  | _ :: ts => .cons none (OVals.empty ts)

def OVals.get? : {ts : List Ty} → {t : Ty} → OVals TT ts → Mem t ts → Option (Val TT t)
  | _, _, .cons v _, .here => v
  | _, _, .cons _ vs, .there m => vs.get? m

def OVals.set : {ts : List Ty} → {t : Ty} → OVals TT ts → Mem t ts → Val TT t → OVals TT ts
  | _, _, .cons _ vs, .here, w => .cons (some w) vs
  | _, _, .cons v vs, .there m, w => .cons v (vs.set m w)

/-- The branch of a union case analysis selected by a member index. -/
def Alts.select : {Γ : Ctx} → {ts : List Ty} → {t u : Ty} → Alts TT Γ ts u → Mem t ts →
    Expr TT (⟨t, false⟩ :: Γ) u
  | _, _, _, _, .cons e _, .here => e
  | _, _, _, _, .cons _ es, .there m => es.select m

def AltsS.select : {Γ : Ctx} → {ts : List Ty} → {t : Ty} → {ρ : Ty} → AltsS TT Γ ts ρ → Mem t ts →
    Block TT (⟨t, false⟩ :: Γ) ρ
  | _, _, _, _, .cons b _, .here => b
  | _, _, _, _, .cons _ bs, .there m => bs.select m

mutual
/-- Does a statement contain an `await` of its own body (not of nested functions)? -/
def Stmt.hasAwait : {Γ : Ctx} → {ρ : Ty} → Stmt TT Γ ρ → Bool
  | _, _, .ite _ b1 b2 => b1.hasAwait || b2.hasAwait
  | _, _, .while _ b => b.hasAwait
  | _, _, .doWhile b _ => b.hasAwait
  | _, _, .forLoop _ b s => b.hasAwait || s.hasAwait
  | _, _, .forOf _ b => b.hasAwait
  | _, _, .forOfMap _ b => b.hasAwait
  | _, _, .forOfSet _ b => b.hasAwait
  | _, _, .forOfStr _ b => b.hasAwait
  | _, _, .try b h f => b.hasAwait || h.hasAwait || f.hasAwait
  | _, _, .tryFin b f => b.hasAwait || f.hasAwait
  | _, _, .caseOptS _ b1 b2 => b1.hasAwait || b2.hasAwait
  | _, _, .caseUS _ alts => alts.hasAwait
  | _, _, .block b => b.hasAwait
  | _, _, .breakable b => b.hasAwait
  | _, _, _ => false
def Block.hasAwait : {Γ : Ctx} → {ρ : Ty} → Block TT Γ ρ → Bool
  | _, _, .nil => false
  | _, _, .seq s rest => s.hasAwait || rest.hasAwait
  | _, _, .decl _ _ rest => rest.hasAwait
  | _, _, .await _ _ _ => true
def AltsS.hasAwait : {Γ : Ctx} → {ts : List Ty} → {ρ : Ty} → AltsS TT Γ ts ρ → Bool
  | _, _, _, .nil => false
  | _, _, _, .cons b bs => b.hasAwait || bs.hasAwait
end

/-- Normalise a `Map`/`Set` key: `-0` becomes `+0` (ECMA-262 Map.prototype.set step 4). -/
def normKey : (t : Ty) → Val TT t → Val TT t
  | .num, v => match v.toNum with
    | .fin x => if x.man = 0 then .num F64.zero else v
    | _ => v
  | .opt t, .some v => .some (normKey t v)
  | _, v => v


/-- Result of running an async body until it finishes or suspends on a promise. -/
inductive AStep (TT : TypeTable) (ρ : Ty) where
  | finished (c : Completion TT ρ)
  | suspended {t : Ty} (p : Nat) (r : Resumption TT ρ t)

namespace JS

def readArr (t : Ty) (a : Nat) : JS TT (Array (Val TT t)) := JS.read (.arr t) a
def writeArr (t : Ty) (a : Nat) (c : Array (Val TT t)) : JS TT Unit := JS.write (.arr t) a c
def allocArr (t : Ty) (c : Array (Val TT t)) : JS TT (Val TT (.arr t)) := do
  return .arr (← JS.alloc (.arr t) c)

mutual
/-- Allocate the fresh arrays of a value produced by external code (elements first, in order). -/
def materialize : {t : Ty} → EVal TT t → JS TT (Val TT t)
  | _, .val v => pure v
  | _, .arr (t := t) es => do
    let vs ← materializeList es
    allocArr t vs.toArray
  | _, .dyn t e => do
    let v ← materialize e
    pure (.dyn t v)
  | _, .dict (t := t) ks es => do
    let vs ← materializeList es
    let a ← JS.alloc (.dict t) ((ks.zip vs).foldl (fun m (k, v) => m.set (· == ·) k v) {})
    pure (.dict a)
def materializeList {t : Ty} : EVals TT t → JS TT (List (Val TT t))
  | .nil => pure []
  | .cons e es => do
    let v ← materialize e
    let vs ← materializeList es
    pure (v :: vs)
end

def readTA (k : TAKind) (a : Nat) : JS TT (Array (BitVec k.width)) := JS.read (.tarr k) a
def writeTA (k : TAKind) (a : Nat) (c : Array (BitVec k.width)) : JS TT Unit := JS.write (.tarr k) a c

def readObj (c : String) (fs : List Ty) (a : Nat) : JS TT (OVals TT fs) := JS.read (.obj c fs) a
def writeObj (c : String) (fs : List Ty) (a : Nat) (cell : OVals TT fs) : JS TT Unit := JS.write (.obj c fs) a cell

def readMap (k v : Ty) (a : Nat) : JS TT (JSMap (Val TT k) (Val TT v)) := JS.read (.map k v) a
def writeMap (k v : Ty) (a : Nat) (m : JSMap (Val TT k) (Val TT v)) : JS TT Unit := JS.write (.map k v) a m
def readDict (t : Ty) (a : Nat) : JS TT (JSMap JSStr (Val TT t)) := JS.read (.dict t) a
def writeDict (t : Ty) (a : Nat) (m : JSMap JSStr (Val TT t)) : JS TT Unit := JS.write (.dict t) a m
def readSet (t : Ty) (a : Nat) : JS TT (JSMap (Val TT t) Unit) := JS.read (.set t) a
def writeSet (t : Ty) (a : Nat) (m : JSMap (Val TT t) Unit) : JS TT Unit := JS.write (.set t) a m

/-- The content of a box, `none` when it is empty (no exception). -/
def readBoxOpt (t : Ty) (a : Nat) : JS TT (Option (Val TT t)) := JS.read (.box t) a

def readBox (t : Ty) (a : Nat) : JS TT (Val TT t) := do
  match ← JS.read (.box t) a with
  | some v => pure v
  | none => JS.throwJS .referenceError "Cannot access variable before initialization"

def readPromise (t : Ty) (p : Nat) : JS TT (PromiseCell TT t) := JS.read (.promise t) p
def newPromise (t : Ty) : JS TT Nat := JS.alloc (.promise t) {}

/-- The oracle's outcome for the next external call. -/
def extAnswer (name : String) (args : List Ty) (ret : Ty) (vs : Vals TT args) :
    JS TT (Except ErrVal (EVal TT ret)) :=
  modifyGet fun w => (w.ext name args ret vs w.extIdx, { w with extIdx := w.extIdx + 1 })

/-- Settle a pending promise and schedule its reactions (FulfillPromise / RejectPromise +
TriggerPromiseReactions). Settling an already settled promise does nothing. -/
def settle (t : Ty) (p : Nat) (out : Except ErrVal (Val TT t)) : JS TT Unit := do
  let c ← readPromise t p
  match c.state with
  | .pending =>
    let st : PState TT t := match out with
      | .ok v => .fulfilled v
      | .error e => .rejected e
    JS.write (.promise t) p { c with state := st, reactions := [] }
    match out, c.reactions with
    | .error e, [] => modify fun w => { w with unhandled := w.unhandled ++ [(p, e)] }
    | _, _ => pure ()
    for r in c.reactions do JS.enqueue (.react r out)
  | _ => pure ()

/-- PerformPromiseThen: register a reaction, or schedule it now if already settled. -/
def addReaction (t : Ty) (p : Nat) (r : Reaction TT t) : JS TT Unit := do
  let c ← readPromise t p
  match c.state with
  | .pending => JS.write (.promise t) p { c with reactions := c.reactions ++ [r] }
  | .fulfilled v => JS.enqueue (.react r (.ok v))
  | .rejected e => do
    modify fun w => { w with unhandled := w.unhandled.filter (·.1 != p) }
    JS.enqueue (.react r (.error e))

/-- The resolving functions of a `new Promise` executor (with [[AlreadyResolved]]). -/
def resolveOnce (t : Ty) (p : Nat) (out : Except ErrVal (Val TT t)) : JS TT Unit := do
  let c ← readPromise t p
  if c.locked then pure ()
  else
    JS.write (.promise t) p { c with locked := true }
    settle t p out

/-- Settle the promise of an async body from its final completion. -/
def finishAsync (ρ : Ty) (p : Nat) : Completion TT ρ → JS TT Unit
  | .normal => match defaultRet ρ with
    | some v => settle ρ p (.ok v)
    | none => JS.panic "async function ended without return"
  | .ret v => settle ρ p (.ok v)
  | .retP q => JS.enqueue (.resolveThenable ρ p q)
  | .exc e => settle ρ p (.error e)
  | .brk _ | .cont _ => JS.panic "break/continue escaped a function body"

/-! `Promise.all` / `Promise.allSettled` over tuples: one box cell per element, of that element's
type. -/

/-- The promises of a tuple of promises: each one's value type and address. -/
def promsOfTup : (ts : Tys) → Vals TT (ts.map .promise).toList → List (Ty × Nat)
  | .nil, .nil => []
  | .cons t ts, .cons q qs => (t, q.promAddr) :: promsOfTup ts qs

/-- The values in the boxes `as` of the types `ts`, when every box holds one. -/
def readSlots : (ts : List Ty) → List Nat → JS TT (Option (Vals TT ts))
  | [], [] => pure (some .nil)
  | t :: ts, a :: as => do
    match ← readBoxOpt t a with
    | some v => do
      match ← readSlots ts as with
      | some vs => pure (some (.cons v vs))
      | none => pure none
    | none => pure none
  | _, _ => pure none

/-- Resolve `target` with the tuple of values of the types `us` in the boxes `slots`, once every
box holds one (for the empty tuple at once, as PerformPromiseAll does). -/
def tupDone (us : Tys) (target : Nat) (slots : List Nat) : JS TT Unit := do
  match ← readSlots us.toList slots with
  | some vs => settle (.tup us) target (.ok (.tup vs))
  | none => pure ()

/-- The `Promise.allSettled` record of an outcome: `{ status: "fulfilled", value }` or
`{ status: "rejected", reason }` (the reason as a value of type `unknown`). -/
def settledVal {t : Ty} : Except ErrVal (Val TT t) → Val TT t.settled
  | .ok v => .inj (.there .here) (.record (.cons (.str (JSStr.ofString "fulfilled")) (.cons v .nil)))
  | .error e => .inj .here (.record (.cons (.dyn .err (.err e)) (.cons (.str (JSStr.ofString "rejected")) .nil)))

/-- Allocate one empty box of type `box t` per promise (of type `t`) of a tuple, then register the
reaction `r t slots a` on each promise, in order (`a` its box). -/
def tupReactions (qs : List (Ty × Nat)) (box : Ty → Ty) (r : (t : Ty) → List Nat → Nat → Reaction TT t) :
    JS TT (List Nat) := do
  let slots ← qs.mapM fun (t, _) => JS.alloc (.box (box t)) none
  (qs.zip slots).forM fun ((t, q), a) => addReaction t q (r t slots a)
  pure slots

/-- The value of a synchronous function call from the body's completion. -/
def finishSync (ρ : Ty) : Completion TT ρ → JS TT (Val TT ρ)
  | .normal => match defaultRet ρ with
    | some v => pure v
    | none => JS.panic "function ended without return"
  | .ret v => pure v
  | .exc e => throw (.thrown e)
  | .retP _ => JS.panic "promise return in a synchronous function"
  | .brk _ | .cont _ => JS.panic "break/continue escaped a function body"

/-- An index argument used as an array position. -/
def index? (x : Val TT .num) : Option Nat := Conv.arrayIndex? x.toNum

/-- ToIntegerOrInfinity of a number argument. -/
def toInt (x : Val TT .num) : EInt := Conv.toIntegerOrInf x.toNum

def num (n : Nat) : Val TT .num := .num (F64.ofNat n)

/-- `fromIndex` handling of `indexOf`. -/
def startIndex (x : EInt) (len : Nat) : Nat := Conv.relIndex x len

/-! ### Values of type `unknown` that need the heap (StrictTS/Lib/Dyn.lean has the rest) -/

def dynUndef : Val TT .dyn := .dyn .undef .undef

/-- The property read `x[k]` on a value of type `unknown`: own properties of objects used as
dictionaries, records and class instances (an absent key is `undefined`; an inherited
`Object.prototype` property panics), `length` and indices of arrays, tuples and strings (any
other key of an array or tuple is `undefined` unless the array inherits it, which panics),
`message` and `name` of errors; a `TypeError` on `undefined` and `null`. Everything else
(prototype methods, properties of numbers, of external objects, …) panics. -/
def dynGet (d : Val TT .dyn) (k : JSStr) : JS TT (Val TT .dyn) :=
  match Dyn.base d with
  | ⟨.undef, _⟩ => JS.throwJS .typeError s!"Cannot read properties of undefined (reading '{k}')"
  | ⟨.null, _⟩ => JS.throwJS .typeError s!"Cannot read properties of null (reading '{k}')"
  | ⟨.dict u, v⟩ => do
    let c ← readDict u v.dictAddr
    match c.get? (· == ·) k with
    | some x => pure (.dyn u x)
    | none => if Dict.isProtoKey k then JS.panic "read of an inherited Object.prototype property" else pure dynUndef
  | ⟨.record fs, v⟩ =>
    match Dyn.fieldMem k fs with
    | some ⟨u, m⟩ => pure (.dyn u (v.recVals.get m))
    | none => if Dict.isProtoKey k then JS.panic "read of an inherited Object.prototype property" else pure dynUndef
  | ⟨.obj c, v⟩ =>
    match Dyn.fieldMem k (TT.fields c) with
    | some ⟨u, m⟩ => do
      let cell ← readObj c (TT.fields c).types v.objAddr
      match cell.get? m with
      | some x => pure (.dyn u x)
      | none => JS.panic "read of an uninitialised field"
    | none => JS.panic "property of a class instance that is not a field, read as unknown"
  | ⟨.arr u, v⟩ => do
    let c ← readArr u v.arrAddr
    if k == Dyn.lengthKey then pure (.dyn .num (num c.size))
    else match Dict.arrayIndex? k with
      | some i => pure (match c[i]? with | some x => .dyn u x | none => dynUndef)
      | none => if Dict.isArrayProtoKey k then JS.panic "read of an inherited Array.prototype property through unknown" else pure dynUndef
  | ⟨.tup ts, v⟩ =>
    if k == Dyn.lengthKey then pure (.dyn .num (num ts.toList.length))
    else match Dict.arrayIndex? k with
      | some i => pure (match Dyn.nth v.tupVals i with | some ⟨u, x⟩ => .dyn u x | none => dynUndef)
      | none => if Dict.isArrayProtoKey k then JS.panic "read of an inherited Array.prototype property through unknown" else pure dynUndef
  | ⟨t, v⟩ =>
    match Dyn.strOf t v with
    | some s =>
      if k == Dyn.lengthKey then pure (.dyn .num (num s.units.length))
      else match Dict.arrayIndex? k with
        | some i => pure (match s.units[i]? with | some c => .dyn .str (.str ⟨[c]⟩) | none => dynUndef)
        | none => JS.panic "property of a string that is not an index or length, read as unknown"
    | none =>
      match t, v with
      | .err, v =>
        if k == JSStr.ofString "message" then pure (.dyn .str (.str v.toErr.message))
        else if k == JSStr.ofString "name" then pure (.dyn .str (.str v.toErr.name))
        else JS.panic "property of an error other than message and name, read as unknown"
      | _, _ => JS.panic "property read on a value of this runtime type through unknown"

/-- `k in x` on a value of type `unknown` (own keys and `Object.prototype` keys of objects,
indices, `length` and inherited keys of arrays; a `TypeError` on primitives). -/
def dynHas (d : Val TT .dyn) (k : JSStr) : JS TT Bool :=
  match Dyn.base d with
  | ⟨.dict u, v⟩ => do
    let c ← readDict u v.dictAddr
    pure (c.has (· == ·) k || Dict.isProtoKey k)
  | ⟨.record fs, _⟩ => pure ((Dyn.fieldMem k fs).isSome || Dict.isProtoKey k)
  | ⟨.obj c, _⟩ =>
    if (Dyn.fieldMem k (TT.fields c)).isSome || Dict.isProtoKey k then pure true
    else JS.panic "`in` on a class instance for a key that is not a field"
  | ⟨.arr u, v⟩ => do
    let c ← readArr u v.arrAddr
    if k == Dyn.lengthKey then pure true
    else match Dict.arrayIndex? k with
      | some i => pure (i < c.size)
      | none => pure (Dict.isArrayProtoKey k)
  | ⟨.tup ts, _⟩ =>
    if k == Dyn.lengthKey then pure true
    else match Dict.arrayIndex? k with
      | some i => pure (i < ts.toList.length)
      | none => pure (Dict.isArrayProtoKey k)
  | ⟨t, v⟩ =>
    match Dyn.primStr t v with
    | some s => JS.throwJS .typeError s!"Cannot use 'in' operator to search for '{k}' in {s}"
    | none => JS.panic "`in` on a value of this runtime type through unknown"

/-- `String(x)` of a runtime value (not a wrapper); `fuel` bounds the nesting of arrays, whose
elements are joined with commas (`undefined` and `null` elements are empty). -/
def dynStr : (fuel : Nat) → (t : Ty) → Val TT t → JS TT JSStr
  | fuel, t, v =>
    match Dyn.primStr t v with
    | some s => pure s
    | none =>
      match fuel, t, v with
      | 0, _, _ => JS.panic "String of deeply nested arrays"
      | fuel + 1, .arr u, v => do
        let c ← readArr u v.arrAddr
        let parts ← c.toList.mapM fun x =>
          match Dyn.base x with
          | ⟨.undef, _⟩ | ⟨.null, _⟩ => pure ⟨[]⟩
          | ⟨t', x'⟩ => dynStr fuel t' x'
        pure (Dyn.joinComma parts)
      | fuel + 1, .tup _, v => do
        let parts ← (Dyn.sigmas v.tupVals).mapM fun ⟨_, x⟩ =>
          match Dyn.base x with
          | ⟨.undef, _⟩ | ⟨.null, _⟩ => pure ⟨[]⟩
          | ⟨t', x'⟩ => dynStr fuel t' x'
        pure (Dyn.joinComma parts)
      | _, .err, v => pure (Dyn.errStr v.toErr)
      -- an own `toString` / `valueOf` property would be used by ToPrimitive instead
      -- (instances of classes with such methods never become unknown values: the translator)
      | _, .record fs, _ =>
        if fs.names.contains "toString" || fs.names.contains "valueOf" then JS.panic "String of an object with its own toString/valueOf"
        else pure (JSStr.ofString "[object Object]")
      | _, .dict u, v => do
        let c ← readDict u v.dictAddr
        if c.has (· == ·) (JSStr.ofString "toString") || c.has (· == ·) (JSStr.ofString "valueOf") then
          JS.panic "String of an object with its own toString/valueOf"
        else pure (JSStr.ofString "[object Object]")
      | _, .obj _, _ => pure (JSStr.ofString "[object Object]")
      | _, .map _ _, _ => pure (JSStr.ofString "[object Map]")
      | _, .set _, _ => pure (JSStr.ofString "[object Set]")
      | _, .promise _, _ => pure (JSStr.ofString "[object Promise]")
      | _, _, _ => JS.panic "String of a value of this runtime type through unknown"

end JS

open JS

/-- What to do when an async body stops: settle its promise, or wait on the awaited one. -/
def handleStep {ρ : Ty} (p : Nat) (step : AStep TT ρ) : JS TT Unit :=
  match step with
  | .finished c => finishAsync ρ p c
  | .suspended (t := t) q r => addReaction t q (.await r p)

/-- Builtins that call back into user code (evaluated inside the interpreter's fixpoint). -/
def Builtin.hasCallback {args : List Ty} {t : Ty} : Builtin args t → Bool
  | .arrSort .. => true
  | .arrMap .. => true
  | .arrFilter .. => true
  | .arrForEach .. => true
  | .arrFind .. => true
  | .arrFindIndex .. => true
  | .arrFindLast .. => true
  | .arrFindLastIndex .. => true
  | .arrSome .. => true
  | .arrEvery .. => true
  | .arrFlatMap .. => true
  | .arrReduce .. => true
  | .arrReduce1 .. => true
  | .arrReduceRight .. => true
  | .arrFromFn .. => true
  | .mapForEach .. => true
  | .setForEach .. => true
  | .promNew .. => true
  | _ => false

/-- Library operations that do not call back into user code. -/
def evalBuiltinBasic {args : List Ty} {t : Ty} (b : Builtin args t)
    (vs : Vals TT args) : JS TT (Val TT t) :=
  match b with
  | .arrOf t _ => allocArr t (Vals.toList vs).toArray
  | .arrLength t => do
    let a := vs.a0
    let c ← readArr t a.arrAddr
    pure (num c.size)
  | .arrGet t => do
    let a := vs.a0
    let i := vs.a1
    let c ← readArr t a.arrAddr
    match index? i with
    | some k => if h : k < c.size then pure c[k] else JS.panic "array index out of bounds"
    | none => JS.panic "array read at a non-index key"
  | .arrGetOpt t => do
    let a := vs.a0
    let i := vs.a1
    let c ← readArr t a.arrAddr
    match index? i with
    | some k => if h : k < c.size then pure (.some c[k]) else pure .none
    | none => pure .none
  | .arrAt t => do
    let a := vs.a0
    let i := vs.a1
    let c ← readArr t a.arrAddr
    match Conv.atIndex (toInt i) c.size with
    | some k => if h : k < c.size then pure (.some c[k]) else pure .none
    | none => pure .none
  | .arrSet t => do
    let a := vs.a0
    let i := vs.a1
    let v := vs.a2
    let c ← readArr t a.arrAddr
    match index? i with
    | some k =>
      if h : k < c.size then do
        writeArr t a.arrAddr (c.set k v h)
        pure .undef
      else if k = c.size then do
        writeArr t a.arrAddr (c.push v)
        pure .undef
      else JS.panic "array write would create a hole"
    | none => JS.panic "array write at a non-index key"
  | .arrSetLength t => do
    let a := vs.a0
    let n := vs.a1
    let c ← readArr t a.arrAddr
    match index? n with
    | some k =>
      if k ≤ c.size then do
        writeArr t a.arrAddr (c.extract 0 k)
        pure .undef
      else JS.panic "array length extension would create holes"
    | none => JS.throwJS .rangeError "Invalid array length"
  | .arrPush t => do
    let a := vs.a0
    let v := vs.a1
    let c ← readArr t a.arrAddr
    writeArr t a.arrAddr (c.push v)
    pure (num (c.size + 1))
  | .arrPop t => do
    let a := vs.a0
    let c ← readArr t a.arrAddr
    if h : 0 < c.size then do
      writeArr t a.arrAddr c.pop
      pure (.some c[c.size - 1])
    else pure .none
  | .arrShift t => do
    let a := vs.a0
    let c ← readArr t a.arrAddr
    if h : 0 < c.size then do
      writeArr t a.arrAddr (c.extract 1 c.size)
      pure (.some c[0])
    else pure .none
  | .arrUnshift t => do
    let a := vs.a0
    let v := vs.a1
    let c ← readArr t a.arrAddr
    writeArr t a.arrAddr (#[v] ++ c)
    pure (num (c.size + 1))
  | .arrSlice t => do
    let a := vs.a0
    let s := vs.a1
    let e := vs.a2
    let c ← readArr t a.arrAddr
    let k := Conv.relIndex (toInt s) c.size
    let fin := match e with
      | .none => c.size
      | .some e => Conv.relIndex (toInt e) c.size
    allocArr t (c.extract k fin)
  | .arrSplice t => do
    let a := vs.a0
    let s := vs.a1
    let dc := vs.a2
    let items := vs.a3
    let c ← readArr t a.arrAddr
    let its ← readArr t items.arrAddr
    let start := Conv.relIndex (toInt s) c.size
    let del := match toInt dc with
      | .negInf => 0
      | .posInf => c.size - start
      | .fin n => min (max n 0).toNat (c.size - start)
    let r ← allocArr t (c.extract start (start + del))
    writeArr t a.arrAddr (c.extract 0 start ++ its ++ c.extract (start + del) c.size)
    pure r
  | .arrConcat t => do
    let a := vs.a0
    let b := vs.a1
    let x ← readArr t a.arrAddr
    let y ← readArr t b.arrAddr
    allocArr t (x ++ y)
  | .arrCopy t => do
    let a := vs.a0
    let x ← readArr t a.arrAddr
    allocArr t x
  | .arrIndexOf t => do
    if !t.eqable then JS.panic "comparison of values without identity" else
    let a := vs.a0
    let x := vs.a1
    let fromI := vs.a2
    let c ← readArr t a.arrAddr
    let st := Conv.relIndex (toInt fromI) c.size
    match (List.range c.size).find? (fun k => decide (st ≤ k) &&
        (match c[k]? with | some y => Conv.strictEq t y x | none => false)) with
    | some k => pure (num k)
    | none => pure (.num (F64.ofInt (-1)))
  | .arrLastIndexOf t => do
    if !t.eqable then JS.panic "comparison of values without identity" else
    let a := vs.a0
    let x := vs.a1
    let fromI := vs.a2
    let c ← readArr t a.arrAddr
    let hi : Int := match toInt fromI with
      | .negInf => -1
      | .posInf => (c.size : Int) - 1
      | .fin n => if n < 0 then c.size + n else min n ((c.size : Int) - 1)
    match (List.range c.size).reverse.find? (fun (k : Nat) => decide ((k : Int) ≤ hi) &&
        (match c[k]? with | some y => Conv.strictEq t y x | none => false)) with
    | some k => pure (num k)
    | none => pure (.num (F64.ofInt (-1)))
  | .arrIncludes t => do
    if !t.eqable then JS.panic "comparison of values without identity" else
    let a := vs.a0
    let x := vs.a1
    let c ← readArr t a.arrAddr
    pure (.bool (c.any fun y => Conv.svz t y x))
  | .arrJoin => do
    let a := vs.a0
    let sep := vs.a1
    let c ← readArr .str a.arrAddr
    let parts := c.toList.map Val.toStr
    pure (.str (match parts with
      | [] => JSStr.empty
      | p :: ps => ps.foldl (fun acc q => acc ++ sep.toStr ++ q) p))
  | .arrReverse t => do
    let a := vs.a0
    let c ← readArr t a.arrAddr
    writeArr t a.arrAddr c.reverse
    pure a
  | .arrFill t => do
    let a := vs.a0
    let v := vs.a1
    let s := vs.a2
    let e := vs.a3
    let c ← readArr t a.arrAddr
    let k := Conv.relIndex (toInt s) c.size
    let fin := match e with
      | .none => c.size
      | .some e => Conv.relIndex (toInt e) c.size
    writeArr t a.arrAddr (c.mapIdx fun i y => if k ≤ i ∧ i < fin then v else y)
    pure a
  | .arrMakeFill t => do
    let n := vs.a0
    let v := vs.a1
    match index? n with
    | some k => allocArr t (Array.replicate k v)
    | none => JS.throwJS .rangeError "Invalid array length"
  | .arrSortStr => do
    let a := vs.a0
    let c ← readArr .str a.arrAddr
    writeArr .str a.arrAddr (c.toList.mergeSort (fun x y => !JSStr.lt y.toStr x.toStr)).toArray
    pure a
  | .mapNew k v => do
    let a ← JS.alloc (.map k v) {}
    pure (.map a)
  | .mapOfEntries k v => do
    let arr := vs.a0
    let c ← readArr (.tup (.cons k (.cons v .nil))) arr.arrAddr
    let m := c.foldl (fun (m : JSMap (Val TT k) (Val TT v)) e =>
      m.set (Conv.svz k) (normKey k e.tupVals.head) e.tupVals.tail.head) {}
    let a ← JS.alloc (.map k v) m
    pure (.map a)
  | .mapGet k v => do
    let m := vs.a0
    let key := vs.a1
    let c ← readMap k v m.mapAddr
    pure (match c.get? (Conv.svz k) key with | some x => .some x | none => .none)
  | .mapSet k v => do
    let m := vs.a0
    let key := vs.a1
    let val := vs.a2
    let c ← readMap k v m.mapAddr
    writeMap k v m.mapAddr (c.set (Conv.svz k) (normKey k key) val)
    pure m
  | .mapHas k v => do
    let m := vs.a0
    let key := vs.a1
    let c ← readMap k v m.mapAddr
    pure (.bool (c.has (Conv.svz k) key))
  | .mapDelete k v => do
    let m := vs.a0
    let key := vs.a1
    let c ← readMap k v m.mapAddr
    let (c', found) := c.delete (Conv.svz k) key
    writeMap k v m.mapAddr c'
    pure (.bool found)
  | .mapSize k v => do
    let m := vs.a0
    let c ← readMap k v m.mapAddr
    pure (num c.size)
  | .mapClear k v => do
    let m := vs.a0
    let c ← readMap k v m.mapAddr
    writeMap k v m.mapAddr c.clear
    pure .undef
  | .mapKeys k v => do
    let m := vs.a0
    let c ← readMap k v m.mapAddr
    allocArr k (c.toList.map Prod.fst).toArray
  | .mapValues k v => do
    let m := vs.a0
    let c ← readMap k v m.mapAddr
    allocArr v (c.toList.map Prod.snd).toArray
  | .mapEntries k v => do
    let m := vs.a0
    let c ← readMap k v m.mapAddr
    allocArr _ (c.toList.map fun (x, y) => Val.tup (.cons x (.cons y .nil))).toArray
  | .dictNew t => do
    let a ← JS.alloc (.dict t) {}
    pure (.dict a)
  | .dictGet t => do
    let c ← readDict t vs.a0.dictAddr
    match c.get? (· == ·) vs.a1.toStr with
    | some x => pure (.some x)
    | none =>
      if Dict.isProtoKey vs.a1.toStr then JS.panic "read of an inherited Object.prototype property"
      else pure .none
  | .dictSet t => do
    if vs.a1.toStr == JSStr.ofString "__proto__" then JS.panic "assignment to __proto__" else
    let c ← readDict t vs.a0.dictAddr
    writeDict t vs.a0.dictAddr (c.set (· == ·) vs.a1.toStr vs.a2)
    pure .undef
  | .dictHas t => do
    let c ← readDict t vs.a0.dictAddr
    pure (.bool (c.has (· == ·) vs.a1.toStr || Dict.isProtoKey vs.a1.toStr))
  | .dictHasOwn t => do
    let c ← readDict t vs.a0.dictAddr
    pure (.bool (c.has (· == ·) vs.a1.toStr))
  | .dictDelete t => do
    let c ← readDict t vs.a0.dictAddr
    let (c', _) := c.delete (· == ·) vs.a1.toStr
    writeDict t vs.a0.dictAddr c'
    pure (.bool true)
  | .dynGet => JS.dynGet vs.a0 vs.a1.toStr
  | .dynHas => do pure (.bool (← JS.dynHas vs.a0 vs.a1.toStr))
  | .dynToStr => do let b := Dyn.base vs.a0; pure (.str (← JS.dynStr 64 b.1 b.2))
  | .dictKeys t => do
    let c ← readDict t vs.a0.dictAddr
    allocArr .str ((Dict.ordered c.toList).map fun p => Val.str p.1).toArray
  | .dictValues t => do
    let c ← readDict t vs.a0.dictAddr
    allocArr t ((Dict.ordered c.toList).map Prod.snd).toArray
  | .dictEntries t => do
    let c ← readDict t vs.a0.dictAddr
    allocArr _ ((Dict.ordered c.toList).map fun (k, x) => Val.tup (.cons (.str k) (.cons x .nil))).toArray
  | .setNew t => do
    let a ← JS.alloc (.set t) {}
    pure (.set a)
  | .setOfArr t => do
    let arr := vs.a0
    let c ← readArr t arr.arrAddr
    let m := c.foldl (fun (m : JSMap (Val TT t) Unit) x => m.set (Conv.svz t) (normKey t x) ()) {}
    let a ← JS.alloc (.set t) m
    pure (.set a)
  | .setAdd t => do
    let s := vs.a0
    let x := vs.a1
    let c ← readSet t s.setAddr
    writeSet t s.setAddr (if c.has (Conv.svz t) x then c else c.set (Conv.svz t) (normKey t x) ())
    pure s
  | .setHas t => do
    let s := vs.a0
    let x := vs.a1
    let c ← readSet t s.setAddr
    pure (.bool (c.has (Conv.svz t) x))
  | .setDelete t => do
    let s := vs.a0
    let x := vs.a1
    let c ← readSet t s.setAddr
    let (c', found) := c.delete (Conv.svz t) x
    writeSet t s.setAddr c'
    pure (.bool found)
  | .setSize t => do
    let s := vs.a0
    let c ← readSet t s.setAddr
    pure (num c.size)
  | .setClear t => do
    let s := vs.a0
    let c ← readSet t s.setAddr
    writeSet t s.setAddr c.clear
    pure .undef
  | .setValues t => do
    let s := vs.a0
    let c ← readSet t s.setAddr
    allocArr t (c.toList.map Prod.fst).toArray
  | .boxNew t => do
    let v := vs.a0
    let a ← JS.alloc (.box t) (some v)
    pure (.box a)
  | .boxGet t =>
    let bx := vs.a0
    readBox t bx.boxAddr
  | .boxSet t => do
    let bx := vs.a0
    let v := vs.a1
    JS.write (.box t) bx.boxAddr (some v)
    pure .undef
  | .log => do
    let s := vs.a0
    JS.log s.toStr
    pure .undef
  | .random => do
    let x ← modifyGet fun w => (w.rand w.randIdx, { w with randIdx := w.randIdx + 1 })
    pure (.num x)
  | .now => do
    let x ← modifyGet fun w => (w.now w.nowIdx, { w with nowIdx := w.nowIdx + 1 })
    pure (.num x)
  | .promResolve t => do
    let v := vs.a0
    let p ← newPromise t
    settle t p (.ok v)
    pure (.promise p)
  | .promReject t => do
    let e := vs.a0
    let p ← newPromise t
    settle t p (.error e.toErr)
    pure (.promise p)
  | .promThen t u => do
    let p := vs.a0
    let f := vs.a1
    let target ← newPromise u
    addReaction t p.promAddr (.then f target)
    pure (.promise target)
  | .promThenP t u => do
    let p := vs.a0
    let f := vs.a1
    let target ← newPromise u
    addReaction t p.promAddr (.thenP f target)
    pure (.promise target)
  | .promCatch t => do
    let p := vs.a0
    let f := vs.a1
    let target ← newPromise t
    addReaction t p.promAddr (.catch f target)
    pure (.promise target)
  | .promFinally t => do
    let p := vs.a0
    let f := vs.a1
    let target ← newPromise t
    addReaction t p.promAddr (.finally f target)
    pure (.promise target)
  | .promAll t => do
    let arr := vs.a0
    let c ← readArr (.promise t) arr.arrAddr
    let target ← newPromise (.arr t)
    if c.size = 0 then do
      let res ← allocArr t #[]
      settle (.arr t) target (.ok res)
    else do
      let slots ← JS.alloc (.arr (.opt t)) (Array.replicate c.size Val.none)
      (List.range c.size).forM fun i =>
        match c[i]? with
        | some q => addReaction t q.promAddr (.allSlot target slots i)
        | none => pure ()
    pure (.promise target)
  | .promAllTup ts => do
    let target ← newPromise (.tup ts)
    let slots ← tupReactions (promsOfTup ts vs.a0.tupVals) id fun _ slots a => .allTup ts target slots a
    tupDone ts target slots
    pure (.promise target)
  | .promAllSettled t => do
    let arr := vs.a0
    let c ← readArr (.promise t) arr.arrAddr
    let target ← newPromise (.arr t.settled)
    if c.size = 0 then do
      let res ← allocArr t.settled #[]
      settle (.arr t.settled) target (.ok res)
    else do
      let slots ← JS.alloc (.arr (.opt t.settled)) (Array.replicate c.size Val.none)
      (List.range c.size).forM fun i =>
        match c[i]? with
        | some q => addReaction t q.promAddr (.settledSlot target slots i)
        | none => pure ()
    pure (.promise target)
  | .promAllSettledTup ts => do
    let target ← newPromise (.tup (ts.map Ty.settled))
    let slots ← tupReactions (promsOfTup ts vs.a0.tupVals) Ty.settled
      fun _ slots a => .settledTup ts target slots a
    tupDone (ts.map Ty.settled) target slots
    pure (.promise target)
  | .promRace t => do
    let arr := vs.a0
    let c ← readArr (.promise t) arr.arrAddr
    let target ← newPromise t
    c.toList.forM fun q => addReaction t q.promAddr (.forward target)
    pure (.promise target)
  | .queueMicrotask => do
    let f := vs.a0
    JS.enqueue (.callback f)
    pure .undef
  | .setTimeout => do
    let f := vs.a0
    let ms := vs.a1
    -- Node: `if (!(after >= 1 && after <= TIMEOUT_MAX)) after = 1` (TIMEOUT_MAX = 2^31 - 1)
    let delay : Nat :=
      if F64.ge ms.toNum (F64.ofNat 1) && F64.le ms.toNum (F64.ofNat 2147483647) then
        match Conv.toIntegerOrInf ms.toNum with
        | .fin n => n.toNat
        | _ => 1
      else 1
    let id ← modifyGet fun w =>
      (w.seqNo, { w with timers := w.timers ++ [(w.clock + delay, w.seqNo, f)], seqNo := w.seqNo + 1 })
    pure (num (id + 1))
  | .taNew k => do
    match Conv.toIntegerOrInf vs.a0.toNum with
    | .fin n =>
      if 0 ≤ n ∧ n ≤ 2 ^ 53 - 1 then do
        let a ← JS.alloc (.tarr k) (Array.replicate n.toNat (0 : BitVec k.width))
        pure (.tarr a)
      else JS.throwJS .rangeError s!"Invalid typed array length: {(NumFormat.toJSString vs.a0.toNum).toLeanString}"
    | _ => JS.throwJS .rangeError s!"Invalid typed array length: {(NumFormat.toJSString vs.a0.toNum).toLeanString}"
  | .taOfArr k => do
    let c ← readArr k.elem vs.a0.arrAddr
    let a ← JS.alloc (.tarr k) (c.map k.toElem)
    pure (.tarr a)
  | .taLength k => do
    let c ← readTA k vs.a0.tarrAddr
    pure (num c.size)
  | .taGet k => do
    let c ← readTA k vs.a0.tarrAddr
    match index? vs.a1 with
    | some i => if h : i < c.size then pure (k.ofElem c[i]) else JS.panic "typed array index out of bounds"
    | none => JS.panic "typed array read at a non-index key"
  | .taSet k => do
    let c ← readTA k vs.a0.tarrAddr
    match index? vs.a1 with
    | some i =>
      if h : i < c.size then do
        writeTA k vs.a0.tarrAddr (c.set i (k.toElem vs.a2) h)
        pure .undef
      else pure .undef
    | none => pure .undef
  | .taFill k => do
    let c ← readTA k vs.a0.tarrAddr
    writeTA k vs.a0.tarrAddr (Array.replicate c.size (k.toElem vs.a1))
    pure vs.a0
  | .taSlice k => do
    let c ← readTA k vs.a0.tarrAddr
    let st := Conv.relIndex (toInt vs.a1) c.size
    let fin := match vs.a2 with
      | .none => c.size
      | .some e => Conv.relIndex (toInt e) c.size
    let a ← JS.alloc (.tarr k) (c.extract st fin)
    pure (.tarr a)
  | _ => JS.panic "unreachable: callback builtin evaluated as basic"

mutual

/-- Expressions. Expressions do not change the environment. -/
def evalE (I : Impl) (P : Program TT) {Γ : Ctx} {t : Ty} (e : Expr TT Γ t) (env : Env TT Γ) :
    JS TT (Val TT t) :=
  match e with
  | .lit l => pure l.val
  | .var x => pure (env.get x)
  | .gget g => readBox _ g.idx
  | .prim op args => do
    let vs ← evalArgs I P args env
    JS.liftExcept (op.eval I vs)
  | .builtin b args => do
    let vs ← evalArgs I P args env
    if b.hasCallback then evalBuiltin I P b vs else evalBuiltinBasic b vs
  | .and a b => do
    let x ← evalE I P a env
    if x.toBool then evalE I P b env else pure (.bool false)
  | .or a b => do
    let x ← evalE I P a env
    if x.toBool then pure (.bool true) else evalE I P b env
  | .cond c a b => do
    let x ← evalE I P c env
    if x.toBool then evalE I P a env else evalE I P b env
  | .letE _ a body => do
    let v ← evalE I P a env
    evalE I P body (.cons v env)
  | .call f args => do
    let vs ← evalArgs I P args env
    callFun I P f vs
  | .app f args => do
    let fv ← evalE I P f env
    let vs ← evalArgs I P args env
    applyFn I P fv vs
  | .lam Δ caps l => pure (.clo Δ l (caps.capture env))
  | .funVal f => pure (.fnRef f)
  | .mkTup args => do
    let vs ← evalArgs I P args env
    pure (.tup vs)
  | .getTup a m => do
    let v ← evalE I P a env
    pure (v.tupVals.get m)
  | .mkRec args => do
    let vs ← evalArgs I P args env
    pure (.record vs)
  | .getRec a m => do
    let v ← evalE I P a env
    pure (v.recVals.get m)
  | .newObj c fs => do
    let a ← JS.alloc (.obj c fs.types) (OVals.empty fs.types)
    pure (.obj a)
  | .getField (c := c) (fs := fs) o m => do
    let r ← evalE I P o env
    let cell ← readObj c fs.types r.objAddr
    match cell.get? m with
    | some v => pure v
    | none => JS.panic "read of an uninitialised field"
  | .fold a => do
    let v ← evalE I P a env
    pure (.fold v)
  | .unfold a => do
    let v ← evalE I P a env
    pure v.unfold
  | .none => pure .none
  | .some a => do
    let v ← evalE I P a env
    pure (.some v)
  | .unwrap a => do
    let v ← evalE I P a env
    match v with
    | .some x => pure x
    | .none => JS.panic "non-null assertion on undefined"
  | .caseOpt a d f => do
    let v ← evalE I P a env
    match v with
    | .none => evalE I P d env
    | .some x => evalE I P f (.cons x env)
  | .inj m a => do
    let v ← evalE I P a env
    pure (.inj m v)
  | .caseU a alts => do
    let v ← evalE I P a env
    match v with
    | .inj m x => evalE I P (alts.select m) (.cons x env)
  | .enumLit i => pure (.enum i)
  | .extern (args := ts) (t := t) name args => do
    let vs ← evalArgs I P args env
    match ← extAnswer name ts t vs with
    | .ok v => JS.materialize v
    | .error e => throw (.thrown e)
  | .externAsync (args := ts) (t := t) name args => do
    let vs ← evalArgs I P args env
    let out ← extAnswer name ts t vs
    let out' ← match out with
      | .ok v => do pure (.ok (← JS.materialize v))
      | .error e => pure (.error e)
    let p ← newPromise t
    settle t p out'
    pure (.promise p)
partial_fixpoint

/-- Arguments, left to right. -/
def evalArgs (I : Impl) (P : Program TT) {Γ : Ctx} {ts : List Ty} (args : Args TT Γ ts)
    (env : Env TT Γ) : JS TT (Vals TT ts) :=
  match args with
  | .nil => pure .nil
  | .cons a rest => do
    let v ← evalE I P a env
    let vs ← evalArgs I P rest env
    pure (.cons v vs)
partial_fixpoint

/-- Blocks. Declarations are scoped: the environment returned has the shape of `Γ`. -/
def evalB (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) :=
  match b with
  | .nil => pure (.normal, env)
  | .seq s rest => do
    let (c, env') ← evalS I P s env
    match c with
    | .normal => evalB I P rest env'
    | c => pure (c, env')
  | .decl _ e rest => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v =>
      let (c, env') ← evalB I P rest (.cons v env)
      pure (c, env'.tail)
  | .await _ _ _ => JS.panic "await outside an async function body"
partial_fixpoint

/-- Statements. -/
def evalS (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (s : Stmt TT Γ ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) :=
  match s with
  | .expr e => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok _ => pure (.normal, env)
  | .assign x e => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.normal, env.set x v)
  | .gset g e => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => do
      JS.write (.box _) g.idx (some v)
      pure (.normal, env)
  | .setField (c := c) (fs := fs) o m e => do
    match ← catchThrown (do
        let r ← evalE I P o env
        let v ← evalE I P e env
        let cell ← readObj c fs.types r.objAddr
        writeObj c fs.types r.objAddr (cell.set m v)) with
    | .error ex => pure (.exc ex, env)
    | .ok _ => pure (.normal, env)
  | .ite c b1 b2 => do
    match ← catchThrown (evalE I P c env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => if v.toBool then evalB I P b1 env else evalB I P b2 env
  | .while c body => evalLoop I P c body .nil env
  | .forLoop c body step => evalLoop I P c body step env
  | .doWhile body c => evalDo I P body c env
  | .forOf a body => do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok r => evalForOf I P r.arrAddr 0 body env
  | .forOfMap a body => do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok r => evalForOfMap I P r.mapAddr 0 body env
  | .forOfSet a body => do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok r => evalForOfSet I P r.setAddr 0 body env
  | .forOfStr a body => do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => evalForOfStr I P (Conv.codePointStrs v.toStr.units) body env
  | .brk n => pure (.brk n, env)
  | .cont n => pure (.cont n, env)
  | .ret e => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.ret v, env)
  | .retP e => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.retP v.promAddr, env)
  | .throw e => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.exc v.toErr, env)
  | .try body h fin => do
    let (c1, env1) ← evalB I P body env
    let (c2, env2) ← match c1 with
      | .exc ex => do
        let (c, env') ← evalB I P h (.cons (.err ex) env1)
        pure (c, env'.tail)
      | c => pure (c, env1)
    let (c3, env3) ← evalB I P fin env2
    match c3 with
    | .normal => pure (c2, env3)
    | c => pure (c, env3)
  | .tryFin body fin => do
    let (c1, env1) ← evalB I P body env
    let (c3, env3) ← evalB I P fin env1
    match c3 with
    | .normal => pure (c1, env3)
    | c => pure (c, env3)
  | .caseOptS a bn bs => do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok .none => evalB I P bn env
    | .ok (.some x) => do
      let (c, env') ← evalB I P bs (.cons x env)
      pure (c, env'.tail)
  | .caseUS a alts => do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok (.inj m x) => do
      let (c, env') ← evalB I P (alts.select m) (.cons x env)
      pure (c, env'.tail)
  | .block b => evalB I P b env
  | .breakable b => do
    let (c, env') ← evalB I P b env
    match c with
    | .brk 0 => pure (.normal, env')
    | .brk (n + 1) => pure (.brk n, env')
    | c => pure (c, env')
partial_fixpoint

/-- `while (c) body` and `for (; c; step) body` (`step` is empty for `while`). -/
def evalLoop (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (env : Env TT Γ) : JS TT (Completion TT ρ × Env TT Γ) := do
  match ← catchThrown (evalE I P c env) with
  | .error ex => pure (.exc ex, env)
  | .ok v =>
    if v.toBool then do
      let (cb, env1) ← evalB I P body env
      match cb with
      | .normal | .cont 0 => do
        let (cs, env2) ← evalB I P step env1
        match cs with
        | .normal => evalLoop I P c body step env2
        | other => pure (other, env2)
      | .brk 0 => pure (.normal, env1)
      | .brk (n + 1) => pure (.brk n, env1)
      | .cont (n + 1) => pure (.cont n, env1)
      | other => pure (other, env1)
    else pure (.normal, env)
partial_fixpoint

/-- `do body while (c)`. -/
def evalDo (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (body : Block TT Γ ρ) (c : Expr TT Γ .bool)
    (env : Env TT Γ) : JS TT (Completion TT ρ × Env TT Γ) := do
  let (cb, env1) ← evalB I P body env
  match cb with
  | .normal | .cont 0 => do
    match ← catchThrown (evalE I P c env1) with
    | .error ex => pure (.exc ex, env1)
    | .ok v => if v.toBool then evalDo I P body c env1 else pure (.normal, env1)
  | .brk 0 => pure (.normal, env1)
  | .brk (n + 1) => pure (.brk n, env1)
  | .cont (n + 1) => pure (.cont n, env1)
  | other => pure (other, env1)
partial_fixpoint

/-- `for (const x of arr)`: the array iterator re-reads the length and the element at
each step (live iteration). -/
def evalForOf (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Nat) (i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) : JS TT (Completion TT ρ × Env TT Γ) := do
  let cell ← readArr t a
  if h : i < cell.size then do
    let (cb, env1) ← evalB I P body (.cons cell[i] env)
    match cb with
    | .normal | .cont 0 => evalForOf I P a (i + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)
  else pure (.normal, env)
partial_fixpoint

/-- `for (const [k, v] of map)` (live iteration over the entry list). -/
def evalForOfMap (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty} (a : Nat) (i : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) :
    JS TT (Completion TT ρ × Env TT Γ) := do
  let m ← readMap k v a
  match m.nextFrom i with
  | none => pure (.normal, env)
  | some (j, key, val) => do
    let (cb, env1) ← evalB I P body (.cons (.tup (.cons key (.cons val .nil))) env)
    match cb with
    | .normal | .cont 0 => evalForOfMap I P a (j + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)
partial_fixpoint

/-- `for (const x of set)` (live iteration over the entry list). -/
def evalForOfSet (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Nat) (i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) : JS TT (Completion TT ρ × Env TT Γ) := do
  let m ← readSet t a
  match m.nextFrom i with
  | none => pure (.normal, env)
  | some (j, x, _) => do
    let (cb, env1) ← evalB I P body (.cons x env)
    match cb with
    | .normal | .cont 0 => evalForOfSet I P a (j + 1) body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)
partial_fixpoint

/-- `for (const ch of str)`: iteration over code points. -/
def evalForOfStr (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cps : List JSStr)
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) : JS TT (Completion TT ρ × Env TT Γ) :=
  match cps with
  | [] => pure (.normal, env)
  | ch :: rest => do
    let (cb, env1) ← evalB I P body (.cons (.str ch) env)
    match cb with
    | .normal | .cont 0 => evalForOfStr I P rest body env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)
partial_fixpoint

/-- Call a top-level function. -/
def callFun (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : FunRef args ret)
    (vs : Vals TT args.toList) : JS TT (Val TT ret) :=
  match P.funs[f.idx]? with
  | some d =>
    if h : d.args = args ∧ d.ret = ret then
      applyLam I P (h.1 ▸ h.2 ▸ d.lam) .nil vs
    else JS.panic "ill-typed function reference"
  | none => JS.panic "unknown function"
partial_fixpoint

/-- Apply a function value. -/
def applyFn (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (fv : Val TT (.fn args ret))
    (vs : Vals TT args.toList) : JS TT (Val TT ret) :=
  match fv with
  | .clo _ l cenv => applyLam I P l cenv vs
  | .fnRef f => callFun I P f vs
  | .resolver (t := t) p => do
    resolveOnce t p (.ok vs.head)
    pure .undef
  | .rejecter t p => do
    resolveOnce t p (.error vs.head.toErr)
    pure .undef
partial_fixpoint

/-- Apply a function literal to arguments in its captured environment. -/
def applyLam (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} {Δ : Ctx} (l : Lam TT args ret Δ)
    (cenv : Env TT Δ) (vs : Vals TT args.toList) : JS TT (Val TT ret) :=
  match l with
  | .sync params h body => do
    let (c, _) ← evalB I P body ((vs.toEnv params h).append cenv)
    finishSync _ c
  | .async (ret := ρ) params h body => do
    let p ← newPromise ρ
    let step ← execAB I P body ((vs.toEnv params h).append cenv) .done
    handleStep p step
    pure (.promise p)
partial_fixpoint


/-- Async bodies run in continuation-passing style with first-order continuations; a
statement without `await` is executed by the big-step evaluator. -/
def execAB (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ)
    (k : AK TT ρ Γ) : JS TT (AStep TT ρ) :=
  match b with
  | .nil => applyK I P k .normal env
  | .seq s rest => execAS I P s env (.seq rest k)
  | .decl _ e rest => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => applyK I P k (.exc ex) env
    | .ok v => execAB I P rest (.cons v env) (.pop k)
  | .await s e rest => do
    match ← catchThrown (evalE I P e env) with
    | .error ex => applyK I P k (.exc ex) env
    | .ok p => pure (.suspended p.promAddr (.mk s rest env k))
partial_fixpoint

def execAS (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (s : Stmt TT Γ ρ) (env : Env TT Γ)
    (k : AK TT ρ Γ) : JS TT (AStep TT ρ) :=
  if s.hasAwait then
    match s with
    | .ite c b1 b2 => do
      match ← catchThrown (evalE I P c env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok v => execAB I P (if v.toBool then b1 else b2) env k
    | .while c b => loopA I P c b .nil env k
    | .forLoop c b st => loopA I P c b st env k
    | .doWhile b c => execAB I P b env (.doBody b c k)
    | .forOf a b => do
      match ← catchThrown (evalE I P a env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok r => forOfA I P r.arrAddr 0 b env k
    | .forOfMap a b => do
      match ← catchThrown (evalE I P a env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok r => forOfMapA I P r.mapAddr 0 b env k
    | .forOfSet a b => do
      match ← catchThrown (evalE I P a env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok r => forOfSetA I P r.setAddr 0 b env k
    | .forOfStr a b => do
      match ← catchThrown (evalE I P a env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok v => forOfStrA I P (Conv.codePointStrs v.toStr.units) b env k
    | .try b h f => execAB I P b env (.catchFrame h f k)
    | .tryFin b f => execAB I P b env (.finFrame f k)
    | .caseOptS a bn bs => do
      match ← catchThrown (evalE I P a env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok .none => execAB I P bn env k
      | .ok (.some x) => execAB I P bs (.cons x env) (.pop k)
    | .caseUS a alts => do
      match ← catchThrown (evalE I P a env) with
      | .error ex => applyK I P k (.exc ex) env
      | .ok (.inj m x) => execAB I P (alts.select m) (.cons x env) (.pop k)
    | .block b => execAB I P b env k
    | .breakable b => execAB I P b env (.brkFrame k)
    | s => do
      let (c, env') ← evalS I P s env
      applyK I P k c env'
  else do
    let (c, env') ← evalS I P s env
    applyK I P k c env'
partial_fixpoint

def loopA (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool) (b st : Block TT Γ ρ)
    (env : Env TT Γ) (k : AK TT ρ Γ) : JS TT (AStep TT ρ) := do
  match ← catchThrown (evalE I P c env) with
  | .error ex => applyK I P k (.exc ex) env
  | .ok v => if v.toBool then execAB I P b env (.loopBody c b st k) else applyK I P k .normal env
partial_fixpoint

def forOfA (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Nat) (i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (k : AK TT ρ Γ) : JS TT (AStep TT ρ) := do
  let cell ← readArr t a
  if h : i < cell.size then execAB I P body (.cons cell[i] env) (.forOfBody a i body k)
  else applyK I P k .normal env
partial_fixpoint

def forOfMapA (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {kt vt : Ty} (a : Nat) (i : Nat)
    (body : Block TT (⟨.tup (.cons kt (.cons vt .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ)
    (k : AK TT ρ Γ) : JS TT (AStep TT ρ) := do
  let m ← readMap kt vt a
  match m.nextFrom i with
  | none => applyK I P k .normal env
  | some (j, key, val) =>
    execAB I P body (.cons (.tup (.cons key (.cons val .nil))) env) (.forOfMapBody a j body k)
partial_fixpoint

def forOfSetA (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Nat) (i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (k : AK TT ρ Γ) : JS TT (AStep TT ρ) := do
  let m ← readSet t a
  match m.nextFrom i with
  | none => applyK I P k .normal env
  | some (j, x, _) => execAB I P body (.cons x env) (.forOfSetBody a j body k)
partial_fixpoint

def forOfStrA (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (cps : List JSStr)
    (body : Block TT (⟨.str, false⟩ :: Γ) ρ) (env : Env TT Γ) (k : AK TT ρ Γ) : JS TT (AStep TT ρ) :=
  match cps with
  | [] => applyK I P k .normal env
  | ch :: rest => execAB I P body (.cons (.str ch) env) (.forOfStrBody rest body k)
partial_fixpoint

/-- Apply a continuation to a completion. -/
def applyK (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (k : AK TT ρ Γ) (c : Completion TT ρ)
    (env : Env TT Γ) : JS TT (AStep TT ρ) :=
  match k with
  | .done => pure (.finished c)
  | .seq rest k' => match c with
    | .normal => execAB I P rest env k'
    | c => applyK I P k' c env
  | .pop k' => applyK I P k' c env.tail
  | .loopBody cnd b st k' => match c with
    | .normal | .cont 0 => execAB I P st env (.loopStep cnd b st k')
    | .brk 0 => applyK I P k' .normal env
    | .brk (n + 1) => applyK I P k' (.brk n) env
    | .cont (n + 1) => applyK I P k' (.cont n) env
    | c => applyK I P k' c env
  | .loopStep cnd b st k' => match c with
    | .normal => loopA I P cnd b st env k'
    | c => applyK I P k' c env
  | .doBody b cnd k' => match c with
    | .normal | .cont 0 => do
      match ← catchThrown (evalE I P cnd env) with
      | .error ex => applyK I P k' (.exc ex) env
      | .ok v => if v.toBool then execAB I P b env (.doBody b cnd k') else applyK I P k' .normal env
    | .brk 0 => applyK I P k' .normal env
    | .brk (n + 1) => applyK I P k' (.brk n) env
    | .cont (n + 1) => applyK I P k' (.cont n) env
    | c => applyK I P k' c env
  | .forOfBody a i body k' => match c with
    | .normal | .cont 0 => forOfA I P a (i + 1) body env.tail k'
    | .brk 0 => applyK I P k' .normal env.tail
    | .brk (n + 1) => applyK I P k' (.brk n) env.tail
    | .cont (n + 1) => applyK I P k' (.cont n) env.tail
    | c => applyK I P k' c env.tail
  | .forOfMapBody a i body k' => match c with
    | .normal | .cont 0 => forOfMapA I P a (i + 1) body env.tail k'
    | .brk 0 => applyK I P k' .normal env.tail
    | .brk (n + 1) => applyK I P k' (.brk n) env.tail
    | .cont (n + 1) => applyK I P k' (.cont n) env.tail
    | c => applyK I P k' c env.tail
  | .forOfSetBody a i body k' => match c with
    | .normal | .cont 0 => forOfSetA I P a (i + 1) body env.tail k'
    | .brk 0 => applyK I P k' .normal env.tail
    | .brk (n + 1) => applyK I P k' (.brk n) env.tail
    | .cont (n + 1) => applyK I P k' (.cont n) env.tail
    | c => applyK I P k' c env.tail
  | .forOfStrBody rest body k' => match c with
    | .normal | .cont 0 => forOfStrA I P rest body env.tail k'
    | .brk 0 => applyK I P k' .normal env.tail
    | .brk (n + 1) => applyK I P k' (.brk n) env.tail
    | .cont (n + 1) => applyK I P k' (.cont n) env.tail
    | c => applyK I P k' c env.tail
  | .catchFrame h f k' => match c with
    | .exc ex => execAB I P h (.cons (.err ex) env) (.pop (.finFrame f k'))
    | c => execAB I P f env (.finRestore c k')
  | .finFrame f k' => execAB I P f env (.finRestore c k')
  | .finRestore pending k' => match c with
    | .normal => applyK I P k' pending env
    | c => applyK I P k' c env
  | .brkFrame k' => match c with
    | .brk 0 => applyK I P k' .normal env
    | .brk (n + 1) => applyK I P k' (.brk n) env
    | c => applyK I P k' c env
partial_fixpoint

/-- Stable merge of two sorted lists with a JavaScript comparator (`cmp(x, y) > 0` puts
`y` first; NaN counts as 0). -/
def mergeL (I : Impl) (P : Program TT) {t : Ty} (cmp : Val TT (.fn (.cons t (.cons t .nil)) .num))
    (xs ys : List (Val TT t)) : JS TT (List (Val TT t)) :=
  match xs, ys with
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs', y :: ys' => do
    let r ← applyFn I P cmp (.cons x (.cons y .nil))
    if Conv.isPos r.toNum then do
      let rest ← mergeL I P cmp (x :: xs') ys'
      pure (y :: rest)
    else do
      let rest ← mergeL I P cmp xs' (y :: ys')
      pure (x :: rest)
partial_fixpoint

/-- Stable merge sort with a JavaScript comparator. For a consistent comparator every
stable sort gives the same result, so this is implementation-independent. -/
def sortL (I : Impl) (P : Program TT) {t : Ty} (cmp : Val TT (.fn (.cons t (.cons t .nil)) .num))
    (xs : List (Val TT t)) : JS TT (List (Val TT t)) :=
  if xs.length ≤ 1 then pure xs
  else do
    let l ← sortL I P cmp (xs.take (xs.length / 2))
    let r ← sortL I P cmp (xs.drop (xs.length / 2))
    mergeL I P cmp l r
partial_fixpoint

/-- `map.forEach(cb)`: live iteration over the entry list. -/
def mapForEachL (I : Impl) (P : Program TT) {k v : Ty}
    (f : Val TT (.fn (.cons v (.cons k (.cons (.map k v) .nil))) .undef)) (a : Nat) (i : Nat) :
    JS TT Unit := do
  let m ← readMap k v a
  match m.nextFrom i with
  | none => pure ()
  | some (j, key, val) => do
    let _ ← applyFn I P f (.cons val (.cons key (.cons (.map a) .nil)))
    mapForEachL I P f a (j + 1)
partial_fixpoint

/-- `set.forEach(cb)`: live iteration over the entry list. -/
def setForEachL (I : Impl) (P : Program TT) {t : Ty}
    (f : Val TT (.fn (.cons t (.cons t (.cons (.set t) .nil))) .undef)) (a : Nat) (i : Nat) :
    JS TT Unit := do
  let m ← readSet t a
  match m.nextFrom i with
  | none => pure ()
  | some (j, x, _) => do
    let _ ← applyFn I P f (.cons x (.cons x (.cons (.set a) .nil)))
    setForEachL I P f a (j + 1)
partial_fixpoint

/-- Library operations that call back into user code (the rest is `evalBuiltinBasic`).
Callbacks receive `(element, index, array)` like in JavaScript; elements are re-read at every
step, so mutation by a callback is observed as specified, and an element that disappeared
makes a `T`-typed read panic. -/
def evalBuiltin (I : Impl) (P : Program TT) {args : List Ty} {t : Ty} (b : Builtin args t)
    (vs : Vals TT args) : JS TT (Val TT t) :=
  match b with
  | .arrSort t => do
    let a := vs.a0
    let cmp := vs.a1
    let c ← readArr t a.arrAddr
    let sorted ← sortL I P cmp c.toList
    writeArr t a.arrAddr sorted.toArray
    pure a
  | .arrMap t u => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let res ← JS.alloc (.arr u) #[]
    let out ← (List.range len).foldlM (fun (acc : Array (Val TT u)) k => do
      let c ← readArr t a.arrAddr
      if h : k < c.size then do
        let y ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
        pure (acc.push y)
      else JS.panic "array shrank during map (the result would have a hole)") #[]
    writeArr u res out
    pure (.arr res)
  | .arrFilter t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let res ← JS.alloc (.arr t) #[]
    let out ← (List.range len).foldlM (fun (acc : Array (Val TT t)) k => do
      let c ← readArr t a.arrAddr
      if h : k < c.size then do
        let keep ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
        pure (if keep.toBool then acc.push c[k] else acc)
      else pure acc) #[]
    writeArr t res out
    pure (.arr res)
  | .arrForEach t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    (List.range len).forM fun k => do
      let c ← readArr t a.arrAddr
      if h : k < c.size then do
        let _ ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
        pure ()
      else pure ()
    pure .undef
  | .arrFind t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let r ← (List.range len).foldlM (fun (st : Option (Val TT t)) k => do
      match st with
      | some x => pure (some x)
      | none => do
        let c ← readArr t a.arrAddr
        if h : k < c.size then do
          let ok ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
          pure (if ok.toBool then some c[k] else none)
        else JS.panic "find read past the end of a shrunk array") none
    pure (match r with | some x => .some x | none => .none)
  | .arrFindIndex t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let r ← (List.range len).foldlM (fun (st : Option Nat) k => do
      match st with
      | some j => pure (some j)
      | none => do
        let c ← readArr t a.arrAddr
        if h : k < c.size then do
          let ok ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
          pure (if ok.toBool then some k else none)
        else JS.panic "findIndex read past the end of a shrunk array") none
    pure (match r with | some j => num j | none => .num (F64.ofInt (-1)))
  | .arrFindLast t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let r ← (List.range len).reverse.foldlM (fun (st : Option (Val TT t)) k => do
      match st with
      | some x => pure (some x)
      | none => do
        let c ← readArr t a.arrAddr
        if h : k < c.size then do
          let ok ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
          pure (if ok.toBool then some c[k] else none)
        else JS.panic "findLast read past the end of a shrunk array") none
    pure (match r with | some x => .some x | none => .none)
  | .arrFindLastIndex t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let r ← (List.range len).reverse.foldlM (fun (st : Option Nat) k => do
      match st with
      | some j => pure (some j)
      | none => do
        let c ← readArr t a.arrAddr
        if h : k < c.size then do
          let ok ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
          pure (if ok.toBool then some k else none)
        else JS.panic "findLastIndex read past the end of a shrunk array") none
    pure (match r with | some j => num j | none => .num (F64.ofInt (-1)))
  | .arrSome t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let r ← (List.range len).foldlM (fun (st : Bool) k => do
      if st then pure true
      else do
        let c ← readArr t a.arrAddr
        if h : k < c.size then do
          let ok ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
          pure ok.toBool
        else pure false) false
    pure (.bool r)
  | .arrEvery t => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let r ← (List.range len).foldlM (fun (st : Bool) k => do
      if !st then pure false
      else do
        let c ← readArr t a.arrAddr
        if h : k < c.size then do
          let ok ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
          pure ok.toBool
        else pure true) true
    pure (.bool r)
  | .arrFlatMap t u => do
    let a := vs.a0
    let f := vs.a1
    let len := (← readArr t a.arrAddr).size
    let res ← JS.alloc (.arr u) #[]
    let out ← (List.range len).foldlM (fun (acc : Array (Val TT u)) k => do
      let c ← readArr t a.arrAddr
      if h : k < c.size then do
        let r ← applyFn I P f (.cons c[k] (.cons (num k) (.cons a .nil)))
        let inner ← readArr u r.arrAddr
        pure (acc ++ inner)
      else pure acc) #[]
    writeArr u res out
    pure (.arr res)
  | .arrReduce t _ => do
    let a := vs.a0
    let f := vs.a1
    let init := vs.a2
    let len := (← readArr t a.arrAddr).size
    (List.range len).foldlM (fun acc k => do
      let c ← readArr t a.arrAddr
      if h : k < c.size then applyFn I P f (.cons acc (.cons c[k] (.cons (num k) (.cons a .nil))))
      else pure acc) init
  | .arrReduce1 t => do
    let a := vs.a0
    let f := vs.a1
    let c0 ← readArr t a.arrAddr
    if h : 0 < c0.size then
      (List.range c0.size).tail.foldlM (fun acc k => do
        let c ← readArr t a.arrAddr
        if h : k < c.size then applyFn I P f (.cons acc (.cons c[k] (.cons (num k) (.cons a .nil))))
        else pure acc) c0[0]
    else JS.throwJS .typeError "Reduce of empty array with no initial value"
  | .arrReduceRight t _ => do
    let a := vs.a0
    let f := vs.a1
    let init := vs.a2
    let len := (← readArr t a.arrAddr).size
    (List.range len).reverse.foldlM (fun acc k => do
      let c ← readArr t a.arrAddr
      if h : k < c.size then applyFn I P f (.cons acc (.cons c[k] (.cons (num k) (.cons a .nil))))
      else pure acc) init
  | .arrFromFn t => do
    let n := vs.a0
    let f := vs.a1
    let len : Nat ← match toInt n with
      | .fin k => pure k.toNat
      | .negInf => pure 0
      | .posInf => JS.throwJS .rangeError "Invalid array length"
    let res ← JS.alloc (.arr t) #[]
    let out ← (List.range len).foldlM (fun (acc : Array (Val TT t)) k => do
      let y ← applyFn I P f (.cons .undef (.cons (num k) .nil))
      pure (acc.push y)) #[]
    writeArr t res out
    pure (.arr res)
  | .mapForEach _ _ => do
    let m := vs.a0
    let f := vs.a1
    mapForEachL I P f m.mapAddr 0
    pure .undef
  | .setForEach _ => do
    let s := vs.a0
    let f := vs.a1
    setForEachL I P f s.setAddr 0
    pure .undef
  | .promNew t => do
    let ex := vs.a0
    let p ← newPromise t
    match ← catchThrown (applyFn I P ex (.cons (.resolver p) (.cons (.rejecter t p) .nil))) with
    | .error e => resolveOnce t p (.error e)
    | .ok _ => pure ()
    pure (.promise p)
  | b => evalBuiltinBasic b vs
partial_fixpoint

end

/-- Resume a suspended async body with the outcome of the awaited promise. -/
def resume (I : Impl) (P : Program TT) {ρ t : Ty} (r : Resumption TT ρ t)
    (out : Except ErrVal (Val TT t)) : JS TT (AStep TT ρ) :=
  match r, out with
  | .mk _ rest env k, .ok v => execAB I P rest (.cons v env) (.pop k)
  | .mk _ _ env k, .error e => applyK I P k (.exc e) env

/-- Run one microtask (ECMA-262 PromiseReactionJob / NewPromiseResolveThenableJob). -/
def runJob (I : Impl) (P : Program TT) : Job TT → JS TT Unit
  | .react (t := t) r out =>
    match r, out with
    | .await res p, out => do
      let step ← resume I P res out
      handleStep p step
    | .then (u := u) f target, .ok v => do
      match ← catchThrown (applyFn I P f (.cons v .nil)) with
      | .ok y => settle u target (.ok y)
      | .error e => settle u target (.error e)
    | .then (u := u) _ target, .error e => settle u target (.error e)
    | .thenP (u := u) f target, .ok v => do
      match ← catchThrown (applyFn I P f (.cons v .nil)) with
      | .ok q => JS.enqueue (.resolveThenable u target q.promAddr)
      | .error e => settle u target (.error e)
    | .thenP (u := u) _ target, .error e => settle u target (.error e)
    | .catch _ target, .ok v => settle t target (.ok v)
    | .catch f target, .error e => do
      match ← catchThrown (applyFn I P f (.cons (.err e) .nil)) with
      | .ok y => settle t target (.ok y)
      | .error e' => settle t target (.error e')
    | .finally f target, out => do
      match ← catchThrown (applyFn I P f .nil) with
      | .error e => settle t target (.error e)
      | .ok _ => do
        let p2 ← newPromise .undef
        settle .undef p2 (.ok .undef)
        let p3 ← newPromise t
        addReaction .undef p2 (.const p3 out)
        JS.enqueue (.resolveThenable t target p3)
    | .forward target, out => settle t target out
    | .const (u := u) target out', _ => settle u target out'
    | .allSlot target slots idx, .ok v => do
      let c ← readArr (.opt t) slots
      let c' := c.set! idx (.some v)
      writeArr (.opt t) slots c'
      let vals := c'.toList.filterMap fun | .some x => some x | .none => none
      if vals.length = c'.size then do
        let res ← allocArr t vals.toArray
        settle (.arr t) target (.ok res)
      else pure ()
    | .allSlot target _ _, .error e => settle (.arr t) target (.error e)
    | .allTup ts target slots a, .ok v => do
      JS.write (.box t) a (some v)
      tupDone ts target slots
    | .allTup ts target _ _, .error e => settle (.tup ts) target (.error e)
    | .settledSlot target slots idx, out => do
      let c ← readArr (.opt t.settled) slots
      let c' := c.set! idx (.some (settledVal out))
      writeArr (.opt t.settled) slots c'
      let vals := c'.toList.filterMap fun | .some x => some x | .none => none
      if vals.length = c'.size then do
        let res ← allocArr t.settled vals.toArray
        settle (.arr t.settled) target (.ok res)
      else pure ()
    | .settledTup ts target slots a, out => do
      JS.write (.box t.settled) a (some (settledVal out))
      tupDone (ts.map Ty.settled) target slots
  | .resolveThenable t target q => addReaction t q (.forward target)
  | .callback f => do
    let _ ← applyFn I P f .nil
    pure ()

/-- Run microtasks until the queue is empty. -/
def drain (I : Impl) (P : Program TT) : JS TT Unit := do
  let w ← get
  match w.jobs with
  | [] => pure ()
  | j :: rest => do
    set { w with jobs := rest }
    runJob I P j
    drain I P
partial_fixpoint

/-- The earliest pending timer (by due time, then creation order). -/
def earliestTimer (ts : List (Nat × Nat × Val TT (.fn .nil .undef))) :
    Option (Nat × Nat × Val TT (.fn .nil .undef)) :=
  ts.foldl (fun best x => match best with
    | none => some x
    | some b => if x.1 < b.1 ∨ (x.1 = b.1 ∧ x.2.1 < b.2.1) then some x else some b) none

/-- The event loop: drain microtasks, then run timers in order, draining after each. A
promise still rejected without a handler once the queue is empty ends the run with that
error, as Node does (`--unhandled-rejections=throw`, the default). -/
def eventLoop (I : Impl) (P : Program TT) : JS TT Unit := do
  drain I P
  let w ← get
  match w.unhandled with
  | (_, e) :: _ => throw (.thrown e)
  | [] =>
  match earliestTimer w.timers with
  | none => pure ()
  | some (due, sq, f) => do
    set { w with timers := w.timers.filter (fun x => x.2.1 != sq), clock := max w.clock due }
    let _ ← applyFn I P f .nil
    eventLoop I P
partial_fixpoint

/-- Run a whole program: allocate the module variables, run the module body, then the
event loop. An exception escaping the module body or a callback is reported as `thrown`. -/
def runProgram (I : Impl) (P : Program TT) : JS TT Unit := do
  for t in P.globals do
    let _ ← JS.alloc (.box t) none
  let (c, _) ← evalB I P P.main .nil
  match c with
  | .exc e => throw (.thrown e)
  | _ => eventLoop I P

/-- The initial world (empty heap, no output). -/
def World.init (TT : TypeTable) : World TT := { heap := ∅, next := 0 }

/-- Outcome and console output of a whole run; `none` means divergence. -/
def runOutput (I : Impl) (P : Program TT) : Option (Except Exc Unit × List JSStr) :=
  ((runProgram I P).run.run (World.init TT)).map fun (r, w) => (r, w.out)

end StrictTS
