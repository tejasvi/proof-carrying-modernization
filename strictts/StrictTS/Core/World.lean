/-
StrictTS core: completions, async continuations, heap cells, the world state and the
evaluation monad.

The monad is the standard transformer stack `ExceptT Exc (StateT (World TT) Option)`:
`Option` models divergence (least fixpoint, via `partial_fixpoint`), `StateT` the world
(heap, console output, job queue), `ExceptT` exceptions. Being a standard stack, it works
with `Std.Do`/`mvcgen` and with the monotonicity machinery of `partial_fixpoint`.
-/
import StrictTS.Core.Val
import Std.Data.ExtDHashMap

namespace StrictTS

/-- Exceptions of the evaluation monad. `thrown` is a JavaScript exception. `panic` marks a
step outside the sound subset: an access TypeScript typed as `T` that would produce
`undefined` or a hole, a missing `return`, a dangling reference in a hand-written initial
heap, ... Panics are not catchable; proofs show they do not happen. -/
inductive Exc where
  | thrown (e : ErrVal)
  | panic (msg : String)
  deriving Repr

/-- Completion records of statements (ECMA-262 §6.2.4). -/
inductive Completion (TT : TypeTable) (ρ : Ty) where
  | normal
  | brk (n : Nat)
  | cont (n : Nat)
  | ret (v : Val TT ρ)
  /-- an async body returned a promise (its address) -/
  | retP (p : Nat)
  /-- a JavaScript exception -/
  | exc (e : ErrVal)

/-- First-order (defunctionalised) continuations of async function bodies: `AK TT ρ Γ`
continues after a statement executed in context `Γ` of an async body returning `ρ`. -/
inductive AK (TT : TypeTable) (ρ : Ty) : Ctx → Type where
  | done {Γ : Ctx} : AK TT ρ Γ
  | seq {Γ : Ctx} : Block TT Γ ρ → AK TT ρ Γ → AK TT ρ Γ
  | pop {Γ : Ctx} {s : Slot} : AK TT ρ Γ → AK TT ρ (s :: Γ)
  /-- after the body of `while`/`for` (condition, body, step block) -/
  | loopBody {Γ : Ctx} : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → AK TT ρ Γ → AK TT ρ Γ
  /-- after the step block of a `for` loop -/
  | loopStep {Γ : Ctx} : Expr TT Γ .bool → Block TT Γ ρ → Block TT Γ ρ → AK TT ρ Γ → AK TT ρ Γ
  /-- after the body of `do … while` -/
  | doBody {Γ : Ctx} : Block TT Γ ρ → Expr TT Γ .bool → AK TT ρ Γ → AK TT ρ Γ
  /-- after iteration `i` of `for (const x of arr)` over the array at address `a` -/
  | forOfBody {Γ : Ctx} {t : Ty} : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → AK TT ρ Γ →
      AK TT ρ (⟨t, false⟩ :: Γ)
  /-- after the iteration at entry index `i` of a `Map` -/
  | forOfMapBody {Γ : Ctx} {k v : Ty} : Nat → Nat →
      Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ → AK TT ρ Γ →
      AK TT ρ (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ)
  /-- after the iteration at entry index `i` of a `Set` -/
  | forOfSetBody {Γ : Ctx} {t : Ty} : Nat → Nat → Block TT (⟨t, false⟩ :: Γ) ρ → AK TT ρ Γ →
      AK TT ρ (⟨t, false⟩ :: Γ)
  /-- after an iteration over the code points of a string (remaining code points) -/
  | forOfStrBody {Γ : Ctx} : List JSStr → Block TT (⟨.str, false⟩ :: Γ) ρ → AK TT ρ Γ →
      AK TT ρ (⟨.str, false⟩ :: Γ)
  /-- inside a `try` body: handler and finally block -/
  | catchFrame {Γ : Ctx} : Block TT (⟨.err, false⟩ :: Γ) ρ → Block TT Γ ρ → AK TT ρ Γ → AK TT ρ Γ
  /-- inside a `try` body without catch, or inside a handler: the finally block -/
  | finFrame {Γ : Ctx} : Block TT Γ ρ → AK TT ρ Γ → AK TT ρ Γ
  /-- while running a finally block: the completion to resume afterwards -/
  | finRestore {Γ : Ctx} : Completion TT ρ → AK TT ρ Γ → AK TT ρ Γ
  /-- inside a `breakable` block -/
  | brkFrame {Γ : Ctx} : AK TT ρ Γ → AK TT ρ Γ

/-- A suspended async body waiting for a value: `const x = await p; rest`. -/
inductive Resumption (TT : TypeTable) (ρ : Ty) : Ty → Type where
  | mk {Γ : Ctx} (s : Slot) (rest : Block TT (s :: Γ) ρ) (env : Env TT Γ) (k : AK TT ρ Γ) :
      Resumption TT ρ s.ty

/-- Reactions registered on a promise of type `t` (ECMA-262 PromiseReaction records,
specialised to the handlers StrictTS can create). Targets are promise addresses. -/
inductive Reaction (TT : TypeTable) (t : Ty) where
  /-- resume an async body; `result` is that body's own promise -/
  | await {ρ : Ty} (r : Resumption TT ρ t) (result : Nat)
  | then {u : Ty} (f : Val TT (.fn (.cons t .nil) u)) (target : Nat)
  | thenP {u : Ty} (f : Val TT (.fn (.cons t .nil) (.promise u))) (target : Nat)
  | catch (f : Val TT (.fn (.cons .err .nil) t)) (target : Nat)
  | finally (f : Val TT (.fn .nil .undef)) (target : Nat)
  /-- settle `target` the same way (thenable resolution, `Promise.race`) -/
  | forward (target : Nat)
  /-- one element of `Promise.all`: store into the slot array `arr` (of `opt t`) at `idx`;
  when every slot is filled, resolve `target` with a fresh array of the values -/
  | allSlot (target : Nat) (arr : Nat) (idx : Nat)
  /-- one element of `Promise.all` over a tuple of types `ts`: store the value into its box
  `slot` (of type `t`); when every box of `slots` holds a value, resolve `target` with the tuple
  of the values -/
  | allTup (ts : Tys) (target : Nat) (slots : List Nat) (slot : Nat)
  /-- one element of `Promise.allSettled` over an array: store the settled record of the outcome
  into the slot array `arr` (of `opt t.settled`) at `idx`; when every slot is filled, resolve
  `target` with a fresh array of the records -/
  | settledSlot (target : Nat) (arr : Nat) (idx : Nat)
  /-- one element of `Promise.allSettled` over a tuple of types `ts`: store the settled record of
  the outcome into its box `slot` (of type `t.settled`); when every box is filled, resolve
  `target` with the tuple of the records -/
  | settledTup (ts : Tys) (target : Nat) (slots : List Nat) (slot : Nat)
  /-- settle `target` with a fixed outcome (the value thunk / thrower of `finally`) -/
  | const {u : Ty} (target : Nat) (out : Except ErrVal (Val TT u))

/-- Microtasks (ECMA-262 jobs). -/
inductive Job (TT : TypeTable) where
  | react {t : Ty} (r : Reaction TT t) (outcome : Except ErrVal (Val TT t))
  /-- NewPromiseResolveThenableJob: `target` was resolved with the promise `q` -/
  | resolveThenable (t : Ty) (target : Nat) (q : Nat)
  /-- `queueMicrotask(f)` -/
  | callback (f : Val TT (.fn .nil .undef))

inductive PState (TT : TypeTable) (t : Ty) where
  | pending
  | fulfilled (v : Val TT t)
  | rejected (e : ErrVal)

structure PromiseCell (TT : TypeTable) (t : Ty) where
  state : PState TT t := .pending
  reactions : List (Reaction TT t) := []
  /-- the resolving functions of this promise have been used ([[AlreadyResolved]]) -/
  locked : Bool := false

/-- Insertion-ordered maps (ECMA-262 [[MapData]]): deleted entries stay as `none`
tombstones so that live iterators see the specified order. -/
structure JSMap (K V : Type) where
  entries : List (Option (K × V)) := []

/-- Field values of a class instance; `none` = not yet initialised by the constructor. -/
inductive OVals (TT : TypeTable) : List Ty → Type where
  | nil : OVals TT []
  | cons {t : Ty} {ts : List Ty} : Option (Val TT t) → OVals TT ts → OVals TT (t :: ts)

/-- Kinds of heap cells. The heap is keyed by `(kind, address)`, so cells of different
kinds or element types never alias: a write to a `number[]` provably leaves every
`string[]`, `Map` and object unchanged. -/
inductive HKind where
  | arr (t : Ty)
  | tarr (k : TAKind)
  | map (k v : Ty)
  | set (t : Ty)
  | obj (c : String) (fs : List Ty)
  | promise (t : Ty)
  | box (t : Ty)
  | dict (t : Ty)
  deriving DecidableEq, Hashable, Repr

/-- Contents of a heap cell of each kind. -/
@[reducible] def HKind.Cell (TT : TypeTable) : HKind → Type
  | .arr t => Array (Val TT t)
  | .tarr k => Array (BitVec k.width)
  | .map k v => JSMap (Val TT k) (Val TT v)
  | .set t => JSMap (Val TT t) Unit
  | .obj _ fs => OVals TT fs
  | .promise t => PromiseCell TT t
  | .box t => Option (Val TT t)
  | .dict t => JSMap JSStr (Val TT t)

abbrev HKey := HKind × Nat

/-- The heap: an extensional dependent map from keys to cells (extensional, so two
programs that leave the same cells have equal heaps). -/
abbrev Heap (TT : TypeTable) := Std.ExtDHashMap HKey (fun key => HKind.Cell TT key.1)

mutual
/-- A value produced by external code: an ordinary value, or the elements of an array that the
program receives as a fresh object (allocated when the answer arrives, e.g. the result of
`s.split(re)` or of `JSON.parse` at an array type). -/
inductive EVal (TT : TypeTable) : Ty → Type where
  | val {t : Ty} : Val TT t → EVal TT t
  | arr {t : Ty} : EVals TT t → EVal TT (.arr t)
  /-- a value of type `unknown` with the runtime type `t` (e.g. an untyped `JSON.parse` result) -/
  | dyn (t : Ty) : EVal TT t → EVal TT .dyn
  /-- a fresh object used as a dictionary: its keys, in order, and their values -/
  | dict {t : Ty} : List JSStr → EVals TT t → EVal TT (.dict t)
/-- The elements of a fresh array produced by external code. -/
inductive EVals (TT : TypeTable) : Ty → Type where
  | nil {t : Ty} : EVals TT t
  | cons {t : Ty} : EVal TT t → EVals TT t → EVals TT t
end

/-- Oracle for external functions: the outcome of the `n`-th external call, given the function's
name, signature and arguments (a value, possibly with fresh arrays, or the error it throws).
External code is assumed not to modify the program's own heap. -/
abbrev ExtOracle (TT : TypeTable) :=
  (name : String) → (args : List Ty) → (ret : Ty) → Vals TT args → Nat → Except ErrVal (EVal TT ret)

/-- The whole observable state. -/
structure World (TT : TypeTable) where
  heap : Heap TT
  /-- next fresh address (addresses are never reused) -/
  next : Nat
  /-- console output, oldest first -/
  out : List JSStr := []
  /-- microtask queue, next job first -/
  jobs : List (Job TT) := []
  /-- pending timers: (due time, sequence number, callback) -/
  timers : List (Nat × Nat × Val TT (.fn .nil .undef)) := []
  clock : Nat := 0
  seqNo : Nat := 0
  /-- oracle for `Math.random()` and how many values were drawn -/
  rand : Nat → F64 := fun _ => F64.zero
  randIdx : Nat := 0
  /-- oracle for `Date.now()` (indexed by call count) -/
  now : Nat → F64 := fun _ => F64.zero
  nowIdx : Nat := 0
  /-- promises rejected while no handler was attached (HostPromiseRejectionTracker); checked
  when the microtask queue is empty, as Node does -/
  unhandled : List (Nat × ErrVal) := []
  /-- oracle for external calls and how many were made -/
  ext : ExtOracle TT := fun _ _ _ _ _ => .error ⟨JSStr.ofString "Error", JSStr.ofString "external call"⟩
  extIdx : Nat := 0

/-- The evaluation monad. -/
abbrev JS (TT : TypeTable) := ExceptT Exc (StateT (World TT) Option)

/-- Implementation-defined parts of ECMAScript: implementation-approximated `Math`
functions and locale/Unicode-dependent string functions. Theorems are stated for all
`Impl` (or under explicit assumptions about it). -/
structure Impl where
  pow : F64 → F64 → F64
  atan2 : F64 → F64 → F64
  hypot : F64 → F64 → F64
  /-- transcendental unary `Math` functions (`cbrt`, `exp`, …, `atanh`) -/
  un : NumUn → F64 → F64
  toUpper : JSStr → JSStr
  toLower : JSStr → JSStr
  localeCompare : JSStr → JSStr → F64

variable {TT : TypeTable}

def ErrKind.name : ErrKind → String
  | .error => "Error" | .typeError => "TypeError" | .rangeError => "RangeError"
  | .syntaxError => "SyntaxError" | .referenceError => "ReferenceError"

def mkErr (k : ErrKind) (msg : JSStr) : ErrVal := ⟨JSStr.ofString k.name, msg⟩

namespace JS

def panic {α : Type} (msg : String) : JS TT α := throw (.panic msg)

def throwJS {α : Type} (k : ErrKind) (msg : String) : JS TT α :=
  throw (.thrown (mkErr k (JSStr.ofString msg)))

/-- Run `m`, turning a thrown JavaScript exception into a value; panics propagate. -/
def catchThrown {α : Type} (m : JS TT α) : JS TT (Except ErrVal α) :=
  ExceptT.mk (do
    let r ← m.run
    match r with
    | .ok a => pure (.ok (.ok a))
    | .error (.thrown e) => pure (.ok (.error e))
    | .error (.panic msg) => pure (.error (.panic msg)))

def liftExcept {α : Type} : Except Exc α → JS TT α
  | .ok a => pure a
  | .error e => throw e

/-- Allocate a fresh cell. -/
def alloc (k : HKind) (c : k.Cell TT) : JS TT Nat :=
  modifyGet fun w => (w.next, { w with heap := w.heap.insert (k, w.next) c, next := w.next + 1 })

/-- Read a cell (panics only on addresses no allocation produced). -/
def read (k : HKind) (a : Nat) : JS TT (k.Cell TT) := do
  match (← get).heap.get? (k, a) with
  | some c => pure c
  | none => panic "dangling reference"

def write (k : HKind) (a : Nat) (c : k.Cell TT) : JS TT Unit :=
  modify fun w => { w with heap := w.heap.insert (k, a) c }

def log (s : JSStr) : JS TT Unit :=
  modify fun w => { w with out := w.out ++ [s] }

def enqueue (j : Job TT) : JS TT Unit :=
  modify fun w => { w with jobs := w.jobs ++ [j] }

end JS
end StrictTS
