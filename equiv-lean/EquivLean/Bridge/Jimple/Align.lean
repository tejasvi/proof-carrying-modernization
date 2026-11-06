import EquivLean.Bridge.Jimple.Rel

/-!
# Jimple bridge: loop alignment and candidate couplings from runs (executable)

The data side of `equiv_jimple` (`Bridge/Jimple/Auto.lean`): ordinary executable Lean over
JimpleLean's syntax and interpreter.  The tactic evaluates `analyze` on the two programs while
it runs and turns the result into couplings; the kernel then checks the product (`ProdVC`) as
usual, so nothing here is trusted: a wrong candidate only makes the proof fail.

* Control flow of a body: successors (with trap handlers), loop heads (the targets of backward
  jumps), natural loops, live locals (`liveIn`), locals assigned inside a loop (`loopDefs`),
  statements that may write the heap (`mayWrite`), the longest path between cut points
  (`segFuel`, the exploration budget).
* Samples: arguments by declared parameter type (primitives, arrays of primitives, `String`,
  objects of application classes; the receiver of an instance method) in a fresh heap, from a
  fixed pseudo-random seed; odd samples draw from narrow value ranges, so that values meet (a
  searched key that occurs), even ones from wide ranges, so that unrelated values differ.
* Runs: JimpleLean's own `step`/`afterStep`/`runR`, recording the frame and the state at every
  visit of a loop head of the top-level body (`traceHeads`).
* Facts at the k-th pair of loop heads, kept when they hold at every aligned visit (the i-th
  visit of one head with the i-th visit of the other) of every sample (`headFacts`): live locals
  equal across the two sides; the entry value of a live local (an argument, the length of an
  array argument, or a constant; only constants for a local the loop assigns, e.g. a flag set on
  the iteration that leaves the loop); bounds `0 ≤ v ≤ length` for `int` locals; the heap of the
  call's entry when neither side writes the heap up to and inside the loop.
* What no proof can follow is reported, not hidden: different numbers of loops (an error);
  samples whose head visits do not align (visit counts that differ, i.e. loops not in lockstep,
  or heaps that differ at a pair of heads) are left out and listed (`Analysis.dropped`; an error
  if no sample is left); samples on which the two runs end differently are listed
  (`Analysis.diffs`: counterexamples for `Sim (· = ·)` when the sample meets the statement's
  precondition, which the samples do not know).
-/

open Jimple

namespace EquivLean.Jimple.Align

/-! ## Control flow -/

/-- Jump targets of a statement. -/
def stmtTargets : Stmt → List Nat
  | .goto t => [t]
  | .ifGoto _ _ _ t => [t]
  | .tableSwitch _ _ ts d => d :: ts
  | .lookupSwitch _ cs d => d :: cs.map (·.2)
  | _ => []

/-- The statement can continue with the next one. -/
def fallsThrough : Stmt → Bool
  | .goto _ | .tableSwitch .. | .lookupSwitch .. | .ret _ | .returnVal _ | .returnVoid
  | .throw _ => false
  | _ => true

/-- Successors of a statement: the next one, jump targets, and the handlers of the traps
covering it. -/
def succs (b : Body) (pc : Nat) : List Nat :=
  match b.stmts[pc]? with
  | none => []
  | some s =>
    let n := (if fallsThrough s then [pc + 1] else []) ++ stmtTargets s
    let h := b.traps.filterMap fun t => if t.first ≤ pc ∧ pc < t.last then some t.handler else none
    (n ++ h).eraseDups

/-- Loop heads: the targets of backward jumps, in increasing order. -/
def loopHeads (b : Body) : List Nat :=
  let hs := (List.range b.stmts.size).flatMap fun pc =>
    match b.stmts[pc]? with
    | some s => (stmtTargets s).filter (· ≤ pc)
    | none => []
  (hs.eraseDups.toArray.qsort (· < ·)).toList

def immUses : Imm → List Nat
  | .loc x => [x]
  | .const _ => []

def refUses : Ref → List Nat
  | .instField b _ => [b]
  | .staticField _ => []
  | .arrayElem b i => b :: immUses i

def invUses : Invoke → List Nat
  | .inst _ b _ ys => b :: ys.flatMap immUses
  | .static _ ys => ys.flatMap immUses
  | .dynamic _ _ _ ys _ zs => (ys ++ zs).flatMap immUses

def exprUses : Jimple.Expr → List Nat
  | .imm a => immUses a
  | .binop _ a b => immUses a ++ immUses b
  | .unop _ a => immUses a
  | .cast _ a => immUses a
  | .instOf a _ => immUses a
  | .new _ => []
  | .newArray _ n => immUses n
  | .newMultiArray _ ss _ => ss.flatMap immUses
  | .invoke i => invUses i
  | .ref r => refUses r

def stmtUses : Stmt → List Nat
  | .assign (.loc _) e => exprUses e
  | .assign (.ref r) e => refUses r ++ exprUses e
  | .enterMonitor a | .exitMonitor a | .returnVal a | .throw a => immUses a
  | .ifGoto _ a b _ => immUses a ++ immUses b
  | .invoke i => invUses i
  | .tableSwitch k _ _ _ | .lookupSwitch k _ _ => immUses k
  | .ret x => [x]
  | _ => []

def stmtDefs : Stmt → List Nat
  | .identity x _ => [x]
  | .assign (.loc x) _ => [x]
  | _ => []

/-- Live locals at the start of each statement (backward fixpoint). -/
def liveness (b : Body) : Array (List Nat) := Id.run do
  let n := b.stmts.size
  let mut live : Array (List Nat) := Array.replicate n []
  let mut changed := true
  let mut iter := 0
  while changed && iter < 4 * n + 8 do
    changed := false
    iter := iter + 1
    for k in [0:n] do
      let pc := n - 1 - k
      let s := b.stmts[pc]!
      let out := (succs b pc).flatMap fun q => live.getD q []
      let inn := (stmtUses s ++ out.filter (fun x => !(stmtDefs s).contains x)).eraseDups
      if inn.length != (live.getD pc []).length then
        live := live.set! pc inn
        changed := true
  return live

/-- Live locals at `pc`, in increasing order. -/
def liveIn (b : Body) (pc : Nat) : List Nat :=
  (((liveness b).getD pc []).toArray.qsort (· < ·)).toList

/-- The natural loop of head `h`: `h` and the statements that reach one of its back edges
without passing through `h`. -/
def loopBody (b : Body) (h : Nat) : List Nat := Id.run do
  let n := b.stmts.size
  let backs := (List.range n).filter fun pc =>
    h ≤ pc && (match b.stmts[pc]? with
      | some s => (stmtTargets s).contains h
      | none => false)
  let preds (q : Nat) : List Nat := (List.range n).filter fun p => (succs b p).contains q
  let mut seen : List Nat := [h]
  let mut work := backs
  let mut fuel := n * n + 8
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => fuel := 0
    | q :: rest =>
      work := rest
      unless seen.contains q do
        seen := q :: seen
        work := preds q ++ work
  return (seen.toArray.qsort (· < ·)).toList

/-- Locals assigned inside the loop of head `h`. -/
def loopDefs (b : Body) (h : Nat) : List Nat :=
  ((loopBody b h).flatMap fun pc => match b.stmts[pc]? with
    | some s => stmtDefs s
    | none => []).eraseDups

/-- The immediate allocates (string and class constants). -/
def immAllocs : Imm → Bool
  | .const (.str _) | .const (.strUnits _) | .const (.clazz _) | .const (.methodHandle _) => true
  | _ => false

/-- The statement may change the heap or the static state on a normal path (stores,
allocations, calls, class initialization by static field accesses, allocating constants). -/
def mayWrite : Stmt → Bool
  | .assign (.ref _) _ => true
  | .assign _ (.new _) | .assign _ (.newArray ..) | .assign _ (.newMultiArray ..)
  | .assign _ (.invoke _) | .invoke _ | .assign _ (.ref (.staticField _)) => true
  | .enterMonitor _ | .exitMonitor _ => true
  | s => (stmtImms s).any immAllocs
where
  stmtImms : Stmt → List Imm
    | .assign _ (.imm a) | .assign _ (.unop _ a) | .assign _ (.cast _ a)
    | .assign _ (.instOf a _) | .returnVal a | .throw a => [a]
    | .assign _ (.binop _ a c) | .ifGoto _ a c _ => [a, c]
    | _ => []

/-- Statements reachable from `0` without passing through `h`, then the loop of `h`: none of
them writes the heap. -/
def heapFrozenUpTo (b : Body) (h : Nat) : Bool := Id.run do
  let n := b.stmts.size
  let mut seen : List Nat := []
  let mut work := [0]
  let mut fuel := n * n + 8
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => fuel := 0
    | q :: rest =>
      work := rest
      unless q == h || seen.contains q do
        seen := q :: seen
        work := succs b q ++ work
  let region := seen ++ loopBody b h
  return region.all fun pc => match b.stmts[pc]? with
    | some s => !mayWrite s
    | none => true

/-- Number of statements of the longest path between cut points (`0` and the loop heads), an
exploration budget for symbolic execution of a segment (paths that do not reach a cut point,
which a correct choice of loop heads excludes, are capped at the body's size). -/
def segFuel (b : Body) (cuts : List Nat) : Nat := Id.run do
  let n := b.stmts.size
  -- len[pc]: statements executed from `pc` until a cut point (excluded) or the end
  let mut len : Array Nat := Array.replicate (n + 1) 0
  for _ in [0:n + 1] do
    for pc in [0:n] do
      let m := ((succs b pc).map fun q => if cuts.contains q || q ≥ n then 0 else len[q]!).foldl max 0
      len := len.set! pc (min (n + 1) (1 + m))
  return ((0 :: cuts).map fun c => len[c]!).foldl max 0

/-- The body has calls or static field accesses (callees and class initializers are inlined). -/
def hasCalls (b : Body) : Bool :=
  b.stmts.any fun s => match s with
    | .invoke _ | .assign _ (.invoke _) | .assign _ (.ref (.staticField _))
    | .assign (.ref (.staticField _)) _ | .assign _ (.new _) => true
    | _ => false

/-! ## Samples -/

/-- A linear congruential generator (fixed seed: the analysis is deterministic). -/
structure Rng where
  s : Nat

def Rng.next (r : Rng) : Nat × Rng :=
  let s' := (r.s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  (s' / 65536, ⟨s'⟩)

def Rng.range (r : Rng) (lo hi : Int) : Int × Rng :=
  let (x, r') := r.next
  (lo + ((x % (hi - lo + 1).toNat : Nat) : Int), r')

/-- A random value of a primitive type: from a wide range, or (`narrow`) from a small one, so
that some values meet (a searched key that occurs, equal neighbours). -/
def samplePrim (p : PrimType) (narrow : Bool) (r : Rng) : Option (Value × Rng) :=
  let int (lo hi : Int) : Option (Value × Rng) :=
    let (x, r) := r.range lo hi; some (.int (BitVec.ofInt 32 x), r)
  match p with
  | .int => if narrow then int (-2) 2 else int (-1000) 1000
  | .short | .byte => if narrow then int (-2) 2 else int (-100) 100
  | .char => if narrow then int 97 99 else int 0 255
  | .boolean => int 0 1
  | .long =>
    let (x, r) := if narrow then r.range (-2) 2 else r.range (-1000000) 1000000
    some (.long (BitVec.ofInt 64 x), r)
  | _ => none

/-- Array lengths of the samples, in turn. -/
def sampleLengths : List Nat := [0, 1, 2, 3, 5, 4, 3, 6, 2, 1, 4, 3]

/-- A random value of type `t` for sample `k` (odd samples draw from narrow ranges), allocated
in `σ` if needed: primitives, arrays of primitives, strings, and objects of application classes
(primitive fields sampled, reference fields `null`). -/
def sampleArg (P : Program) (t : JType) (k : Nat) (σ : State) (r : Rng) :
    Option (Value × State × Rng) :=
  let narrow := k % 2 == 1
  match t with
  | .prim p => (samplePrim p narrow r).map fun (v, r) => (v, σ, r)
  | .array (.prim p) => Id.run do
    let len := sampleLengths.getD (k % sampleLengths.length) 3
    let mut r := r
    let mut xs : Array Value := #[]
    for _ in [0:len] do
      match samplePrim p narrow r with
      | some (v, r') => xs := xs.push v; r := r'
      | none => return none
    let (a, σ) := σ.alloc (.array (.prim p) xs.toList)
    return some (.ref a, σ, r)
  | .cls "java.lang.String" =>
    let (n, r) := r.range 0 4
    let (cs, r) := (List.range n.toNat).foldl (fun (acc, r) _ =>
      let (c, r) := if narrow then r.range 97 98 else r.range 97 122
      (acc ++ [BitVec.ofInt 16 c], r)) ([], r)
    let (a, σ) := σ.alloc (.str cs)
    some (.ref a, σ, r)
  | .cls c => Id.run do
    let some d := P.findClass c | return none
    if d.isAbstract || d.isInterface then return none
    let mut r := r
    let mut fs : Array (FieldKey × Value) := #[]
    for (key, ft) in P.instanceFields c do
      match ft with
      | .prim p =>
        match samplePrim p narrow r with
        | some (v, r') => fs := fs.push (key, v); r := r'
        | none => return none
      | _ => fs := fs.push (key, ft.default)
    let (a, σ) := σ.alloc (.plain c fs.toList)
    return some (.ref a, σ, r)
  | _ => none

/-- Arguments of a call of `m` (the receiver first for an instance method), in a fresh heap. -/
def sampleArgs (P : Program) (m : MethodRef) (k : Nat) (seed : Nat) :
    Option (List Value × State) := Id.run do
  let mut r : Rng := ⟨seed * 7919 + k * 104729 + 17⟩
  let mut σ : State := State.empty
  let mut vs : Array Value := #[]
  let ts := (if m.decl.mods.isStatic then [] else [JType.cls m.cls]) ++ m.decl.params
  for t in ts do
    match sampleArg P t k σ r with
    | some (v, σ', r') => vs := vs.push v; σ := σ'; r := r'
    | none => return none
  return some (vs.toList, σ)

/-! ## Runs -/

/-- One run of body `b` (calls by JimpleLean's interpreter `runR`), recording the frame and the
state at each visit of a statement of `heads`; also the outcome (`none`: out of fuel). -/
def traceHeads (P : Program) (b : Body) (heads : List Nat) :
    Nat → Nat → Frame → State → Array (Nat × Frame × State) →
      Option Outcome × Array (Nat × Frame × State)
  | 0, _, _, _, acc => (none, acc)
  | n + 1, pc, fr, σ, acc =>
    let acc := if heads.contains pc then acc.push (pc, fr, σ) else acc
    match runR P n (step P b pc fr σ) with
    | some r =>
      match afterStep P b pc fr r with
      | .cont pc' fr' σ' => traceHeads P b heads n pc' fr' σ' acc
      | .done o => (some o, acc)
    | none => (none, acc)

/-- Structural equality of heap objects (the kinds a comparison needs; others compare
unequal). -/
def objEq : Obj → Obj → Bool
  | .plain c fs, .plain c' fs' => c == c' && fs == fs'
  | .array t xs, .array t' xs' => t == t' && xs == xs'
  | .str s, .str s' => s == s'
  | .builder c s, .builder c' s' => c == c' && s == s'
  | .boxed c v, .boxed c' v' => c == c' && v == v'
  | .bigInt i, .bigInt i' => i == i'
  | .dec d, .dec d' => d == d'
  | .stream f, .stream f' => f == f'
  | .clazz d, .clazz d' => d == d'
  | _, _ => false

def stateEq (σ σ' : State) : Bool :=
  σ.mem.size == σ'.mem.size && (σ.mem.zip σ'.mem).all (fun (o, o') => objEq o o') &&
    σ.statics == σ'.statics && σ.inits == σ'.inits && σ.monitors == σ'.monitors && σ.out == σ'.out

/-! ## Candidate facts -/

/-- A value at a loop head given by the call's entry: argument `i`, the length of the array
argument `i`, or a constant. -/
inductive Feature where
  | arg (i : Nat)
  | len (i : Nat)
  | const (v : Value)
  deriving Inhabited, Repr, BEq

/-- How a local's value is described: `int`, `long`, reference to an object, any value. -/
inductive VKind where
  | int | long | ref | any
  deriving Inhabited, Repr, BEq, DecidableEq

/-- The facts kept at one pair of loop heads `(h₁, h₂)` (side 1 = target, side 2 = source). -/
structure HeadFacts where
  h₁ : Nat
  h₂ : Nat
  /-- `(x₁, x₂, kind)`: local `x₁` of the target equals local `x₂` of the source -/
  eqs : List (Nat × Nat × VKind)
  /-- `(x, f)`: local `x` (not assigned in the loop) holds the entry value `f` -/
  entry₁ : List (Nat × Feature)
  entry₂ : List (Nat × Feature)
  /-- `(side, x, i)`: `int` local `x` of `side` lies in `[0, length of array argument i]` -/
  bounds : List (Nat × Nat × Nat)
  /-- the heap is the one of the call's entry at every visit -/
  heapEntry : Bool
  /-- locals assigned inside the loops -/
  mod₁ : List Nat
  mod₂ : List Nat
  deriving Inhabited, Repr

structure Analysis where
  heads : List HeadFacts
  fuel₁ : Nat
  fuel₂ : Nat
  depth : Nat
  isStatic₁ : Bool
  isStatic₂ : Bool
  /-- samples run, aligned head visits compared -/
  samples : Nat
  visits : Nat
  /-- samples on which the two runs end differently (rendered): counterexamples to `Sim (· = ·)`
  when the sample satisfies the statement's precondition -/
  diffs : List String
  /-- samples left out because their loop-head visits do not align (rendered, with the reason) -/
  dropped : List String
  deriving Inhabited, Repr

/-- The kind common to the values of a list (all defined). -/
def kindOf (vs : List (Option Value)) : Option VKind :=
  if vs.all fun v => match v with | some (.int _) => true | _ => false then some .int
  else if vs.all fun v => match v with | some (.long _) => true | _ => false then some .long
  else if vs.all fun v => match v with | some (.ref _) => true | _ => false then some .ref
  else if vs.all (·.isSome) then some .any
  else none

/-- The length of the array a value refers to. -/
def arrLen (σ : State) : Value → Option Nat
  | .ref a => match σ.heap a with
    | some (.array _ xs) => some xs.length
    | _ => none
  | _ => none

/-- One aligned visit: the sample's arguments and entry state, the two frames and states. -/
structure Visit where
  args : List Value
  σ0 : State
  fr₁ : Frame
  σ₁ : State
  fr₂ : Frame
  σ₂ : State

/-- The value of a feature in a visit. -/
def Feature.eval (f : Feature) (v : Visit) : Option Value :=
  match f with
  | .arg i => v.args[i]?
  | .len i => (v.args[i]?.bind (arrLen v.σ0)).map fun n => .int (BitVec.ofNat 32 n)
  | .const c => some c

/-- The entry features a local may hold: arguments, lengths of array arguments, then the
constant it holds in the first visit. -/
def candFeatures (nargs : Nat) (first : Option Value) : List Feature :=
  (List.range nargs).map .arg ++ (List.range nargs).map .len ++
    (match first with | some c => [.const c] | none => [])

/-- Facts at one pair of heads from the aligned visits `vs`. -/
def headFacts (b₁ b₂ : Body) (h₁ h₂ : Nat) (nargs : Nat) (vs : List Visit) : HeadFacts :=
  let live₁ := liveIn b₁ h₁
  let live₂ := liveIn b₂ h₂
  let mod₁ := loopDefs b₁ h₁
  let mod₂ := loopDefs b₂ h₂
  let val₁ (x : Nat) : List (Option Value) := vs.map (·.fr₁.get x)
  let val₂ (x : Nat) : List (Option Value) := vs.map (·.fr₂.get x)
  -- equal locals across the sides (defined at every visit)
  let eqs := live₁.flatMap fun x₁ => live₂.filterMap fun x₂ =>
    let a := val₁ x₁
    if a == val₂ x₂ then (kindOf a).map fun k => (x₁, x₂, k) else none
  -- entry values of locals the loop does not assign
  let entryOf (get : Visit → Option Value) : Option Feature :=
    let first := (vs.head?.bind get)
    (candFeatures nargs first).find? fun f => vs.all fun v => get v == f.eval v ∧ (get v).isSome
  -- a local the loop assigns may still hold one value at every visit of the head (a flag set
  -- only on the iteration that leaves the loop): only constants are kept for those
  let isConst : Feature → Bool := fun f => match f with | .const _ => true | _ => false
  let entry₁ := live₁.filterMap fun x =>
    (entryOf (·.fr₁.get x)).bind fun f => if mod₁.contains x && !isConst f then none else some (x, f)
  let entry₂ := live₂.filterMap fun x =>
    (entryOf (·.fr₂.get x)).bind fun f => if mod₂.contains x && !isConst f then none else some (x, f)
  -- bounds by the length of an array argument, for `int` locals that vary
  let boundOf (get : Visit → Option Value) (i : Nat) : Bool :=
    let ok := vs.all fun v => match get v, v.args[i]?.bind (arrLen v.σ0) with
      | some (.int x), some n => 0 ≤ x.toInt ∧ x.toInt ≤ n
      | _, _ => false
    let distinct := ((vs.map get).eraseDups).length ≥ 2
    ok && distinct
  let arrArgs := (List.range nargs).filter fun i => vs.all fun v => (v.args[i]?.bind (arrLen v.σ0)).isSome
  let bounds₁ := live₁.flatMap fun x => (arrArgs.filter (boundOf (·.fr₁.get x))).map fun i => (1, x, i)
  let bounds₂ := live₂.flatMap fun x => (arrArgs.filter (boundOf (·.fr₂.get x))).map fun i => (2, x, i)
  let heapEntry := (heapFrozenUpTo b₁ h₁ && heapFrozenUpTo b₂ h₂) &&
    vs.all fun v => stateEq v.σ₁ v.σ0 && stateEq v.σ₂ v.σ0
  { h₁, h₂, eqs, entry₁, entry₂, bounds := bounds₁ ++ bounds₂, heapEntry, mod₁, mod₂ }

/-- A value for messages (arrays with their elements). -/
def showVal (σ : State) : Value → String
  | .ref a => match σ.heap a with
    | some (.array _ xs) => "[" ++ ", ".intercalate (xs.map (showValue σ)) ++ "]"
    | _ => showValue σ (.ref a)
  | v => showValue σ v

/-- An outcome for messages. -/
def showOutcome : Outcome → String
  | .normal (some v) σ => s!"returns {showVal σ v}"
  | .normal none _ => "returns"
  | .exc e σ => match σ.heap e with
    | some o => match o.ty with
      | .cls c => s!"throws {c}"
      | _ => "throws"
    | none => "throws"
  | .wrong m => s!"goes wrong ({m})"

/-- The two runs end the same way: same value or exception and the same final state; nothing is
owed when the source goes wrong. -/
def sameOutcome : Outcome → Outcome → Bool
  | _, .wrong _ => true
  | .normal v σ, .normal v' σ' => v == v' && stateEq σ σ'
  | .exc e σ, .exc e' σ' => e == e' && stateEq σ σ'
  | _, _ => false

/-- **The analysis**: loop heads paired in order, aligned visits from `nSamples` runs of both
methods on the same sampled arguments, the facts kept at each pair of heads; exploration fuel,
inlining depth and the methods' `static` flags.  An error explains why no candidate exists
(different loop structure, unsupported parameter types, iteration counts that differ, heaps
that differ at a head). -/
def analyze (P₁ : Program) (m₁ : MethodRef) (P₂ : Program) (m₂ : MethodRef)
    (nSamples seed : Nat) : Except String Analysis := do
  let some b₁ := m₁.decl.body | throw "the target method has no body"
  let some b₂ := m₂.decl.body | throw "the source method has no body"
  let hs₁ := loopHeads b₁
  let hs₂ := loopHeads b₂
  unless hs₁.length == hs₂.length do
    throw s!"different numbers of loops: target heads {hs₁}, source heads {hs₂}"
  unless m₁.decl.params == m₂.decl.params do throw "different parameter types"
  let s₁ := m₁.decl.mods.isStatic
  let s₂ := m₂.decl.mods.isStatic
  unless s₁ == s₂ do throw "one method is static, the other is not"
  let fuelRun := 1000000
  -- per pair of heads, the aligned visits of all samples
  let mut visits : Array (List Visit) := Array.replicate hs₁.length []
  let mut nrun := 0
  let mut diffs : Array String := #[]
  let mut dropped : Array String := #[]
  for k in [0:nSamples] do
    let some (args, σ0) := sampleArgs P₁ m₁ k seed
      | throw s!"unsupported parameter types {repr m₁.decl.params}"
    let (o₁, t₁) := traceHeads P₁ b₁ hs₁ fuelRun 0 (Frame.init s₁ args) σ0 #[]
    let (o₂, t₂) := traceHeads P₂ b₂ hs₂ fuelRun 0 (Frame.init s₂ args) σ0 #[]
    let (some o₁, some o₂) := (o₁, o₂) | continue
    let shownArgs := ", ".intercalate (args.map (showVal σ0))
    unless sameOutcome o₁ o₂ do
      diffs := diffs.push s!"arguments ({shownArgs}): target {showOutcome o₁}, source {showOutcome o₂}"
    -- a sample whose head visits cannot be aligned is dropped (it may violate the statement's
    -- precondition, which the samples do not know); the reason is kept for messages
    let mut sampleVisits : Array (List Visit) := Array.replicate hs₁.length []
    let mut why : Option String := none
    for j in [0:hs₁.length] do
      let v₁ := t₁.toList.filter (·.1 == hs₁[j]!)
      let v₂ := t₂.toList.filter (·.1 == hs₂[j]!)
      unless v₁.length == v₂.length do
        why := some s!"arguments ({shownArgs}): head {hs₁[j]!} visited {v₁.length} times, head {hs₂[j]!} {v₂.length} times (not lockstep)"
        break
      for ((_, f₁, σ₁), (_, f₂, σ₂)) in v₁.zip v₂ do
        unless stateEq σ₁ σ₂ do
          why := some s!"arguments ({shownArgs}): the heaps differ at heads ({hs₁[j]!}, {hs₂[j]!})"
        sampleVisits := sampleVisits.modify j (· ++ [{ args, σ0, fr₁ := f₁, σ₁, fr₂ := f₂, σ₂ }])
      if why.isSome then break
    match why with
    | some w => dropped := dropped.push w
    | none =>
      nrun := nrun + 1
      for j in [0:hs₁.length] do
        visits := visits.modify j (· ++ sampleVisits[j]!)
  if nrun == 0 then
    throw s!"no sample gives aligned loop-head visits: {"; ".intercalate dropped.toList}"
  let nargs := m₁.decl.params.length + (if s₁ then 0 else 1)
  let heads := (List.range hs₁.length).map fun j =>
    headFacts b₁ b₂ hs₁[j]! hs₂[j]! nargs (visits.getD j [])
  let depth := if hasCalls b₁ || hasCalls b₂ then 8 else 0
  return { heads, fuel₁ := segFuel b₁ hs₁ + 1, fuel₂ := segFuel b₂ hs₂ + 1, depth,
           isStatic₁ := s₁, isStatic₂ := s₂, samples := nrun, diffs := diffs.toList,
           dropped := dropped.toList,
           visits := visits.foldl (fun n l => n + l.length) 0 }

end EquivLean.Jimple.Align
