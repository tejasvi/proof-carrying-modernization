/-
StrictTS: random differential testing of two functions through the Lean semantics.

Before proving an equivalence, `diffCheck` runs both functions on many random inputs (with
special values such as NaN, ±0, ±Infinity, empty strings and arrays, astral characters) using
the compiled interpreter, and reports the first input on which their observable behaviour
(result, thrown error, console output, final contents of argument arrays) differs.
-/
import StrictTS.Core.Sem
import StrictTS.Num.Format

namespace StrictTS.Testing

variable {TT : TypeTable}

/-- A small deterministic PRNG (splitmix64). -/
structure Rng where
  s : UInt64

def Rng.next (r : Rng) : Rng × UInt64 :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (⟨s⟩, z ^^^ (z >>> 31))

def Rng.below (r : Rng) (n : Nat) : Rng × Nat :=
  let (r, x) := r.next
  (r, if n = 0 then 0 else x.toNat % n)

/-- Random doubles: special values half of the time, otherwise random bit patterns or small
integers and halves. -/
def genF64 (r : Rng) : Rng × F64 :=
  let (r, k) := r.below 12
  match k with
  | 0 => (r, .nan)
  | 1 => (r, .inf false)
  | 2 => (r, .inf true)
  | 3 => (r, F64.zero false)
  | 4 => (r, F64.zero true)
  | 5 => let (r, x) := r.next; (r, F64.ofBits (BitVec.ofNat 64 x.toNat))
  | 6 => let (r, n) := r.below 2000; (r, F64.ofInt ((n : Int) - 1000) / F64.ofNat 2)
  | 7 => let (r, n) := r.below 4294967296; (r, F64.ofNat n)
  | _ => let (r, n) := r.below 200; (r, F64.ofInt ((n : Int) - 100))

def alphabet : List (List UInt16) :=
  [[97], [98], [65], [48], [32], [0xE9], [0xD83D, 0xDE00], [0xD800], [44]]

def genStr (r : Rng) : Rng × JSStr :=
  let (r, len) := r.below 8
  let rec go : Nat → Rng → List UInt16 → Rng × List UInt16
    | 0, r, acc => (r, acc)
    | n + 1, r, acc =>
      let (r, i) := r.below alphabet.length
      go n r (acc ++ alphabet.getD i [97])
  let (r, us) := go len r []
  (r, ⟨us⟩)

mutual
/-- Random values of the types `diffCheck` supports: primitives, string-literal enums, optionals,
records, tuples and arrays of those (arrays are allocated in the world). -/
partial def genVal (r : Rng) (w : World TT) : (t : Ty) → Option (Rng × Val TT t × World TT)
  | .num => let (r, x) := genF64 r; some (r, .num x, w)
  | .str => let (r, s) := genStr r; some (r, .str s, w)
  | .bool => let (r, b) := r.below 2; some (r, .bool (b == 1), w)
  | .bigint => let (r, n) := r.below 2001; some (r, .bigint ((n : Int) - 1000), w)
  | .undef => some (r, .undef, w)
  | .null => some (r, .null, w)
  | .enum cs =>
    if h : 0 < cs.length then
      let (r, i) := r.below cs.length
      some (r, .enum ⟨i % cs.length, Nat.mod_lt _ h⟩, w)
    else none
  | .opt t =>
    let (r, b) := r.below 4
    if b == 0 then some (r, .none, w)
    else match genVal r w t with
      | some (r, v, w) => some (r, .some v, w)
      | none => none
  | .record fs => match genArgs r w fs.types with
    | some (r, vs, w) => some (r, .record vs, w)
    | none => none
  | .tup ts => match genArgs r w ts.toList with
    | some (r, vs, w) => some (r, .tup vs, w)
    | none => none
  | .arr t =>
    let (r, len) := r.below 6
    let rec elems : Nat → Rng → World TT → Array (Val TT t) → Option (Rng × Array (Val TT t) × World TT)
      | 0, r, w, acc => some (r, acc, w)
      | n + 1, r, w, acc => match genVal r w t with
        | some (r, v, w) => elems n r w (acc.push v)
        | none => none
    match elems len r w #[] with
    | some (r, xs, w) =>
      let a := w.next
      some (r, .arr a, { w with heap := w.heap.insert (.arr t, a) xs, next := a + 1 })
    | none => none
  | _ => none

partial def genArgs (r : Rng) (w : World TT) : (ts : List Ty) → Option (Rng × Vals TT ts × World TT)
  | [] => some (r, .nil, w)
  | t :: ts => match genVal r w t with
    | some (r, v, w) => match genArgs r w ts with
      | some (r, vs, w) => some (r, .cons v vs, w)
      | none => none
    | none => none
end

/-- Printable form of a value (arrays dereferenced in `w`). -/
partial def showVal (w : World TT) : (t : Ty) → Val TT t → String
  | .num, v => toString (NumFormat.toJSString v.toNum) ++ (if v.toNum == F64.zero true then " (-0)" else "")
  | .str, v => repr v.toStr |>.pretty
  | .bool, v => toString v.toBool
  | .bigint, v => toString v.toBig ++ "n"
  | .undef, _ => "undefined"
  | .arr t, v => match w.heap.get? (.arr t, v.arrAddr) with
    | some xs => "[" ++ ", ".intercalate (xs.toList.map (showVal w t)) ++ "]"
    | none => "<dangling>"
  | .null, _ => "null"
  | .enum cs, v => repr (cs.get v.enumIdx) |>.pretty
  | .opt _, .none => "undefined"
  | .opt t, .some v => showVal w t v
  | .record fs, v => "{" ++ ", ".intercalate (showFields w fs v.recVals) ++ "}"
  | _, _ => "<value>"
where
  showFields (w : World TT) : (fs : Fields) → Vals TT fs.types → List String
    | .nil, _ => []
    | .cons n t fs, vs => (n ++ ": " ++ showVal w t vs.head) :: showFields w fs vs.tail

def showArgs (w : World TT) : (ts : List Ty) → Vals TT ts → List String
  | [], _ => []
  | t :: ts, vs => showVal w t vs.head :: showArgs w ts vs.tail

/-- Observable behaviour of one run: outcome, console output, argument arrays afterwards. -/
def observe (ts : List Ty) (ret : Ty) (args : Vals TT ts)
    (r : Option (Except Exc (Val TT ret) × World TT)) : String :=
  match r with
  | none => "diverges"
  | some (out, w) =>
    let o := match out with
      | .ok v => "returns " ++ showVal w ret v
      | .error (.thrown e) => s!"throws {e.name}: {e.message}"
      | .error (.panic m) => s!"PANIC {m}"
    o ++ s!" | console {w.out.map toString} | args after {showArgs w ts args}"

/-- The world after the module's initialisation (its variables allocated, its body run; output
discarded), so that functions reading module-level constants can be tested. -/
def initWorld (I : Impl) (P : Program TT) : World TT :=
  let init : JS TT Unit := do
    for t in P.globals do
      let _ ← JS.alloc (.box t) none
    let _ ← evalB I P P.main .nil
  match init.run.run (World.init TT) with
  | some (_, w) => { w with out := [], jobs := [], timers := [], unhandled := [] }
  | none => World.init TT

/-- Run `f` and `g` (same signature) on `n` random inputs; return the first input where their
observable behaviour differs, or `none`. -/
def diffCheck (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f g : FunRef args ret)
    (n : Nat := 1000) (seed : UInt64 := 42) : Option String := Id.run do
  let mut r : Rng := ⟨seed⟩
  for _ in [0:n] do
    let w0 : World TT := initWorld I P
    match genArgs r w0 args.toList with
    | none => return some "diffCheck: unsupported argument type"
    | some (r', vs, w) =>
      r := r'
      let a := observe args.toList ret vs (JS.exec' (callFun I P f vs) w)
      let b := observe args.toList ret vs (JS.exec' (callFun I P g vs) w)
      if a != b then
        return some s!"inputs {showArgs w args.toList vs}:\n  first:  {a}\n  second: {b}"
  return none
where
  JS.exec' {α : Type} (m : JS TT α) (w : World TT) : Option (Except Exc α × World TT) := m.run.run w

/-- Random testing of a contract (e.g. one generated from JSDoc by `tools/jsdoc_specs.js`): on
`n` random inputs where the precondition `req` returns `true`, `f` must return normally and the
postcondition `ens` (applied to the result and the inputs, in the final world) must return
`true`. Returns the first counterexample, or `none`. -/
def specCheck (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : FunRef args ret)
    (req : FunRef args .bool) (ens : FunRef (.cons ret args) .bool)
    (n : Nat := 1000) (seed : UInt64 := 42) : Option String := Id.run do
  let mut r : Rng := ⟨seed⟩
  for _ in [0:n] do
    let w0 : World TT := initWorld I P
    match genArgs r w0 args.toList with
    | none => return some "specCheck: unsupported argument type"
    | some (r', vs, w) =>
      r := r'
      match (callFun I P req vs).run.run w with
      | some (.ok (.bool true), _) =>
        let run := (callFun I P f vs).run.run w
        match run with
        | some (.ok v, w') =>
          match (callFun I P ens (.cons v vs)).run.run w' with
          | some (.ok (.bool true), _) => pure ()
          | _ => return some s!"inputs {showArgs w args.toList vs}: {observe args.toList ret vs run}, \
              and the postcondition does not hold"
        | none => pure ()
        | _ => return some s!"inputs {showArgs w args.toList vs}: {observe args.toList ret vs run}"
      | _ => pure ()
  return none

end StrictTS.Testing
