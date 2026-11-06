/-
Counterexample search for the uniform `JS.NoPanic` sweep of tools/public: run a function of an
emitted module through the compiled Lean interpreter on random and edge-value inputs, in the
initialised module world, and report the first inputs whose run panics.

The inputs satisfy the hypotheses of the NoPanic attempts: every argument array, Map, Set,
dictionary and object is an allocated cell, objects have every field initialised, references
below the first level are allocated as well (the world is closed). `Math.random()` answers
values in [0, 1). Values come from `StrictTS.Testing` (doubles with NaN, ±0, ±Infinity, random
bit patterns, small integers and halves; short strings with astral and lone-surrogate code
units), extended to Maps, Sets, dictionaries, objects, unions, named types and `unknown`, and to
the strings that name properties of `Object.prototype`.

Each finding is appended at once to the output file (a later diverging input cannot lose it):
  NPCE <function> :: <panic message> :: <arguments as a JavaScript array literal>
and the search ends with `NPDONE <function> <runs>` (or `NPUNSUPPORTED <function>`).
-/
import StrictTS.Testing
import StrictTS.Lib.Prim

namespace StrictTS.PanicSearch
open StrictTS.Testing

variable {TT : TypeTable}

def specialStrs : List String :=
  ["__proto__", "toString", "constructor", "hasOwnProperty", "valueOf", "length", "", "-0", "NaN", "0", "1"]

def genStr' (r : Rng) : Rng × JSStr :=
  let (r, k) := r.below 4
  if k == 0 then
    let (r, i) := r.below specialStrs.length
    (r, JSStr.ofString (specialStrs.getD i ""))
  else genStr r

/-- Small doubles only (a second pass for functions whose loops or recursion a large argument
makes run for too long): NaN, ±0, small integers and halves; no infinities. -/
def genF64Small (r : Rng) : Rng × F64 :=
  let (r, k) := r.below 6
  match k with
  | 0 => (r, .nan)
  | 1 => (r, F64.zero true)
  | 2 => let (r, n) := r.below 21; (r, F64.ofInt ((n : Int) - 10) / F64.ofNat 2)
  | _ => let (r, n) := r.below 13; (r, F64.ofInt ((n : Int) - 3))

/-- A double in [0, 1) for `Math.random()`. -/
def genUnit (r : Rng) : Rng × F64 :=
  let (r, n) := r.below 1000
  (r, F64.ofNat n / F64.ofNat 1000)

def memAt : (ts : List Ty) → (i : Nat) → (h : i < ts.length) → Mem (ts.get ⟨i, h⟩) ts
  | _ :: _, 0, _ => .here
  | _ :: ts, i + 1, h => .there (memAt ts i (by simp at h; omega))

/-- The initialised fields of an object, all of them. -/
def toOVals : {ts : List Ty} → Vals TT ts → OVals TT ts
  | _, .nil => .nil
  | _, .cons v vs => .cons (some v) (toOVals vs)

mutual
/-- Random values of type `t` (`none`: a type the search does not generate, e.g. functions);
`d` bounds the depth of named (recursive) types. -/
partial def gen (r : Rng) (w : World TT) (d : Nat) (sm : Bool := false) : (t : Ty) → Option (Rng × Val TT t × World TT)
  | .num => let (r, x) := if sm then genF64Small r else genF64 r; some (r, .num x, w)
  | .str => let (r, s) := genStr' r; some (r, .str s, w)
  | .bool => let (r, b) := r.below 2; some (r, .bool (b == 1), w)
  | .bigint => let (r, n) := r.below 2001; some (r, .bigint ((n : Int) - 1000), w)
  | .undef => some (r, .undef, w)
  | .null => some (r, .null, w)
  | .err => let (r, s) := genStr r; some (r, .err (mkErr .error s), w)
  | .enum cs =>
    if h : 0 < cs.length then
      let (r, i) := r.below cs.length
      some (r, .enum ⟨i % cs.length, Nat.mod_lt _ h⟩, w)
    else none
  | .opt t =>
    let (r, b) := r.below 4
    if b == 0 then some (r, .none, w)
    else (gen r w d sm t).map fun (r, v, w) => (r, .some v, w)
  | .record fs => (genList r w d sm fs.types).map fun (r, vs, w) => (r, .record vs, w)
  | .tup ts => (genList r w d sm ts.toList).map fun (r, vs, w) => (r, .tup vs, w)
  | .union ts =>
    let l := ts.toList
    if h : 0 < l.length then
      let (r, i) := r.below l.length
      let i := i % l.length
      have hi : i < l.length := Nat.mod_lt _ h
      (gen r w d sm (l.get ⟨i, hi⟩)).map fun (r, v, w) => (r, .inj (memAt l i hi) v, w)
    else none
  | .named n => if d = 0 then none else (gen r w (d - 1) sm (TT.alias n)).map fun (r, v, w) => (r, .fold v, w)
  | .dyn =>
    -- a value of any type: primitives, an array, a bigint, or an object of the host (an
    -- external handle: in JavaScript, some object the program did not create)
    let (r, k) := r.below 8
    match k with
    | 0 => (gen r w d sm .num).map fun (r, v, w) => (r, .dyn .num v, w)
    | 1 => (gen r w d sm .str).map fun (r, v, w) => (r, .dyn .str v, w)
    | 2 => (gen r w d sm .bool).map fun (r, v, w) => (r, .dyn .bool v, w)
    | 3 => some (r, .dyn .undef .undef, w)
    | 4 => some (r, .dyn .null .null, w)
    | 5 => (gen r w d sm (.arr .num)).map fun (r, v, w) => (r, .dyn (.arr .num) v, w)
    | 6 => (gen r w d sm .bigint).map fun (r, v, w) => (r, .dyn .bigint v, w)
    | _ => some (r, .dyn (.ext "host") (.ext 0), w)
  | .arr t =>
    let (r, len) := r.below (if d = 0 then 1 else 6)
    -- elements of a type the search does not generate (functions): an empty array
    let (r, xs, w) := (genElems r w d sm t len #[]).getD (r, #[], w)
    let a := w.next
    some (r, .arr a, { w with heap := w.heap.insert (.arr t, a) xs, next := a + 1 })
  | .map k v =>
    let (r, len) := r.below (if d = 0 then 1 else 5)
    match genEntries r w d sm k v len {} with
    | some (r, m, w) =>
      let a := w.next
      some (r, .map a, { w with heap := w.heap.insert (.map k v, a) m, next := a + 1 })
    | none => none
  | .set t =>
    let (r, len) := r.below (if d = 0 then 1 else 5)
    match genEntries r w d sm t .undef len {} with
    | some (r, m, w) =>
      let s : JSMap (Val TT t) Unit := ⟨m.entries.map (·.map fun (k, _) => (k, ()))⟩
      let a := w.next
      some (r, .set a, { w with heap := w.heap.insert (.set t, a) s, next := a + 1 })
    | none => none
  | .dict t =>
    let (r, len) := r.below (if d = 0 then 1 else 5)
    match genDict r w d sm t len {} with
    | some (r, m, w) =>
      let a := w.next
      some (r, .dict a, { w with heap := w.heap.insert (.dict t, a) m, next := a + 1 })
    | none => none
  | .obj c =>
    let fs := (TT.fields c).types
    match genList r w d sm fs with
    | some (r, vs, w) =>
      let a := w.next
      some (r, .obj a, { w with heap := w.heap.insert (.obj c fs, a) (toOVals vs), next := a + 1 })
    | none => none
  | _ => none

partial def genList (r : Rng) (w : World TT) (d : Nat) (sm : Bool := false) : (ts : List Ty) → Option (Rng × Vals TT ts × World TT)
  | [] => some (r, .nil, w)
  | t :: ts => match gen r w d sm t with
    | some (r, v, w) => (genList r w d sm ts).map fun (r, vs, w) => (r, .cons v vs, w)
    | none => none

partial def genElems (r : Rng) (w : World TT) (d : Nat) (sm : Bool) (t : Ty) :
    Nat → Array (Val TT t) → Option (Rng × Array (Val TT t) × World TT)
  | 0, acc => some (r, acc, w)
  | n + 1, acc => match gen r w (d - 1) sm t with
    | some (r, v, w) => genElems r w d sm t n (acc.push v)
    | none => none

partial def genEntries (r : Rng) (w : World TT) (d : Nat) (sm : Bool) (k v : Ty) :
    Nat → JSMap (Val TT k) (Val TT v) → Option (Rng × JSMap (Val TT k) (Val TT v) × World TT)
  | 0, m => some (r, m, w)
  | n + 1, m => match gen r w (d - 1) sm k with
    | some (r, kv, w) => match gen r w (d - 1) sm v with
      | some (r, vv, w) => genEntries r w d sm k v n (m.set (Conv.svz k) (normKey k kv) vv)
      | none => none
    | none => none

partial def genDict (r : Rng) (w : World TT) (d : Nat) (sm : Bool) (t : Ty) :
    Nat → JSMap JSStr (Val TT t) → Option (Rng × JSMap JSStr (Val TT t) × World TT)
  | 0, m => some (r, m, w)
  | n + 1, m =>
    let (r, key) := genStr' r
    if key == JSStr.ofString "__proto__" then genDict r w d sm t n m else
    match gen r w (d - 1) sm t with
    | some (r, vv, w) => genDict r w d sm t n (m.set (· == ·) key vv)
    | none => none
end

def hex4 (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - ds.length) '0' ++ ds)

def jsStr (s : JSStr) : String :=
  "\"" ++ String.join (s.units.map fun u =>
    let n := u.toNat
    if n == 34 then "\\\"" else if n == 92 then "\\\\"
    else if 32 ≤ n && n < 127 then String.singleton (Char.ofNat n) else "\\u" ++ hex4 n) ++ "\""

def jsNum (x : F64) : String :=
  if x == F64.zero true then "-0" else
  match x with
  | .nan => "NaN"
  | .inf false => "Infinity"
  | .inf true => "-Infinity"
  | _ => toString (NumFormat.toJSString x)

/-- A JavaScript expression for a value (the Node harness defines `__mk(class, fields)` and
`__err(name, message)`). -/
partial def toJS (w : World TT) : (t : Ty) → Val TT t → String
  | .num, v => jsNum v.toNum
  | .str, v => jsStr v.toStr
  | .bool, v => toString v.toBool
  | .bigint, v => toString v.toBig ++ "n"
  | .undef, _ => "undefined"
  | .null, _ => "null"
  | .err, v => "__err(" ++ jsStr v.toErr.name ++ ", " ++ jsStr v.toErr.message ++ ")"
  | .enum cs, .enum i => jsStr (JSStr.ofString (cs.get i))
  | .opt _, .none => "undefined"
  | .opt t, .some v => toJS w t v
  | .record fs, .record vs => "{" ++ ", ".intercalate (fieldsJS w fs vs) ++ "}"
  | .tup ts, .tup vs => "[" ++ ", ".intercalate (listJS w ts.toList vs) ++ "]"
  | .union _, .inj (t := t) _ v => toJS w t v
  | .named n, .fold v => toJS w (TT.alias n) v
  | .dyn, .dyn t v => toJS w t v
  | .ext _, _ => "({})"
  | .arr t, v => match w.heap.get? (.arr t, v.arrAddr) with
    | some xs => "[" ++ ", ".intercalate (xs.toList.map (toJS w t)) ++ "]"
    | none => "<dangling>"
  | .map k vt, v => match w.heap.get? (.map k vt, v.mapAddr) with
    | some m => "new Map([" ++ ", ".intercalate (m.toList.map fun (a, b) => "[" ++ toJS w k a ++ ", " ++ toJS w vt b ++ "]") ++ "])"
    | none => "<dangling>"
  | .set t, v => match w.heap.get? (.set t, v.setAddr) with
    | some m => "new Set([" ++ ", ".intercalate (m.toList.map fun (a, _) => toJS w t a) ++ "])"
    | none => "<dangling>"
  | .dict t, .dict a => match w.heap.get? (.dict t, a) with
    | some m => "Object.fromEntries([" ++ ", ".intercalate (m.toList.map fun (k, b) => "[" ++ jsStr k ++ ", " ++ toJS w t b ++ "]") ++ "])"
    | none => "<dangling>"
  | .obj c, v => match w.heap.get? (.obj c (TT.fields c).types, v.objAddr) with
    | some os => "__mk(" ++ jsStr (JSStr.ofString c) ++ ", {" ++ ", ".intercalate (objJS w (TT.fields c) os) ++ "})"
    | none => "<dangling>"
  | _, _ => "<value>"
where
  fieldsJS (w : World TT) : (fs : Fields) → Vals TT fs.types → List String
    | .nil, _ => []
    | .cons n t fs, .cons v vs => (jsStr (JSStr.ofString n) ++ ": " ++ toJS w t v) :: fieldsJS w fs vs
  listJS (w : World TT) : (ts : List Ty) → Vals TT ts → List String
    | [], _ => []
    | t :: ts, .cons v vs => toJS w t v :: listJS w ts vs
  objJS (w : World TT) : (fs : Fields) → OVals TT fs.types → List String
    | .nil, _ => []
    | .cons n t fs, .cons o os =>
      (jsStr (JSStr.ofString n) ++ ": " ++ (match o with | some v => toJS w t v | none => "undefined")) :: objJS w fs os

def argsJS (w : World TT) : (ts : List Ty) → Vals TT ts → List String
  | [], _ => []
  | t :: ts, .cons v vs => toJS w t v :: argsJS w ts vs

/-- Run `f` on `n` random inputs (seed `seed`); append each panicking input (at most `maxFound`
distinct panic messages) to `out`. -/
def search (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : FunRef args ret) (name : String)
    (out : System.FilePath) (n : Nat := 300) (seed : UInt64 := 7) (maxFound : Nat := 3) (small : Bool := false) :
    IO Unit := do
  let emit (s : String) : IO Unit := IO.FS.withFile out .append fun h => do h.putStrLn s; h.flush
  let mut r : Rng := ⟨seed⟩
  let mut msgs : List String := []
  let mut runs := 0
  for _ in [0:n] do
    let w0 : World TT := initWorld I P
    let (r1, s) := r.next
    r := r1
    let w0 := { w0 with rand := fun i => (genUnit ⟨s + i.toUInt64⟩).2 }
    match genList r w0 3 small args.toList with
    | none => emit s!"NPUNSUPPORTED {name}"; return
    | some (r', vs, w) =>
      r := r'
      runs := runs + 1
      match (callFun I P f vs).run.run w with
      | some (.error (.panic m), _) =>
        if !msgs.contains m then
          msgs := m :: msgs
          emit s!"NPCE {name} :: {m} :: [{", ".intercalate (argsJS w args.toList vs)}]"
          if msgs.length ≥ maxFound then break
      | _ => pure ()
  emit s!"NPDONE {name} {runs}"

end StrictTS.PanicSearch
