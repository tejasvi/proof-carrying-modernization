import CIR

/-!
  `vo-cirrun [--show] UNIT.cir... -- FUNCTION ARGS…`: veriforch's runner for LINKED C programs. It is cirlean's
  `cirrun` (CirRun.lean, copied unchanged below the documentation: argument parsing, result printing) with one
  difference: it takes several translation units and links them as `cir2lean --link` does (string literals named
  by content, internal symbols of a unit prefixed `<unit>$`, `CIR.Frontend.linkUnits`), so a function of a linked
  build is run in the linked program, with its calls into other units resolved. With one unit it is `cirrun`.

  `FUNCTION` is a linked symbol (`re$matchpattern` for a static function of re.c), a mangled symbol, a full
  demangled name, or a plain function name. Arguments and output are cirrun's (see below).

  Original documentation of cirrun:
  `cirrun FILE.cir FUNCTION ARGS…`: run a function of a ClangIR module in
  the Lean semantics and print its result.

  `FUNCTION` is a mangled symbol, a full demangled name, or a plain function
  name (`sum_to` matches `sum_to(int)`). Arguments, by parameter type:
  * integer or `bool` parameter: an integer, `5`;
  * `std::vector<T>` (by value) or a reference/pointer to one: `[1,2,3]`;
  * pointer or reference to an integer: `&5`; to the first element of an
    integer array: `&[1,2,3]`;
  * reference to a class whose data members are integers: `{1,2}`.

  Output: the returned value (integers; bools as 0/1; containers as
  `[…]`), `void`, `exception <typeinfo>`, or `UB: <reason>`. With `--show`,
  one more line gives the final contents of the pointer arguments. With the
  environment variable `CIR_TRACE` set, the named local variables are printed
  to stderr at every loop head (`@LOOP name=value …`).
  Non-terminating programs do not terminate here either (run under `timeout`).
-/

open CIR CIR.Frontend

def nameMatches (f : FuncDecl) (n : String) : Bool :=
  f.sym == n || f.demangled == n ||
    (f.demangled.splitOn "(").head? == some n

def strTrim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- `[1,2,3]` / `{1,2}` → the integers. -/
def parseInts (s : String) (op cl : Char) : Option (List Int) := do
  guard (s.startsWith op.toString && s.endsWith cl.toString)
  let inner := ((s.drop 1).dropRight 1).toString
  if (strTrim inner).isEmpty then return []
  (inner.splitOn ",").mapM fun t => (strTrim t).toInt?

/-- The element type of a `std::vector<T, …>` record name (integers only). -/
def vecElem? (name : String) : Option Ty :=
  let afterVec := (name.splitOn "vector<").getD 1 ""
  let elem := strTrim ((afterVec.splitOn ",").headD "")
  match elem with
  | "int" => some (.int true 32)
  | "unsigned int" => some (.int false 32)
  | "long" | "long long" | "int64_t" => some (.int true 64)
  | "unsigned long" | "unsigned long long" | "uint64_t" | "size_t" => some (.int false 64)
  | "short" => some (.int true 16)
  | "unsigned short" => some (.int false 16)
  | "char" | "signed char" => some (.int true 8)
  | "unsigned char" => some (.int false 8)
  | "bool" => some .bool
  | _ => none

def isVecName (n : String) : Bool := (n.splitOn "vector<").length > 1

def elemVal (t : Ty) (i : Int) : Except String Val :=
  match t with
  | .int s w => if inRange s w i then .ok (.int i) else .error s!"{i} out of range for the element type"
  | .bool => .ok (.bool (i != 0))
  | _ => .error "unsupported element type"

/-- Build an argument value, allocating the blocks it points to. -/
def argVal (ctx : CIR.Ctx) (ty : Ty) (s : String) (m : Mem) : Except String (Val × Mem) := do
  match ty with
  | .int sg w =>
    let some i := s.toInt? | throw s!"not an integer: {s}"
    if inRange sg w i then return (.int i, m) else throw s!"{i} out of range for the parameter"
  | .bool =>
    let some i := s.toInt? | throw s!"not an integer: {s}"
    return (.bool (i != 0), m)
  | .record n =>
    unless isVecName n do throw s!"unsupported by-value parameter type {n}"
    let some e := vecElem? n | throw s!"unsupported vector element type in {n}"
    let some xs := parseInts s '[' ']' | throw s!"expected [..] for {n}"
    let vs ← xs.mapM (elemVal e)
    let (g, m) := Std.fresh m
    return (.vec g vs, m)
  | .ptr (.record n) =>
    if isVecName n then
      let some e := vecElem? n | throw s!"unsupported vector element type in {n}"
      let some xs := parseInts s '[' ']' | throw s!"expected [..] for {n}"
      let vs ← xs.mapM (elemVal e)
      let (g, m) := Std.fresh m
      let (b, m) := m.alloc .stack (.record n) (.vec g vs)
      return (.ptr (.loc b []), m)
    else
      let some xs := parseInts s '{' '}' | throw ("expected {..} for " ++ n)
      let some r := ctx.record? n | throw s!"unknown class {n}"
      let tys := (r.members.filter (fun mt => mt.1 == .data)).map (·.2)
      unless tys.length == xs.length do throw s!"{n} has {tys.length} data members"
      let fields ← (tys.zip xs).mapM fun (t, x) => elemVal t x
      -- padding members hold nothing
      let rec fill (ms : List (MemberKind × Ty)) (fs : List Val) : List Val :=
        match ms, fs with
        | [], _ => []
        | (.data, _) :: ms, f :: fs => f :: fill ms fs
        | (_, t) :: ms, fs => ctx.initVal 32 t :: fill ms fs
      let (b, m) := m.alloc .stack (.record n) (.agg (fill r.members fields))
      return (.ptr (.loc b []), m)
  | .ptr t =>
    if let some xs := parseInts ((s.drop 1).toString) '[' ']' then
      let vs ← xs.mapM (elemVal t)
      let (b, m) := m.alloc .stack (.array t vs.length) (.arr vs)
      return (.ptr (.loc b [.idx 0]), m)
    else
      let some i := ((s.drop 1).toString).toInt? | throw s!"expected &n or &[..] for a pointer: {s}"
      let v ← elemVal t i
      let (b, m) := m.alloc .stack t v
      return (.ptr (.loc b []), m)
  | _ => throw "unsupported parameter type"

def showVal (m : Mem) (v : Val) : String :=
  match v with
  | .int i => toString i
  | .bool b => if b then "1" else "0"
  | .vec _ xs | .arr xs =>
    "[" ++ ",".intercalate (xs.map fun x => match x with
      | .int i => toString i | .bool b => if b then "1" else "0" | _ => "?") ++ "]"
  | .opt none => "nullopt"
  | .opt (some (.int i)) => s!"opt {i}"
  | .ptr (.loc b path) =>
    match m.read? (.loc b path) with
    | some (.int i) => s!"*{i}"
    | _ => "pointer"
  | _ => "value"

def showResult (r : Res (Exit × Mem)) : String :=
  match r with
  | .ok (.ret (some v), m) => showVal m v
  | .ok (.ret none, _) => "void"
  | .ok (.exn x, _) => s!"exception {x.typeinfo}"
  | .ok (_, _) => "abnormal exit"
  | .ub msg => s!"UB: {msg}"
  | .div => "diverges"

/-- The program of the given units: one unit as cirrun loads it, several linked as `cir2lean --link` does. -/
def loadLinked (files : List String) : IO Module := do
  match files with
  | [f] => loadModule f
  | _ =>
    let mut units : Array (String × Module) := #[]
    let mut tags : Std.HashSet String := {}
    for inp in files do
      let m ← loadModule inp
      let stem := (System.FilePath.mk inp).fileStem.getD "unit"
      let base := String.ofList (stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
      let mut tag := base
      let mut k := 1
      while tags.contains tag do
        k := k + 1
        tag := s!"{base}_{k}"
      tags := tags.insert tag
      units := units.push (tag, contentNamedLiterals m)
    match linkUnits "VoCirRun" units.toList with
    | .error e => throw (IO.userError s!"link: {e}")
    | .ok (merged, _) => pure merged

def main (args : List String) : IO UInt32 := do
  let show_ := args.contains "--show"
  let args := args.filter (· != "--show")
  let files := args.takeWhile (· != "--")
  let rest0 := (args.dropWhile (· != "--")).drop 1
  match files, rest0 with
  | _ :: _, fn :: rest =>
    let m ← loadLinked files
    let some f := m.funcs.find? (nameMatches · fn) |
      IO.eprintln s!"vo-cirrun: no function {fn} in {files}"; return 2
    if f.params.length != rest.length then
      IO.eprintln s!"vo-cirrun: {f.demangled} takes {f.params.length} arguments"; return 2
    let ctx := Ctx.ofModule m
    let mut mem := m.initMem
    let mut vals : Array Val := #[]
    for (t, s) in f.params.zip rest do
      match argVal ctx t s mem with
      | .ok (v, mem') => vals := vals.push v; mem := mem'
      | .error e => IO.eprintln s!"vo-cirrun: {e}"; return 2
    let r := evalCall ctx f.sym vals.toList mem
    IO.println (showResult r)
    if show_ then
      if let .ok (_, m') := r then
        let outs := vals.toList.filterMap fun v => match v with
          | .ptr (.loc b path) => some (match m'.read? (.loc b path) with
            | some w => showVal m' w
            | none => "dead")
          | _ => none
        IO.println ("args " ++ " ".intercalate outs)
    return 0
  | _, _ =>
    IO.eprintln "usage: vo-cirrun [--show] UNIT.cir... -- FUNCTION ARGS..."
    return 2
