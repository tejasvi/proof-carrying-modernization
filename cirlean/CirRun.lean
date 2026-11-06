import CIR

/-!
  `cirrun FILE.cir FUNCTION ARGS…`: run a function of a ClangIR module in
  the Lean semantics and print its result.

  `FUNCTION` is a mangled symbol, a full demangled name, or a plain function
  name (`sum_to` matches `sum_to(int)`). Arguments, by parameter type:
  * integer or `bool` parameter: an integer, `5`;
  * `std::vector<T>` (by value) or a reference/pointer to one: `[1,2,3]`;
  * pointer or reference to an integer: `&5`; to the first element of an
    integer array: `&[1,2,3]`;
  * reference to a class whose data members are integers: `{1,2}`.
  `main` run without arguments gets those of the runner's harness (`mainArgs`): `argc` = 1 for
  `main(int)`, and `argv` = `{"prog", NULL}` too for `main(int, char **)`.

  As around `main`, the module's global constructors run before the function, and when it
  returns or calls `exit` the exit sequence follows: the `atexit` handlers and the global
  destructors (`CIR/Semantics/Program.lean`); `_Exit` and `quick_exit` skip it.

  Output: the returned value (integers; bools as 0/1; containers as
  `[…]`), `void`, `exception <typeinfo>`, or `UB: <reason>`. A program that
  ends by `exit(n)` (or `_Exit`, `quick_exit`, also from a constructor, a
  handler or a destructor) prints `n`, as a return of `n` from `main` would.
  With `--show`,
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

/-- The arguments of `main` run without any, as the runner's harness passes them (README, trust
base): `argc` = 1 for `main(int)` (C11 5.1.2.2.1p1 allows such implementation-defined forms; GCC and
glibc pass `argc`), and `argv` = `{"prog", NULL}` too for `main(int, char **)`, its string
modifiable (p2); `none` for any other parameter list. -/
def mainArgs (params : List Ty) (m : Mem) : Option (List Val × Mem) :=
  match params with
  | [.int _ 32] => some ([.int 1], m)
  | [.int _ 32, .ptr (.ptr (.int sg 8))] =>
    let (sb, m) := m.alloc .global (.array (.int sg 8) 5) (.arr (([112, 114, 111, 103, 0] : List Int).map Val.int))
    let (ab, m) := m.alloc .global (.array (.ptr (.int sg 8)) 2) (.arr [.ptr (.loc sb [.idx 0]), .ptr .null])
    some ([.int 1, .ptr (.loc ab [.idx 0])], m)
  | _ => none

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
  -- `exit(n)`: printed as `main` returning `n` (C11 5.1.2.2.3)
  | .ok (.halt n, _) => toString n
  | .ok (_, _) => "abnormal exit"
  | .ub msg => s!"UB: {msg}"
  | .div => "diverges"

def main (args : List String) : IO UInt32 := do
  let show_ := args.contains "--show"
  let args := args.filter (· != "--show")
  match args with
  | file :: fn :: rest =>
    let m ← loadModule file
    let some f := m.funcs.find? (nameMatches · fn) |
      IO.eprintln s!"cirrun: no function {fn} in {file}"; return 2
    -- `main` with parameters run without arguments gets those of the runner's harness (`mainArgs`)
    let auto := rest.isEmpty && f.sym == "main" && !f.params.isEmpty
    if !auto && f.params.length != rest.length then
      IO.eprintln s!"cirrun: {f.demangled} takes {f.params.length} arguments"; return 2
    let ctx := Ctx.ofModule m
    -- the global constructors run first, as before `main`; one of them may end the program
    let mut mem ← match runCtors ctx m m.initMem with
      | .ok (none, mem) => pure mem
      | .ok (some n, mem) => IO.println (showResult (endProgram ctx m (.halt n) mem)); return 0
      | .ub msg => IO.println s!"UB: {msg}"; return 0
      | .div => IO.println "diverges"; return 0
    let mut vals : Array Val := #[]
    if auto then
      match mainArgs f.params mem with
      | some (vs, mem') => vals := vs.toArray; mem := mem'
      | none => IO.eprintln s!"cirrun: {f.demangled} takes {f.params.length} arguments"; return 2
    else
      for (t, s) in f.params.zip rest do
        match argVal ctx t s mem with
        | .ok (v, mem') => vals := vals.push v; mem := mem'
        | .error e => IO.eprintln s!"cirrun: {e}"; return 2
    let r := evalCall ctx f.sym vals.toList mem
    -- after a return or `exit`: the exit sequence
    let r := match r with
      | .ok (e, m') =>
        match endProgram ctx m e m' with
        | .ub msg => .ub s!"{msg} (after {fn} ended)"
        | r' => r'
      | r => r
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
  | _ =>
    IO.eprintln "usage: cirrun [--show] FILE.cir FUNCTION ARGS..."
    return 2
