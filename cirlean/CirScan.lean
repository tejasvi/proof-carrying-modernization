import CIR

/-!
  `cirscan [--json] FILE.cir…`: coverage of the user functions of ClangIR
  modules (`--json`: one JSON object per function, with parameter names and
  types, for tools).

  For each function defined in the user's code (not a standard library
  instantiation), follows direct calls through everything that would be
  executed, the module's global constructors and destructors included
  (callees with a library model are not entered), and reports, as one
  tab-separated line:

    file  function  loops  status  external-calls  unknown-ops  library-bodies  params

  `status` is `in_scope` when every executed function has a body or a model
  and contains only operations the semantics knows; otherwise the blockers
  are listed (`external:` functions with neither body nor model, `unknown:`
  operations). `library-bodies` counts library functions without a model
  whose bodies would be executed (libc++ internals).
-/

open CIR CIR.Frontend

structure BodyInfo where
  calls : Array String := #[]
  indirect : Nat := 0
  unknown : Array String := #[]
  loops : Nat := 0

mutual
partial def scanOp (acc : BodyInfo) : Op → BodyInfo
  | .call _ _ (.direct s) _ _ _ _ => { acc with calls := acc.calls.push s }
  | .call _ _ (.indirect _) _ _ _ _ => { acc with indirect := acc.indirect + 1 }
  | .unknown n _ => { acc with unknown := acc.unknown.push n }
  | .scope _ r => scanRegion acc r
  | .cleanupScope _ a b => scanRegion (scanRegion acc a) b
  | .ifOp _ a b => scanRegion (scanRegion acc a) b
  | .ternary _ _ a b => scanRegion (scanRegion acc a) b
  | .forOp _ a b c cl =>
    let acc := { acc with loops := acc.loops + 1 }
    let acc := scanRegion (scanRegion (scanRegion acc a) b) c
    match cl with | some (_, r) => scanRegion acc r | none => acc
  | .whileOp _ a b cl =>
    let acc := { acc with loops := acc.loops + 1 }
    let acc := scanRegion (scanRegion acc a) b
    match cl with | some (_, r) => scanRegion acc r | none => acc
  | .doWhileOp _ a b =>
    scanRegion (scanRegion { acc with loops := acc.loops + 1 } a) b
  | .switch _ _ r | .setjmp _ _ _ _ _ r | .setjmpRun _ _ _ r => scanRegion acc r
  | .case _ _ r => scanRegion acc r
  | .tryOp b hs u =>
    let acc := scanRegion acc b
    let acc := hs.foldl (fun acc (_, r) => scanRegion acc r) acc
    match u with | some r => scanRegion acc r | none => acc
  | _ => acc
partial def scanRegion (acc : BodyInfo) : Region → BodyInfo
  | .mk bs => bs.foldl (fun acc (.mk _ ops) => ops.foldl scanOp acc) acc
end

/-- The qualified name of a demangled function signature: the last token at
template depth 0 before the parameter list (drops a leading return type). -/
def qualifiedName (d : String) : String := Id.run do
  let head := (d.splitOn "(").headD d
  if (head.splitOn "operator").length > 1 then
    return "operator" ++ ((head.splitOn "operator").getLastD "")
  let mut depth := 0
  let mut cur := ""
  for c in head.toList do
    if c == '<' then depth := depth + 1
    if c == '>' then depth := depth - 1
    if c == ' ' && depth == 0 then cur := "" else cur := cur.push c
  return cur

/-- Library code, by the mangled name: namespaces `std` (libc++ `std::__1`),
`__gnu_cxx`, `__cxxabiv1`, runtime symbols `__…`, and `operator new`/`delete`. -/
def isLibrary (f : FuncDecl) : Bool :=
  let s := f.sym
  ["__", "_ZNSt", "_ZNKSt", "_ZSt", "_ZNVKSt", "_ZN9__gnu_cxx", "_ZNK9__gnu_cxx", "_ZN10__cxxabiv1",
   "_Znw", "_Zna", "_Zdl", "_Zda"].any (fun (p : String) => s.startsWith p)

def paramKind (t : Ty) : String :=
  match t with
  | .int s w => s!"{if s then "i" else "u"}{w}"
  | .bool => "bool"
  | .float _ => "float"
  | .ptr (.record n) => if (n.splitOn "vector").length > 1 then "vec&" else s!"&{(n.take 30).toString}"
  | .ptr (.int _ _) => "int*"
  | .ptr _ => "ptr"
  | .record n => s!"rec:{(n.take 30).toString}"
  | .array _ _ => "array"
  | _ => "other"

/-- The C++ names of a function's parameters: the allocas the entry block
stores its arguments into (`""` when not found). -/
def paramNames (f : FuncDecl) : List String :=
  match f.body with
  | some (.mk (.mk params ops :: _)) =>
    let allocas : List (VId × String) := ops.filterMap fun op => match op with
      | .alloca r _ n => some (r, n)
      | .allocaConst r _ n => some (r, n)
      | _ => none
    params.map fun p =>
      let target := ops.findSome? fun op => match op with
        | .store v a _ => if v == p then some a else none
        | _ => none
      match target with
      | some a => ((allocas.find? (·.1 == a)).map (·.2)).getD ""
      | none => ""
  | _ => f.params.map fun _ => ""

def jsonStr (s : String) : String := s.quote

def jsonList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def scanModule (file : String) (m : Module) (json : Bool) : IO Unit := do
  let byName : Std.HashMap String FuncDecl :=
    m.funcs.foldl (fun h f => h.insert f.sym f) {}
  let info : Std.HashMap String BodyInfo :=
    m.funcs.foldl (fun h f => match f.body with
      | some r => h.insert f.sym (scanRegion {} r)
      | none => h) {}
  for f in m.funcs do
    if f.body.isNone || isLibrary f then continue
    -- everything that would be executed (the module's constructors and destructors run around
    -- any entry)
    let mut seen : Std.HashSet String := {}
    let mut work := #[f.sym] ++ (m.ctors ++ m.dtors).toArray.map (·.1)
    let mut externals : Array String := #[]
    let mut unknown : Array String := #[]
    let mut libBodies := 0
    while h : work.size > 0 do
      let s := work[work.size - 1]
      work := work.pop
      if seen.contains s then continue
      seen := seen.insert s
      match byName[s]? with
      | none => externals := externals.push s
      | some g =>
        if g.model.isSome then continue
        match info[s]? with
        | none =>
          let d := if g.demangled.isEmpty then g.sym else g.demangled
          externals := externals.push (d.take 60).toString
        | some bi =>
          if s != f.sym && isLibrary g && !s.startsWith "__cxx_global_var_init" then
            libBodies := libBodies + 1
          for u in bi.unknown do
            unless unknown.contains u do unknown := unknown.push u
          for c in bi.calls do
            unless seen.contains c do work := work.push c
    let loops := (info[f.sym]?.map (·.loops)).getD 0
    let status :=
      if externals.isEmpty && unknown.isEmpty then "in_scope"
      else if !externals.isEmpty then "external" else "unknown_op"
    let name := if f.demangled.isEmpty then f.sym else f.demangled
    if json then
      let params := (f.params.zip (paramNames f)).map fun (t, n) =>
        "{" ++ s!"\"name\":{jsonStr n},\"ty\":{jsonStr (Emit.ty t)},\"kind\":{jsonStr (paramKind t)}" ++ "}"
      IO.println ("{" ++ s!"\"file\":{jsonStr file},\"sym\":{jsonStr f.sym},\"name\":{jsonStr name}," ++
        s!"\"loops\":{loops},\"status\":{jsonStr status},\"ret\":{jsonStr (Emit.ty f.ret)}," ++
        s!"\"externals\":{jsonList (externals.toList.map jsonStr)},\"unknown\":{jsonList (unknown.toList.map jsonStr)}," ++
        s!"\"library_bodies\":{libBodies},\"params\":{jsonList params}," ++
        s!"\"callees\":{jsonList (((info[f.sym]?.map (·.calls.toList)).getD []).eraseDups.map jsonStr)}," ++
        s!"\"globals\":{m.globals.length}" ++ "}")
    else
      IO.println s!"{file}\t{name}\t{loops}\t{status}\t{",".intercalate externals.toList}\t{",".intercalate unknown.toList}\t{libBodies}\t{" ".intercalate (f.params.map paramKind)}"

def main (args : List String) : IO UInt32 := do
  let json := args.contains "--json"
  let args := args.filter (· != "--json")
  if args.isEmpty then
    IO.eprintln "usage: cirscan [--json] FILE.cir..."
    return 2
  for file in args do
    try
      let m ← loadModule file
      scanModule file m json
    catch e =>
      IO.eprintln s!"{file}: {e}"
  return 0
