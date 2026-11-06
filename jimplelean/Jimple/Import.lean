/-
  Jimple/Import.lean

  `jimple_import "path" as Foo` parses a `.jimple` file, or all `*.jimple` files of a
  directory (sorted by file name), when the command is elaborated, and defines
  * `Foo.«C».«m(T1,T2)» : Jimple.Body` for each method body, where `C` is the class name and
    `T1,T2` the parameter types printed without quotes (`«main(java.lang.String[])»`,
    `«safeDiv(int,int)»`); only if two methods of a class share name and parameters (bridge
    methods) is the return type appended: `«m(T1,T2):R»`;
  * `Foo.«C» : Jimple.ClassDecl`, whose `MethodDecl.body` fields are those constants, so goals
    about a class do not contain the bodies;
  * `Foo.prog : Jimple.Program`, the classes in file order.
  The definitions are compiled, so they can be run with `#eval`. Relative paths are resolved
  against the working directory of the Lean process. The prefix `Foo` is relative to the
  current namespace, as for `def`.
-/
import Lean.Elab.Command
import Jimple.Parser

namespace Jimple.Import

deriving instance Lean.ToExpr for PrimType
deriving instance Lean.ToExpr for JType
deriving instance Lean.ToExpr for MethodSig
deriving instance Lean.ToExpr for FieldSig
deriving instance Lean.ToExpr for Const
deriving instance Lean.ToExpr for Imm
deriving instance Lean.ToExpr for IdRef
deriving instance Lean.ToExpr for Ref
deriving instance Lean.ToExpr for BinOp
deriving instance Lean.ToExpr for UnOp
deriving instance Lean.ToExpr for InvKind
deriving instance Lean.ToExpr for Invoke
deriving instance Lean.ToExpr for Expr
deriving instance Lean.ToExpr for LValue
deriving instance Lean.ToExpr for Stmt
deriving instance Lean.ToExpr for Trap
deriving instance Lean.ToExpr for Body
deriving instance Lean.ToExpr for MethodMods
deriving instance Lean.ToExpr for FieldDecl

open Lean Elab Command

/-- `name(T1,T2)` -/
def methodKey (m : MethodDecl) : String := s!"{m.name}({Parser.paramsStr m.params})"

/-- The name components of the body constants of a class, in method order. -/
def methodKeys (c : ClassDecl) : List String :=
  c.methods.map fun m =>
    let k := methodKey m
    if (c.methods.filter (methodKey · == k)).length > 1 then s!"{k}:{Parser.typeStr m.ret}"
    else k

private def listExpr (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [.zero]) ty)

/-- `MethodDecl` whose body is the constant `body?` (if any). -/
private def methodDeclExpr (m : MethodDecl) (body? : Option Name) : Lean.Expr :=
  let bodyTy := mkConst ``Jimple.Body
  let b := match body? with
    | some n => mkApp2 (mkConst ``Option.some [.zero]) bodyTy (mkConst n)
    | none => mkApp (mkConst ``Option.none [.zero]) bodyTy
  mkAppN (mkConst ``Jimple.MethodDecl.mk)
    #[toExpr m.name, toExpr m.params, toExpr m.ret, toExpr m.mods, toExpr m.throws, b]

private def classDeclExpr (c : ClassDecl) (methods : List Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``Jimple.ClassDecl.mk)
    #[toExpr c.name, toExpr c.isInterface, toExpr c.isAbstract, toExpr c.isEnum, toExpr c.super,
      toExpr c.interfaces, toExpr c.fields, listExpr (mkConst ``Jimple.MethodDecl) methods]

/-- Number of list elements inside a statement (switch targets, arguments, ...). -/
private def stmtWidth : Stmt → Nat
  | .tableSwitch _ _ ts _ => ts.length
  | .lookupSwitch _ cs _ => cs.length
  | .invoke i | .assign _ (.invoke i) => invWidth i
  | .assign _ (.newMultiArray _ ss _) => ss.length
  | _ => 0
where
  invWidth : Invoke → Nat
    | .inst _ _ m as | .static m as => m.params.length + as.length
    | .dynamic _ _ ps as bsm bas => ps.length + as.length + bsm.params.length + bas.length

/-- Number of list elements in a body. -/
private def bodySize (b : Body) : Nat :=
  b.stmts.foldl (fun n s => n + 1 + stmtWidth s) (b.locals.length + b.traps.length)

/-- Add and compile `n : type := value`, where `value` is a literal with about `size` list
    elements. Checking and compiling a list literal takes recursion depth and time proportional
    to its length (with the default limits the compiler stops at a few hundred statements), so
    `maxRecDepth` and `maxHeartbeats` are raised with `size`, both as options (read by the
    kernel and the compiler) and in the `CoreM` context. Extracting closed subterms is turned
    off: the whole value is a closed term already, and this divides the compilation time by
    about three. -/
private def addDef (n : Name) (type value : Lean.Expr) (size : Nat) : CoreM Unit := do
  let opts ← getOptions
  let depth := max (maxRecDepth.get opts) (32 * size + 1024)
  let hb := maxHeartbeats.get opts
  let hb := if hb == 0 then 0 else max hb (50 * size)
  let opts := (maxHeartbeats.set (maxRecDepth.set opts depth) hb).setBool
    `compiler.extract_closed false
  withOptions (fun _ => opts) <| withAtLeastMaxRecDepth depth <|
    withReader (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) do
      addAndCompile <| .defnDecl {
        name := n, levelParams := [], type := type, value := value,
        hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }

/-- The `.jimple` files denoted by `p`: `p` itself, or the `*.jimple` files of the directory
    `p` sorted by name. -/
def jimpleFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if (← p.isDir) then
    let es ← p.readDir
    let fs := es.filter (·.fileName.endsWith ".jimple")
    return (fs.qsort (·.fileName < ·.fileName)).map (·.path)
  else if (← p.pathExists) then
    return #[p]
  else
    throw <| IO.userError s!"no such file or directory: {p}"

/-- `jimple_import "path" as Foo`: import a `.jimple` file or a directory of them (see the
    module documentation of `Jimple.Import`). -/
syntax (name := jimpleImport) "jimple_import " str " as " ident : command

@[command_elab jimpleImport]
def elabJimpleImport : CommandElab := fun stx => do
  let `(jimple_import $path:str as $ns:ident) := stx | throwUnsupportedSyntax
  let p : System.FilePath := path.getString
  let p ← if p.isAbsolute then pure p else pure ((← IO.currentDir) / p)
  let files ← try jimpleFiles p catch e => throwErrorAt path "jimple_import: {e.toMessageData}"
  if files.isEmpty then throwErrorAt path "jimple_import: no .jimple files in {p.toString}"
  let base := (← getCurrNamespace) ++ ns.getId
  let mut classConsts : Array Name := #[]
  let mut decls : Array ClassDecl := #[]
  let mut seen : Std.HashSet Name := {}
  for f in files do
    let src ← IO.FS.readFile f
    let c ← match Parser.parseClass src with
      | .ok c => pure c
      | .error e => throwErrorAt path "jimple_import: {f.toString}: {e}"
    let cName := base.str c.name
    if c.name == "prog" then
      throwErrorAt path "jimple_import: {f.toString}: a class named 'prog' clashes with {base}.prog"
    if seen.contains cName then
      throwErrorAt path "jimple_import: {f.toString}: class {c.name} is defined twice"
    let keys := methodKeys c
    if keys.eraseDups.length != keys.length then
      throwErrorAt path "jimple_import: {f.toString}: class {c.name} declares a method twice"
    let mut methods : Array Lean.Expr := #[]
    for (m, k) in c.methods.zip keys do
      let declE ← match m.body with
        | some b =>
          let bName := cName.str k
          liftCoreM <| addDef bName (mkConst ``Jimple.Body) (toExpr b) (bodySize b)
          pure (methodDeclExpr m bName)
        | none => pure (methodDeclExpr m none)
      methods := methods.push declE
      -- `Foo.C.«m(sig)».ref : MethodRef`, so that statements name methods without the program
      liftCoreM <| addDef ((cName.str k).str "ref") (mkConst ``Jimple.MethodRef)
        (mkApp2 (mkConst ``Jimple.MethodRef.mk) (toExpr c.name) declE) (1 + m.params.length)
    let size := c.methods.foldl (fun n m => n + 1 + m.params.length + m.throws.length)
      (c.fields.length + c.interfaces.length)
    liftCoreM <| addDef cName (mkConst ``Jimple.ClassDecl) (classDeclExpr c methods.toList) size
    classConsts := classConsts.push cName
    decls := decls.push c
    seen := seen.insert cName
  let classes := listExpr (mkConst ``Jimple.ClassDecl) (classConsts.toList.map (mkConst ·))
  -- the index, precomputed (the same tree `ClassTree.ofList` builds), over the class constants
  let tree := ClassTree.ofList (decls.toList)
  let rec treeExpr : ClassTree → Lean.Expr
    | .leaf => mkConst ``Jimple.ClassTree.leaf
    | .node l h ds r => mkAppN (mkConst ``Jimple.ClassTree.node)
        #[treeExpr l, mkNatLit h,
          listExpr (mkConst ``Jimple.ClassDecl) (ds.map fun d => mkConst (base.str d.name)),
          treeExpr r]
  liftCoreM <| addDef (base.str "prog") (mkConst ``Jimple.Program)
    (mkApp2 (mkConst ``Jimple.Program.mk) classes (treeExpr tree)) classConsts.size

/-- The classes of the `.jimple` files denoted by `path` (a file or a directory). -/
private def parseClasses (path : TSyntax `str) : CommandElabM (Array (System.FilePath × ClassDecl)) := do
  let p : System.FilePath := path.getString
  let p ← if p.isAbsolute then pure p else pure ((← IO.currentDir) / p)
  let files ← try jimpleFiles p catch e => throwErrorAt path "{e.toMessageData}"
  if files.isEmpty then throwErrorAt path "no .jimple files in {p.toString}"
  files.mapM fun f => do
    let src ← IO.FS.readFile f
    match Parser.parseClass src with
    | .ok c => pure (f, c)
    | .error e => throwErrorAt path "{f.toString}: {e}"

/-- `MethodDecl` without its body (`Body.erased` in place of a body, as `MethodDecl.erase`). -/
private def erasedMethodDeclExpr (m : MethodDecl) : Lean.Expr :=
  let bodyTy := mkConst ``Jimple.Body
  let b := if m.body.isSome then mkApp2 (mkConst ``Option.some [.zero]) bodyTy (mkConst `Jimple.Body.erased)
    else mkApp (mkConst ``Option.none [.zero]) bodyTy
  mkAppN (mkConst ``Jimple.MethodDecl.mk)
    #[toExpr m.name, toExpr m.params, toExpr m.ret, toExpr m.mods, toExpr m.throws, b]

/-- `jimple_shape "path" as Foo`: for each class `C` of the file (or directory),
    `Foo.«C» : Jimple.ClassDecl`, the class without method bodies — definitionally the
    `ClassDecl.erase` of the class `jimple_import` defines. It changes only when signatures,
    modifiers, fields or the hierarchy change, so body proofs stated with `Shapes` over it are
    not affected by edits of other methods' bodies. -/
syntax (name := jimpleShape) "jimple_shape " str " as " ident : command

@[command_elab jimpleShape]
def elabJimpleShape : CommandElab := fun stx => do
  let `(jimple_shape $path:str as $ns:ident) := stx | throwUnsupportedSyntax
  let base := (← getCurrNamespace) ++ ns.getId
  for (_, c) in ← parseClasses path do
    let methods := c.methods.map erasedMethodDeclExpr
    let size := c.methods.foldl (fun n m => n + 1 + m.params.length + m.throws.length)
      (c.fields.length + c.interfaces.length)
    liftCoreM <| addDef (base.str c.name) (mkConst ``Jimple.ClassDecl) (classDeclExpr c methods) size

/-- `jimple_method "path" "m(T1,T2)" as Foo`: one method of the class in `path` (a file), as
    `jimple_import` would define it: `Foo.«C».«m(T1,T2)» : Jimple.Body` and
    `Foo.«C».«m(T1,T2)».ref : Jimple.MethodRef`. A body proof that imports only this module and
    the shapes it needs depends on no other method body. -/
syntax (name := jimpleMethod) "jimple_method " str str " as " ident : command

@[command_elab jimpleMethod]
def elabJimpleMethod : CommandElab := fun stx => do
  let `(jimple_method $path:str $key:str as $ns:ident) := stx | throwUnsupportedSyntax
  let base := (← getCurrNamespace) ++ ns.getId
  let cs ← parseClasses path
  let some (_, c) := cs[0]? | throwErrorAt path "no class"
  if cs.size != 1 then throwErrorAt path "jimple_method: expected one class file"
  let keys := methodKeys c
  let some (m, k) := (c.methods.zip keys).find? (·.2 == key.getString)
    | throwErrorAt key "jimple_method: class {c.name} has no method {key.getString} (methods: {keys})"
  let cName := base.str c.name
  let declE ← match m.body with
    | some b =>
      let bName := cName.str k
      liftCoreM <| addDef bName (mkConst ``Jimple.Body) (toExpr b) (bodySize b)
      pure (methodDeclExpr m bName)
    | none => pure (methodDeclExpr m none)
  liftCoreM <| addDef ((cName.str k).str "ref") (mkConst ``Jimple.MethodRef)
    (mkApp2 (mkConst ``Jimple.MethodRef.mk) (toExpr c.name) declE) (1 + m.params.length)

/-- The class constants of a program defined by `jimple_import` or `jimple_program`. -/
private def progClassConsts (n : Name) : CoreM (Array Name) := do
  let some (.defnInfo d) := (← getEnv).find? (n.str "prog")
    | throwError "jimple_program: {n}.prog is not a program definition"
  let some classes := d.value.getAppArgs[0]?
    | throwError "jimple_program: unexpected form of {n}.prog"
  let mut acc : Array Name := #[]
  let mut e := classes
  while e.isAppOfArity ``List.cons 3 do
    match e.appFn!.appArg! with
    | .const c _ => acc := acc.push c
    | _ => throwError "jimple_program: {n}.prog lists a class that is not a constant"
    e := e.appArg!
  return acc

/-- The name of a class constant (its definition is `ClassDecl.mk "name" …`). -/
private def classConstName (c : Name) : CoreM String := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "jimple_program: {c} is not a class"
  match d.value.getAppArgs[0]? with
  | some (Lean.Expr.lit (Lean.Literal.strVal s)) => return s
  | _ => throwError "jimple_program: {c} is not a class declaration"

/-- `jimple_program A B C as Foo`: `Foo.prog`, the program made of the classes imported as
    `A`, `B`, `C` (each by its own `jimple_import`, typically one class per module), with its
    index precomputed. Proofs about one class then only depend on that class's module. -/
syntax (name := jimpleProgram) "jimple_program " ident+ " as " ident : command

@[command_elab jimpleProgram]
def elabJimpleProgram : CommandElab := fun stx => do
  let `(jimple_program $parts:ident* as $ns:ident) := stx | throwUnsupportedSyntax
  let mut consts : Array Name := #[]
  for p in parts do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (p.getId.str "prog")) <|> pure (p.getId.str "prog")
    consts := consts ++ (← liftCoreM <| progClassConsts n.getPrefix)
  let names ← liftCoreM <| consts.mapM classConstName
  let base := (← getCurrNamespace) ++ ns.getId
  let classes := listExpr (mkConst ``Jimple.ClassDecl) (consts.toList.map (mkConst ·))
  let byName : Std.HashMap String Name := (names.zip consts).foldl (fun m (s, c) => m.insert s c) {}
  let tree := ClassTree.ofList (names.toList.map fun s => ({ name := s } : ClassDecl))
  let rec treeExpr : ClassTree → Lean.Expr
    | .leaf => mkConst ``Jimple.ClassTree.leaf
    | .node l h ds r => mkAppN (mkConst ``Jimple.ClassTree.node)
        #[treeExpr l, mkNatLit h,
          listExpr (mkConst ``Jimple.ClassDecl) (ds.map fun d => mkConst (byName.getD d.name .anonymous)),
          treeExpr r]
  liftCoreM <| addDef (base.str "prog") (mkConst ``Jimple.Program)
    (mkApp2 (mkConst ``Jimple.Program.mk) classes (treeExpr tree)) consts.size

end Jimple.Import
