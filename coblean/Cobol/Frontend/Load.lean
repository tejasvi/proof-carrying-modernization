/-
# Loading extractor output

* JSON (de)serialization of the surface IR (`deriving FromJson, ToJson`: an inductive value
  is `{"ctor": {...fields...}}`, a structure is an object; optional fields may be omitted).
* `cobol_program P from "file.json"` elaborates at compile time: reads the surface IR,
  resolves it (`Cobol.Resolve.program`) and defines `P : Cobol.Program` as a literal term,
  so proofs about `P` unfold to concrete statements with concrete descriptors.
* `Cobol.loadProgram path : IO Program` does the same at run time (for `cobolrun`).
-/
import Lean
import Cobol.Frontend.Resolve
import Cobol.Logic.Ground
import Cobol.Sem.Exec

namespace Cobol
open Lean

instance : FromJson UInt8 := ⟨fun j => do pure (UInt8.ofNat (← j.getNat?))⟩
instance : ToJson UInt8 := ⟨fun b => toJson b.toNat⟩

deriving instance FromJson, ToJson for Charset, ZonedSign, Trunc, Config, Usage, ESym,
  Figurative, Pic, Value, CondVal
deriving instance FromJson, ToJson for Item
deriving instance FromJson, ToJson for Surface.Sub, Surface.Ref, Surface.Lit, Surface.Operand
deriving instance FromJson, ToJson for Surface.Expr
deriving instance FromJson, ToJson for Surface.Cond
deriving instance FromJson, ToJson for Surface.Receiver, Surface.Loop
deriving instance FromJson, ToJson for Surface.InspPhrase
deriving instance FromJson, ToJson for Surface.UnstrDelim, Surface.UnstrInto
deriving instance FromJson, ToJson for Surface.SearchKey
deriving instance FromJson, ToJson for Surface.StrGroup
deriving instance FromJson, ToJson for Surface.Stmt
deriving instance FromJson, ToJson for Surface.FileDecl
deriving instance FromJson, ToJson for Surface.Paragraph, Surface.Dialect, Surface.UseDecl
deriving instance FromJson, ToJson for Surface.AlphaPhrase
deriving instance FromJson, ToJson for Surface.OdoDecl
deriving instance FromJson, ToJson for Surface.Program

deriving instance ToExpr for RoundingMode
deriving instance ToExpr for Charset
deriving instance ToExpr for ZonedSign
deriving instance ToExpr for Trunc
deriving instance ToExpr for Config
deriving instance ToExpr for Usage
deriving instance ToExpr for NumFmt
deriving instance ToExpr for ESym
deriving instance ToExpr for FieldKind
deriving instance ToExpr for FieldDesc
deriving instance ToExpr for SubExpr
deriving instance ToExpr for Subscript
deriving instance ToExpr for RefMod
deriving instance ToExpr for DataRef
deriving instance ToExpr for Figurative
deriving instance ToExpr for AlnumFn
deriving instance ToExpr for Operand
deriving instance ToExpr for DateFn
deriving instance ToExpr for Expr
deriving instance ToExpr for CmpOp
deriving instance ToExpr for ExitPt
deriving instance ToExpr for ClassTest
deriving instance ToExpr for Cond
deriving instance ToExpr for Receiver
deriving instance ToExpr for ArithOp
deriving instance ToExpr for StopKind
deriving instance ToExpr for OpenMode
deriving instance ToExpr for CloseOpt
deriving instance ToExpr for FileOrg
deriving instance ToExpr for AccessMode
deriving instance ToExpr for KeyDecl
deriving instance ToExpr for FileDecl
deriving instance ToExpr for InspKind
deriving instance ToExpr for InspPhrase
deriving instance ToExpr for UnstrInto
deriving instance ToExpr for Stmt
deriving instance ToExpr for Paragraph
deriving instance ToExpr for UseProc
deriving instance ToExpr for Program

/-- Surface program of a JSON document (`files` and `use` may be omitted). -/
def surfaceOfJson (j : Json) : Except String Surface.Program :=
  let j := match j.getObjVal? "files" with
    | .ok _ => j
    | .error _ => j.setObjVal! "files" (Json.arr #[])
  let j := match j.getObjVal? "use" with
    | .ok _ => j
    | .error _ => j.setObjVal! "use" (Json.arr #[])
  fromJson? (α := Surface.Program) j

/-- Parse and resolve a surface-IR JSON document. -/
def programOfJson (j : Json) : Except String Program := do
  Resolve.program (← surfaceOfJson j)

/-- Lean identifier for a COBOL data name (`ACCT-BALANCE` ↦ `ACCT_BALANCE`). -/
def dataIdent (n : String) : Name := Name.mkSimple (n.map fun c => if c == '-' then '_' else c)

/-- Read, parse and resolve a surface-IR JSON file. -/
def loadProgram (path : System.FilePath) : IO Program := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  IO.ofExcept (programOfJson j)

open Elab Meta in
/-- One constant per statement, `P.sN : Stmt := ⟨literal⟩`, whose statement lists are lists of
statement constants (so no term ever contains a large literal program fragment).  Returns the
constant and records `(name, literal)` for the execution equations added once `P` exists. -/
partial def stmtConst (P : Name) (ctr : IO.Ref Nat) (acc : IO.Ref (Array (Name × Lean.Expr)))
    (s : Stmt) : TermElabM Lean.Expr := do
  let list (ss : List Stmt) : TermElabM Lean.Expr := do
    mkListLit (mkConst ``Stmt) (← ss.mapM (stmtConst P ctr acc))
  let lit ← match s with
    | .arith op rcv trap on non =>
      pure (mkAppN (mkConst ``Stmt.arith) #[toExpr op, toExpr rcv, toExpr trap, ← list on, ← list non])
    | .divRem a b q r trap on non =>
      pure (mkAppN (mkConst ``Stmt.divRem)
        #[toExpr a, toExpr b, toExpr q, toExpr r, toExpr trap, ← list on, ← list non])
    | .ite c t e => pure (mkApp3 (mkConst ``Stmt.ite) (toExpr c) (← list t) (← list e))
    | .performVarying id ta init c step first exit =>
      pure (mkAppN (mkConst ``Stmt.performVarying)
        #[toExpr id, toExpr ta, ← list init, toExpr c, ← list step, toExpr first, toExpr exit])
    | .block body => pure (mkApp (mkConst ``Stmt.block) (← list body))
    | .inlineTimes n body => pure (mkApp2 (mkConst ``Stmt.inlineTimes) (toExpr n) (← list body))
    | .inlineUntil ta c body =>
      pure (mkApp3 (mkConst ``Stmt.inlineUntil) (toExpr ta) (toExpr c) (← list body))
    | .inlineVarying ta init c step body =>
      pure (mkAppN (mkConst ``Stmt.inlineVarying)
        #[toExpr ta, ← list init, toExpr c, ← list step, ← list body])
    | .read file r into atEnd notAtEnd =>
      pure (mkAppN (mkConst ``Stmt.read)
        #[toExpr file, toExpr r, toExpr into, ← list atEnd, ← list notAtEnd])
    | .fread file key into trap exc noExc =>
      pure (mkAppN (mkConst ``Stmt.fread)
        #[toExpr file, toExpr key, toExpr into, toExpr trap, ← list exc, ← list noExc])
    | .fwrite file r trap exc noExc =>
      pure (mkAppN (mkConst ``Stmt.fwrite) #[toExpr file, toExpr r, toExpr trap, ← list exc, ← list noExc])
    | .frewrite file r trap exc noExc =>
      pure (mkAppN (mkConst ``Stmt.frewrite) #[toExpr file, toExpr r, toExpr trap, ← list exc, ← list noExc])
    | .fdelete file trap exc noExc =>
      pure (mkAppN (mkConst ``Stmt.fdelete) #[toExpr file, toExpr trap, ← list exc, ← list noExc])
    | s => pure (toExpr s)
  let k ← ctr.modifyGet fun k => (k, k + 1)
  let n := P ++ Name.mkSimple s!"s{k}"
  addAndCompile <| .defnDecl {
    name := n, levelParams := [], type := mkConst ``Stmt, value := lit, hints := .regular 0,
    safety := .safe }
  acc.modify (·.push (n, lit))
  pure (mkConst n)

open Elab Meta in
/-- `execStmt Q env rec fuel P.sN st = execStmt Q env rec fuel ⟨literal⟩ st` (for every program
`Q`, so that summaries stated for an abstract program use it) in `cobol_eval`: a statement
constant is unfolded only when the statement is executed. -/
def addStmtEqn (ext : SimpExtension) (n : Name) (lit : Lean.Expr) : TermElabM Unit := do
  let resT ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``State) (mkConst ``Sem.Res))
  withLocalDeclD `Q (mkConst ``Program) fun Q =>
  withLocalDeclD `env (mkConst ``Env) fun env =>
  withLocalDeclD `rec resT fun rc =>
  withLocalDeclD `fuel (mkConst ``Nat) fun fuel =>
  withLocalDeclD `st (mkConst ``State) fun st => do
    let lhs := mkAppN (mkConst ``Sem.execStmt) #[Q, env, rc, fuel, mkConst n, st]
    let rhs := mkAppN (mkConst ``Sem.execStmt) #[Q, env, rc, fuel, lit, st]
    let ty ← mkForallFVars #[Q, env, rc, fuel, st] (← mkEq lhs rhs)
    let pf ← mkLambdaFVars #[Q, env, rc, fuel, st] (← mkEqRefl lhs)
    addDecl <| .thmDecl { name := n ++ `exec, levelParams := [], type := ty, value := pf }
    addSimpTheorem ext (n ++ `exec) (post := true) (inv := false) .global (prio := eval_prio default)

open Elab Meta in
/-- `execSentences Q env rec fuel P.parak.body st = execSentences Q env rec fuel ⟨body⟩ st` in
`cobol_eval`, for every program `Q`. -/
def addBodyEqn (ext : SimpExtension) (pn : Name) (body : Lean.Expr) : TermElabM Unit := do
  let resT ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``State) (mkConst ``Sem.Res))
  let bodyC ← mkAppM ``Paragraph.body #[mkConst pn]
  withLocalDeclD `Q (mkConst ``Program) fun Q =>
  withLocalDeclD `env (mkConst ``Env) fun env =>
  withLocalDeclD `rec resT fun rc =>
  withLocalDeclD `fuel (mkConst ``Nat) fun fuel =>
  withLocalDeclD `st (mkConst ``State) fun st => do
    let lhs := mkAppN (mkConst ``Sem.execSentences) #[Q, env, rc, fuel, bodyC, st]
    let rhs := mkAppN (mkConst ``Sem.execSentences) #[Q, env, rc, fuel, body, st]
    let ty ← mkForallFVars #[Q, env, rc, fuel, st] (← mkEq lhs rhs)
    let pf ← mkLambdaFVars #[Q, env, rc, fuel, st] (← mkEqRefl lhs)
    addDecl <| .thmDecl { name := pn ++ `exec, levelParams := [], type := ty, value := pf }
    addSimpTheorem ext (pn ++ `exec) (post := true) (inv := false) .global (prio := eval_prio default)

open Elab Command Meta in
/-- `cobol_program P from "path.json"`: define `P : Cobol.Program` from extractor output
(path relative to the current file).

Besides `P`, it defines one constant per paragraph, named after it (`P.«1000-READ»`; unnamed
or duplicate names: `P.para3`), and one per statement (`P.«1000-READ».s0`, …, see
`stmtConst`), and registers `cobol_eval` equations for the
projections of `P` (`P.paras[k]? = some P.parak`, `P.parak.body = …`, `P.cfg = …`, …) and for
executing each statement constant.  Symbolic execution then never unfolds `P` itself, and a
statement's text appears only while it executes: the statements still to run stay constants,
so the proof terms do not grow with the program text.

For statements about storage it also defines, per uniquely named data item, a reducible
`P.NAME : FieldDesc` (offset, length, kind; the first occurrence for an item under `OCCURS`)
and, for numeric items, `P.NAME.fmt : NumFmt`: `decodeNum {} P.ACCT_BALANCE.fmt
(m.field P.ACCT_BALANCE) = some bal`. -/
elab "cobol_program " id:ident " from " path:str : command => do
  let fileName ← getFileName
  let dir := (System.FilePath.mk fileName).parent.getD "."
  let p := dir / path.getString
  let txt ← IO.FS.readFile p
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "JSON parse error in {p}: {e}"
  let prog ← match programOfJson j with
    | .ok prog => pure prog
    | .error e => throwError "cannot resolve {p}: {e}"
  let sp ← match surfaceOfJson j with
    | .ok sp => pure sp
    | .error e => throwError "{p}: {e}"
  let L := layout sp.config sp.data
  let declName := (← getCurrNamespace) ++ id.getId
  liftTermElabM do
    let some ext ← getSimpExtension? `cobol_eval | throwError "cobol_eval simp set missing"
    let addDef (n : Name) (ty v : Lean.Expr) : TermElabM Unit := do
      addAndCompile <| .defnDecl {
        name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }
      enableRealizationsForConst n
    let addEqn (n : Name) (lhs rhs : Lean.Expr) : TermElabM Unit := do
      let ty ← mkEq lhs rhs
      let pf ← mkEqRefl lhs
      addDecl <| .thmDecl { name := n, levelParams := [], type := ty, value := pf }
      addSimpTheorem ext n (post := true) (inv := false) .global (prio := eval_prio default)
    -- statements and paragraphs as separate constants
    let acc ← IO.mkRef #[]
    -- paragraphs are named after their COBOL names (`P.«1000-READ»`), statements after their
    -- paragraph (`P.«1000-READ».s0`, …): a statement about one paragraph keeps its meaning when
    -- other paragraphs are added or edited
    let paraNames := (List.range prog.paras.size).map (fun k =>
      let n := prog.paras[k]!.name
      declName ++ Name.mkSimple (if n.isEmpty || prog.paras.toList.countP (·.name == n) > 1
        then s!"para{k}" else n))
    let mut bodies : Array Lean.Expr := #[]
    for (k, pn) in (List.range prog.paras.size).zip paraNames do
      let ctr ← IO.mkRef 0
      let para := prog.paras[k]!
      let sentences ← para.body.mapM (fun ss => do
        mkListLit (mkConst ``Stmt) (← ss.mapM (stmtConst pn ctr acc)))
      let body ← mkListLit (mkApp (mkConst ``List [Level.zero]) (mkConst ``Stmt)) sentences
      bodies := bodies.push body
      addDef pn (mkConst ``Paragraph) (mkApp2 (mkConst ``Paragraph.mk) (toExpr para.name) body)
    let parasE ← mkArrayLit (mkConst ``Paragraph) (paraNames.map mkConst)
    let value := mkAppN (mkConst ``Program.mk) #[toExpr prog.name, toExpr prog.cfg, parasE,
      toExpr prog.secEnd, toExpr prog.memSize, toExpr prog.inits, toExpr prog.isMain,
      toExpr prog.files, toExpr prog.useProcs]
    addDef declName (mkConst ``Program) value
    let P := mkConst declName
    -- projection equations
    let natT := mkConst ``Nat
    for (k, pn) in (List.range prog.paras.size).zip paraNames do
      let lhs ← mkAppM ``GetElem?.getElem? #[← mkAppM ``Program.paras #[P], mkNatLit k]
      addEqn (declName ++ Name.mkSimple s!"paras_{k}") lhs (← mkAppM ``Option.some #[mkConst pn])
      -- `body_eq` is not a `cobol_eval` lemma: a paragraph body is unfolded only when it runs
      -- (`addBodyEqn`), so that a summary stated for `P.parak.body` applies at a call site
      let bodyTy ← mkEq (← mkAppM ``Paragraph.body #[mkConst pn]) bodies[k]!
      addDecl <| .thmDecl { name := pn ++ `body_eq, levelParams := [], type := bodyTy,
                            value := ← mkEqRefl (← mkAppM ``Paragraph.body #[mkConst pn]) }
      addBodyEqn ext pn bodies[k]!
    let lhsOut ← mkAppM ``GetElem?.getElem? #[← mkAppM ``Program.paras #[P], mkNatLit prog.paras.size]
    addEqn (declName ++ `paras_end) lhsOut (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Paragraph))
    addEqn (declName ++ `cfg_eq) (← mkAppM ``Program.cfg #[P]) (toExpr prog.cfg)
    addEqn (declName ++ `secEnd_eq) (← mkAppM ``Program.secEnd #[P]) (toExpr prog.secEnd)
    addEqn (declName ++ `memSize_eq) (← mkAppM ``Program.memSize #[P]) (toExpr prog.memSize)
    addEqn (declName ++ `inits_eq) (← mkAppM ``Program.inits #[P]) (toExpr prog.inits)
    addEqn (declName ++ `isMain_eq) (← mkAppM ``Program.isMain #[P]) (toExpr prog.isMain)
    addEqn (declName ++ `files_eq) (← mkAppM ``Program.files #[P]) (toExpr prog.files)
    addEqn (declName ++ `useProcs_eq) (← mkAppM ``Program.useProcs #[P]) (toExpr prog.useProcs)
    for (n, lit) in ← acc.get do
      addStmtEqn ext n lit
    let _ := natT
    -- field descriptors
    let names := L.items.map (·.name)
    for pl in L.items do
      if pl.name == "FILLER" || pl.name == "" || names.count pl.name != 1 then continue
      let fn := declName ++ dataIdent pl.name
      if (← getEnv).contains fn then continue
      addDef fn (mkConst ``FieldDesc) (toExpr pl.desc)
      setReducibleAttribute fn
      if let .num f := pl.desc.kind then
        addDef (fn ++ `fmt) (mkConst ``NumFmt) (toExpr f)
        setReducibleAttribute (fn ++ `fmt)
  logInfo m!"{declName}: {prog.paras.size} paragraphs, {prog.memSize} bytes of storage"

end Cobol
