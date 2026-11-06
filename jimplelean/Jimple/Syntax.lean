/-
  Jimple/Syntax.lean

  Abstract syntax of Soot's Jimple intermediate representation.

  Jimple is a typed, stackless, 3-address code: every operand of an expression is an
  *immediate* (a local variable or a constant), every statement does at most one
  memory access or call, and exception handling is a per-method table of typed traps.
  The grammar followed here is Soot's own `jimple.scc` (soot-oss/soot, develop branch).

  The 15 statement forms (`Stmt`) are exactly Soot's:
    NopStmt, BreakpointStmt, IdentityStmt, AssignStmt, EnterMonitorStmt, ExitMonitorStmt,
    GotoStmt, IfStmt, InvokeStmt, TableSwitchStmt, LookupSwitchStmt, RetStmt,
    ReturnStmt, ReturnVoidStmt, ThrowStmt.

  Conventions of this formalization:
  * branch targets are statement indices (labels are resolved by the importer);
  * locals are numbered (`LocalIdx`); a `Body` keeps their source names and declared types;
  * class, field and method references keep their full Jimple signatures, so class
    hierarchies, interfaces and overriding are resolved by the semantics, not erased.
-/
namespace Jimple

abbrev ClassName := String
/-- Statement index inside a method body (labels are resolved to indices). -/
abbrev Label := Nat
/-- Index of a local variable inside a method body. -/
abbrev LocalIdx := Nat

inductive PrimType where
  | boolean | byte | char | short | int | long | float | double
  deriving DecidableEq, Repr, Inhabited, Hashable

inductive JType where
  | prim (p : PrimType)
  /-- class or interface type -/
  | cls (name : ClassName)
  | array (elem : JType)
  /-- Jimple's `null_type` -/
  | null
  /-- Jimple's `unknown` (untyped local) -/
  | unknown
  | void
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace JType
abbrev int : JType := .prim .int
abbrev long : JType := .prim .long
abbrev boolean : JType := .prim .boolean
abbrev float : JType := .prim .float
abbrev double : JType := .prim .double
abbrev object : JType := .cls "java.lang.Object"
abbrev string : JType := .cls "java.lang.String"

/-- Reference types: classes, interfaces, arrays and the null type. -/
def isRef : JType → Bool
  | .cls _ | .array _ | .null => true
  | _ => false
end JType

/-- A method reference as written in Jimple: `<cls: ret name(params)>`. -/
structure MethodSig where
  cls : ClassName
  ret : JType
  name : String
  params : List JType
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The part of a method signature used for overriding and dispatch
    (JVM: name + descriptor). -/
structure SubSig where
  name : String
  params : List JType
  ret : JType
  deriving DecidableEq, Repr, Inhabited, Hashable

def MethodSig.sub (m : MethodSig) : SubSig := ⟨m.name, m.params, m.ret⟩

/-- A field reference as written in Jimple: `<cls: ty name>`. -/
structure FieldSig where
  cls : ClassName
  ty : JType
  name : String
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Literal constants. Booleans are JVM ints (`true` = 1, `false` = 0); `char`, `byte`
    and `short` constants are ints as well. Floating-point constants are stored as their
    IEEE-754 bit patterns. -/
inductive Const where
  | int (v : Int)
  | long (v : Int)
  | float (bits : BitVec 32)
  | double (bits : BitVec 64)
  /-- string literal (well-formed Unicode; evaluated to UTF-16 code units) -/
  | str (s : String)
  /-- string literal given as raw UTF-16 code units (for lone surrogates) -/
  | strUnits (u : List Nat)
  | null
  /-- class constant, e.g. `class "Ljava/lang/String;"` -/
  | clazz (desc : String)
  /-- method handle constant (kept opaque) -/
  | methodHandle (desc : String)
  deriving DecidableEq, Repr, Inhabited

/-- Immediates: the only operands allowed in Jimple expressions. -/
inductive Imm where
  | loc (x : LocalIdx)
  | const (c : Const)
  deriving DecidableEq, Repr, Inhabited

/-- Right-hand sides of identity statements: `@this`, `@parameterN`, `@caughtexception`. -/
inductive IdRef where
  | this (t : JType)
  | param (i : Nat) (t : JType)
  | caught
  deriving DecidableEq, Repr, Inhabited

/-- Memory references (the only places where Jimple touches the heap). -/
inductive Ref where
  | instField (base : LocalIdx) (f : FieldSig)
  | staticField (f : FieldSig)
  | arrayElem (base : LocalIdx) (idx : Imm)
  deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | rem
  | and | or | xor | shl | shr | ushr
  | cmp | cmpl | cmpg
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

inductive UnOp where
  | neg | lengthof
  deriving DecidableEq, Repr, Inhabited

inductive InvKind where
  | virtual | special | interface
  deriving DecidableEq, Repr, Inhabited

inductive Invoke where
  /-- `virtualinvoke` / `specialinvoke` / `interfaceinvoke base.<sig>(args)` -/
  | inst (k : InvKind) (base : LocalIdx) (m : MethodSig) (args : List Imm)
  /-- `staticinvoke <sig>(args)` -/
  | static (m : MethodSig) (args : List Imm)
  /-- `dynamicinvoke "name" <ret (params)>(args) <bsm>(bsmArgs)` -/
  | dynamic (name : String) (ret : JType) (params : List JType) (args : List Imm)
      (bsm : MethodSig) (bsmArgs : List Imm)
  deriving DecidableEq, Repr, Inhabited

def Invoke.sig? : Invoke → Option MethodSig
  | .inst _ _ m _ => some m
  | .static m _ => some m
  | .dynamic .. => none

inductive Expr where
  | imm (a : Imm)
  | binop (op : BinOp) (a b : Imm)
  | unop (op : UnOp) (a : Imm)
  | cast (t : JType) (a : Imm)
  | instOf (a : Imm) (t : JType)
  | new (c : ClassName)
  /-- `newarray (elem)[size]` -/
  | newArray (elem : JType) (size : Imm)
  /-- `newmultiarray (base)[d1]...[dk][]...[]`: `sizes` are the given dimensions,
      `dims` the total number of dimensions -/
  | newMultiArray (base : JType) (sizes : List Imm) (dims : Nat)
  | invoke (i : Invoke)
  | ref (r : Ref)
  deriving DecidableEq, Repr, Inhabited

inductive LValue where
  | loc (x : LocalIdx)
  | ref (r : Ref)
  deriving DecidableEq, Repr, Inhabited

/-- The 15 Jimple statements. -/
inductive Stmt where
  | nop
  | breakpoint
  | identity (x : LocalIdx) (r : IdRef)
  | assign (lhs : LValue) (rhs : Expr)
  | enterMonitor (a : Imm)
  | exitMonitor (a : Imm)
  | goto (target : Label)
  /-- `if a op b goto target` -/
  | ifGoto (op : BinOp) (a b : Imm) (target : Label)
  | invoke (i : Invoke)
  /-- `tableswitch(key)`: cases `low, low+1, ...` jump to `targets` in order -/
  | tableSwitch (key : Imm) (low : Int) (targets : List Label) (dflt : Label)
  | lookupSwitch (key : Imm) (cases : List (Int × Label)) (dflt : Label)
  | ret (x : LocalIdx)
  | returnVal (a : Imm)
  | returnVoid
  | throw (a : Imm)
  deriving DecidableEq, Repr, Inhabited

/-- `catch exc from first to last with handler` (`first` inclusive, `last` exclusive). -/
structure Trap where
  exc : ClassName
  first : Label
  last : Label
  handler : Label
  deriving DecidableEq, Repr, Inhabited

structure Body where
  /-- source names and declared Jimple types of the locals, indexed by `LocalIdx` -/
  locals : List (String × JType)
  stmts : Array Stmt
  traps : List Trap
  /-- Java source line of each statement (statement index ↦ line, `0` = unknown), from the
      line number tags of Soot's `-keep-line-number -print-tags` output; empty without tags -/
  lines : Array Nat := #[]
  deriving Repr, Inhabited

def Body.stmtAt (b : Body) (pc : Nat) : Option Stmt := b.stmts[pc]?

structure MethodMods where
  isPublic : Bool := false
  isPrivate : Bool := false
  isProtected : Bool := false
  isStatic : Bool := false
  isFinal : Bool := false
  isAbstract : Bool := false
  isNative : Bool := false
  isSynchronized : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure MethodDecl where
  name : String
  params : List JType
  ret : JType
  mods : MethodMods := {}
  throws : List ClassName := []
  /-- `none` for abstract and native methods -/
  body : Option Body := none
  deriving Repr, Inhabited

def MethodDecl.sub (m : MethodDecl) : SubSig := ⟨m.name, m.params, m.ret⟩

structure FieldDecl where
  name : String
  ty : JType
  isStatic : Bool := false
  isFinal : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure ClassDecl where
  name : ClassName
  isInterface : Bool := false
  isAbstract : Bool := false
  isEnum : Bool := false
  super : Option ClassName := none
  interfaces : List ClassName := []
  fields : List FieldDecl := []
  methods : List MethodDecl := []
  deriving Repr, Inhabited

/-- A resolved method: declaring class plus declaration. -/
structure MethodRef where
  cls : ClassName
  decl : MethodDecl
  deriving Repr, Inhabited

def MethodRef.sig (m : MethodRef) : MethodSig := ⟨m.cls, m.decl.ret, m.decl.name, m.decl.params⟩

/-- Hash of a class name, evaluated by the kernel as a fold over the characters. -/
def nameHash (s : String) : Nat := s.toList.foldl (fun h c => (h * 31 + c.toNat) % 4294967291) 7

/-- Application classes indexed by name: a binary search tree on `nameHash` whose nodes hold
    the classes with that hash. A lookup takes a logarithmic number of `Nat` comparisons and
    one string comparison, also when the kernel evaluates it. -/
inductive ClassTree where
  | leaf
  | node (l : ClassTree) (h : Nat) (ds : List ClassDecl) (r : ClassTree)
  deriving Repr, Inhabited

namespace ClassTree

def find : ClassTree → Nat → String → Option ClassDecl
  | .leaf, _, _ => none
  | .node l h ds r, k, c =>
    if k < h then l.find k c else if h < k then r.find k c else ds.find? (·.name == c)

def toList : ClassTree → List ClassDecl
  | .leaf => []
  | .node l _ ds r => l.toList ++ ds ++ r.toList

def insert (d : ClassDecl) (k : Nat) : ClassTree → ClassTree
  | .leaf => .node .leaf k [d] .leaf
  | .node l h ds r =>
    if k < h then .node (l.insert d k) h ds r
    else if h < k then .node l h ds (r.insert d k)
    else .node l h (ds ++ [d]) r

/-- The index of a class list (hashes spread the classes, so the tree stays shallow). -/
def ofList (l : List ClassDecl) : ClassTree := l.foldl (fun t d => t.insert d (nameHash d.name)) .leaf

theorem mem_toList_of_find : ∀ {t : ClassTree} {k : Nat} {c : String} {d : ClassDecl},
    t.find k c = some d → d ∈ t.toList ∧ d.name = c
  | .leaf, _, _, _, h => by simp [find] at h
  | .node l h ds r, k, c, d, hf => by
    simp only [find] at hf
    split at hf
    · have := mem_toList_of_find hf
      exact ⟨by simp [toList, this.1], this.2⟩
    · split at hf
      · have := mem_toList_of_find hf
        exact ⟨by simp [toList, this.1], this.2⟩
      · have hm := List.mem_of_find?_eq_some hf
        have hn := List.find?_some hf
        exact ⟨by simp [toList, hm], by simpa using hn⟩

end ClassTree

/-- A Jimple program: the application classes (with bodies), and their index (used by every
    lookup of the semantics; `jimple_import` stores it precomputed). Library classes come from
    the built-in prelude (`Jimple/Prelude.lean`) and are modelled natively. -/
structure Program where
  classes : List ClassDecl
  index : ClassTree := ClassTree.ofList classes
  deriving Repr, Inhabited

/-- The application class named `c`. -/
def Program.findClass (P : Program) (c : ClassName) : Option ClassDecl :=
  P.index.find (nameHash c) c

end Jimple
