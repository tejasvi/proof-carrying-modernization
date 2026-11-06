import CIR.Model

/-! Functions, globals and modules. -/

namespace CIR

/-- `cir.func`. Parameters are the arguments of the entry block of `body`. -/
structure FuncDecl where
  /-- Mangled symbol, e.g. `_Z6sum_toi`. -/
  sym       : String
  /-- Demangled name for display, e.g. `sum_to(int)` (may be empty). -/
  demangled : String := ""
  params    : List Ty := []
  /-- `void` when the function returns nothing. -/
  ret       : Ty := .void
  /-- `none` for a declaration without body. -/
  body      : Option Region := none
  nothrow   : Bool := false
  noreturn  : Bool := false
  special   : SpecialMember := .none
  /-- A native library model replacing the body (see `CIR.Model`). -/
  model     : Option Model := none
  /-- Original SSA names, for diagnostics: `(vid, "%3")`. -/
  ssaNames  : List (VId × String) := []
  /-- Internal linkage (`static`): local to its translation unit. -/
  internal  : Bool := false
  /-- Source position (line, column) of the operation defining each SSA value
  (diagnostics: `cir2lean` writes it to the manifest, not to the Lean module). -/
  ssaLocs   : List (VId × Nat × Nat) := []
  /-- The source file of the function's definition, from its location (`""` when unknown;
  `Frontend.isStdLibFunc`; `cir2lean` does not write it). -/
  srcFile   : String := ""
  /-- The pointers of the function's `volatile` loads and stores (`Frontend.sjNotes`; `cir2lean`
  does not write it). -/
  volPtrs   : List VId := []
  /-- The last parameter is the caller's object that the function's result (of a class
  non-trivial for calls) is built in, the function returns nothing (`Frontend.retObjects`;
  `cir2lean` does not write it). -/
  retObj    : Bool := false
  /-- `cir.func @f(…) alias(@g)`: `f` is another name of the function `g` (Clang's complete-object
  constructor or destructor for the base-object one, `__attribute__((alias("g")))`). The frontend
  gives `f` the body and the model of the function its aliases end at (`Frontend.resolveAliases`). -/
  alias     : Option String := none
  deriving Inhabited

/-- `cir.global`. -/
structure GlobalDecl where
  sym      : String
  ty       : Ty
  init     : Option Const := none
  constant : Bool := false
  /-- Internal linkage (`static`, string literals): local to its translation unit. -/
  internal : Bool := false
  /-- `cir.global @a alias(@g)` (`extern int a __attribute__((alias("g")))`): `a` names the object
  `g`; the frontend makes the module's references to `a` references to `g`
  (`Frontend.resolveAliases`). -/
  alias    : Option String := none
  deriving Inhabited

structure Module where
  name    : String := ""
  records : List RecordDecl := []
  globals : List GlobalDecl := []
  funcs   : List FuncDecl := []
  /-- Size and alignment of a pointer in bytes, from the module's data layout (`!llvm.ptr` in
  `dlti.dl_spec`): 8 (LP64, the default) or 4 (ILP32, e.g. i686). -/
  ptrBytes : Nat := 8
  /-- `cir.lang = #cir.lang<cxx>`: a C++ translation unit (every unit, for a linked module), where
  null pointers take part in pointer arithmetic: `p + 0` and `p - 0` are null for a null `p`, and
  the difference of two null pointers is 0 (C++ [expr.add]p4.1, p5.1); both are undefined in C. -/
  cxx : Bool := false
  /-- `cir.global_ctors`: the functions that run before `main`, with their priorities
  (`__attribute__((constructor(p)))`; C++ dynamic initialization through `_GLOBAL__sub_I_*`, and
  `_GLOBAL__I_00p` for `init_priority(p)`; 65535 when no priority is given). -/
  ctors : List (String × Nat) := []
  /-- `cir.global_dtors`: the functions that run after `main` returns
  (`__attribute__((destructor(p)))`), with their priorities. -/
  dtors : List (String × Nat) := []
  deriving Inhabited

namespace Module

def findFunc? (M : Module) (sym : String) : Option FuncDecl :=
  M.funcs.find? (·.sym == sym)

def findRecord? (M : Module) (name : String) : Option RecordDecl :=
  M.records.find? (·.name == name)

def findGlobal? (M : Module) (sym : String) : Option GlobalDecl :=
  M.globals.find? (·.sym == sym)

end Module

end CIR
