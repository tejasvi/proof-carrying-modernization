import CIR.Frontend.Parser
import CIR.Frontend.Recognize
import CIR.Frontend.Varargs
import CIR.Frontend.Retval
import CIR.Frontend.ByValue
import CIR.Frontend.RetSlot

/-! Loading a `.cir` file: parse, demangle (`c++filt`), attach library models. -/

namespace CIR.Frontend

/-- Demangle `_Z` symbols with `c++filt` (in chunks, symbols as arguments).
Returns `""` for symbols that could not be demangled or when `c++filt` is not
available. -/
def demangleAll (syms : Array String) : IO (Std.HashMap String String) := do
  let mangled := syms.filter (·.startsWith "_Z")
  let mut out : Std.HashMap String String := {}
  let chunk := 200
  let mut i := 0
  while i < mangled.size do
    let part := mangled.extract i (i + chunk)
    i := i + chunk
    let res ← try
        some <$> IO.Process.output { cmd := "c++filt", args := part }
      catch _ => pure none
    match res with
    | some r =>
      if r.exitCode == 0 then
        let lines := (r.stdout.splitOn "\n").toArray
        for h : k in [0:part.size] do
          let d := lines[k]?.getD ""
          -- c++filt echoes symbols it cannot demangle
          if d != part[k] then out := out.insert part[k] d
    | none => pure ()
  return out

/-- glibc's `stdin`, `stdout` and `stderr` are external `FILE *` globals, which a
program reads and passes to the stream functions. Without a definition they
would have no value (`Module.initMem`); they get distinct non-null handles instead,
the integer addresses 1, 2 and 3 (any access through them is undefined), so
that a stream argument can be checked (`fprintf` with a null stream is
undefined, C11 7.1.4p1). -/
def stdStreams (gs : List GlobalDecl) : List GlobalDecl :=
  gs.map fun g =>
    match g.init, g.ty, g.sym with
    | none, .ptr _, "stdin" => { g with init := some (.ptrInt 1) }
    | none, .ptr _, "stdout" => { g with init := some (.ptrInt 2) }
    | none, .ptr _, "stderr" => { g with init := some (.ptrInt 3) }
    | _, _, _ => g

/-- glibc's `__libc_single_threaded` (`<sys/single_threaded.h>`), which a module only declares:
1, its value in a single-threaded process (cirlean runs no threads), read-only (a program only
reads it; libstdc++ does, to skip atomic reference counting). -/
def libcSingleThreaded (gs : List GlobalDecl) : List GlobalDecl :=
  gs.map fun g =>
    match g.init, g.ty, g.sym with
    | none, .int _ 8, "__libc_single_threaded" => { g with init := some (.int 1), constant := true }
    | _, _, _ => g

/-- glibc's `optind` and `opterr` (`<unistd.h>`, getopt) and `signgam` (`<math.h>`), which a module
only declares: their values when a program starts, 1, 1 and 0. getopt is not modelled; `lgamma`'s
model stores the sign of `Γ(x)` in `signgam`, as glibc does. -/
def libcGlobals (gs : List GlobalDecl) : List GlobalDecl :=
  gs.map fun g =>
    match g.init, g.ty, g.sym with
    | none, .int _ 32, "optind" => { g with init := some (.int 1) }
    | none, .int _ 32, "opterr" => { g with init := some (.int 1) }
    | none, .int _ 32, "signgam" => { g with init := some (.int 0) }
    | _, _, _ => g

/-- The C++ standard stream objects, libc++'s (`std::__1::`) and libstdc++'s: `cout`, `cerr`,
`clog`, `cin` and their wide versions. -/
def stdIostreamSyms : List String :=
  ["_ZNSt3__14coutE", "_ZNSt3__14cerrE", "_ZNSt3__14clogE", "_ZNSt3__13cinE",
   "_ZNSt3__15wcoutE", "_ZNSt3__15wcerrE", "_ZNSt3__15wclogE", "_ZNSt3__14wcinE",
   "_ZSt4cout", "_ZSt4cerr", "_ZSt4clog", "_ZSt3cin",
   "_ZSt5wcout", "_ZSt5wcerr", "_ZSt5wclog", "_ZSt4wcin"]

/-- A C++ standard stream object, which a module only declares (the library defines and
constructs it), is a live object of its declared type whose value the module does not know
(`#cir.undef`): the stream models (`operator<<`) take it as their stream, while a read of one of
its members, and a virtual call through its vptr, are undefined. -/
def stdIostreams (gs : List GlobalDecl) : List GlobalDecl :=
  gs.map fun g =>
    if g.init.isNone && stdIostreamSyms.contains g.sym then { g with init := some .undef } else g

/-- The type codes of the fundamental types in the Itanium C++ ABI (`v` void, `b` bool, `c` char,
`i` int, ..., `Dn` `std::nullptr_t`): their typeinfo objects, and those of the pointers to them and
to their const versions, are defined in the C++ runtime library (libc++abi, libsupc++). -/
def fundamentalTypeCodes : List String :=
  ["v", "w", "b", "c", "a", "h", "s", "t", "i", "j", "l", "m", "x", "y", "n", "o", "f", "d", "e", "g",
   "Ds", "Di", "Du", "Dn"]

/-- The mangled type of a fundamental type's typeinfo symbol: `_ZTIi` → `i`, `_ZTIPKc` → `PKc`. -/
def fundamentalTypeinfo? (sym : String) : Option String :=
  if sym.startsWith "_ZTI" then
    let code := (sym.drop 4).toString
    let base := if code.startsWith "PK" then (code.drop 2).toString
      else if code.startsWith "P" then (code.drop 1).toString else code
    if fundamentalTypeCodes.contains base then some code else none
  else none

/-- A module only declares the typeinfo objects of the fundamental types (`_ZTIi`, `_ZTIPi`,
`_ZTIPKi`, ...), which the C++ runtime library defines, so `typeid(int)` read an object without a
value. Each declared one gets its value, read-only, laid out as a class's typeinfo constant: an
indeterminate vptr (the runtime's vtables are not modelled: reading it is undefined) and its name,
a pointer to the first character of `_ZTS…`, the mangled type, which is added (or given its value)
when the module does not define it. -/
def stdTypeinfo (gs : List GlobalDecl) : List GlobalDecl :=
  let codes := gs.filterMap fun g => if g.init.isNone then fundamentalTypeinfo? g.sym else none
  let name (code : String) : GlobalDecl :=
    { sym := "_ZTS" ++ code, ty := .array (.int true 8) (code.length + 1),
      init := some (.str (code.toList.map fun c => (c.toNat : Int)) 1), constant := true }
  let gs := gs.map fun g =>
    match g.init, fundamentalTypeinfo? g.sym with
    | none, some code =>
      { g with ty := .array (.ptr (.int false 8)) 2, constant := true,
               init := some (.array [.undef, .globalAddr ("_ZTS" ++ code) [0]]) }
    | none, none =>
      match codes.find? (fun c => g.sym == "_ZTS" ++ c) with
      | some c => { g with ty := (name c).ty, init := (name c).init, constant := true }
      | none => g
    | some _, _ => g
  gs ++ (codes.filter fun c => !gs.any (·.sym == "_ZTS" ++ c)).map name

/-- `what()` of the standard exception classes whose message is fixed returns one string, as
libc++ and libstdc++ return a literal: a read-only global per message (`whatSym`) that the
`Model.excWhat` models return. -/
def stdWhat (m : Module) : Module :=
  let msgs := m.funcs.foldl (fun acc f => match f.model with
    | some (.excWhat msg) => if acc.contains msg then acc else acc ++ [msg]
    | _ => acc) ([] : List String)
  let gs := msgs.filterMap fun msg =>
    if m.globals.any (·.sym == whatSym msg) then none
    else some { sym := whatSym msg, ty := .array (.int true 8) (msg.length + 1),
                init := some (.str (msg.toList.map fun c => (c.toNat : Int)) 1), constant := true }
  { m with globals := m.globals ++ gs }

/-- The program's `errno`, which glibc's `errno` macro reaches through `__errno_location()`: an
`int` global (`Std.errnoSym`), 0 at program start (C11 7.5p3), added after the other globals (whose
blocks stay the same) of a module that declares `__errno_location`. It is not internal: the units
that `cir2lean --link` links share one. -/
def errnoGlobal (m : Module) : Module :=
  if m.funcs.any (·.sym == "__errno_location") && !m.globals.any (·.sym == Std.errnoSym) then
    { m with globals := m.globals ++ [{ sym := Std.errnoSym, ty := .int true 32, init := some (.int 0) }] }
  else m

/-- Symbol references of a constant renamed by `f`. -/
partial def renameConst (f : String → String) : Const → Const
  | .globalAddr s idx => .globalAddr (f s) idx
  | .vtableAddr vt i k => .vtableAddr (f vt) i k
  | .blockAddr s l => .blockAddr (f s) l
  | .array cs => .array (cs.map (renameConst f))
  | .record cs => .record (cs.map (renameConst f))
  | c => c

mutual
/-- Symbol references of an operation renamed by `f`. -/
partial def renameOp (f : String → String) : Op → Op
  | .call l r (.direct s) a t rt n => .call l r (.direct (f s)) a t rt n
  | .const r t c => .const r t (renameConst f c)
  | .getGlobal r s t => .getGlobal r (f s) t
  | .blockAddress r s l => .blockAddress r (f s) l
  | .indirectGoto t s => .indirectGoto t (f s)
  | .vtableAddressPoint r vt i o => .vtableAddressPoint r (f vt) i o
  | .vttGlobalAddr r vtt n => .vttGlobalAddr r (f vtt) n
  | .scope r b => .scope r (renameRegion f b)
  | .cleanupScope k b c => .cleanupScope k (renameRegion f b) (renameRegion f c)
  | .ifOp c t e => .ifOp c (renameRegion f t) (renameRegion f e)
  | .ternary r c t e => .ternary r c (renameRegion f t) (renameRegion f e)
  | .forOp l c b s cl => .forOp l (renameRegion f c) (renameRegion f b) (renameRegion f s)
      (cl.map fun (k, r) => (k, renameRegion f r))
  | .whileOp l c b cl => .whileOp l (renameRegion f c) (renameRegion f b)
      (cl.map fun (k, r) => (k, renameRegion f r))
  | .doWhileOp l b c => .doWhileOp l (renameRegion f b) (renameRegion f c)
  | .switch c t b => .switch c t (renameRegion f b)
  | .case k v b => .case k v (renameRegion f b)
  | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (renameRegion f b)
  | .setjmpRun r t v b => .setjmpRun r t v (renameRegion f b)
  | .tryOp b hs u => .tryOp (renameRegion f b) (hs.map fun (k, r) => (k, renameRegion f r))
      (u.map (renameRegion f))
  | op => op
partial def renameRegion (f : String → String) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (ops.map (renameOp f)))
end

/-- The function that `f` stands for: `f`, or the function that its alias names, through aliases of
aliases (`seen`: the symbols followed, the latest first); `none` when they end at a symbol that the
module does not have. A cycle is an error. -/
partial def aliasFinal (byName : Std.HashMap String FuncDecl) (seen : List String) (f : FuncDecl) :
    Except String (Option FuncDecl) :=
  match f.alias with
  | none => pure (some f)
  | some t =>
    if seen.contains t then
      throw s!"function aliases in a cycle: {" -> ".intercalate ((t :: seen).reverse.map ("@" ++ ·))}"
    else match byName[t]? with
      | some g => aliasFinal byName (t :: seen) g
      | none => pure none

/-- The global that `g` names: `g`, or the global that its alias names, through aliases of aliases
(`seen` as for `aliasFinal`); `none` when they end at a symbol that the module does not have. -/
partial def globalAliasFinal (byName : Std.HashMap String GlobalDecl) (seen : List String) (g : GlobalDecl) :
    Except String (Option GlobalDecl) :=
  match g.alias with
  | none => pure (some g)
  | some t =>
    if seen.contains t then
      throw s!"global aliases in a cycle: {" -> ".intercalate ((t :: seen).reverse.map ("@" ++ ·))}"
    else match byName[t]? with
      | some h => globalAliasFinal byName (t :: seen) h
      | none => pure none

/-- Aliases resolved (`cir.func @f(…) alias(@g)`, `cir.global @a alias(@g)`). A function alias gets
the body and the model of the function that its aliases end at, and keeps its own symbol, name and
linkage, so that a call of it runs that function (also from another unit, after `linkUnits`); the
module's references to an alias (calls, function addresses, global initializers such as vtables)
name that function, whose address the alias has (C11 6.5.9p6: pointers to the same function
compare equal). An alias declared with another type than that function is no other name of it: a
call of it is undefined (C11 6.5.2.2p9). An alias of a function that the module does not have
stays a declaration (ClangIR emits no `static` function that only an alias uses), so a call of it
is undefined. A global alias names the object of the global that its aliases end at: the
references to it are references to that global (an access of another type is then a type-punned
one). -/
def resolveAliases (m : Module) : Except String Module := do
  if m.funcs.all (·.alias.isNone) && m.globals.all (·.alias.isNone) then return m
  let byName : Std.HashMap String FuncDecl := m.funcs.foldl (fun h f => h.insert f.sym f) {}
  let mut target : Std.HashMap String String := {}
  let mut funcs : Array FuncDecl := #[]
  for f in m.funcs do
    match f.alias, ← aliasFinal byName [f.sym] f with
    | some _, some g =>
      if f.params != g.params || f.ret != g.ret then
        let msg := s!"call of @{f.sym}, an alias of @{g.sym} declared with another type (C11 6.5.2.2p9)"
        funcs := funcs.push { f with model := none, body := some (.mk [.mk [] [.fail msg]]) }
      else
        target := target.insert f.sym g.sym
        funcs := funcs.push
          { g with sym := f.sym, demangled := f.demangled, internal := f.internal, alias := f.alias }
    -- not an alias, or an alias of a function that the module does not have
    | _, _ => funcs := funcs.push f
  let gByName : Std.HashMap String GlobalDecl := m.globals.foldl (fun h g => h.insert g.sym g) {}
  for g in m.globals do
    match g.alias, ← globalAliasFinal gByName [g.sym] g with
    | some _, some h => target := target.insert g.sym h.sym
    | _, _ => pure ()
  let r : String → String := fun s => target.getD s s
  return { m with
    globals := m.globals.map fun g => { g with init := g.init.map (renameConst r) }
    funcs := funcs.toList.map fun f => { f with body := f.body.map (renameRegion r) } }

/-- The pointers through which an operation stores into an object, with whether it is a store
(and not only a `volatile` access) and whether it is a `volatile` access (`vols`: the pointers of
the accesses that count as `volatile` there); `va_start`, `va_end`, `va_arg` and `va_copy` change
their `va_list`. A call stores nothing itself: its callee notes its own stores, and a library
model its own (`Std.sjMarkMem`). -/
def sjNotesOf (vols : List VId) : Op → List (VId × Bool × Bool)
  | .store _ a _ => [(a, true, vols.contains a)]
  | .load _ a _ => if vols.contains a then [(a, false, true)] else []
  | .copy _ d _ => [(d, true, false)]
  | .libc _ (d :: _) => [(d, true, false)]
  | .atomicFetch _ _ _ p _ _ | .atomicXchg _ p _ _ | .atomicCmpXchg _ _ p _ _ _ _ _ => [(p, true, false)]
  | .setBitfield _ p _ _ _ _ _ _ => [(p, true, false)]
  | .vaStart ap | .vaEnd ap | .vaArg _ ap _ | .vaArgP _ ap _ | .vaCopy _ ap => [(ap, true, false)]
  | _ => []

mutual
/-- `ops` with an `Op.sjNote` after each operation that stores into an object or is a `volatile`
access (`sjNotesOf`; `vols`: in the rest of a `setjmp`, the `setjmp`'s `vol`, its accesses through
pointers into objects it does not hold): at run time the live `setjmp` invocations whose objects
it reaches record it (`Std.sjMarkMem`), what a `longjmp` back finds changed (C11 7.13.2.1p3).
After the operation, not before it: a store of a call's result stays right after the call
(`retObjects` on a linked module). -/
partial def sjNoteOps (vols : List VId) : List Op → List Op
  | [] => []
  | .setjmp r e vol svol ok b :: rest =>
    .setjmp r e vol svol ok (sjNoteRegion vol b) :: sjNoteOps vols rest
  | op :: rest =>
    mapRegions (sjNoteRegion vols) op ::
      ((sjNotesOf vols op).map fun (p, st, v) => Op.sjNote p st v) ++ sjNoteOps vols rest
partial def sjNoteRegion (vols : List VId) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (sjNoteOps vols ops))
end

/-- Whether a function of the module has a `setjmp` that a `longjmp` can come back to. -/
def hasSetjmp (m : Module) : Bool :=
  m.funcs.any fun f => match f.body with
    | some body => (allOpsRegion body).any fun op => match op with | .setjmp .. => true | _ => false
    | none => false

/-- In a module with a `setjmp` (`hasSetjmp`), every function notes its stores into objects
(`sjNoteOps`; in a function without a `setjmp`, its `volatile` accesses, `FuncDecl.volPtrs`, count
as `volatile`), so that a callee's store counts, not a pointer passed to it; and the module gets
the registry of the live `setjmp` invocations (`Std.sjRegistrySym`, an empty list at program
start), after the other globals (whose blocks stay the same; not internal: the units that
`cir2lean --link` links share one). A function noted already (another unit's, on a linked module)
stays as it is, so the pass can run again. -/
def sjNotes (m : Module) : Module :=
  if !hasSetjmp m then m else
  let funcs := m.funcs.map fun f =>
    match f.body with
    | some body =>
      let ops := allOpsRegion body
      if ops.any (fun op => match op with | .sjNote .. => true | _ => false) then f else
      let own := ops.any fun op => match op with | .setjmp .. => true | _ => false
      { f with body := some (sjNoteRegion (if own then [] else f.volPtrs) body) }
    | none => f
  let globals :=
    if m.globals.any (·.sym == Std.sjRegistrySym) then m.globals
    else m.globals ++ [{ sym := Std.sjRegistrySym, ty := .array (.int true 64) 0, init := some (.array []) }]
  { m with funcs := funcs, globals := globals }

/-! ### The C++ library's own `<string.h>` calls -/

/-- A demangled name in the C++ standard library's namespaces (libc++'s `std::__1`, libstdc++'s
`std`, `std::__cxx11`, `__gnu_cxx`). -/
def isStdLibName (demangled : String) : Bool :=
  match parseDemangled demangled with
  | some dn =>
    let q := normalizeNs dn.qual
    q == "std" || q.startsWith "std::" || q == "__gnu_cxx" || q.startsWith "__gnu_cxx::"
  | none => false

/-- A header of the C++ standard library: libc++'s `…/c++/v1/…`, libstdc++'s `…/c++/<version>/…`
(also under its target directory, `…/<triple>/c++/<version>/…`). -/
def isStdLibPath (file : String) : Bool :=
  (file.splitOn "/c++/").drop 1 |>.any fun rest =>
    rest.startsWith "v1/" || (rest.toList.head?.any Char.isDigit)

/-- A function of the C++ standard library: in its namespaces and defined in its headers (the
location of the definition), so not a program's specialization of a standard template
([namespace.std]p2) nor a function a program adds to `std`, which are the program's code. -/
def isStdLibFunc (f : FuncDecl) : Bool :=
  isStdLibName f.demangled && isStdLibPath f.srcFile

mutual
/-- `op` with its `cir.libc` operations tagged (`memcpy.std`, `memmove.std`, `memset.std`) and its
direct calls renamed by `ren`. -/
partial def tagStdMemOp (ren : List (String × String)) : Op → Op
  | .libc fn args =>
    if fn == "memcpy" || fn == "memmove" || fn == "memset" then .libc (fn ++ ".std") args else .libc fn args
  | .call l r (.direct s) a t rt n => .call l r (.direct ((ren.lookup s).getD s)) a t rt n
  | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (tagStdMemRegion ren b)
  | op => mapRegions (tagStdMemRegion ren) op
partial def tagStdMemRegion (ren : List (String × String)) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (ops.map (tagStdMemOp ren)))
end

/-- The `<string.h>` calls of the C++ standard library's own code (the bodies of its functions, by
namespace and definition location, `isStdLibFunc`): its `cir.libc` operations become `memcpy.std`,
`memmove.std` and `memset.std`, and
its calls of the module's `memcpy`, `memmove`, `memset` and `memcmp` call `memcpy.std`, ..., which
are declared after the module's functions with the models `Model.memcpyStd`, ... With length 0
these skip the pointer checks: C11 7.24.1p2 binds the program's calls, not the implementation's own
(libc++ relocates and copies empty ranges through null pointers, as its platform allows). The
program's own calls keep the checks. -/
def tagStdMemCalls (m : Module) : Module :=
  let stdModel : Model → Option Model := fun
    | .memcpy => some .memcpyStd
    | .memmove => some .memmoveStd
    | .memset => some .memsetStd
    | .memcmp => some .memcmpStd
    | _ => none
  let decls : List (FuncDecl × Model) := m.funcs.filterMap fun f =>
    (f.model.bind stdModel).map fun md => (f, md)
  let ren : List (String × String) := decls.map fun (f, _) => (f.sym, f.sym ++ ".std")
  let funcs := m.funcs.map fun f =>
    if f.body.isSome && isStdLibFunc f then { f with body := f.body.map (tagStdMemRegion ren) }
    else f
  let called (s : String) : Bool := funcs.any fun f => match f.body with
    | some b => (allOpsRegion b).any fun op => match op with
      | .call _ _ (.direct t) _ _ _ _ => t == s
      | _ => false
    | none => false
  let extra := decls.filterMap fun (f, md) =>
    if called (f.sym ++ ".std") then
      some { f with sym := f.sym ++ ".std", demangled := "", body := none, model := some md, ssaNames := [],
                    ssaLocs := [], alias := none }
    else none
  { m with funcs := funcs ++ extra }

/-- Declarations of `__builtin_setjmp` and `__builtin_longjmp`, whose calls the parser makes of
`cir.eh.setjmp` and `cir.eh.longjmp` (no module declares them), after the module's functions when it
calls them; `recognize` gives them the models of `setjmp` and `longjmp`. -/
def builtinJmpDecls (m : Module) : Module :=
  let called (s : String) : Bool := m.funcs.any fun f => match f.body with
    | some b => (allOpsRegion b).any fun op => match op with
      | .call _ _ (.direct t) _ _ _ _ => t == s
      | _ => false
    | none => false
  let decl (s : String) (ret : Ty) : List FuncDecl :=
    if called s && !m.funcs.any (·.sym == s) then
      [{ sym := s, params := [.ptr (.ptr .void)], ret := ret, nothrow := true }]
    else []
  { m with funcs := m.funcs ++ decl "__builtin_setjmp" (.int true 32) ++ decl "__builtin_longjmp" .void }

/-- A type with no value representation in C++: a complete record, not a union, whose members
are padding, empty members, or of such a type themselves, and an array of such a type. An empty
class object has no value bits ([intro.object]p9), and an empty member may share its address with
another member ([dcl.attr.nouniqueaddr]). -/
def emptyValueTy (recs : List RecordDecl) : Nat → Ty → Bool
  | 0, _ => false
  | d + 1, .record n =>
    match recs.find? (·.name == n) with
    | some r => r.complete && r.kind != .union &&
        r.members.all fun (k, t) => k == .pad || k == .empty || (k == .data && emptyValueTy recs d t)
    | none => false
  | d + 1, .array t _ => emptyValueTy recs d t
  | _, _ => false

mutual
/-- `ops` without the stores and copies of a type with no value representation (`emptyValueTy`),
in nested regions too. -/
partial def dropEmptyStoreOps (recs : List RecordDecl) : List Op → List Op
  | [] => []
  | op :: rest =>
    match op with
    | .store _ _ ty | .copy _ _ ty =>
      if emptyValueTy recs 16 ty then dropEmptyStoreOps recs rest else op :: dropEmptyStoreOps recs rest
    | _ => dropEmptyStoreOp recs op :: dropEmptyStoreOps recs rest
partial def dropEmptyStoreOp (recs : List RecordDecl) : Op → Op
  | .scope r b => .scope r (dropEmptyStoreRegion recs b)
  | .cleanupScope k b c => .cleanupScope k (dropEmptyStoreRegion recs b) (dropEmptyStoreRegion recs c)
  | .ifOp c t e => .ifOp c (dropEmptyStoreRegion recs t) (dropEmptyStoreRegion recs e)
  | .ternary r c t e => .ternary r c (dropEmptyStoreRegion recs t) (dropEmptyStoreRegion recs e)
  | .forOp l c b s cl => .forOp l (dropEmptyStoreRegion recs c) (dropEmptyStoreRegion recs b)
      (dropEmptyStoreRegion recs s) (cl.map fun (k, r) => (k, dropEmptyStoreRegion recs r))
  | .whileOp l c b cl => .whileOp l (dropEmptyStoreRegion recs c) (dropEmptyStoreRegion recs b)
      (cl.map fun (k, r) => (k, dropEmptyStoreRegion recs r))
  | .doWhileOp l b c => .doWhileOp l (dropEmptyStoreRegion recs b) (dropEmptyStoreRegion recs c)
  | .switch c t b => .switch c t (dropEmptyStoreRegion recs b)
  | .case k v b => .case k v (dropEmptyStoreRegion recs b)
  | .setjmp r e vol sv ok b => .setjmp r e vol sv ok (dropEmptyStoreRegion recs b)
  | .setjmpRun r t v b => .setjmpRun r t v (dropEmptyStoreRegion recs b)
  | .tryOp b hs u => .tryOp (dropEmptyStoreRegion recs b) (hs.map fun (k, r) => (k, dropEmptyStoreRegion recs r))
      (u.map (dropEmptyStoreRegion recs))
  | op => op
partial def dropEmptyStoreRegion (recs : List RecordDecl) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (dropEmptyStoreOps recs ops))
end

/-- In a C++ module, the stores and copies of a type with no value representation write nothing,
so they are dropped (`dropEmptyStoreOps`): CIR's records leave an empty member out, and CIR
stores such a member's value through a cast of the address it shares with another member, which
the store would overwrite (libc++'s compressed pairs: `__tree`'s copy constructor builds its node
allocator, from `select_on_container_copy_construction`, on `__end_node_`). C has no empty
structures (only as a GNU extension), so a C module keeps them. -/
def dropEmptyStores (m : Module) : Module :=
  if !m.cxx then m else
  { m with funcs := m.funcs.map fun f => { f with body := f.body.map (dropEmptyStoreRegion m.records) } }

/-- Parse a CIR file and fill demangled names and library models; also the members' names that
the `cir.get_member` operations give (`parseModuleNames`). -/
def loadModuleNamesFromString (src : String) (modName : String := "")
    (recRename : Std.HashMap String String := {}) :
    IO (Module × Std.HashMap String (Std.HashMap Nat String)) := do
  let (m, names) ← match parseModuleNames src modName recRename with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"CIR parse error: {e}")
  let m := dropEmptyStores (builtinJmpDecls m)
  let dm ← demangleAll (m.funcs.map (·.sym)).toArray
  let funcs := m.funcs.map fun f =>
    let d := dm.getD f.sym ""
    let info : FuncInfo :=
      { sym := f.sym, demangled := d, params := f.params, ret := f.ret,
        special := f.special, records := m.records }
    -- a function with internal linkage and a body is the program's own (a
    -- `static double asin(double)` in a file without <math.h>), not the library's; so is
    -- one with a body named like a function of a library whose names C and C++ do not
    -- reserve (libevent, POSIX; `__errno_location`: `nonReservedModel`), whatever its linkage
    let mdl := if f.internal && f.body.isSome then none else recognize info
    let mdl := if f.body.isSome && (mdl.map nonReservedModel).getD false then none else mdl
    { f with demangled := d, model := mdl }
  -- an alias runs the function it names
  let m ← match resolveAliases { m with funcs := funcs } with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"CIR parse error: {e}")
  -- the variadic arguments of calls to functions with a body keep their types; a return slot
  -- that may be unstored at a `cir.return` gives an indeterminate value, and a discarded
  -- aggregate result is not stored; the arguments of printf-family calls with a literal format
  -- are checked against it; the rest of a `setjmp` notes its stores; the C++ library's own
  -- `<string.h>` calls are tagged; a by-value parameter of a class non-trivial for calls is the
  -- caller's object, and so is a result of such a class; the library's typeinfo objects and
  -- what() strings are added; the C library's objects that a module only declares and that are
  -- modelled get their values (the standard streams, `__libc_single_threaded`, `optind`,
  -- `opterr`, `signgam`), the C++ standard stream objects become live objects, and after the
  -- other globals the program's `errno` when the module declares `__errno_location`
  return (checkFormats (boxVarargs (sjNotes (markRetDiscards (markRetLoads (tagStdMemCalls
    (retObjects (objectParams (errnoGlobal (stdWhat { m with
      globals := stdTypeinfo (stdIostreams (libcGlobals (libcSingleThreaded
        (stdStreams m.globals)))) }))))))))),
    names)

/-- Parse a CIR file and fill demangled names and library models. -/
def loadModuleFromString (src : String) (modName : String := "")
    (recRename : Std.HashMap String String := {}) : IO Module := do
  return (← loadModuleNamesFromString src modName recRename).1

def loadModule (path : System.FilePath) (modName : String := "")
    (recRename : Std.HashMap String String := {}) : IO Module := do
  loadModuleFromString (← IO.FS.readFile path) modName recRename

/-- `loadModule`, with the members' names (`loadModuleNamesFromString`). -/
def loadModuleNames (path : System.FilePath) (modName : String := "") :
    IO (Module × Std.HashMap String (Std.HashMap Nat String)) := do
  loadModuleNamesFromString (← IO.FS.readFile path) modName

/-! ### Statistics -/

mutual
partial def countUnknownOp (acc : Std.HashMap String Nat) : Op → Std.HashMap String Nat
  | .unknown n _ => acc.insert n (acc.getD n 0 + 1)
  | .scope _ r => countUnknownRegion acc r
  | .cleanupScope _ a b => countUnknownRegion (countUnknownRegion acc a) b
  | .ifOp _ a b => countUnknownRegion (countUnknownRegion acc a) b
  | .ternary _ _ a b => countUnknownRegion (countUnknownRegion acc a) b
  | .forOp _ a b c cl =>
    let acc := countUnknownRegion (countUnknownRegion (countUnknownRegion acc a) b) c
    match cl with | some (_, r) => countUnknownRegion acc r | none => acc
  | .whileOp _ a b cl =>
    let acc := countUnknownRegion (countUnknownRegion acc a) b
    match cl with | some (_, r) => countUnknownRegion acc r | none => acc
  | .doWhileOp _ a b => countUnknownRegion (countUnknownRegion acc a) b
  | .switch _ _ r | .setjmp _ _ _ _ _ r | .setjmpRun _ _ _ r => countUnknownRegion acc r
  | .case _ _ r => countUnknownRegion acc r
  | .tryOp b hs u =>
    let acc := countUnknownRegion acc b
    let acc := hs.foldl (fun acc (_, r) => countUnknownRegion acc r) acc
    match u with | some r => countUnknownRegion acc r | none => acc
  | _ => acc
partial def countUnknownRegion (acc : Std.HashMap String Nat) : Region → Std.HashMap String Nat
  | .mk bs => bs.foldl (fun acc (.mk _ ops) => ops.foldl countUnknownOp acc) acc
end

mutual
/-- Symbols of the functions an operation calls directly or whose address it
takes (`cir.get_global` of a function). -/
partial def calleesOp (acc : Array String) : Op → Array String
  | .call _ _ (.direct s) _ _ _ _ => if acc.contains s then acc else acc.push s
  | .getGlobal _ s (.func ..) => if acc.contains s then acc else acc.push s
  | .scope _ r => calleesRegion acc r
  | .cleanupScope _ a b => calleesRegion (calleesRegion acc a) b
  | .ifOp _ a b => calleesRegion (calleesRegion acc a) b
  | .ternary _ _ a b => calleesRegion (calleesRegion acc a) b
  | .forOp _ a b c cl =>
    let acc := calleesRegion (calleesRegion (calleesRegion acc a) b) c
    match cl with | some (_, r) => calleesRegion acc r | none => acc
  | .whileOp _ a b cl =>
    let acc := calleesRegion (calleesRegion acc a) b
    match cl with | some (_, r) => calleesRegion acc r | none => acc
  | .doWhileOp _ a b => calleesRegion (calleesRegion acc a) b
  | .switch _ _ r | .setjmp _ _ _ _ _ r | .setjmpRun _ _ _ r => calleesRegion acc r
  | .case _ _ r => calleesRegion acc r
  | .tryOp b hs u =>
    let acc := calleesRegion acc b
    let acc := hs.foldl (fun acc (_, r) => calleesRegion acc r) acc
    match u with | some r => calleesRegion acc r | none => acc
  | _ => acc
partial def calleesRegion (acc : Array String) : Region → Array String
  | .mk bs => bs.foldl (fun acc (.mk _ ops) => ops.foldl calleesOp acc) acc
end

mutual
/-- Source locations of an operation shifted by `f` (relative positions for
`cir2lean --modular`). -/
partial def mapLocOp (f : Loc → Loc) : Op → Op
  | .call l r c a t rt n => .call (f l) r c a t rt n
  | .scope r b => .scope r (mapLocRegion f b)
  | .cleanupScope k b c => .cleanupScope k (mapLocRegion f b) (mapLocRegion f c)
  | .ifOp c t e => .ifOp c (mapLocRegion f t) (mapLocRegion f e)
  | .ternary r c t e => .ternary r c (mapLocRegion f t) (mapLocRegion f e)
  | .forOp l c b s cl => .forOp (f l) (mapLocRegion f c) (mapLocRegion f b) (mapLocRegion f s)
      (cl.map fun (k, r) => (k, mapLocRegion f r))
  | .whileOp l c b cl => .whileOp (f l) (mapLocRegion f c) (mapLocRegion f b)
      (cl.map fun (k, r) => (k, mapLocRegion f r))
  | .doWhileOp l b c => .doWhileOp (f l) (mapLocRegion f b) (mapLocRegion f c)
  | .switch c t b => .switch c t (mapLocRegion f b)
  | .case k v b => .case k v (mapLocRegion f b)
  | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (mapLocRegion f b)
  | .setjmpRun r t v b => .setjmpRun r t v (mapLocRegion f b)
  | .tryOp b hs u => .tryOp (mapLocRegion f b) (hs.map fun (k, r) => (k, mapLocRegion f r))
      (u.map (mapLocRegion f))
  | op => op
partial def mapLocRegion (f : Loc → Loc) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (ops.map (mapLocOp f)))
end

mutual
/-- The smallest line number among the source locations of an operation. -/
partial def minLineOp (acc : Nat) : Op → Nat
  | .call l .. => if l.line != 0 then min acc l.line else acc
  | .scope _ b => minLineRegion acc b
  | .cleanupScope _ b c => minLineRegion (minLineRegion acc b) c
  | .ifOp _ t e => minLineRegion (minLineRegion acc t) e
  | .ternary _ _ t e => minLineRegion (minLineRegion acc t) e
  | .forOp l c b s cl =>
    let acc := if l.line != 0 then min acc l.line else acc
    let acc := minLineRegion (minLineRegion (minLineRegion acc c) b) s
    match cl with | some (_, r) => minLineRegion acc r | none => acc
  | .whileOp l c b cl =>
    let acc := if l.line != 0 then min acc l.line else acc
    let acc := minLineRegion (minLineRegion acc c) b
    match cl with | some (_, r) => minLineRegion acc r | none => acc
  | .doWhileOp l b c =>
    minLineRegion (minLineRegion (if l.line != 0 then min acc l.line else acc) b) c
  | .switch _ _ b | .setjmp _ _ _ _ _ b | .setjmpRun _ _ _ b => minLineRegion acc b
  | .case _ _ b => minLineRegion acc b
  | .tryOp b hs u =>
    let acc := hs.foldl (fun acc (_, r) => minLineRegion acc r) (minLineRegion acc b)
    match u with | some r => minLineRegion acc r | none => acc
  | _ => acc
partial def minLineRegion (acc : Nat) : Region → Nat
  | .mk bs => bs.foldl (fun acc (.mk _ ops) => ops.foldl minLineOp acc) acc
end

/-- `f` with its source lines relative to its first located line (returned),
so that an edit elsewhere in the file does not change its text. -/
def relativeLines (f : FuncDecl) : FuncDecl × Nat :=
  match f.body with
  | none => (f, 0)
  | some r =>
    let base := minLineRegion 1000000000 r
    if base == 1000000000 then (f, 0)
    else ({ f with body := some (mapLocRegion (fun l => if l.line == 0 then l else { l with line := l.line - base + 1 }) r) }, base)

/-- The functions a function calls (or takes the address of), in order. -/
def funcCallees (f : FuncDecl) : List String :=
  match f.body with
  | some r => (calleesRegion #[] r).toList
  | none => []

def unknownOps (m : Module) : List (String × Nat) :=
  let acc := m.funcs.foldl (fun acc f => match f.body with
    | some r => countUnknownRegion acc r
    | none => acc) {}
  (acc.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))).toList

end CIR.Frontend

namespace CIR.Frontend

mutual
/-- Number of operations, including nested ones. -/
partial def countOpsOp : Op → Nat
  | .scope _ r => 1 + countOpsRegion r
  | .cleanupScope _ a b => 1 + countOpsRegion a + countOpsRegion b
  | .ifOp _ a b => 1 + countOpsRegion a + countOpsRegion b
  | .ternary _ _ a b => 1 + countOpsRegion a + countOpsRegion b
  | .forOp _ a b c cl => 1 + countOpsRegion a + countOpsRegion b + countOpsRegion c +
      (match cl with | some (_, r) => countOpsRegion r | none => 0)
  | .whileOp _ a b cl => 1 + countOpsRegion a + countOpsRegion b +
      (match cl with | some (_, r) => countOpsRegion r | none => 0)
  | .doWhileOp _ a b => 1 + countOpsRegion a + countOpsRegion b
  | .switch _ _ r | .setjmp _ _ _ _ _ r | .setjmpRun _ _ _ r => 1 + countOpsRegion r
  | .case _ _ r => 1 + countOpsRegion r
  | .tryOp b hs u => 1 + countOpsRegion b + (hs.map fun (_, r) => countOpsRegion r).sum +
      (match u with | some r => countOpsRegion r | none => 0)
  | _ => 1
partial def countOpsRegion : Region → Nat
  | .mk bs => (bs.map fun (.mk _ ops) => (ops.map countOpsOp).sum).sum
end

def countOps (m : Module) : Nat :=
  (m.funcs.map fun f => match f.body with | some r => countOpsRegion r | none => 0).sum

end CIR.Frontend
