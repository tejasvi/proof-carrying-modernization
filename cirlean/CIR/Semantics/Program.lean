import CIR.Semantics.Eval
import CIR.Semantics.Init

/-!
  A whole program run: what happens before and after the entry function.

  Before `main`, the module's constructors run (`cir.global_ctors`): functions marked
  `__attribute__((constructor(p)))`, and the `_GLOBAL__sub_I_*` / `_GLOBAL__I_00p` functions that
  ClangIR emits for the dynamic initialization of C++ globals (`init_priority(p)`), lower
  priorities first and, among equal priorities, in module order (as the ELF `.init_array` sections
  run them).

  The program ends when the entry returns, or at a call of `exit(n)`, `_Exit(n)` or
  `quick_exit(n)` (`Exit.halt n`), wherever it is called, a constructor included. After a return
  and at `exit`, the exit sequence runs (`runExit`): the functions registered with `atexit` /
  `__cxa_atexit` (the destructors of C++ objects with static storage duration), the last
  registered first, those registered meanwhile included (C11 7.22.4.4p3); then the
  `cir.global_dtors` (`__attribute__((destructor(p)))`), in the reverse of the constructor order
  (a higher priority number first). At `exit` the automatic objects of the calls in progress are
  still alive (`Exit.leaveMem`), so the handlers may use them; after a return from the entry its
  own have ended. `_Exit` and `quick_exit` run none of them; `quick_exit` runs the functions
  registered with `at_quick_exit` instead, the last registered first (C11 7.22.4.7), and then
  ends the program. During the exit sequence `_Exit` ends the
  program at once, and a call of `exit` or `quick_exit` is undefined (C11 7.22.4.4p2, 7.22.4.7p2:
  a program calls them at most once, and a return from `main` counts as a call of `exit`). An
  exception that escapes a constructor, handler or destructor calls `std::terminate`, which
  aborts: undefined, like `abort()`, in this semantics.
-/

namespace CIR

/-- The constructors of `M` in the order they run: by priority, then in module order. -/
def Module.ctorOrder (M : Module) : List String :=
  (M.ctors.mergeSort (fun a b => a.2 ≤ b.2)).map (·.1)

/-- The `cir.global_dtors` of `M` in the order they run: the reverse of the order by priority
(then module order). -/
def Module.dtorOrder (M : Module) : List String :=
  ((M.dtors.mergeSort (fun a b => a.2 ≤ b.2)).map (·.1)).reverse

/-- Run the functions `fs` (each with the arguments given) in order: `none` when they all
return, `some n` when one of them ends the program with status `n` (the rest do not run). `what`
names them in diagnostics. -/
def runEach (ctx : Ctx) (what : String) : List (String × List Val) → Mem → Res (Option Int × Mem)
  | [], m => pure (none, m)
  | (f, args) :: fs, m => do
    let (e, m) ← evalCall ctx f args m
    match e with
    | .ret _ => runEach ctx what fs m
    | .halt n => pure (some n, m)
    | .exn _ => .ub s!"exception escaping {what} {f} (std::terminate)"
    | _ => .ub s!"abnormal exit from {what} {f}"

/-- Run the module's constructors on the initial memory (before the program's entry): `some n`
when one of them ends the program with status `n`. A module that calls `rand` or `srand` first
gets the generator's state, as `srand(1)` leaves it, in the first block after the globals
(`Std.randBlock`). -/
def runCtors (ctx : Ctx) (M : Module) (m : Mem) : Res (Option Int × Mem) :=
  let m := if M.funcs.any (fun f => f.model matches some (.rand _)) then
      let (st, f, r) := Std.randSeed 1
      (m.alloc .global (.other "rand") (Std.randVal st f r)).2
    else m
  runEach ctx "constructor" (M.ctorOrder.map (·, [])) m

/-- The function registered last as a handler of `kind` (`atexit`: by `atexit` / `__cxa_atexit`;
`at_quick_exit`) in `m`, with the argument it is called with, and the memory without that
registration (the models keep the registrations of a kind in one block, in order,
`Std.handlerRegistry`; a module without the registering function has none, and its blocks are not
searched); `none` when no registration is left. -/
def popHandler (kind : String) (M : Module) (m : Mem) : Option ((String × List Val) × Mem) :=
  if M.funcs.any (fun f => match f.model with
      | some (.atexit _) => kind == "atexit"
      | some .atQuickExit => kind == "at_quick_exit"
      | _ => false) then
    match Std.handlerRegistry kind m M.globals.length with
    | some (b, es) =>
      match es.getLast?, m.write? (.loc b []) (.arr es.dropLast) with
      | some (.agg (.ptr (.fn f) :: args)), some m => some ((f, args), m)
      | _, _ => none
    | none => none
  else none

/-- The memory once a handler called with `args` has returned: a destructor that `__cxa_atexit`
registered for an object of static storage duration (a complete object, a `global` block) has
ended that object's lifetime (C++ [basic.start.term]p1, [basic.life]p1.4), so its block is dead
and every later access is undefined ([basic.life]p7), from a handler registered before the
object's construction too, which runs after its destructor ([basic.start.term]p3). Other
handlers leave memory as it is. -/
def endStatic (args : List Val) (m : Mem) : Mem :=
  match args with
  | [.ptr (.loc b [])] =>
    match m.live? b with
    | some blk => if blk.kind = .global then m.setBlock b { blk with alive := false } else m
    | none => m
  | _ => m

/-- Run the handlers of `kind`, the last registered first, until none is left: a handler
registered while they run runs too, before the earlier ones that have not run yet (C11
7.22.4.4p3, 7.22.4.7p2: in the reverse order of registration; glibc does the same). `some n`
when one of them ends the program with status `n` (the rest do not run). A static object's
destructor ends its lifetime (`endStatic`). -/
def runHandlers (kind : String) (ctx : Ctx) (M : Module) (m : Mem) : Res (Option Int × Mem) :=
  match popHandler kind M m with
  | none => pure (none, m)
  | some ((f, args), m) => do
    let (e, m) ← evalCall ctx f args m
    match e with
    | .ret _ => runHandlers kind ctx M (endStatic args m)
    | .halt n => pure (some n, m)
    | .exn _ => .ub s!"exception escaping {kind} handler {f} (std::terminate)"
    | _ => .ub s!"abnormal exit from {kind} handler {f}"
partial_fixpoint

/-- The function, `_Exit` or `quick_exit`, whose call ended the program without the exit sequence
(their models leave a read-only block of that type, the last block allocated: nothing runs after
the call); `none` when neither was called. -/
def exitNowBy (m : Mem) : Option String :=
  match m.blocks (m.next - 1) with
  | some ⟨.readonly, true, .other f, _⟩ => if f == "_Exit" || f == "quick_exit" then some f else none
  | _ => none

/-- The exit sequence, after the entry returns or at `exit`: the `atexit` handlers, the last
registered first (`runHandlers`), then the module's destructors. `some n` when one of them ends
the program by `_Exit(n)` (the rest do not run); `exit` and `quick_exit` are undefined there. -/
def runExit (ctx : Ctx) (M : Module) (m : Mem) : Res (Option Int × Mem) := do
  let (r, m) ← runHandlers "atexit" ctx M m
  let (r, m) ← match r with
    | none => runEach ctx "destructor" (M.dtorOrder.map (·, [])) m
    | some n => pure (some n, m)
  match r with
  | none => pure (none, m)
  | some n =>
    if exitNowBy m == some "_Exit" then pure (some n, m)
    else .ub "exit or quick_exit called during the exit sequence (C11 7.22.4.4p2, 7.22.4.7p2)"

/-- The end of a program whose code (a constructor, or the entry) finished with `e` in `m`: after a
return and after `exit(n)`, the exit sequence (`runExit`); after `quick_exit(n)`, the
`at_quick_exit` handlers, the last registered first (C11 7.22.4.7p2: `_Exit` may end the program
there, `exit` and `quick_exit` are undefined); `_Exit(n)` ends it at once. The result is the
entry's return, or `.halt n` with the program's exit status. -/
def endProgram (ctx : Ctx) (M : Module) (e : Exit) (m : Mem) : Res (Exit × Mem) :=
  match e with
  | .ret v => do
    let (r, m) ← runExit ctx M m
    pure (match r with | some n => .halt n | none => .ret v, m)
  | .halt n =>
    match exitNowBy m with
    | some "_Exit" => pure (.halt n, m)
    | some _ => do
      let (r, m) ← runHandlers "at_quick_exit" ctx M m
      match r with
      | none => pure (.halt n, m)
      | some k =>
        if exitNowBy m == some "_Exit" then pure (.halt k, m)
        else .ub "exit or quick_exit called by an at_quick_exit handler (C11 7.22.4.7p2)"
    | none => do
      let (r, m) ← runExit ctx M m
      pure (.halt (r.getD n), m)
  | e => pure (e, m)

end CIR
