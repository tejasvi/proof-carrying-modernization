import CIR.Semantics.Context

/-!
  The initial memory of a module: global `i` (in `Module.globals` order) is
  allocated in block `i`, matching `Ctx.ofModule`. Globals start with their
  constant initializer (a definition without one in the source has CIR's
  zero initializer). A global without an initializer is one the module only
  declares: it is defined in another translation unit or a library, so the
  module does not know its value, and its block (of kind `external`) is not
  alive: every access is undefined ("external object without a model",
  `Ctx.reachIn`); a constant one keeps a read-only block, which is not alive
  either (its accesses fail as on any block that is not alive), so that the
  read-only blocks are exactly those of the constant globals
  (`Module.RoGlobals.frame`). The frontend gives the C library's objects that
  are modelled their values (`Frontend.stdStreams`,
  `Frontend.libcSingleThreaded`, `Frontend.stdTypeinfo`) and the C++ standard
  stream objects a live block of indeterminate value (`Frontend.stdIostreams`),
  and `cir2lean --link` gives a global the definition from the unit that has it.
  Dynamic initialisers (global constructors) are not run here: a whole program run
  starts with `runCtors` (`CIR/Semantics/Program.lean`).
  `constant` globals (string literals, `const` data) are read-only.
-/

namespace CIR

/-- The kind of a global's block: `readonly` for a constant one (also one the module only
declares, whose block is not alive), `external` for another global the module only declares (no
initializer), else `global`. -/
def GlobalDecl.blockKind (g : GlobalDecl) : BlockKind :=
  if g.constant then .readonly else if g.init.isNone then .external else .global

def Module.initMem (M : Module) : Mem := Id.run do
  let ctx := Ctx.ofModule M
  let mut m := Mem.empty
  for g in M.globals do
    let v := match g.init with
      | some c => (ctx.constVal 32 g.ty c).getD .undef
      | none => .undef
    let (_, m') := m.allocAs g.blockKind g.init.isSome g.ty v
    m := m'
  return m

/-- The constant globals of `M` (string literals, `const` data) hold their
initial values in `m`. This holds in every memory reached from `M.initMem`
unless the program writes an indeterminate position of a constant global (an
undefined, poison or unmodelled initializer, a union member other than the
initialized one), which `Mem.write?` takes for the initialization of a const
object (`Val.initBy`), or calls a destructor on a constant global of class
type, which ends its lifetime (`endLifetime`): read-only blocks are written
nowhere else, and globals are never freed. Stated as an assumption of a
function's specification, it lets the proof read string literals and lookup
tables (`cir_ro_globals`). -/
def Module.RoGlobals (M : Module) (m : Mem) : Prop :=
  ∀ (i : Nat) (g : GlobalDecl), M.globals[i]? = some g → g.constant = true →
    m.blocks i = M.initMem.blocks i

end CIR
