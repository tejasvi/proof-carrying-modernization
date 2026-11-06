import CIR.Semantics.Basic

/-! The verification context of a module. -/

namespace CIR

/-- Context of a module: global `i` (in `Module.globals` order) lives in
block `i`; the initial memory allocates the globals first. -/
def Ctx.ofModule (M : Module) : Ctx :=
  { mod := M, gaddr := fun s => M.globals.findIdx? (·.sym == s) }

end CIR
