import CIR

/-!
  Declared-only globals: a global a module only declares (defined in another
  translation unit or a library) has no value in the module, so a read is
  undefined ("external object without a model"); `cir2lean --link` gives it its
  definition from the unit that defines it. `tests/extern/extern_a.c` reads
  `shared_count`, which `tests/extern/extern_b.c` defines as 41.
  Run: `lake env lean tests/ExternGlob.lean` (every check must hold).
-/

open CIR CIR.Frontend

/-- Load units as `cir2lean --link` does and link them (one unit: the unit itself). -/
def loadUnits (paths : List String) : IO Module := do
  let mut units : Array (String × Module) := #[]
  for inp in paths do
    let (m, names) ← loadModuleNames inp
    let ren := anonContentNames m names
    let m ← if ren.isEmpty then pure m else loadModule inp (recRename := ren)
    let stem := (System.FilePath.mk inp).fileStem.getD "unit"
    units := units.push (stem, contentNamedLiterals m)
  match units.toList with
  | [(_, m)] => pure m
  | us =>
    match linkUnits "Test.ExternGlob" us with
    | .error e => throw (IO.userError s!"link: {e}")
    | .ok (merged, _) => pure merged

/-- Run `fn` with no arguments on the initial memory, as `cirrun` shows the result. -/
def runFn (paths : List String) (fn : String) : IO String := do
  let M ← loadUnits paths
  let ctx := Ctx.ofModule M
  return match evalCall ctx fn [] M.initMem with
    | .ok (.ret (some (.int i)), _) => toString i
    | .ok _ => "other"
    | .ub msg => s!"UB: {msg}"
    | .div => "diverges"

#eval show IO Unit from do
  -- unit a alone: `shared_count` is only declared
  let r1 ← runFn ["tests/extern/extern_a.cir"] "read_shared"
  unless r1 == "UB: external object without a model" do
    throw (IO.userError s!"unit a alone: {r1}")
  -- linked with unit b: its definition (41)
  let r2 ← runFn ["tests/extern/extern_a.cir", "tests/extern/extern_b.cir"] "read_shared"
  unless r2 == "42" do
    throw (IO.userError s!"units a and b linked: {r2}")
  -- the declaration's block in unit a alone has no value (it is not alive), its definition's has
  let Ma ← loadUnits ["tests/extern/extern_a.cir"]
  let Mab ← loadUnits ["tests/extern/extern_a.cir", "tests/extern/extern_b.cir"]
  let alive (M : Module) : Option Bool := do
    let i ← M.globals.findIdx? (·.sym == "shared_count")
    let blk ← M.initMem.blocks i
    pure blk.alive
  unless alive Ma == some false && alive Mab == some true do
    throw (IO.userError s!"blocks: {alive Ma} {alive Mab}")
  IO.println "ExternGlob: ok"
