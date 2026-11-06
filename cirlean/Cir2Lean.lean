import CIR.Frontend.Emit
import CIR.Frontend.Link

/-!
  `cir2lean INPUT.cir LeanNamespace OUTPUT.lean`

  Parses ClangIR text (as printed by
  `clang++ -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering`)
  and writes a Lean file defining the module as a `CIR.Module` value.
-/

open CIR CIR.Frontend

def usage : String :=
  "usage: cir2lean INPUT.cir LeanNamespace OUTPUT.lean\n" ++
  "       cir2lean --modular INPUT.cir LeanNamespace OUTPUT_ROOT\n" ++
  "       cir2lean --link LeanNamespace OUTPUT_ROOT UNIT1.cir UNIT2.cir ...\n" ++
  "         (link translation units into one module, written as with --modular;\n" ++
  "          internal symbols of a unit are renamed <unit>$<symbol>, anonymous\n" ++
  "          records anon.<12 hex> after the named record member holding them,\n" ++
  "          else after their structure and member names)\n" ++
  "         (one module per function under OUTPUT_ROOT/<namespace path>/F/, records and\n" ++
  "          globals in <namespace>.Types, module and ctx in <namespace>, and\n" ++
  "          <namespace path>/manifest.json)"

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, ns, output] =>
    let m ← try loadModule input
      catch e =>
        IO.eprintln s!"{input}: {e}"
        return 1
    let src := emitModule ns m input
    IO.FS.writeFile output src
    let withBody := (m.funcs.filter (·.body.isSome)).length
    let models := (m.funcs.filter (·.model.isSome)).length
    IO.println s!"{input}: {m.funcs.length} funcs ({withBody} with body, {models} modelled), {m.records.length} records, {m.globals.length} globals, {countOps m} ops"
    let unk := unknownOps m
    if !unk.isEmpty then
      IO.println s!"  unknown ops: {", ".intercalate (unk.map fun (n, k) => s!"{n}×{k}")}"
    return 0
  | ["--modular", input, ns, root] =>
    let m ← try loadModule input
      catch e =>
        IO.eprintln s!"{input}: {e}"
        return 1
    let m := contentNamedLiterals m
    let (files, manifest) := emitModular ns m input
    for (rel, src) in files do
      let p := System.FilePath.mk root / rel
      if let some d := p.parent then IO.FS.createDirAll d
      IO.FS.writeFile p src
    IO.FS.writeFile (System.FilePath.mk root / (ns.replace "." "/") / "manifest.json") manifest
    IO.println s!"{input}: {m.funcs.length} function modules, {m.records.length} records, {m.globals.length} globals"
    return 0
  | "--link" :: ns :: root :: inputs@(_ :: _) =>
    let mut units : Array (String × Module) := #[]
    let mut tags : Std.HashSet String := {}
    for inp in inputs do
      let (m, names) ← try loadModuleNames inp
        catch e =>
          IO.eprintln s!"{inp}: {e}"
          return 1
      -- a unit with anonymous records is parsed again with them named after what identifies them
      let ren := anonContentNames m names
      let m ← if ren.isEmpty then pure m else
        try loadModule inp (recRename := ren)
        catch e =>
          IO.eprintln s!"{inp}: {e}"
          return 1
      let stem := (System.FilePath.mk inp).fileStem.getD "unit"
      let base := String.ofList (stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
      let mut tag := base
      let mut k := 1
      while tags.contains tag do
        k := k + 1
        tag := s!"{base}_{k}"
      tags := tags.insert tag
      units := units.push (tag, contentNamedLiterals m)
    match linkUnits ns units.toList with
    | .error e =>
      IO.eprintln s!"link: {e}"
      return 1
    | .ok (merged, warnings) =>
      for w in warnings do IO.eprintln s!"link: warning: {w}"
      let (files, manifest) := emitModular ns merged (" ".intercalate inputs)
      for (rel, src) in files do
        let p := System.FilePath.mk root / rel
        if let some d := p.parent then IO.FS.createDirAll d
        IO.FS.writeFile p src
      IO.FS.writeFile (System.FilePath.mk root / (ns.replace "." "/") / "manifest.json") manifest
      IO.println s!"linked {units.size} units: {merged.funcs.length} functions ({(merged.funcs.filter (·.body.isSome)).length} with body), {merged.records.length} records, {merged.globals.length} globals"
      return 0
  | _ =>
    IO.eprintln usage
    return 2
