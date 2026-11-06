/-
  Jimple/UnicodeImport.lean

  `unicode_tables "data/unidata.txt"` reads the Unicode character data of the JDK (dumped by
  `data/UniDump.java` from JDK 17's `java.lang.Character` and `String.toUpperCase`/`toLowerCase`)
  and defines the tables of `Jimple/Unicode.lean` as literal arrays, so that lookups evaluate in
  compiled code and in the kernel alike.
-/
import Lean.Elab.Command

namespace Jimple.UnicodeImport

open Lean Elab Command

private def natArrayExpr (xs : Array Nat) : Lean.Expr :=
  let l := xs.toList.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Nat) (mkNatLit x) acc)
    (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat))
  mkApp2 (mkConst ``List.toArray [.zero]) (mkConst ``Nat) l

private def addTable (n : Name) (value : Lean.Expr) (size : Nat) : CoreM Unit := do
  let depth := 32 * size + 2048
  let opts := (maxRecDepth.set (← getOptions) depth).setBool `compiler.extract_closed false
  withOptions (fun _ => opts) <| withAtLeastMaxRecDepth depth <|
    withReader (fun ctx => { ctx with maxHeartbeats := 0 }) do
      addAndCompile <| .defnDecl {
        name := n, levelParams := [], type := mkApp (mkConst ``Array [.zero]) (mkConst ``Nat),
        value, hints := .abbrev, safety := .safe }

syntax (name := unicodeTables) "unicode_tables " str : command

@[command_elab unicodeTables]
def elabUnicodeTables : CommandElab := fun stx => do
  let `(unicode_tables $path:str) := stx | throwUnsupportedSyntax
  let p : System.FilePath := path.getString
  let p ← if p.isAbsolute then pure p else pure ((← IO.currentDir) / p)
  let src ← IO.FS.readFile p
  let mut runStart : Array Nat := #[]
  let mut runProp : Array Nat := #[]
  let mut tbl : Std.HashMap String (Array Nat × Array Nat) := {}
  let mut special : Array Nat := #[]   -- flattened: kind (0 upper, 1 lower), char, length, units…
  for line in src.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws with
    | ["R", a, _, t, f] => runStart := runStart.push a.toNat!; runProp := runProp.push (t.toNat! * 256 + f.toNat!)
    | [k, a, b] =>
      let (ks, vs) := tbl.getD k (#[], #[])
      -- numeric values are stored plus 2 (`getNumericValue` answers -2 for non-integers)
      let v := if k == "N" then (b.toInt?.get! + 2).toNat else b.toNat!
      tbl := tbl.insert k (ks.push a.toNat!, vs.push v)
    | k :: c :: units =>
      if k == "SU" || k == "SL" then
        special := special ++ #[if k == "SU" then 0 else 1, c.toNat!, units.length] ++ (units.map (·.toNat!)).toArray
    | _ => pure ()
  let ns := (← getCurrNamespace) ++ `Unicode
  liftCoreM do
    addTable (ns ++ `runStarts) (natArrayExpr runStart) runStart.size
    addTable (ns ++ `runProps) (natArrayExpr runProp) runProp.size
    addTable (ns ++ `special) (natArrayExpr special) special.size
    for (k, nm) in [("U", "upper"), ("L", "lower"), ("T", "title"), ("N", "numeric"), ("D", "digit")] do
      let (ks, vs) := tbl.getD k (#[], #[])
      addTable (ns ++ Name.mkSimple (nm ++ "Keys")) (natArrayExpr ks) ks.size
      addTable (ns ++ Name.mkSimple (nm ++ "Vals")) (natArrayExpr vs) vs.size

end Jimple.UnicodeImport
