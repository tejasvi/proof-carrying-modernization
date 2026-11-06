import EquivLean.Bridge.Cobol.Records
import Cobol.Target.Codepage
import Aeneas

/-!
# COBOL records as Rust structs (Charon + Aeneas)

The Rust translations hold a record of schema `s` (`EquivLean.Cobol.Rec.Schema`) in a struct
`s.tname` with one field per elementary item, named `f.rname`: an `i64` holding the scaled value of
a numeric field, a `[u8; n]` holding the CP037-decoded characters of an alphanumeric field as
Latin-1 bytes (CP037 maps every byte to a code point in `0 ..= 255`).

`rust_record_vals F : S from "p.ir.json" record "R"` defines `F : S → List FVal`, the field values
of a value of the Aeneas struct `S`, in the order of the schema of `R` (each alphanumeric field
mapped back to EBCDIC bytes).  It reads the schema from the IR as `cobol_schema` does and fails if
a struct field is missing or has the wrong type: the struct is checked against the naming rule.
A DISPLAY line is a `Vec<u8>` of the CP037-decoded characters (`rustLine`).
-/

open Aeneas Aeneas.Std Lean Elab Command

namespace EquivLean.Cobol.Rec

/-- The EBCDIC byte of a Latin-1 code point (CP037 is a bijection on `0 ..= 255`). -/
def ebcdicOfLatin1 (u : Nat) : UInt8 :=
  (_root_.Cobol.Codepage.cp037Byte (Char.ofNat u)).getD 0

/-- The Latin-1 code point of an EBCDIC byte. -/
def latin1OfEbcdic (b : UInt8) : Nat := (_root_.Cobol.Codepage.cp037Char b).toNat

/-- The Rust bytes (`Vec<u8>`) of a DISPLAY line (EBCDIC bytes). -/
def rustLine (bs : List UInt8) : List Nat := bs.map latin1OfEbcdic

/-- `rust_record_vals F : S from "p.ir.json" record "R"` (see the module doc). -/
elab "rust_record_vals " fn:ident " : " sty:ident " from " path:str " record " rec:str : command => do
  let fileName ← liftCoreM getFileName
  let dir := (System.FilePath.mk fileName).parent.getD "."
  let p := dir / path.getString
  let txt ← IO.FS.readFile p
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "JSON parse error in {p}: {e}"
  let sp ← match _root_.Cobol.surfaceOfJson j with
    | .ok sp => pure sp
    | .error e => throwError "{p}: {e}"
  let s ← match schemaOf sp rec.getString with
    | .ok s => pure s
    | .error e => throwError "{p}: {e}"
  let env ← getEnv
  let some sName := (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo sty) |> some
    | throwError "unknown struct {sty}"
  let some info := getStructureInfo? env sName
    | throwError "{sName} is not a structure"
  let fieldNames := info.fieldNames.map (·.toString)
  let c := mkIdent `c
  let mut elems : Array Term := #[]
  for f in s.fields do
    unless fieldNames.contains f.rname do
      throwError "{sName} has no field {f.rname} (COBOL {f.cname}); fields: {fieldNames}"
    -- `c.<field>`, then for an item under OCCURS its element at each index (an `[T; k]` is an
    -- Aeneas `Array T k` holding a list); then `.val`: the value (`Int` for `i64`, the `List U8`
    -- of a `[u8; n]`)
    let mut elem : Term := mkIdent (Name.mkStr `c f.rname)
    for k in f.idx do
      let kk := Syntax.mkNumLit (toString k)
      elem ← `(($elem).val.getD $kk default)
    let projVal ← `(($elem).val)
    match f.desc.kind with
    | .num _ => elems := elems.push (← `(EquivLean.Cobol.Rec.FVal.num $projVal))
    | .alnum _ =>
      elems := elems.push (← `(EquivLean.Cobol.Rec.FVal.str
        ($projVal |>.map fun u => EquivLean.Cobol.Rec.ebcdicOfLatin1 u.val)))
    | _ => throwError "field {f.cname}: only numeric and alphanumeric items are supported"
  let rnames := s.fields.foldl (fun (acc : List String) f => if acc.contains f.rname then acc else acc ++ [f.rname]) []
  if fieldNames.size != rnames.length then
    throwError "{sName} has {fieldNames.size} fields, the record {s.cname} has {rnames.length}"
  let tyId := mkIdent sName
  elabCommand (← `(command|
    def $fn:ident ($c : $tyId) : List EquivLean.Cobol.Rec.FVal := [$elems,*]))

end EquivLean.Cobol.Rec
