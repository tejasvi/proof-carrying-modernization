/-
# Hierarchical data division and storage layout

The data division is kept as the record hierarchy the extractor produces from the resolved
AST and copybooks (`Item` trees: 01 records, groups, elementary items, `OCCURS`,
`REDEFINES`, `VALUE`, level-88 conditions).  `layout` assigns byte offsets with IBM rules:

* elementary sizes from `PICTURE` and `USAGE` (`NumFmt.byteLen`);
* a group is the concatenation of its children; `OCCURS n` multiplies by `n`;
* a `REDEFINES` item starts at the offset of the item it redefines; storage after the
  redefinition continues after the larger of the two;
* `SYNCHRONIZED` binary items are aligned to their size, relative to the start of their record
  or, inside a table, of the table's occurrence (the front end refuses `SYNCHRONIZED` items
  inside a group with `OCCURS`: where the slack bytes of such tables go is not modelled);
* 01 / 77 levels are placed one after the other (a level-01 `REDEFINES` overlays).

The result maps every item id to its descriptor (first occurrence) and to the strides and
bounds of the enclosing tables, which is what the resolver puts into `DataRef`s.
-/
import Cobol.Sem.Arith

namespace Cobol

/-- Normalized `PICTURE` of an elementary item. -/
inductive Pic where
  /-- `X(n)` / `A(n)`. -/
  | alnum (len : Nat)
  /-- `S9(i)V9(d)`, `9(i)PPP`, `VPP9(d)`: `digits` positions, `scale` decimal scale. -/
  | num (digits : Nat) (scale : Int) (signed : Bool)
  /-- Numeric-edited picture. -/
  | numEdited (pic : List ESym)
  deriving DecidableEq, Repr, Inhabited

/-- A `VALUE` clause. -/
inductive Value where
  | num (v : Int) (scale : Int := 0)
  | alnum (bs : List UInt8)
  | fig (f : Figurative)
  deriving DecidableEq, Repr, Inhabited

/-- A level-88 value: single value or `THRU` range. -/
structure CondVal where
  lo : Value
  hi : Option Value := none
  deriving DecidableEq, Repr, Inhabited

/-- A data item of the data division (after copybook expansion). -/
structure Item where
  id : Nat
  level : Nat
  name : String
  /-- `none` for a group item. -/
  pic : Option Pic := none
  usage : Usage := .display
  /-- `OCCURS n` (`1` = not a table). -/
  occurs : Nat := 1
  /-- Id of the redefined item (a preceding sibling). -/
  redefines : Option Nat := none
  value : Option Value := none
  just : Bool := false
  signSep : Bool := false
  signLead : Bool := false
  bwz : Bool := false
  sync : Bool := false
  /-- Level-88 condition names: `(id, name, values)`. -/
  conds : List (Nat × String × List CondVal) := []
  children : List Item := []
  deriving Repr, Inhabited

/-- Placement of one item. -/
structure Placed where
  id : Nat
  name : String
  desc : FieldDesc
  /-- `(stride, occurs)` of each enclosing table, outermost first (including the item's own
  `OCCURS`). -/
  dims : List (Nat × Nat)
  value : Option Value
  /-- Inside the scope of a `REDEFINES` (not initialized by `VALUE` / `INITIALIZE`). -/
  redef : Bool
  deriving Repr, Inhabited

/-- Numeric format of an elementary numeric item. -/
def Item.numFmt (it : Item) : Option NumFmt :=
  match it.pic with
  | some (.num d s sg) =>
    some { digits := d, scale := s, signed := sg, usage := it.usage,
           signSep := it.signSep, signLead := it.signLead }
  | _ => none

/-- Kind and byte length of an elementary item. -/
def Item.elemKind (c : Config) (it : Item) : Option (FieldKind × Nat) :=
  match it.pic with
  | some (.alnum n) => some (.alnum it.just, n)
  | some (.num d s sg) =>
    let f : NumFmt := { digits := d, scale := s, signed := sg, usage := it.usage,
                        signSep := it.signSep, signLead := it.signLead }
    some (.num f, f.byteLen c)
  | some (.numEdited p) => some (.numEdited p it.bwz, Edit.picWidth p)
  | none => none

/-- Alignment of a `SYNCHRONIZED` item (its binary size, else 1). -/
def Item.align (c : Config) (it : Item) : Nat :=
  match it.pic, it.usage with
  | some (.num d _ _), .binary | some (.num d _ _), .comp5 => if it.sync then c.binBytes d else 1
  | _, _ => 1

/-- Round `off` up to a multiple of `a` (relative to `base`). -/
def alignUp (base off a : Nat) : Nat :=
  if a ≤ 1 then off else base + (off - base + a - 1) / a * a

/-- Offset, relative to its parent, of an item that starts no earlier than `off` and must be
aligned to `a` from its alignment base, the parent being `rel` bytes from that base. -/
def alignFrom (rel off a : Nat) : Nat := alignUp 0 (rel + off) a - rel

/-- Alignment base offset of the children of an item that is `rel` bytes from its own base: the
occurrence of a table is the base of its children. -/
def Item.childRel (it : Item) (rel : Nat) : Nat := if it.occurs > 1 then 0 else rel

mutual
/-- Size of one occurrence of an item `rel` bytes from its alignment base (its record, or the
occurrence of the innermost enclosing table). -/
def Item.size (c : Config) (rel : Nat) : Item → Nat
  | it@{ pic := some _, .. } => ((it.elemKind c).map (·.2)).getD 0
  | it@{ pic := none, children := cs, .. } => Item.sizeList c (it.childRel rel) cs 0 []

/-- Size of a list of siblings whose parent is `rel` bytes from its alignment base; `placed`
remembers `(id, start, length)` of placed siblings so that a `REDEFINES` restarts at the
redefined item. `off` is the running offset. -/
def Item.sizeList (c : Config) (rel : Nat) : List Item → Nat → List (Nat × Nat × Nat) → Nat
  | [], off, _ => off
  | it :: rest, off, placed =>
    match it.redefines with
    | some j =>
      match placed.lookup j with
      | some (start, len) =>
        let sz := Item.size c (rel + start) it * it.occurs
        Item.sizeList c rel rest (max off (start + max len sz)) placed
      | none =>
        let sz := Item.size c (rel + off) it * it.occurs
        Item.sizeList c rel rest (off + sz) ((it.id, off, sz) :: placed)
    | none =>
      let start := alignFrom rel off (it.align c)
      let sz := Item.size c (rel + start) it * it.occurs
      Item.sizeList c rel rest (start + sz) ((it.id, start, sz) :: placed)
end

mutual
/-- Place an item at `off`, `rel` bytes from its alignment base; `dims` = enclosing tables;
`redef` = inside a `REDEFINES`. -/
def Item.place (c : Config) (rel : Nat) : Item → Nat → List (Nat × Nat) → Bool → List Placed
  | it@{ children := cs, .. }, off, dims, redef =>
  let sz := Item.size c rel it
  let dims' := if it.occurs > 1 then dims ++ [(sz, it.occurs)] else dims
  let redef' := redef || it.redefines.isSome
  let kind := ((it.elemKind c).map (·.1)).getD .group
  let me : Placed := { id := it.id, name := it.name, desc := { off, len := sz, kind },
                       dims := dims', value := it.value, redef := redef' }
  me :: Item.placeList c (it.childRel rel) cs off 0 [] dims' redef'

/-- Place siblings; `base` = start of the parent, `rel` = its distance from its alignment base,
`off` = offset relative to `base`. -/
def Item.placeList (c : Config) (rel : Nat) : List Item → Nat → Nat → List (Nat × Nat × Nat) →
    List (Nat × Nat) → Bool → List Placed
  | [], _, _, _, _, _ => []
  | it :: rest, base, off, placed, dims, redef =>
    match it.redefines with
    | some j =>
      match placed.lookup j with
      | some (start, len) =>
        let sz := Item.size c (rel + start) it * it.occurs
        Item.place c (rel + start) it (base + start) dims redef ++
          Item.placeList c rel rest base (max off (start + max len sz)) placed dims redef
      | none =>
        let sz := Item.size c (rel + off) it * it.occurs
        Item.place c (rel + off) it (base + off) dims redef ++
          Item.placeList c rel rest base (off + sz) ((it.id, off, sz) :: placed) dims redef
    | none =>
      let start := alignFrom rel off (it.align c)
      let sz := Item.size c (rel + start) it * it.occurs
      Item.place c (rel + start) it (base + start) dims redef ++
        Item.placeList c rel rest base (start + sz) ((it.id, start, sz) :: placed) dims redef
end

/-- Size of the 01 / 77 items placed one after the other; each is its own alignment base. -/
def sizeRecords (c : Config) : List Item → Nat → List (Nat × Nat × Nat) → Nat
  | [], off, _ => off
  | it :: rest, off, placed =>
    let sz := Item.size c 0 it * it.occurs
    match it.redefines.bind (fun j => placed.lookup j) with
    | some (start, len) => sizeRecords c rest (max off (start + max len sz)) placed
    | none => sizeRecords c rest (off + sz) ((it.id, off, sz) :: placed)

/-- Place the 01 / 77 items one after the other (a level-01 `REDEFINES` overlays the item it
redefines); each is its own alignment base. -/
def placeRecords (c : Config) : List Item → Nat → List (Nat × Nat × Nat) → List Placed
  | [], _, _ => []
  | it :: rest, off, placed =>
    let sz := Item.size c 0 it * it.occurs
    match it.redefines.bind (fun j => placed.lookup j) with
    | some (start, len) =>
      Item.place c 0 it start [] false ++ placeRecords c rest (max off (start + max len sz)) placed
    | none => Item.place c 0 it off [] false ++ placeRecords c rest (off + sz) ((it.id, off, sz) :: placed)

/-- Layout of a data division (01 / 77 items in order). -/
structure Layout where
  items : List Placed
  size : Nat
  deriving Repr, Inhabited

/-- Compute the layout of a data division. -/
def layout (c : Config) (records : List Item) : Layout :=
  { items := placeRecords c records 0 []
    size := sizeRecords c records 0 [] }

/-- Placement of item `id`. -/
def Layout.find? (L : Layout) (id : Nat) : Option Placed := L.items.find? (·.id == id)

/-! ## Initial storage from `VALUE` clauses -/

/-- Bytes of a `VALUE` for an item of kind `k` and length `len`. -/
def valueBytes (c : Config) (k : FieldKind) (len : Nat) : Value → Option (List UInt8)
  | .num v s =>
    match k with
    | .num f => some (encodeNum c f (Sem.fitNum c f (rescale .truncation v s f.scale)).2)
    | .numEdited p bwz => Edit.edit c p bwz v s
    | _ => none
  | .alnum bs => some (Sem.padRight c bs len)
  | .fig f =>
    match f, k with
    | .zero, .num nf => some (encodeNum c nf 0)
    | _, _ => some (Sem.fillPattern (Sem.figBytes c f) len)

/-- All offsets of an item (every occurrence of every enclosing table). -/
def occOffsets (off : Nat) : List (Nat × Nat) → List Nat
  | [] => [off]
  | (stride, n) :: rest => (List.range n).flatMap (fun i => occOffsets (off + i * stride) rest)

/-- `VALUE`-clause writes `(offset, bytes)`, outer items first (so inner `VALUE`s win). -/
def Layout.inits (c : Config) (L : Layout) : List (Nat × List UInt8) :=
  L.items.flatMap (fun p =>
    if p.redef then [] else
    match p.value with
    | none => []
    | some v =>
      match valueBytes c p.desc.kind p.desc.len v with
      | none => []
      | some bs => (occOffsets p.desc.off p.dims).map (·, bs))

end Cobol
