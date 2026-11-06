import CIR.Frontend.Emit
import CIR.Frontend.Varargs

/-!
  Linking translation units (`cir2lean --link`).

  Each unit is a module parsed from its own `.cir` file. The linked module
  has every function, global and record once:
  * symbols with internal linkage (`static` functions and globals, string
    literals) stay local to their unit: they are renamed `<unit>$<sym>`, in
    their declarations and in every reference of that unit (calls, global
    addresses, vtables, global initializers);
  * an external symbol defined in one unit and declared in others resolves to
    the definition (a body, or else a library model); an alias defines its
    symbol with the body of the function it names (`resolveAliases`, when the
    unit is loaded), so a constructor that another unit calls by its
    complete-object name (C1) runs the base-object one (C2), and a global
    alias names its target's object, in the other units' references too
    (`resolveAliases` again on the linked module);
  * the same definition in several units (inline functions and templates,
    instantiated in each unit) is kept once; different definitions of one
    symbol are an error, as are different layouts of one record.
  * anonymous records, which clang numbers per unit (`anon.N`), are named after
    what identifies them (`anonContentNames`) when the units are loaded: the
    member of a named record that holds one, else its structure and its members'
    names; equal ones in two units become one record and different ones stay
    apart, whatever the order of the units, so the error above concerns named
    records.
-/

namespace CIR.Frontend

/-- 12 hexadecimal digits of a hash. -/
def hex12 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList ((List.replicate (16 - s.length) '0' ++ s.toList).take 12)

/-- String-literal globals (clang's internal `.str`, `.str.N`) renamed after
their type and contents, `.str.<12 hex>` (with `.k` for the `k`-th
duplicate), in their declarations and every reference. Adding a literal to
a file renumbers clang's names of the later literals, not these, so the
module text of an unchanged function stays the same (`--modular`,
`--link`). -/
def contentNamedLiterals (m : Module) : Module := Id.run do
  let mut map : Std.HashMap String String := {}
  let mut used : Std.HashMap String Nat := {}
  for g in m.globals do
    if g.internal && (g.sym == ".str" || g.sym.startsWith ".str.") then
      let key := Emit.ty g.ty ++ "|" ++ (match g.init with | some c => Emit.const c | none => "")
      let base := ".str." ++ hex12 (hash key)
      let k := used.getD base 0
      used := used.insert base (k + 1)
      map := map.insert g.sym (if k == 0 then base else base ++ "." ++ toString k)
  if map.isEmpty then return m
  let f : String → String := fun s => map.getD s s
  return { m with
    globals := m.globals.map fun g => { g with sym := f g.sym, init := g.init.map (renameConst f) }
    funcs := m.funcs.map fun fd => { fd with body := fd.body.map (renameRegion f) } }

/-- An anonymous record: clang's `anon.N` (numbered per translation unit), or the parser's
`anon_struct.N` / `anon_union.N` (a record type printed without a name). -/
def isAnonRecordName (n : String) : Bool :=
  let after (p : String) : Bool :=
    n.startsWith p && (let d := (n.drop p.length).toString; !d.isEmpty && d.all Char.isDigit)
  after "anon." || after "anon_struct." || after "anon_union."

mutual
/-- A type's part of an anonymous record's key (`anonContentNames`): a named record stands for
itself, an anonymous one for its own key (for its name in the unit when it is reached again
inside itself). With `withNames` the key also holds the members' names. -/
partial def anonTyKey (recs : Std.HashMap String RecordDecl)
    (names : Std.HashMap String (Std.HashMap Nat String)) (withNames : Bool) (busy : List String) :
    Ty → String
  | .record n =>
    if isAnonRecordName n then
      if busy.contains n then "<" ++ n ++ ">"
      else match recs[n]? with
        | some r => "{" ++ anonRecKey recs names withNames (n :: busy) r ++ "}"
        | none => "<" ++ n ++ ">"
    else Emit.ty (.record n)
  | .ptr t => "ptr(" ++ anonTyKey recs names withNames busy t ++ ")"
  | .array t k => s!"array({anonTyKey recs names withNames busy t}, {k})"
  | .func ps r v =>
    "func(" ++ ", ".intercalate (ps.map (anonTyKey recs names withNames busy)) ++ ") " ++
      anonTyKey recs names withNames busy r ++ (if v then " ..." else "")
  | t => Emit.ty t
/-- The key of a record: its kind, packing, members (kind, with `withNames` the name, and type)
and tail padding. A member whose name no `cir.get_member` gives is `?`. -/
partial def anonRecKey (recs : Std.HashMap String RecordDecl)
    (names : Std.HashMap String (Std.HashMap Nat String)) (withNames : Bool) (busy : List String)
    (r : RecordDecl) : String :=
  let kind := match r.kind with | .struct => "struct" | .class => "class" | .union => "union"
  let nm := names.getD r.name {}
  let mem (mi : (MemberKind × Ty) × Nat) : String :=
    (match mi.1.1 with | .data => "data " | .pad => "pad " | .empty => "empty " | .bitfield => "bitfield ") ++
      (if withNames then (match nm[mi.2]? with | some x => x.quote ++ " " | none => "? ") else "") ++
      anonTyKey recs names withNames busy mi.1.2
  s!"{kind} packed={r.packed} complete={r.complete} " ++ "; ".intercalate (r.members.zipIdx.map mem) ++
    " | padding " ++ "; ".intercalate (r.padding.map (anonTyKey recs names withNames busy))
end

/-- The anonymous record a member of type `t` holds by value: `t`, or the element type of the
array `t`. -/
def anonHeld : Ty → Option String
  | .array t _ => anonHeld t
  | .record a => if isAnonRecordName a then some a else none
  | _ => none

/-- The anonymous records that a named record holds by value (as a member or an array's elements,
inside other anonymous members too), each with the least path that reaches it,
`<named record>/<member index>/...` (by string order). -/
def anonContainers (recs : Std.HashMap String RecordDecl) (rs : List RecordDecl) :
    Std.HashMap String String := Id.run do
  let mut best : Std.HashMap String String := {}
  for r in rs do
    if !isAnonRecordName r.name then
      -- depth-first over the anonymous records held by value (they cannot hold themselves)
      let mut stack : List (String × RecordDecl × Nat) := [(r.name, r, 0)]
      while !stack.isEmpty do
        match stack with
        | (path, q, d) :: rest =>
          stack := rest
          for (mt, i) in q.members.zipIdx do
            if let some a := anonHeld mt.2 then
              let p := path ++ "/" ++ toString i
              if (best[a]?.all fun b => decide (p < b)) then best := best.insert a p
              if let some qa := recs[a]? then
                if d < 64 then stack := (p, qa, d + 1) :: stack
        | [] => pure ()
  return best

/-- The anonymous records of a unit named after what identifies them: `anon.<12 hex>` of a key,
with `.k` for the `k`-th later record of the same key in the unit, which stays a type of its own.
A record that a named record holds by value is that member of that type (C11 6.2.7p1, the ODR):
its key is the least such path and its structure (`anonContainers`, `anonRecKey`). Any other one
is its structure and its members' names, as far as the unit's `cir.get_member` operations give
them (a name they do not give is `?`), since two anonymous types of two units are compatible only
if their members have the same names (C11 6.2.7p1). Clang numbers anonymous records per
translation unit, so the `anon.0` of two units may be different types, and one type, std::string's
union, may be `anon.0` in one unit and `anon.9` in another. With these names an anonymous type of
two units is one record of the linked module, and different ones stay apart, whatever the order of
the units. `cir2lean --link` parses a unit that has anonymous records again with them
(`parseModule`'s `recRename`). -/
def anonContentNames (m : Module) (names : Std.HashMap String (Std.HashMap Nat String)) :
    Std.HashMap String String := Id.run do
  let recs : Std.HashMap String RecordDecl := m.records.foldl (fun acc r => acc.insert r.name r) {}
  let cont := anonContainers recs m.records
  let mut map : Std.HashMap String String := {}
  let mut used : Std.HashMap String Nat := {}
  for r in m.records do
    if isAnonRecordName r.name && !map.contains r.name then
      let key := match cont[r.name]? with
        | some path => "in " ++ path ++ ": " ++ anonRecKey recs names false [r.name] r
        | none => anonRecKey recs names true [r.name] r
      let base := "anon." ++ hex12 (hash key)
      let k := used.getD base 0
      used := used.insert base (k + 1)
      map := map.insert r.name (if k == 0 then base else base ++ "." ++ toString k)
  return map

/-- Link the units `(tag, module)`; `tag` prefixes the unit's internal
symbols. Also returns warnings: external functions defined in several units
whose definitions differ only after the renaming (inline functions that use
a unit's string literals); the first definition is kept. -/
def linkUnits (name : String) (units : List (String × Module)) :
    Except String (Module × List String) := do
  let mut warnings : Array String := #[]
  let mut funcs : Array FuncDecl := #[]
  let mut fidx : Std.HashMap String Nat := {}
  let mut globals : Array GlobalDecl := #[]
  let mut gidx : Std.HashMap String Nat := {}
  let mut records : Array RecordDecl := #[]
  let mut ridx : Std.HashMap String Nat := {}
  let ptrBytes := match units with
    | (_, M) :: _ => M.ptrBytes
    | [] => 8
  -- constructors and destructors of all units, in link order
  let mut ctors : Array (String × Nat) := #[]
  let mut dtors : Array (String × Nat) := #[]
  for (tag, M) in units do
    if M.ptrBytes != ptrBytes then
      throw s!"unit {tag}: {M.ptrBytes}-byte pointers, the first unit has {ptrBytes}"
    let internal : Std.HashSet String := Std.HashSet.ofList
      ((M.funcs.filter (·.internal)).map (·.sym) ++ (M.globals.filter (·.internal)).map (·.sym))
    let f : String → String := fun s => if internal.contains s then tag ++ "$" ++ s else s
    ctors := ctors ++ M.ctors.map fun (s, p) => (f s, p)
    dtors := dtors ++ M.dtors.map fun (s, p) => (f s, p)
    for r in M.records do
      match ridx[r.name]? with
      | none =>
        ridx := ridx.insert r.name records.size
        records := records.push r
      | some i =>
        let old := records[i]!
        if !old.complete && r.complete then records := records.set! i r
        else if old.complete && r.complete && Emit.record "x" old != Emit.record "x" r then
          throw s!"record {r.name}: different layouts in two units"
    for g in M.globals do
      let g := { g with sym := f g.sym, init := g.init.map (renameConst f), alias := g.alias.map f }
      match gidx[g.sym]? with
      | none =>
        gidx := gidx.insert g.sym globals.size
        globals := globals.push g
      | some i =>
        let old := globals[i]!
        -- a declaration yields to a definition, or to an alias (another name of a definition)
        if old.init.isNone && old.alias.isNone && (g.init.isSome || g.alias.isSome) then globals := globals.set! i g
        else if old.init.isSome && g.init.isSome && Emit.global "x" old != Emit.global "x" g then
          throw s!"global {g.sym}: defined differently in two units"
    for fd in M.funcs do
      let fd := { fd with sym := f fd.sym, body := fd.body.map (renameRegion f), alias := fd.alias.map f }
      match fidx[fd.sym]? with
      | none =>
        fidx := fidx.insert fd.sym funcs.size
        funcs := funcs.push fd
      | some i =>
        let old := funcs[i]!
        if old.body.isSome && fd.body.isSome then
          if Emit.func "x" { old with ssaNames := [] } != Emit.func "x" { fd with ssaNames := [] } then
            warnings := warnings.push s!"function {fd.sym}: definitions differ between units; the first is kept"
        else if old.body.isNone && (fd.body.isSome || (old.model.isNone && fd.model.isSome)) then
          funcs := funcs.set! i fd
  let linked : Module :=
    { name := name, records := records.toList, globals := globals.toList, funcs := funcs.toList,
      ptrBytes := ptrBytes, ctors := ctors.toList, dtors := dtors.toList,
      -- C++ pointer arithmetic on null pointers only when every unit is C++
      cxx := !units.isEmpty && units.all (·.2.cxx) }
  -- another unit's references to an alias name its target too
  let linked ← resolveAliases linked
  -- calls into another unit's variadic functions get their `va_box`es now; a by-value parameter
  -- or a result whose class only another unit shows non-trivial becomes the caller's object now;
  -- with a unit's `setjmp`, the other units' functions note their stores too
  return (boxVarargs (sjNotes (retObjects (objectParams linked))), warnings.toList)

end CIR.Frontend
