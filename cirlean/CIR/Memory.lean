import CIR.Value
import Lean.Data.PersistentHashMap

/-!
  Memory: a map from block ids to blocks of structured values.

  * `cir.alloca` allocates a `stack` block; when the region that executed the
    alloca exits, the block dies (lexical lifetime, `AutomaticAllocationScope`).
  * A `readonly` block (a constant global, a string literal, a const-qualified
    local object) accepts only writes that fill positions whose value is still
    indeterminate (`Val.initBy`): the initialization of a const local (C11
    6.7.3p6). A region exit ends stack blocks only, so a const local
    (`Op.allocaConst`) outlives its region: an access through a pointer to it
    after its region has exited is not detected.
  * Every access checks that the block is alive, so a pointer that outlives
    its scope (or a deleted heap object) is caught as undefined behaviour.
  * Block ids are never reused.
-/

namespace CIR

/-- Point update of a function. Kept as an opaque constructor during symbolic
execution (only applications are unfolded), so states stay compact. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

inductive BlockKind where
  | stack | heap | global | readonly | exn
  /-- A global the module only declares (defined in another translation unit or a library): its
  block is not alive, so no access is defined (`Module.initMem`; a constant one has a `readonly`
  block that is not alive). -/
  | external
  deriving Repr, DecidableEq, Inhabited

structure MemBlock where
  kind  : BlockKind
  alive : Bool
  ty    : Ty
  val   : Val
  deriving Inhabited

structure Mem where
  blocks : Nat → Option MemBlock
  /-- Next fresh block id; every existing block id is below it. -/
  next   : Nat

/-- The blocks after a region exit: the stack blocks allocated while the
region ran (ids in `[lo, hi)`) are removed. Removal is observationally the
same as marking them dead, since every access requires a live block and
block ids are never reused. -/
def killRange (lo hi : Nat) (bs : Nat → Option MemBlock) : Nat → Option MemBlock :=
  fun b => if lo ≤ b ∧ b < hi then
      (match bs b with
       | some blk => if blk.kind = .stack then none else some blk
       | none => none)
    else bs b

/-! ### Runtime representation

Compiled code (the `cirrun` and `cirscan` interpreters) does not build `Mem.blocks` as the chain
of `upd` / `killRange` closures that the definitions below describe: a lookup in that chain walks
every layer added since the block's last update, so a loop reading a block it does not write ran
in quadratic time. `Mem.empty`, `Mem.setBlock`, `Mem.alloc`, `Mem.allocAs`, `Mem.endScope` and
`Std.fresh` are implemented (`@[implemented_by]`) by the operations of this section, which keep
the blocks in a persistent hash map. The run-time cell of such a memory is a `MemRT.Cell.rt`, cast
to `Mem`: its fields 0 and 1 are `Mem`'s own, `blocks` (a lookup in the map) and `next`, so the
rest of the compiled code reads it as a `Mem`; field 2 is the map, field 3 the reference chain of
the check below, field 4 the closure of field 0 again, field 5 the ids of the stack blocks, the
latest first, and a flag whether that list is complete. Invariant: when fields 0 and 4 are the same
closure (pointer-equal), field 2 holds exactly the blocks of field 0, and, under the flag, field 5
holds the id of every stack block among them. A region exit then removes the stack blocks by
popping the ids from `lo` up off that list, so it visits only the blocks it removes (without the
flag, every id in `[lo, next)`). A `Mem` built in any other way (a cell of `Mem`'s own layout, or
one whose field 0 was replaced) has its map and list built from `blocks` over `[0, next)`
(`MemRT.build`; every reachable memory is well formed, `Mem.WF`). Proofs, the kernel and symbolic
execution see the definitions only. With the environment variable
`CIR_MEMCHECK` set, every memory also carries the chain the definitions build (field 3), and every
lookup checks that the map gives the same block (pointer-equal) or none on both sides: a
divergence ends the program with exit status 97. -/

namespace MemRT

/-- The blocks by id (compiled code only). -/
abbrev Map := Lean.PersistentHashMap Nat MemBlock

/-- The run-time cell of a memory (compiled code only): `plain` is `Mem`'s own layout, `rt` the
one that the operations below build. -/
inductive Cell where
  | plain (blocks : Nat → Option MemBlock) (next : Nat)
  | rt (blocks : Nat → Option MemBlock) (next : Nat) (map : Map)
      (ref : Option (Nat → Option MemBlock)) (self : Nat → Option MemBlock) (stk : List Nat)
      (exact : Bool)

/-- The parts of a memory besides `blocks` and `next` (compiled code only): the map, the reference
chain of `CIR_MEMCHECK`, the ids of the stack blocks, the latest first, and whether that list holds
every stack block of the map. -/
structure Parts where
  map : Map
  ref : Option (Nat → Option MemBlock)
  stk : List Nat
  exact : Bool

/-- Whether `CIR_MEMCHECK` is set (read once). -/
unsafe def memcheck : Bool := unsafeBaseIO do return (← IO.getEnv "CIR_MEMCHECK").isSome

/-- The file that each divergence is also appended to, `CIR_MEMCHECK_LOG` (read once). -/
unsafe def memcheckLog : Option String := unsafeBaseIO do return (← IO.getEnv "CIR_MEMCHECK_LOG")

/-- A lookup of block `b` where the map and the reference chain differ: exit status 97. -/
@[noinline] unsafe def diverged (b : Nat) : Option MemBlock :=
  match unsafeIO (do
      let msg := s!"CIR_MEMCHECK: block {b}: the map and the reference chain differ"
      IO.eprintln msg
      if let some path := memcheckLog then
        IO.FS.withFile path .append fun h => h.putStrLn msg
      IO.Process.exit 97 : IO (Option MemBlock)) with
  | .ok r => r
  | .error _ => none

/-- The same block (the same object), or none on both sides. -/
unsafe def same : Option MemBlock → Option MemBlock → Bool
  | some x, some y => ptrAddrUnsafe x == ptrAddrUnsafe y
  | none, none => true
  | _, _ => false

/-- `Mem.blocks` of the memory with map `map` and, under `CIR_MEMCHECK`, reference chain `ref`. -/
unsafe def lookup (map : Map) (ref : Option (Nat → Option MemBlock)) (b : Nat) :
    Option MemBlock :=
  match ref with
  | none => map.find? b
  | some f =>
    let r := map.find? b
    if same r (f b) then r else diverged b

/-- The memory with parts `p` and next id `next`. -/
@[inline] unsafe def mk (p : Parts) (next : Nat) : Mem :=
  let f := lookup p.map p.ref
  unsafeCast (Cell.rt f next p.map p.ref f p.stk p.exact)

/-- The parts of `m` built from `m.blocks` over `[0, m.next)`: its map, its stack blocks, and the
reference chain `m.blocks`. -/
unsafe def build (m : Mem) : Parts :=
  let (map, stk) := (List.range m.next).foldl (fun (acc, stk) b => match m.blocks b with
      | some blk => (acc.insert b blk, if blk.kind = .stack then b :: stk else stk)
      | none => (acc, stk)) (({} : Map), ([] : List Nat))
  { map, ref := if memcheck then some m.blocks else none, stk, exact := true }

/-- The parts of `m`, its fields 2, 3 and 5 and its flag, when `mk` built its cell and field 0 is
still that cell's closure (the invariant). -/
@[inline] unsafe def own? (m : Mem) : Option Parts :=
  match (unsafeCast m : Cell) with
  | .rt f _ map ref self stk exact =>
    if ptrAddrUnsafe f == ptrAddrUnsafe self then some ⟨map, ref, stk, exact⟩ else none
  | .plain .. => none

/-- The parts of `m` (`own?`, else `build m`). -/
@[inline] unsafe def view (m : Mem) : Parts :=
  match own? m with
  | some p => p
  | none => build m

/-- `Mem.empty`. -/
unsafe def empty : Mem := mk ⟨{}, if memcheck then some (fun _ => none) else none, [], true⟩ 0

/-- `Mem.setBlock`. The list of stack blocks stays complete when the block written is no stack
block or replaces one; a stack block written where none was ends the flag. -/
unsafe def setBlock (m : Mem) (b : Nat) (blk : MemBlock) : Mem :=
  let p := view m
  let exact := p.exact && match blk.kind with
    | .stack => match p.map.find? b with
      | some old => old.kind = .stack
      | none => false
    | _ => true
  mk ⟨p.map.insert b blk, p.ref.map fun f => upd f b (some blk), p.stk, exact⟩ m.next

/-- `Mem.allocAs`: a stack block's id goes on the list of stack blocks. -/
unsafe def allocAs (m : Mem) (k : BlockKind) (alive : Bool) (ty : Ty) (v : Val) : Nat × Mem :=
  let blk : MemBlock := ⟨k, alive, ty, v⟩
  let p := view m
  let stk := match k with
    | .stack => m.next :: p.stk
    | _ => p.stk
  (m.next, mk ⟨p.map.insert m.next blk, p.ref.map fun f => upd f m.next (some blk), stk, p.exact⟩
    (m.next + 1))

/-- `Mem.alloc`. -/
unsafe def alloc (m : Mem) (k : BlockKind) (ty : Ty) (v : Val) : Nat × Mem :=
  allocAs m k true ty v

/-- `map` without the stack blocks among the ids `[b, hi)` (when the list of stack blocks is not
complete). -/
unsafe def kill (map : Map) (b hi : Nat) : Map :=
  if b < hi then
    kill (match map.find? b with
      | some blk => if blk.kind = .stack then map.erase b else map
      | none => map) (b + 1) hi
  else map

/-- `map` without the stack blocks among the ids of `stk` from `lo` up, and the rest of `stk`. -/
unsafe def killStk (map : Map) (stk : List Nat) (lo : Nat) : Map × List Nat :=
  match stk with
  | b :: rest =>
    if lo ≤ b then
      killStk (match map.find? b with
        | some blk => if blk.kind = .stack then map.erase b else map
        | none => map) rest lo
    else (map, stk)
  | [] => (map, [])

/-- `Mem.endScope`: `m` itself when no block was allocated since `lo`, or, in a cell of `mk`,
no stack block. -/
unsafe def endScope (m : Mem) (lo : Nat) : Mem :=
  if m.next ≤ lo then m else
    match own? m with
    | some p =>
      if p.exact then
        let (map', stk') := killStk p.map p.stk lo
        if ptrAddrUnsafe stk' == ptrAddrUnsafe p.stk then m
        else mk ⟨map', p.ref.map fun f => killRange lo m.next f, stk', true⟩ m.next
      else
        let map' := kill p.map lo m.next
        if ptrAddrUnsafe map' == ptrAddrUnsafe p.map then m
        else mk ⟨map', p.ref.map fun f => killRange lo m.next f, p.stk, false⟩ m.next
    | none =>
      let p := build m
      let (map', stk') := killStk p.map p.stk lo
      mk ⟨map', p.ref.map fun f => killRange lo m.next f, stk', true⟩ m.next

/-- `m` with next id `n` (`Std.fresh`): in a cell of `mk`, the same closure and parts. -/
unsafe def withNext (m : Mem) (n : Nat) : Mem :=
  match (unsafeCast m : Cell) with
  | .rt f _ map ref self stk exact =>
    if ptrAddrUnsafe f == ptrAddrUnsafe self then unsafeCast (Cell.rt f n map ref self stk exact)
    else mk (build m) n
  | .plain .. => mk (build m) n

end MemRT

namespace Mem

@[implemented_by MemRT.empty]
def empty : Mem := ⟨fun _ => none, 0⟩

instance : Inhabited Mem := ⟨empty⟩

/-- Overwrite one block. -/
@[implemented_by MemRT.setBlock]
def setBlock (m : Mem) (b : Nat) (blk : MemBlock) : Mem :=
  { m with blocks := upd m.blocks b (some blk) }

/-- Allocate a fresh live block. -/
@[implemented_by MemRT.alloc]
def alloc (m : Mem) (k : BlockKind) (ty : Ty) (v : Val) : Nat × Mem :=
  (m.next, { blocks := upd m.blocks m.next (some ⟨k, true, ty, v⟩), next := m.next + 1 })

/-- Allocate a fresh block, live or not (`Module.initMem`: a global the module only declares has
an `external` block that is not alive). -/
@[implemented_by MemRT.allocAs]
def allocAs (m : Mem) (k : BlockKind) (alive : Bool) (ty : Ty) (v : Val) : Nat × Mem :=
  (m.next, { blocks := upd m.blocks m.next (some ⟨k, alive, ty, v⟩), next := m.next + 1 })

/-- The live block `b`. -/
def live? (m : Mem) (b : Nat) : Option MemBlock :=
  match m.blocks b with
  | some blk => if blk.alive then some blk else none
  | none => none

/-- Read the value a pointer designates. -/
def read? (m : Mem) : Ptr → Option Val
  | .loc b p => match m.live? b with
    | some blk => blk.val.get? p
    | none => none
  | _ => none

/-- Write the value a pointer designates (in a read-only block only as part of
its initialization, `Val.initBy`: that of a const local). -/
def write? (m : Mem) : Ptr → Val → Option Mem
  | .loc b p, w => match m.live? b with
    | some blk =>
      if blk.kind = .readonly then
        if (blk.val.get? p).all (Val.initBy · w) then
          match blk.val.set? p w with
          | some v' => some (m.setBlock b { blk with val := v' })
          | none => none
        else none
      else match blk.val.set? p w with
        | some v' => some (m.setBlock b { blk with val := v' })
        | none => none
    | none => none
  | _, _ => none

/-- End the lifetime of the stack blocks allocated since `m.next` was `lo`. -/
@[implemented_by MemRT.endScope]
def endScope (m : Mem) (lo : Nat) : Mem :=
  { m with blocks := killRange lo m.next m.blocks }

/-- Well-formed memory: no block at or above `next`. Every reachable memory is
well formed; function specifications assume it of the initial memory. -/
def WF (m : Mem) : Prop := ∀ b, m.next ≤ b → m.blocks b = none

/-- Free a live heap block (`operator delete`). -/
def free? (m : Mem) (b : Nat) : Option Mem :=
  match m.live? b with
  | some blk => if blk.kind = .heap then some (m.setBlock b { blk with alive := false }) else none
  | none => none

end Mem

/-! ### Pointer arithmetic -/

/-- Split a path into its parent and last step. -/
def splitLast : List PathElem → Option (List PathElem × PathElem)
  | [] => none
  | [e] => some ([], e)
  | e :: e' :: es => (splitLast (e' :: es)).map fun (pre, l) => (e :: pre, l)

/-- The index of the last path step, when the pointer designates an element
of an array (`arr`) or container (`vec`), together with the parent path and
the number of elements of the parent. -/
def Mem.elemPos? (m : Mem) : Ptr → Option (Nat × List PathElem × PathElem × Nat)
  | .loc b path => match splitLast path with
    | some (pre, .idx i) => match m.read? (.loc b pre) with
      | some (.arr xs) => some (b, pre, .idx i, xs.length)
      | _ => none
    | some (pre, .vel g i) => match m.read? (.loc b pre) with
      | some (.vec g' xs) => if g = g' then some (b, pre, .vel g i, xs.length) else none
      | _ => none
    | _ => none
  | _ => none

@[reducible] def PathElem.index : PathElem → Nat
  | .idx i => i
  | .vel _ i => i
  | .byte k => k

@[reducible] def PathElem.withIndex : PathElem → Nat → PathElem
  | .idx _, j => .idx j
  | .vel g _, j => .vel g j
  | .byte _, j => .byte j

/-- `p + n` for a pointer to an array or container element; the result may
be one past the last element. -/
def Mem.stride? (m : Mem) (p : Ptr) (n : Int) : Option Ptr :=
  match m.elemPos? p with
  | some (b, pre, e, len) =>
    -- (for `n = 0` this is `p` itself: one case, one branch for symbolic `n`)
    let j := (e.index : Int) + n
    if 0 ≤ j ∧ j ≤ len then some (.loc b (pre ++ [e.withIndex j.toNat])) else none
  | none => if n = 0 then (match p with | .loc _ _ => some p | _ => none) else none

/-- `p - q` for two pointers into the same array or container. -/
def Mem.diff? (m : Mem) (p q : Ptr) : Option Int :=
  match m.elemPos? p, m.elemPos? q with
  | some (b, pre, e, _), some (b', pre', e', _) =>
    if b = b' ∧ pre = pre' then some ((e.index : Int) - e'.index) else none
  | _, _ => none

/-- A pointer one past the last element of an array or container. -/
def Mem.isPastEnd (m : Mem) (p : Ptr) : Bool :=
  match m.elemPos? p with
  | some (_, _, e, len) => e.index == len
  | none => false

/-- Pointer equality. Comparing a past-the-end pointer with a pointer into a
different object is unspecified in C++, so it is undefined here (`none`). -/
def Mem.ptrEq? (m : Mem) : Ptr → Ptr → Option Bool
  | .null, .null => some true
  | .null, .loc _ _ | .loc _ _, .null => some false
  | .addr a, .addr b => some (a == b)
  | .addr _, .null | .null, .addr _ => some false
  -- an integer address against an object: unspecified, undefined here
  | .addr _, .loc _ _ | .loc _ _, .addr _ => none
  | .fn f, .fn g => some (f == g)
  | .fn _, _ | _, .fn _ => some false
  -- label addresses: equal when they designate the same label
  | .label f l, .label f' l' => some (f == f' && l == l')
  | .label .., _ | _, .label .. => some false
  | .vtable s i k, .vtable s' i' k' => some (s == s' && i == i' && k == k')
  | .vtable .., _ | _, .vtable .. => none
  | .loc b p, .loc b' p' =>
    if b = b' then some (p == p')
    else if m.isPastEnd (.loc b p) || m.isPastEnd (.loc b' p') then none
    else some false

/-- Relational comparison: only between elements of the same array. -/
def Mem.ptrLt? (m : Mem) (p q : Ptr) : Option Bool :=
  (m.diff? p q).map (· < 0)

end CIR
