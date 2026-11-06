/-
# Files: `OPEN`, `READ`, `WRITE`, `REWRITE`, `DELETE`, `CLOSE`

The operations of declared files (`FileDecl`), following IBM Enterprise COBOL for
sequential (QSAM) and indexed (VSAM KSDS) files with fixed-length records.  Each operation
returns the file status code it produces and the new state; `Cobol.Sem.Exec` stores the
status in the `FILE STATUS` item and selects the phrase to run (`ioNext`).

Status codes produced: `00` success, `02` (an alternate key `WITH DUPLICATES`: a `READ` whose
next record has the same value of the key of reference, a `WRITE` / `REWRITE` that created a
duplicate value), `05` (`OPEN` of an absent `OPTIONAL` file), `07` (`CLOSE … REEL` / `UNIT` / `NO
REWIND` of a disk file, `fileCloseOpt`), `10` end of file, `21` key
sequence error, `22` duplicate key, `23` record not found, `44` (`WRITE` / `REWRITE` of a variable-length record outside its length range), `41` `OPEN` of an open file, `42` `CLOSE` of a closed file, `43` sequential
`REWRITE` / `DELETE` without a preceding successful `READ`, `38` (`OPEN` of a file closed `WITH LOCK`,
`fileOpenL`), `46` `READ` after the end of file, a
failed `START` or (dynamic access) a failed keyed `READ`,
`47` / `48` / `49` statement not allowed in the open mode, and whatever the environment
reports for a failing `OPEN` (`Env.openError`).

Assumptions (documented model limits): the initial contents of an indexed file are in
ascending record-key order with unique record keys (true of every KSDS); I/O never fails
for physical reasons; a record of a fixed-length file has the length of the record area, a
record of a variable-length file (`RECORD VARYING … DEPENDING ON`) a length in its range.  The
records in an indexed file before the run come first among duplicates of an alternate key, in
record-key order (as in an alternate index built from the file).  Alternate keys as keys of
reference and duplicates: the section on `FileDecl.keyRef` below.
-/
import Cobol.Sem.Data

namespace Cobol
namespace Sem

/-- The two characters of a file status code. -/
def statusBytes (c : Config) (code : Nat) : List UInt8 :=
  [c.digitByte (code / 10 % 10), c.digitByte (code % 10)]

/-- Declaration of file `f`. -/
def fileDecl (P : Program) (f : Nat) : Option FileDecl := P.files.find? (·.id == f)

/-- Run-time state of file `f` (closed, with its initial contents, before first use). -/
def fileSt (st : State) (f : Nat) : FileSt :=
  match st.files.lookup f with
  | some s => s
  | none => { recs := (st.inp.lookup f).getD [] }

/-- Update the state of file `f` in place (files stay in the order of their first use, so the
shape of the file list does not depend on the path taken). -/
def setFile (st : State) (f : Nat) (s : FileSt) : State :=
  { st with files := if st.files.any (·.1 == f) then st.files.map (fun p => if p.1 == f then (f, s) else p)
                     else st.files ++ [(f, s)] }

/-- Forget the record of the last `READ`: every I/O statement except a successful `READ` does
(a sequential `REWRITE` / `DELETE` needs the last statement to be a successful `READ`). -/
def clearCur (st : State) (f : Nat) : State :=
  setFile st f { fileSt st f with cur := none }

/-- Store a status code in the `FILE STATUS` item of a file. -/
def setStatus (c : Config) (d : FileDecl) (code : Nat) (st : State) : State :=
  match d.status with
  | some sd => writeBytes st sd (statusBytes c code)
  | none => st

/-- Key field of a record. -/
def keyOf (k : KeyDecl) (r : List UInt8) : List UInt8 := (r.drop k.off).take k.len

/-- Unsigned lexicographic order of byte strings (the collating order of VSAM keys). -/
def bytesLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && bytesLt as bs)

/-- Insert a record into a list in ascending key order. -/
def insertByKey (k : KeyDecl) (r : List UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [r]
  | x :: xs => if bytesLt (keyOf k r) (keyOf k x) then r :: x :: xs else x :: insertByKey k r xs

/-- The key field `k` in the record area (`keyOf k` of the area's bytes, read directly). -/
def keyField (st : State) (d : FileDecl) (k : KeyDecl) : List UInt8 :=
  st.mem.read (d.area.off + k.off) k.len

/-- Index of the first record whose key `k` is `v`. -/
def findKey (k : KeyDecl) (v : List UInt8) : List (List UInt8) → Option Nat
  | [] => none
  | r :: rs => if keyOf k r == v then some 0 else (findKey k v rs).map (· + 1)

/-- Key of reference `k`: `0` = record key, `j + 1` = alternate key `j`. -/
def keyDecl (d : FileDecl) : Nat → Option KeyDecl
  | 0 => d.key
  | j + 1 => d.alt[j]?

/-- Some alternate key without duplicates of `r` is already used by a record other than
record `skip`. -/
def altClash (d : FileDecl) (rs : List (List UInt8)) (r : List UInt8) (skip : Option Nat) : Bool :=
  d.alt.any fun a =>
    !a.dups && (rs.zipIdx.any fun (x, i) => some i != skip && keyOf a x == keyOf a r)

def canRead (s : FileSt) : Bool := s.mode == some .input || s.mode == some .io

/-- `ACCESS DYNAMIC` indexed file: the file position indicator at record `r` (its record key),
the record itself read next or not. -/
def boundAt (d : FileDecl) (r : Option (List UInt8)) (incl : Bool) : Option (List UInt8 × Bool) :=
  match d.key, r with
  | some kd, some r => some (keyOf kd r, incl)
  | _, _ => none

/-- Is a record with key `v` read next by `READ NEXT` when it lands at the reading position:
does `v` come after the file position indicator `b` (or at it, when the record there is read
next)?  A `WRITE` of a key below the indicator does not move the reading back to it. -/
def afterBound (b : Option (List UInt8 × Bool)) (v : List UInt8) : Bool :=
  match b with
  | none => true
  | some (k, incl) => if incl then !bytesLt v k else bytesLt k v

/-- A record length the file allows: the record area's for fixed-length files, `min ..= max`
for `RECORD VARYING FROM min TO max`. -/
def recLenOk (d : FileDecl) (n : Nat) : Bool :=
  match d.varying with
  | some (mn, mx) => mn ≤ n && n ≤ mx
  | none => n == d.area.len

/-- The bytes a `WRITE` / `REWRITE` of record `rd` writes: the record, or, for a
variable-length file with a `DEPENDING ON` item, that many bytes of the record area. -/
def recordOut (c : Config) (d : FileDecl) (rd : FieldDesc) (st : State) : SemM (List UInt8) :=
  match d.varying, d.dependsOn with
  | some _, some dd =>
    match dd.kind with
    | .num f =>
      match decodeNum c f (readBytes st dd) with
      | some v => .ok (st.mem.read d.area.off v.toNat)
      | none => .error .invalidData
    | _ => .error (.unsupported "DEPENDING ON item is not numeric")
  | _, _ => .ok (readBytes st rd)

/-- The record of the last successful `READ` as a field: the record area, shortened to the
length of the record read for a variable-length file (the source of `READ … INTO`). -/
def recordIn (d : FileDecl) (st : State) : FieldDesc :=
  match d.varying, (fileSt st d.id).cur with
  | some _, some i => { d.area with len := ((fileSt st d.id).recs.getD i []).length }
  | _, _ => d.area

/-- After a successful `READ` of a variable-length file: its `DEPENDING ON` item holds the
length of the record read. -/
def setRecLen (c : Config) (d : FileDecl) (st : State) : State :=
  match d.varying, d.dependsOn with
  | some _, some dd =>
    match dd.kind, (fileSt st d.id).cur with
    | .num f, some i =>
      writeBytes st dd
        (encodeNum c f (fitNum c f (((fileSt st d.id).recs.getD i []).length : Int)).2)
    | _, _ => st
  | _, _ => st

def lenFault : Fault := .unsupported "record length differs from the record area"

/-! ### The record key as the key of reference

The operations of files without `FileDecl.keyRef` (`fileOpen`, `fileRead`, … below call these for
them).  The files with `keyRef` use them too, for what does not depend on alternate keys. -/

/-- `OPEN`.  An `OPTIONAL` file that is absent (`Env.absent`, and no `OPEN` has created it yet)
opens as an empty file with status 05 (IBM, OPEN statement notes, Table 1): `INPUT` leaves it
absent (the first `READ` gives the at-end or invalid-key condition), `I-O` and `EXTEND` create
it.  `OUTPUT` creates it with status 00, as it creates any file. -/
def fileOpenBasic (env : Env) (d : FileDecl) (mode : OpenMode) (st : State) : Nat × State :=
  let s := fileSt st d.id
  if s.mode.isSome then (41, clearCur st d.id)
  else
    match env.openError d.id mode with
    | some code => (code, st)
    | none =>
      if d.optional && env.absent d.id && !s.created then
        (if mode == .output then 0 else 5,
         setFile st d.id { s with mode := some mode, pos := 0, eof := false, cur := none, recs := [],
                                  bound := none, created := mode != .input })
      else
      if d.access == .dynamic then
        -- the file position indicator holds the first record's key, that record read next
        let recs := if mode == .output then [] else s.recs
        (0, setFile st d.id { s with mode := some mode, pos := 0, eof := false, cur := none, recs,
                                     bound := boundAt d recs.head? true })
      else
      (0, setFile st d.id { s with mode := some mode, pos := 0, eof := false, cur := none,
                                   recs := if mode == .output then [] else s.recs })

/-- `CLOSE`. -/
def fileClose (d : FileDecl) (st : State) : Nat × State :=
  let s := fileSt st d.id
  match s.mode with
  | none => (42, st)
  | some _ => (0, setFile st d.id { s with mode := none, cur := none })

/-- `READ`: the next record (`key = none`) or the record with a given key. -/
def fileReadBasic (d : FileDecl) (key : Option Nat) (st : State) : SemM (Nat × State) :=
  let s := fileSt st d.id
  if !canRead s then .ok (47, clearCur st d.id)
  else
    match key with
    | none =>
      if s.eof then .ok (46, clearCur st d.id)
      else
        match s.recs[s.pos]? with
        | none => .ok (10, setFile st d.id { s with eof := true, cur := none })
        | some r =>
          if recLenOk d r.length then
            if d.access == .dynamic then
              .ok (0, setFile (writeBytes st d.area r) d.id
                { s with pos := s.pos + 1, cur := some s.pos, bound := boundAt d (some r) false })
            else
            .ok (0, setFile (writeBytes st d.area r) d.id
              { s with pos := s.pos + 1, cur := some s.pos })
          else .error lenFault
    | some k =>
      match keyDecl d k with
      | none => .error (.unsupported "READ by an undeclared key")
      | some kd =>
        if kd.dups then .error (.unsupported "READ by an alternate key with duplicates")
        else
          let v := keyField st d kd
          match findKey kd v s.recs with
          | none =>
            if d.access == .dynamic then
              -- the file position indicator is undefined after a failed READ (IBM), so a READ NEXT
              -- gets 46: "The preceding READ statement was unsuccessful but did not cause an
              -- at-end condition"
              .ok (23, setFile st d.id { s with cur := none, eof := true })
            else
            .ok (23, setFile st d.id { s with cur := none })
          | some i =>
            let r := s.recs.getD i []
            if recLenOk d r.length then
              if d.access == .dynamic then
                .ok (0, setFile (writeBytes st d.area r) d.id
                  { s with pos := i + 1, eof := false, cur := some i, bound := boundAt d (some r) false })
              else
              .ok (0, setFile (writeBytes st d.area r) d.id
                { s with pos := i + 1, eof := false, cur := some i })
            else .error lenFault

/-- `WRITE` of the record bytes `bs`. -/
def fileWriteBasic (d : FileDecl) (bs : List UInt8) (st : State) : SemM (Nat × State) :=
  let st := clearCur st d.id
  let s := fileSt st d.id
  -- a variable-length record outside `min ..= max` is a boundary violation (status 44)
  if !recLenOk d bs.length then (if d.varying.isSome then .ok (44, st) else .error lenFault)
  else
    match d.org with
    | .sequential =>
      if s.mode == some .output || s.mode == some .extend then
        .ok (0, setFile { st with out := .write d.id bs :: st.out } d.id
          { s with recs := s.recs ++ [bs] })
      else .ok (48, st)
    | .indexed =>
      match d.key with
      | none => .error (.unsupported "indexed file without a record key")
      | some kd =>
        -- sequential access: OUTPUT / EXTEND, ascending keys; random / dynamic: OUTPUT / I-O
        let allowed := if d.access == .sequential then s.mode == some .output || s.mode == some .extend
          else s.mode == some .output || s.mode == some .io
        if !allowed then .ok (48, st)
        -- sequential access: a key below the previous one is a sequence error (checked first)
        else if d.access == .sequential &&
            (s.recs.getLast?.map (fun r => bytesLt (keyOf kd bs) (keyOf kd r))).getD false then
          .ok (21, st)
        else if (findKey kd (keyOf kd bs) s.recs).isSome then .ok (22, st)
        else if altClash d s.recs bs none then .ok (22, st)
        else if d.access == .dynamic then
          -- dynamic access: reading continues in key order from the file position indicator; a
          -- record inserted before the reading position moves it up, and so does one inserted
          -- at it whose key does not come after the indicator (IBM, GnuCOBOL)
          let j := (s.recs.filter fun r => bytesLt (keyOf kd r) (keyOf kd bs)).length
          let pos := if j < s.pos || (j == s.pos && !afterBound s.bound (keyOf kd bs))
            then s.pos + 1 else s.pos
          .ok (0, setFile { st with out := .write d.id bs :: st.out } d.id
            { s with recs := insertByKey kd bs s.recs, pos })
        else
          -- a record inserted before the reading position moves it up (no reading follows a
          -- WRITE in sequential or random access; the position is kept consistent)
          let pos := if (s.recs.filter fun r => bytesLt (keyOf kd r) (keyOf kd bs)).length < s.pos
            then s.pos + 1 else s.pos
          .ok (0, setFile { st with out := .write d.id bs :: st.out } d.id
            { s with recs := insertByKey kd bs s.recs, pos })

/-- `REWRITE` with the record bytes `bs`. -/
def fileRewriteBasic (d : FileDecl) (bs : List UInt8) (st0 : State) : SemM (Nat × State) :=
  let s := fileSt st0 d.id
  let st := clearCur st0 d.id
  if !recLenOk d bs.length then (if d.varying.isSome then .ok (44, st) else .error lenFault)
  else if s.mode != some .io then .ok (49, st)
  else
    let replace (i : Nat) : SemM (Nat × State) :=
      if altClash d s.recs bs (some i) then .ok (22, st)
      else
        .ok (0, setFile { st with out := .rewrite d.id bs :: st.out } d.id
          { s with recs := s.recs.set i bs, cur := none })
    match d.org, d.access, d.key with
    | .indexed, .sequential, some kd =>
      -- the record of the last READ; its key must not change
      match s.cur with
      | none => .ok (43, st)
      | some i => if keyOf kd (s.recs.getD i []) != keyOf kd bs then .ok (21, st) else replace i
    | .indexed, _, some kd =>
      -- random / dynamic access: the record with this record key
      match findKey kd (keyOf kd bs) s.recs with
      | none => .ok (23, st)
      | some i => replace i
    | .indexed, _, none => .error (.unsupported "indexed file without a record key")
    | .sequential, _, _ =>
      match s.cur with
      | none => .ok (43, st)
      | some i =>
        -- a sequential file's record keeps its length (IBM: 44 otherwise)
        if d.varying.isSome && bs.length != (s.recs.getD i []).length then .ok (44, st)
        else replace i

/-- `DELETE` (indexed files). -/
def fileDeleteBasic (d : FileDecl) (st0 : State) : SemM (Nat × State) :=
  let s := fileSt st0 d.id
  let st := clearCur st0 d.id
  match d.org, d.key with
  | .sequential, _ => .error (.unsupported "DELETE on a sequential file")
  | .indexed, none => .error (.unsupported "indexed file without a record key")
  | .indexed, some kd =>
    if s.mode != some .io then .ok (49, st)
    else
      let del (i : Nat) : Nat × State :=
        (0, setFile { st with out := .delete d.id (keyOf kd (s.recs.getD i [])) :: st.out } d.id
          { s with recs := s.recs.eraseIdx i, pos := if i < s.pos then s.pos - 1 else s.pos,
                   cur := none })
      if d.access != .sequential then
        match findKey kd (keyField st d kd) s.recs with
        | none => .ok (23, st)
        | some i => .ok (del i)
      else
        match s.cur with
        | none => .ok (43, st)
        | some i => .ok (del i)

/-- Index of the first record satisfying `p`. -/
def firstRec (p : List UInt8 → Bool) : List (List UInt8) → Option Nat
  | [] => none
  | r :: rs => if p r then some 0 else (firstRec p rs).map (· + 1)

/-- `START`: the first record whose key `k` (the record key or its leading part) satisfies
`op` (`eq` / `gt` / `ge`) with the value in the record area.  Not found: `23`, and the
position is lost (a `READ NEXT` then gets `46`). -/
def fileStartBasic (d : FileDecl) (op : CmpOp) (k : KeyDecl) (st : State) : Nat × State :=
  let s := fileSt st d.id
  if !canRead s then (47, clearCur st d.id)
  else
    let v := keyField st d k
    let ok (r : List UInt8) : Bool :=
      match op with
      | .eq => keyOf k r == v
      | .gt => bytesLt v (keyOf k r)
      | _ => !bytesLt (keyOf k r) v
    match firstRec ok s.recs with
    | some i =>
      if d.access == .dynamic then
        -- the file position indicator holds the key of the record found, read next
        (0, setFile st d.id { s with pos := i, eof := false, cur := none,
                                     bound := boundAt d s.recs[i]? true })
      else
      (0, setFile st d.id { s with pos := i, eof := false, cur := none })
    | none => (23, setFile st d.id { s with eof := true, cur := none })

/-! ### Alternate keys of reference, duplicates (files with `FileDecl.keyRef`)

IBM: a successful `START` makes the key it names (the record key, an alternate key, or a leading
part of either) the key of reference of the `READ`s that follow, and in dynamic access a keyed
`READ` does too; `OPEN` makes it the record key.  `READ NEXT` returns the records in ascending
order of the key of reference, records with one value of an alternate key `WITH DUPLICATES` "in
the order in which they were placed in the file"; a keyed `READ` by such a key returns the first
record of the value written.  The file position indicator is a place in that order (`AltPos`):
`WRITE`, `REWRITE` and `DELETE` do not move it, so a record deleted there is skipped and a record
written after it is read.  Status 02: a `READ` whose next record in the key of reference has the
same value of the key, and a `WRITE` / `REWRITE` that "created a duplicate key value" of an
alternate key `WITH DUPLICATES` (for a `REWRITE`, a key whose value it changed: VSAM reports a
duplicate key "created in an alternate index").  The record key's behaviour is the `…Basic`
functions'. -/

/-- The record key of record `r` (`[]` without a record key). -/
def recKey (d : FileDecl) (r : List UInt8) : List UInt8 :=
  match d.key with
  | some kd => keyOf kd r
  | none => []

/-- The stamp of the value of alternate key `j` of the record with record key `k`. -/
def stampOf (s : FileSt) (j : Nat) (k : List UInt8) : Option Nat :=
  (s.stamps.find? (·.1 == (j, k))).map (·.2)

/-- The place of record `r` in the order of alternate key `j` (declared as `a`). -/
def altPos (d : FileDecl) (s : FileSt) (j : Nat) (a : KeyDecl) (r : List UInt8) : AltPos :=
  { val := keyOf a r, stamp := if a.dups then stampOf s j (recKey d r) else none,
    key := recKey d r }

/-- Placement order: the records in the file before the run (no stamp) first. -/
def stampLt : Option Nat → Option Nat → Bool
  | none, some _ => true
  | some m, some n => m < n
  | _, _ => false

/-- The order of an alternate key: value, then placement, then record key. -/
def altLt (p q : AltPos) : Bool :=
  bytesLt p.val q.val ||
    (p.val == q.val && (stampLt p.stamp q.stamp || (p.stamp == q.stamp && bytesLt p.key q.key)))

/-- Index of the first record satisfying `p` in the order of alternate key `j` (`a`). -/
def altFirst (d : FileDecl) (s : FileSt) (j : Nat) (a : KeyDecl) (p : List UInt8 → Bool) :
    Option Nat :=
  (s.recs.zipIdx.foldl (fun best (r, i) =>
    if !p r then best
    else match best with
      | some (_, q) => if altLt (altPos d s j a r) q then some (i, altPos d s j a r) else best
      | none => some (i, altPos d s j a r)) (none : Option (Nat × AltPos))).map (·.1)

/-- Status of a successful `READ` of record `r` with alternate key `j` (`a`) as the key of
reference: `02` when the next record in that order has the same value of the key. -/
def dupNext (d : FileDecl) (s : FileSt) (j : Nat) (a : KeyDecl) (r : List UInt8) : Nat :=
  if a.dups && s.recs.any (fun x => keyOf a x == keyOf a r && altLt (altPos d s j a r) (altPos d s j a x))
  then 2 else 0

/-- Some alternate key `j` `WITH DUPLICATES` with `chg j` has the same value in record `r` as in a
record of `rs` other than record `skip`. -/
def dupMade (d : FileDecl) (rs : List (List UInt8)) (r : List UInt8) (skip : Option Nat)
    (chg : Nat → Bool) : Bool :=
  d.alt.zipIdx.any fun (a, j) =>
    a.dups && chg j && (rs.zipIdx.any fun (x, i) => some i != skip && keyOf a x == keyOf a r)

/-- The stamps after record `r` took its values of the alternate keys `j` `WITH DUPLICATES` with
`chg j`, stamped `s.nstamp`. -/
def restamp (d : FileDecl) (s : FileSt) (r : List UInt8) (chg : Nat → Bool) :
    List ((Nat × List UInt8) × Nat) :=
  let js := (d.alt.zipIdx.filter fun (a, j) => a.dups && chg j).map (·.2)
  (s.stamps.filter fun e => !(e.1.2 == recKey d r && js.contains e.1.1)) ++
    js.map fun j => ((j, recKey d r), s.nstamp)

/-- `OPEN` (`keyRef`): the record key becomes the key of reference; an empty file has no
stamps. -/
def fileOpenK (env : Env) (d : FileDecl) (mode : OpenMode) (st : State) : Nat × State :=
  let (code, st1) := fileOpenBasic env d mode st
  if code == 0 || code == 5 then
    let s := fileSt st1 d.id
    (code, setFile st1 d.id { s with kor := 0, abound := none,
                                     stamps := if s.recs.isEmpty then [] else s.stamps })
  else (code, st1)

/-- `READ` (`keyRef`): `READ NEXT` with an alternate key of reference, and a keyed `READ` by an
alternate key, in that key's order; by the record key as `fileReadBasic`.  The key of a keyed
`READ` becomes the key of reference, and after a failed one `READ NEXT` gives 46 (IBM's status
table: "The preceding READ statement was unsuccessful but did not cause an at-end condition"). -/
def fileReadK (d : FileDecl) (key : Option Nat) (st : State) : SemM (Nat × State) :=
  let s := fileSt st d.id
  match key, s.kor with
  | none, 0 => fileReadBasic d none st
  | none, j + 1 =>
    if !canRead s then .ok (47, clearCur st d.id)
    else if s.eof then .ok (46, clearCur st d.id)
    else
      match d.alt[j]? with
      | none => .error (.unsupported "READ NEXT by an undeclared key")
      | some a =>
        -- the first record at (`incl`) or after the file position indicator
        let after (r : List UInt8) : Bool :=
          match s.abound with
          | none => true
          | some (b, incl) =>
            if incl then !altLt (altPos d s j a r) b else altLt b (altPos d s j a r)
        match altFirst d s j a after with
        | none => .ok (10, setFile st d.id { s with eof := true, cur := none })
        | some i =>
          let r := s.recs.getD i []
          if recLenOk d r.length then
            .ok (dupNext d s j a r, setFile (writeBytes st d.area r) d.id
              { s with cur := some i, abound := some (altPos d s j a r, false) })
          else .error lenFault
  | some 0, _ =>
    match fileReadBasic d (some 0) st with
    | .ok (code, st1) =>
      if code == 0 || code == 23 then
        .ok (code, setFile st1 d.id { fileSt st1 d.id with kor := 0, eof := code == 23 })
      else .ok (code, st1)
    | .error f => .error f
  | some (j + 1), _ =>
    if !canRead s then .ok (47, clearCur st d.id)
    else
      match d.alt[j]? with
      | none => .error (.unsupported "READ by an undeclared key")
      | some a =>
        let v := keyField st d a
        match altFirst d s j a (fun r => keyOf a r == v) with
        | none => .ok (23, setFile st d.id { s with cur := none, eof := true, kor := j + 1 })
        | some i =>
          let r := s.recs.getD i []
          if recLenOk d r.length then
            .ok (dupNext d s j a r, setFile (writeBytes st d.area r) d.id
              { s with eof := false, cur := some i, kor := j + 1,
                       abound := some (altPos d s j a r, false) })
          else .error lenFault

/-- `WRITE` (`keyRef`): `fileWriteBasic`; 02 when the record has the value of an alternate key
`WITH DUPLICATES` of another record; the record's values are stamped. -/
def fileWriteK (d : FileDecl) (bs : List UInt8) (st : State) : SemM (Nat × State) :=
  match fileWriteBasic d bs st with
  | .ok (0, st1) =>
    let s1 := fileSt st1 d.id
    .ok (if dupMade d (fileSt st d.id).recs bs none (fun _ => true) then 2 else 0,
      setFile st1 d.id { s1 with stamps := restamp d s1 bs (fun _ => true), nstamp := s1.nstamp + 1 })
  | r => r

/-- `REWRITE` (`keyRef`): `fileRewriteBasic`; 02 when an alternate key `WITH DUPLICATES` whose
value changed now has the value of another record; the changed values are stamped. -/
def fileRewriteK (d : FileDecl) (bs : List UInt8) (st : State) : SemM (Nat × State) :=
  let s := fileSt st d.id
  -- the record replaced: the last one read (sequential access), else the one with the record key
  let old : Option Nat :=
    if d.access == .sequential then s.cur
    else match d.key with
      | some kd => findKey kd (keyOf kd bs) s.recs
      | none => none
  match fileRewriteBasic d bs st, old with
  | .ok (0, st1), some i =>
    let chg (j : Nat) : Bool :=
      match d.alt[j]? with
      | some a => keyOf a (s.recs.getD i []) != keyOf a bs
      | none => false
    let s1 := fileSt st1 d.id
    .ok (if dupMade d s.recs bs (some i) chg then 2 else 0,
      setFile st1 d.id { s1 with stamps := restamp d s1 bs chg, nstamp := s1.nstamp + 1 })
  | r, _ => r

/-- `DELETE` (`keyRef`): `fileDeleteBasic`; the deleted record's stamps go. -/
def fileDeleteK (d : FileDecl) (st : State) : SemM (Nat × State) :=
  match fileDeleteBasic d st with
  | .ok (0, st1) =>
    let s1 := fileSt st1 d.id
    .ok (0, setFile st1 d.id
      { s1 with stamps := s1.stamps.filter fun e => s1.recs.any (recKey d · == e.1.2) })
  | r => r

/-- `START` (`keyRef`) by an alternate key `j` or a leading part `k` of it: the first record in
`j`'s order whose key field satisfies the relation; `j` becomes the key of reference and the file
position indicator is at that record.  Not found: `23`, and a `READ NEXT` then gets `46`.  By the
record key: `fileStartBasic`, the record key becomes the key of reference. -/
def fileStartK (d : FileDecl) (op : CmpOp) (k : KeyDecl) (st : State) : Nat × State :=
  -- IBM: an alternate key's leftmost character position is not that of another key
  match d.alt.zipIdx.find? (·.1.off == k.off) with
  | none =>
    let (code, st1) := fileStartBasic d op k st
    (code, setFile st1 d.id { fileSt st1 d.id with kor := 0 })
  | some (a, j) =>
    let s := fileSt st d.id
    if !canRead s then (47, clearCur st d.id)
    else
      let v := keyField st d k
      let ok (r : List UInt8) : Bool :=
        match op with
        | .eq => keyOf k r == v
        | .gt => bytesLt v (keyOf k r)
        | _ => !bytesLt (keyOf k r) v
      match altFirst d s j a ok with
      | some i =>
        (0, setFile st d.id { s with eof := false, cur := none, kor := j + 1,
                                     abound := some (altPos d s j a (s.recs.getD i []), true) })
      | none => (23, setFile st d.id { s with eof := true, cur := none, kor := j + 1 })

/-! ### The operations -/

/-- `OPEN` of a file that some `CLOSE … WITH LOCK` names (`FileDecl.lockable`): 38 once the file is
locked (it stays closed; IBM: "An OPEN statement was attempted on a file previously closed with
lock"), else as `OPEN`. -/
def fileOpenL (env : Env) (d : FileDecl) (mode : OpenMode) (st : State) : Nat × State :=
  if (fileSt st d.id).locked then (38, st)
  else if d.keyRef then fileOpenK env d mode st else fileOpenBasic env d mode st

/-- `OPEN`. -/
def fileOpen (env : Env) (d : FileDecl) (mode : OpenMode) (st : State) : Nat × State :=
  if d.lockable then fileOpenL env d mode st else
  if d.keyRef then fileOpenK env d mode st else fileOpenBasic env d mode st

/-- `READ`: the next record (`key = none`) or the record with a given key. -/
def fileRead (d : FileDecl) (key : Option Nat) (st : State) : SemM (Nat × State) :=
  if d.keyRef then fileReadK d key st else fileReadBasic d key st

/-- `WRITE` of the record bytes `bs`. -/
def fileWrite (d : FileDecl) (bs : List UInt8) (st : State) : SemM (Nat × State) :=
  if d.keyRef then fileWriteK d bs st else fileWriteBasic d bs st

/-- `REWRITE` with the record bytes `bs`. -/
def fileRewrite (d : FileDecl) (bs : List UInt8) (st : State) : SemM (Nat × State) :=
  if d.keyRef then fileRewriteK d bs st else fileRewriteBasic d bs st

/-- `DELETE` (indexed files). -/
def fileDelete (d : FileDecl) (st : State) : SemM (Nat × State) :=
  if d.keyRef then fileDeleteK d st else fileDeleteBasic d st

/-- `START`: position for `READ NEXT` by key `k` (a key of the file or a leading part of one). -/
def fileStart (d : FileDecl) (op : CmpOp) (k : KeyDecl) (st : State) : Nat × State :=
  if d.keyRef then fileStartK d op k st else fileStartBasic d op k st

/-! ### `CLOSE` with a phrase

IBM (Language Reference 6.4, `CLOSE` statement, Tables 35, 36 and 38) by file type: a sequential file
on disk is a non-reel/unit file ("The term reel applies only to tape devices"; `REEL` and `UNIT` "are
interchangeable"; on a storage device other than tape the phrases leave "a status key value ... to
indicate the file was on a non-reel medium"), so `REEL` / `UNIT` closes no volume: "The file remains in
the open mode and no action takes place except that the value of the I-O status associated with the
file is updated" (status 07: "the referenced file was on a non-reel/unit medium"); `FOR REMOVAL` is
"Treated as a comment" with the same status; `WITH NO REWIND` closes the file "as if none of the
optional phrases were present", with status 07.  `WITH LOCK` (sequential and indexed files) closes the
file and locks it: "The compiler ensures that this file cannot be opened again during this execution
of the object program" (an `OPEN` gets 38: "An OPEN statement was attempted on a file previously closed
with lock").  `REEL`, `UNIT` and `NO REWIND` "are not valid for VSAM files".  An `OPTIONAL` file that
is not present (opened `INPUT`, `Env.absent`) is on no medium: IBM keeps its "file position indicator
and current volume pointer" and gives no status, so the model reports such a `CLOSE` with `REEL`,
`UNIT` or `NO REWIND` as unsupported. -/

/-- `CLOSE` with a phrase: on an open sequential file `REEL` / `UNIT` (also `WITH NO REWIND`, `FOR
REMOVAL`) gives 07 and the file stays open (the statement is an I/O statement: a sequential
`REWRITE` after it gets 43); `WITH NO REWIND` closes it with 07; `WITH LOCK` closes and locks it
(00); a file not in an open mode gives 42 (and stays locked if it was). -/
def fileCloseOpt (env : Env) (d : FileDecl) (opt : CloseOpt) (st : State) : SemM (Nat × State) :=
  let s := fileSt st d.id
  if d.org != .sequential && opt != .lock then
    .error (.unsupported "CLOSE ... REEL / UNIT or NO REWIND of an indexed file")
  else
    match s.mode, opt with
    | none, _ => .ok (42, st)
    | some _, .lock => .ok (0, setFile st d.id { s with mode := none, cur := none, locked := true })
    | some _, _ =>
      if d.optional && env.absent d.id && !s.created then
        .error (.unsupported "CLOSE ... REEL / UNIT or NO REWIND of an OPTIONAL file that is not present")
      else if opt == .noRewind then .ok (7, setFile st d.id { s with mode := none, cur := none })
      else .ok (7, clearCur st d.id)

/-! ### `OPEN … REVERSED`

IBM: "REVERSED  Valid only for sequential single-reel files. REVERSED is not valid for VSAM files. If
the concept of reels has no meaning for the storage medium (for example, a direct access device), the
REVERSED and NO REWIND phrases do not apply"; on a tape "Subsequent READ statements make the data
records available in reversed order", and "the record format must be fixed".  IBM does not say where
the `READ`s of a disk file opened `REVERSED` start, so the model runs such an `OPEN` only where that
cannot matter: when it fails (nothing is positioned) and when the file has at most one record. -/

/-- `OPEN INPUT … REVERSED` of a sequential file with fixed-length records: the result of `OPEN INPUT`
when it fails or leaves at most one record to read; otherwise unsupported. -/
def fileOpenRev (env : Env) (d : FileDecl) (st : State) : SemM (Nat × State) :=
  if d.org != .sequential || d.varying.isSome then
    .error (.unsupported "OPEN ... REVERSED of an indexed or variable-length file")
  else
    let (code, st1) := fileOpen env d .input st
    if 10 ≤ code || (fileSt st1 d.id).recs.length ≤ 1 then .ok (code, st1)
    else .error (.unsupported "OPEN ... REVERSED of a disk file with more than one record")

/-- What follows an I/O statement with status `code`: the `NOT AT END` / `NOT INVALID KEY`
statements on success (`0x`); the `AT END` / `INVALID KEY` statements when the status is
that condition (`cond`) and the phrase is present (`trap`); otherwise the next statement if
the file has a `FILE STATUS` item, else an abend. -/
inductive IoNext where
  | ok | exc | cont | abend
  deriving DecidableEq, Repr

def ioNext (d : FileDecl) (code : Nat) (trap cond : Bool) : IoNext :=
  if code < 10 then .ok
  else if cond && trap then .exc
  else if d.status.isSome then .cont
  else .abend

/-- The at-end condition (sequential `READ`). -/
def atEndCond (code : Nat) : Bool := code == 10

/-- The invalid-key condition (keyed operations). -/
def invalidKeyCond (code : Nat) : Bool := code / 10 == 2

end Sem
end Cobol
