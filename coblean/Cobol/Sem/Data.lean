/-
# Data semantics: references, storing, `MOVE`

* `resolve`: subscripts and reference modification (out of range = `Fault.range`).
* `fitNum`: what is stored when a value (already at the receiver's scale) does not fit the
  receiver: decimal high-order truncation, binary wrap for full-binary items, absolute value
  for unsigned items.  Also reports whether the value overflowed (size error).
* `MOVE` follows the standard category rules (IBM Enterprise COBOL):
  - group sender or group receiver: bytes, no conversion, space padding on the right (a group
    sender into a `JUSTIFIED` receiver: right-justified, IBM's group move being an
    alphanumeric-to-alphanumeric elementary move);
  - alphanumeric receiver: left justified (right if `JUSTIFIED`), space padded/truncated;
    a numeric integer sender is moved as its unsigned digit characters;
  - numeric receiver: decimal-point alignment, truncation at both ends, no rounding;
    an alphanumeric sender is read as an unsigned integer;
  - numeric-edited receiver: editing (`Cobol.Edit`);
  - numeric-edited sender and numeric or numeric-edited receiver: the sender is de-edited
    (`deEdit`: the value whose editing is the sender's content) and that value is moved;
    to the other receivers a numeric-edited sender is alphanumeric;
  - figurative constants fill the receiver (`ZERO` is the number zero for numeric
    receivers).
  Overlapping (non-identical) sender and receiver is undefined (`Fault.overlap`).
-/
import Cobol.IR
import Cobol.Edit

namespace Cobol

/-- Semantic monad of data operations. -/
abbrev SemM := Except Fault

/-- The bytes of field `d` in storage `m` (for statements about input / output fields; the
loader defines a reducible `FieldDesc` constant per data item). -/
abbrev Mem.field (m : Mem) (d : FieldDesc) : List UInt8 := m.read d.off d.len

namespace Sem

/-! The data semantics is written with explicit `match` on `Except` results instead of
`do`-notation: simp evaluates a `match` lazily (discriminant first, then only the selected
arm), whereas the continuation lambda of a `>>=` would be simplified on a symbolic argument.
This is what keeps symbolic execution linear in the size of the program. -/


/-- Value of an index name. -/
def idxVal (st : State) (i : Nat) : SemM Int :=
  match st.idx.lookup i with
  | some v => .ok v
  | none => .error (.unsupported "index name used before SET")

/-- Bytes of a resolved item. -/
def readBytes (st : State) (d : FieldDesc) : List UInt8 := st.mem.read d.off d.len

/-- Replace the bytes of a resolved item. -/
def writeBytes (st : State) (d : FieldDesc) (bs : List UInt8) : State :=
  { st with mem := st.mem.write d.off bs }

/-- Numeric value and scale of a resolved numeric item. -/
def numOf (c : Config) (st : State) (d : FieldDesc) : SemM (Int × Int) :=
  match d.kind with
  | .num f =>
    match decodeNum c f (readBytes st d) with
    | some v => .ok (v, f.scale)
    | none => .error .invalidData
  | _ => .error (.unsupported "non-numeric item used as a number")

/-- Value of a subscript / reference-modification operand. -/
def evalSub (c : Config) (st : State) : SubExpr → SemM Int
  | .lit n => .ok n
  | .ref d k =>
    match numOf c st d with
    | .error e => .error e
    | .ok (v, s) => if s = 0 then .ok (v + k) else .error (.unsupported "non-integer subscript")
  | .idx i k =>
    match idxVal st i with
    | .error e => .error e
    | .ok v => .ok (v + k)

/-- Byte offset after applying subscripts. -/
def subsOff (c : Config) (st : State) : List Subscript → Nat → SemM Nat
  | [], off => .ok off
  | s :: ss, off =>
    match evalSub c st s.e with
    | .error e => .error e
    | .ok k =>
      if 1 ≤ k ∧ k ≤ s.max then subsOff c st ss (off + (k.toNat - 1) * s.stride)
      else .error .range

/-- Reference modification of a descriptor at offset `off`. -/
def refMod (c : Config) (st : State) (d : FieldDesc) (off : Nat) (rm : RefMod) : SemM FieldDesc :=
  match evalSub c st rm.start with
  | .error e => .error e
  | .ok start =>
    let lenR := match rm.len with
      | some l => evalSub c st l
      | none => .ok ((d.len : Int) - start + 1)
    match lenR with
    | .error e => .error e
    | .ok len =>
      if 1 ≤ start ∧ 1 ≤ len ∧ start + len - 1 ≤ d.len then
        .ok { off := off + (start - 1).toNat, len := len.toNat, kind := .alnum }
      else .error .range

/-- Effective descriptor of a reference: subscripts, then reference modification (whose
result is alphanumeric). -/
def resolve (c : Config) (st : State) : DataRef → SemM FieldDesc
  | ⟨_, d, [], none⟩ => .ok d
  | ⟨_, d, subs, rm⟩ =>
    match subsOff c st subs d.off with
    | .error e => .error e
    | .ok off =>
      match rm with
      | none => .ok { d with off := off }
      | some rm => refMod c st d off rm

/-! ## Storing numeric values -/

/-- Wrap `v` into the binary range of an `n`-byte item (two's complement if signed). -/
def wrapBin (n : Nat) (signed : Bool) (v : Int) : Int :=
  if signed then (v + binHalf n) % (binMod n : Int) - binHalf n else v % (binMod n : Int)

/-- `v` is in the binary range of an `n`-byte item. -/
def inBinRange (n : Nat) (signed : Bool) (v : Int) : Bool :=
  if signed then -(binHalf n : Int) ≤ v ∧ v < binHalf n else 0 ≤ v ∧ v < binMod n

/-- Decimal capacity check: overflow flag and high-order-truncated value. -/
def fitDec (n : Nat) (v : Int) : Bool × Int :=
  if v.natAbs < 10 ^ n then (false, v) else (true, truncDigits v n)

/-- Binary capacity check: overflow flag and wrapped value. -/
def fitBin (n : Nat) (signed : Bool) (v : Int) : Bool × Int :=
  if inBinRange n signed v then (false, v) else (true, wrapBin n signed v)

/-- For a result `v` already at the scale of item `f`: whether it overflows the item (size
error), and the value that is stored when overflow is not trapped.  Unsigned items store
the absolute value. -/
def fitNum (c : Config) (f : NumFmt) (v : Int) : Bool × Int :=
  let v1 : Int := if f.signed then v else (v.natAbs : Int)
  if f.fullBinary c then fitBin (c.binBytes f.digits) f.signed v1 else fitDec f.digits v1

/-- An overflowing store whose result is unpredictable rather than truncated. -/
def overflowUndefined (c : Config) (f : NumFmt) : Bool :=
  f.usage == .binary && c.trunc == .opt

/-- Store `v` (at the item's scale) as `MOVE` does: truncation, never a size error. -/
def storeMove (c : Config) (st : State) (d : FieldDesc) (f : NumFmt) (v : Int) : SemM State :=
  let r := fitNum c f v
  if r.1 && overflowUndefined c f then .error .sizeUndefined
  else .ok (writeBytes st d (encodeNum c f r.2))

/-! ## Alphanumeric helpers -/

/-- Left-justify `bs` in `len` bytes: truncate or pad with spaces on the right. -/
def padRight (c : Config) (bs : List UInt8) (len : Nat) : List UInt8 :=
  (bs ++ List.replicate (len - bs.length) c.space).take len

/-- Right-justify `bs` in `len` bytes (`JUSTIFIED RIGHT`): truncate or pad on the left. -/
def padLeft (c : Config) (bs : List UInt8) (len : Nat) : List UInt8 :=
  if len ≤ bs.length then bs.drop (bs.length - len)
  else List.replicate (len - bs.length) c.space ++ bs

/-- Repeat `pat` to exactly `len` bytes. -/
def fillPattern (pat : List UInt8) (len : Nat) : List UInt8 :=
  (List.range len).map (fun i => pat.getD (i % pat.length) 0)

/-- Bytes of a figurative constant (one repetition). -/
def figBytes (c : Config) : Figurative → List UInt8
  | .zero => [c.zeroChar]
  | .space => [c.space]
  | .high => [0xFF]
  | .low => [0x00]
  | .quote => [c.quote]
  | .all bs => bs

/-- `width` unsigned digit characters of `n`. -/
def digitChars (c : Config) (width n : Nat) : List UInt8 :=
  (Digits.toDigits 10 width n).map c.digitByte

/-- Number of decimal digits of `n` (at least 1). -/
def numDigits (n : Nat) : Nat := go n n
where
  go : Nat → Nat → Nat
    | 0, _ => 1
    | fuel + 1, n => if n < 10 then 1 else go fuel (n / 10) + 1

/-- An alphanumeric sender read as an unsigned integer `DISPLAY` item. -/
def alnumAsInt (c : Config) (bs : List UInt8) : SemM Int :=
  match decodeNum c { digits := bs.length } bs with
  | some v => .ok v
  | none => .error .invalidData

/-! ## Alphanumeric intrinsic functions -/

/-- `FUNCTION UPPER-CASE` of one character: the 26 letters `a`-`z` become `A`-`Z` (IBM: by
their EBCDIC positions, whatever the code page); every other character is unchanged. -/
def upperByte (c : Config) (b : UInt8) : UInt8 :=
  match c.charset with
  | .ascii => if 0x61 ≤ b && b ≤ 0x7A then b - 0x20 else b
  | .ebcdic =>
    if (0x81 ≤ b && b ≤ 0x89) || (0x91 ≤ b && b ≤ 0x99) || (0xA2 ≤ b && b ≤ 0xA9) then b + 0x40
    else b

/-- `FUNCTION LOWER-CASE` of one character: `A`-`Z` become `a`-`z`. -/
def lowerByte (c : Config) (b : UInt8) : UInt8 :=
  match c.charset with
  | .ascii => if 0x41 ≤ b && b ≤ 0x5A then b + 0x20 else b
  | .ebcdic =>
    if (0xC1 ≤ b && b ≤ 0xC9) || (0xD1 ≤ b && b ≤ 0xD9) || (0xE2 ≤ b && b ≤ 0xE9) then b - 0x40
    else b

/-- An alphanumeric function applied to its argument's characters (same length). -/
def applyAfn (c : Config) : AlnumFn → List UInt8 → List UInt8
  | .upperCase, bs => bs.map (upperByte c)
  | .lowerCase, bs => bs.map (lowerByte c)
  | .reverse, bs => bs.reverse

/-- Characters of an alphanumeric function argument (an alphanumeric item, an alphanumeric
literal or another alphanumeric function); for `.afn f a`, the function's value. -/
def afnArg (c : Config) (st : State) : Operand → SemM (List UInt8)
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      match d.kind with
      | .num _ => .error (.unsupported "intrinsic function of a numeric item")
      | _ => .ok (readBytes st d)
  | .alnum bs => .ok bs
  | .afn f a =>
    match afnArg c st a with
    | .error e => .error e
    | .ok bs => .ok (applyAfn c f bs)
  | _ => .error (.unsupported "intrinsic function of a numeric literal or figurative constant")

/-! ## Collating sequences: `ORD`, `CHAR`, alphanumeric `MAX` / `MIN` -/

/-- Lexicographic comparison of byte strings of equal length by the collating positions `pos`
(`pos[b]` for byte `b`): characters that share a position compare equal. -/
def cmpSeq (pos : List Nat) : List UInt8 → List UInt8 → Ordering
  | a :: as, b :: bs =>
    let x := pos.getD a.toNat 0
    let y := pos.getD b.toNat 0
    if x < y then .lt else if y < x then .gt else cmpSeq pos as bs
  | _, _ => .eq

/-- The value `v` (at scale `s`) of an argument that must be an integer. -/
def intOf (v s : Int) : SemM Int :=
  if s ≤ 0 then .ok (v * 10 ^ (-s).toNat)
  else if v % 10 ^ s.toNat = 0 then .ok (v / 10 ^ s.toNat)
  else .error (.unsupported "non-integer argument of FUNCTION CHAR")

/-- Characters of `FUNCTION CHAR`, of an alphanumeric `MAX` / `MIN` and of their alphanumeric
arguments (items, literals, functions). `CHAR` of a position outside the collating sequence is a
`range` fault (IBM: the argument must be at least 1 and at most the number of positions). -/
def fnBytes (c : Config) (st : State) : Operand → SemM (List UInt8)
  | .chr a chars =>
    let n : SemM Int := match a with
      | .ref r =>
        match resolve c st r with
        | .error e => .error e
        | .ok d =>
          match numOf c st d with
          | .error e => .error e
          | .ok (v, s) => intOf v s
      | .num v s _ => intOf v s
      | _ => .error (.unsupported "FUNCTION CHAR of a non-numeric argument")
    match n with
    | .error e => .error e
    | .ok k => if 1 ≤ k ∧ k ≤ chars.length then .ok [chars.getD (k.toNat - 1) 0] else .error .range
  | .amax mx a b pos =>
    match fnBytes c st a with
    | .error e => .error e
    | .ok x =>
      match fnBytes c st b with
      | .error e => .error e
      | .ok y =>
        let n := max x.length y.length
        let o := cmpSeq pos (padRight c x n) (padRight c y n)
        .ok (if (if mx then o == .lt else o == .gt) then y else x)
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      match d.kind with
      | .num _ => .error (.unsupported "intrinsic function of a numeric item")
      | _ => .ok (readBytes st d)
  | .alnum bs => .ok bs
  | .afn f a => afnArg c st (.afn f a)
  | _ => .error (.unsupported "intrinsic function of a numeric literal or figurative constant")

/-- `fnBytes` of each argument. -/
def fnBytesAll (c : Config) (st : State) : List Operand → SemM (List (List UInt8))
  | [] => .ok []
  | o :: os =>
    match fnBytes c st o with
    | .error e => .error e
    | .ok b =>
      match fnBytesAll c st os with
      | .error e => .error e
      | .ok bs => .ok (b :: bs)

/-- Position (from 1) of the leftmost greatest (`mx`) or least of byte strings of equal length,
compared by the collating positions `pos`; `k` = position of the head, `best` / `bi` = the
greatest (least) so far and its position. -/
def pickIdxGo (pos : List Nat) (mx : Bool) : List (List UInt8) → Nat → List UInt8 → Nat → Nat
  | [], _, _, bi => bi
  | v :: vs, k, best, bi =>
    let o := cmpSeq pos v best
    if (if mx then o == .gt else o == .lt) then pickIdxGo pos mx vs (k + 1) v k
    else pickIdxGo pos mx vs (k + 1) best bi

/-- `ORD-MAX` (`mx`) / `ORD-MIN` of alphanumeric values: they are compared padded with spaces to
a common length (as in a relation condition). -/
def pickIdx (c : Config) (pos : List Nat) (mx : Bool) (vs : List (List UInt8)) : Nat :=
  let n := (vs.map List.length).foldl max 0
  match vs.map (fun v => padRight c v n) with
  | [] => 0
  | p :: ps => pickIdxGo pos mx ps 2 p 1

/-! ## `MOVE` -/

/-- The sending operand of a `MOVE`, evaluated once before the receivers. -/
inductive SrcVal where
  /-- Alphanumeric-category bytes (`group = true`: a group, never converted). -/
  | bytes (bs : List UInt8) (group : Bool)
  /-- A numeric item: its raw bytes and format (decoded only if a receiver needs the value). -/
  | numItem (bs : List UInt8) (f : NumFmt)
  /-- A numeric literal. -/
  | numLit (v : Int) (scale : Int) (digits : Nat)
  | fig (f : Figurative)

/-- Evaluate the sender; also returns its storage range (for the overlap check). -/
def srcVal (c : Config) (st : State) : Operand → SemM (SrcVal × Option FieldDesc)
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      let bs := readBytes st d
      match d.kind with
      | .group => .ok (.bytes bs true, some d)
      | .num f => .ok (.numItem bs f, some d)
      | _ => .ok (.bytes bs false, some d)
  | .num v s n => .ok (.numLit v s n, none)
  | .alnum bs => .ok (.bytes bs false, none)
  | .fig f => .ok (.fig f, none)
  | .afn f a =>
    match afnArg c st (.afn f a) with
    | .error e => .error e
    | .ok bs => .ok (.bytes bs false, none)
  | .chr a cs =>
    match fnBytes c st (.chr a cs) with
    | .error e => .error e
    | .ok bs => .ok (.bytes bs false, none)
  | .amax mx a b pos =>
    match fnBytes c st (.amax mx a b pos) with
    | .error e => .error e
    | .ok bs => .ok (.bytes bs false, none)

/-- A numeric value moved into a resolved receiver.  `width` = number of integer digit
positions of the sender (for alphanumeric receivers). -/
def numInto (c : Config) (st : State) (v s : Int) (width : Nat) (d : FieldDesc) :
    SemM State :=
  match d.kind with
  | .num f => storeMove c st d f (rescale .truncation v s f.scale)
  | .numEdited pic bwz =>
    match Edit.edit c pic bwz v s with
    | some bs => .ok (writeBytes st d bs)
    | none => .error (.unsupported "numeric-edited picture")
  | .alnum just =>
    if s ≤ 0 then
      let bs := digitChars c width (v.natAbs * 10 ^ (-s).toNat)
      .ok (writeBytes st d (if just then padLeft c bs d.len else padRight c bs d.len))
    else .error (.unsupported "non-integer numeric item moved to an alphanumeric item")
  | .group =>
    if s ≤ 0 then
      .ok (writeBytes st d (padRight c (digitChars c width (v.natAbs * 10 ^ (-s).toNat)) d.len))
    else .error (.unsupported "non-integer numeric literal moved to a group")

/-- Integer digit positions of a numeric item (including `P` scaling positions). -/
def intWidth (f : NumFmt) : Nat := (f.digits - f.scale).toNat

/-- Move an evaluated sender into one resolved receiver. -/
def moveInto (c : Config) (st : State) (sv : SrcVal) (d : FieldDesc) : SemM State :=
  match sv with
  | .bytes bs true =>
    match d.kind with
    | .alnum true => .ok (writeBytes st d (padLeft c bs d.len))
    | _ => .ok (writeBytes st d (padRight c bs d.len))
  | .bytes bs false =>
    match d.kind with
    | .group => .ok (writeBytes st d (padRight c bs d.len))
    | .alnum just => .ok (writeBytes st d (if just then padLeft c bs d.len else padRight c bs d.len))
    | .num f =>
      match alnumAsInt c bs with
      | .error e => .error e
      | .ok v => storeMove c st d f (rescale .truncation v 0 f.scale)
    | .numEdited _ _ =>
      match alnumAsInt c bs with
      | .error e => .error e
      | .ok v => numInto c st v 0 bs.length d
  | .numItem bs f =>
    match d.kind with
    | .group => .ok (writeBytes st d (padRight c bs d.len))
    | _ =>
      match decodeNum c f bs with
      | some v => numInto c st v f.scale (intWidth f) d
      | none => .error .invalidData
  | .numLit v s n =>
    numInto c st v s (if n = 0 then numDigits (v.natAbs * 10 ^ (-s).toNat) else n) d
  | .fig fg =>
    match fg, d.kind with
    | .zero, .num f => storeMove c st d f 0
    | .zero, .numEdited _ _ => numInto c st 0 0 1 d
    | _, _ => .ok (writeBytes st d (fillPattern (figBytes c fg) d.len))

/-- Two storage ranges share a byte but are not identical. -/
def badOverlap (a b : FieldDesc) : Bool :=
  a.off < b.off + b.len && b.off < a.off + a.len && !(a.off == b.off && a.len == b.len)

/-- Move an evaluated sender into each receiver in turn (each receiver's subscripts are
evaluated just before it is stored). -/
def moveList (c : Config) (sv : SrcVal) (sd : Option FieldDesc) : State → List DataRef → SemM State
  | st, [] => .ok st
  | st, r :: rs =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      let res : SemM State := match sd with
        | some s => if badOverlap s d then .error .overlap else moveInto c st sv d
        | none => moveInto c st sv d
      match res with
      | .error e => .error e
      | .ok st' => moveList c sv sd st' rs

/-! ### De-editing

IBM: "When the sending item is numeric-edited, the compiler de-edits the sending data to
establish the unedited value of the numeric-edited item (this value can be signed). The
unedited numeric value is used in the move to the receiving numeric or numeric-edited data
item."  The unedited value of an edited content is the value it is the editing of: the digits
of the digit positions (a position that zero suppression, replacement or floating insertion
filled holds a leading zero), scaled by the picture's decimal point, with the sign that
editing shows.  Content that no value edits to (IBM does not define its unedited value) is
invalid data. -/

/-- The digits of the digit positions of edited content `bs` laid out by the positions `ps`
(`Edit.classify`), as a number (`acc`: the digits so far); a digit position that holds no
digit counts as 0. -/
def editDigits (c : Config) : List Edit.Pos → List UInt8 → Nat → Nat
  | [], _, acc => acc
  | .implied :: ps, bs, acc => editDigits c ps bs acc
  | .fixed s :: ps, bs, acc => editDigits c ps (bs.drop (Edit.width s)) acc
  | .digit _ :: ps, b :: bs, acc => editDigits c ps bs (acc * 10 + (c.decDigit b).getD 0)
  | _ :: ps, _ :: bs, acc => editDigits c ps bs acc
  | _ :: _, [], acc => acc

/-- The unedited value of a numeric-edited item with picture `pic` (`bwz`: `BLANK WHEN ZERO`)
holding `bs`, at the scale of the picture's decimal places: the value read from the digit
positions, positive or negative, whose editing gives `bs` back.  `invalidData` if no value
edits to `bs`; `unsupported` for a picture that editing does not model. -/
def deEdit (c : Config) (pic : List ESym) (bwz : Bool) (bs : List UInt8) : SemM (Int × Int) :=
  let ps := (Edit.classify pic).getD []
  let f : Int := Edit.fracDigits ps
  let v : Int := editDigits c ps bs 0
  match Edit.edit c pic bwz v f with
  | none => .error (.unsupported "numeric-edited picture")
  | some e =>
    if e == bs then .ok (v, f)
    else if Edit.edit c pic bwz (-v) f == some bs then .ok (-v, f)
    -- a negative value that editing truncated to zero (`-0.00`): zero (negative zero is not
    -- modelled)
    else if v == 0 && Edit.edit c pic bwz (-1) (f + 1) == some bs then .ok (0, f)
    else .error .invalidData

/-- `moveList` for a numeric-edited sender `s` (picture `pic`, `bwz`) whose content is `bs`:
a numeric or numeric-edited receiver gets the de-edited value, aligned, truncated and edited
as from a numeric sender (`numInto`); any other receiver is stored as from an alphanumeric
sender (`moveInto`). -/
def moveListE (c : Config) (bs : List UInt8) (s : FieldDesc) (pic : List ESym) (bwz : Bool) :
    State → List DataRef → SemM State
  | st, [] => .ok st
  | st, r :: rs =>
    match resolve c st r with
    | .error e => .error e
    | .ok d =>
      let res : SemM State :=
        if badOverlap s d then .error .overlap
        else match d.kind with
          | .num _ | .numEdited _ _ =>
            match deEdit c pic bwz bs with
            | .error e => .error e
            | .ok (v, sc) => numInto c st v sc 0 d
          | _ => moveInto c st (.bytes bs false) d
      match res with
      | .error e => .error e
      | .ok st' => moveListE c bs s pic bwz st' rs

/-- `MOVE src TO dsts`: the sender is evaluated once; each receiver's subscripts are
evaluated just before it is stored.  A numeric-edited item as the sender takes `moveListE`
(de-editing), every other sender `moveList`. -/
def move (c : Config) (st : State) (src : Operand) (dsts : List DataRef) : SemM State :=
  match srcVal c st src with
  | .error e => .error e
  | .ok (sv, sd) =>
    match sv, sd with
    | .bytes bs false, some s =>
      match s.kind with
      | .numEdited pic bwz => moveListE c bs s pic bwz st dsts
      | _ => moveList c sv sd st dsts
    | _, _ => moveList c sv sd st dsts

end Sem
end Cobol
