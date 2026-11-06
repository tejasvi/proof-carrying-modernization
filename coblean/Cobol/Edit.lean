/-
# Numeric editing

`edit c pic bwz v s` is the content of a numeric-edited item with picture `pic` after
`MOVE`-ing the value `v * 10^(-s)` into it (standard editing rules):

* digit positions: `9`, `Z`, `*`, and every floating insertion symbol after the first;
* the value is aligned on the decimal point (`.` or `V`) and truncated at both ends;
* zero suppression (`Z`, `*`) and floating insertion (`$$`, `++`, `--`) replace leading
  zeros up to the first non-zero digit, the first `9`, or the decimal point; simple
  insertion characters (`,` `B` `0` `/`) inside the suppressed part are replaced too, and
  so are those right before the decimal point when the whole integer part is suppressed
  (IBM: they are part of the string), but not those left of the string, before its first
  symbol; the floating symbol goes immediately left of the first significant digit or of the
  decimal point;
* fixed `+` / `-` / `CR` / `DB` / `$` insertion;
* a zero value with no `9` position gives all spaces (`Z`, floating) or all `*` except the
  decimal point (`*`); `BLANK WHEN ZERO` gives all spaces.

A picture that starts with `.chars d m s` (programs with `DECIMAL-POINT IS COMMA` or `CURRENCY
SIGN`; the front end writes the picture with the standard roles of `.`, `,` and `$`) is edited
without it, and every `.`, `,` and `$` of the result becomes `d`, `m` and `s`.

`P` positions in edited pictures and floating strings extending past the decimal point are
not modelled (`none`).
-/
import Cobol.Data
import Cobol.Digits
import Cobol.Round

namespace Cobol.Edit

/-- Printable width of a picture symbol. -/
def width : ESym → Nat
  | .v | .p => 0
  | .cr | .db => 2
  | .chars .. => 0
  | _ => 1

/-- Picture width in bytes. -/
def picWidth (pic : List ESym) : Nat := (pic.map width).sum

/-- The floating insertion symbol of a picture (two or more of `$`, `+` or `-`). -/
def floatSym (pic : List ESym) : Option ESym :=
  if (pic.filter (· == .cs)).length ≥ 2 then some .cs
  else if (pic.filter (· == .plus)).length ≥ 2 then some .plus
  else if (pic.filter (· == .minus)).length ≥ 2 then some .minus
  else none

/-- Classification of each picture position. -/
inductive Pos where
  /-- digit position, with its suppression kind (`none` for `9`) -/
  | digit (supp : Option ESym)
  /-- the first symbol of a floating string (no digit) -/
  | floatHead
  | insert (s : ESym)
  | point
  | implied
  | fixed (s : ESym)
  deriving DecidableEq, Repr

/-- Classify the positions of a picture (`storeEdited` and `arithList` read the receiver's
digit positions from it, so a leading `.chars` is skipped). -/
def classify (pic : List ESym) : Option (List Pos) :=
  let fs := floatSym pic
  let rec go (seenFloat : Bool) : List ESym → Option (List Pos)
    | [] => some []
    | s :: rest =>
      let here : Option (Pos × Bool) :=
        match s with
        | .nine => some (.digit none, seenFloat)
        | .z => some (.digit (some .z), seenFloat)
        | .star => some (.digit (some .star), seenFloat)
        | .comma | .b | .zero | .slash => some (.insert s, seenFloat)
        | .dot => some (.point, seenFloat)
        | .v => some (.implied, seenFloat)
        | .p => none
        | .cr | .db => some (.fixed s, seenFloat)
        | .cs | .plus | .minus =>
          if fs == some s then
            if seenFloat then some (.digit (some s), true) else some (.floatHead, true)
          else some (.fixed s, seenFloat)
        | .chars .. => none
      match here with
      | none => none
      | some (p, sf) => (go sf rest).map (p :: ·)
  -- a leading `.chars` holds no position (`edit`); anywhere else the picture is malformed
  go false (match pic with | .chars .. :: rest => rest | _ => pic)

/-- Number of digit positions after the decimal point. -/
def fracDigits (ps : List Pos) : Nat :=
  let after := ps.dropWhile (fun p => p != .point && p != .implied)
  (after.filter (fun p => match p with | .digit _ => true | _ => false)).length

/-- Number of digit positions. -/
def numDigitPos (ps : List Pos) : Nat :=
  (ps.filter (fun p => match p with | .digit _ => true | _ => false)).length

/-- No floating string runs into the fraction part. -/
def floatBeforePoint (ps : List Pos) : Bool :=
  let after := ps.dropWhile (fun p => p != .point && p != .implied)
  after.all (fun p => match p with
    | .digit (some .cs) | .digit (some .plus) | .digit (some .minus) | .floatHead => false
    | _ => true)

/-- Character of a symbol in the platform character set. -/
def symChar (c : Config) : ESym → UInt8
  | .comma => c.chr 0x2C
  | .b => c.space
  | .zero => c.zeroChar
  | .slash => c.chr 0x2F
  | .dot => c.chr 0x2E
  | .cs => c.chr 0x24
  | .plus => c.plusChar
  | .minus => c.minusChar
  | .star => c.chr 0x2A
  | _ => c.space

/-- Sign character shown by a `+` / `-` symbol. -/
def signChar (c : Config) (s : ESym) (neg : Bool) : UInt8 :=
  match s with
  | .plus => if neg then c.minusChar else c.plusChar
  | _ => if neg then c.minusChar else c.space

/-- Bytes of a fixed insertion symbol. -/
def fixedBytes (c : Config) (s : ESym) (neg : Bool) : List UInt8 :=
  match s with
  | .cs => [c.chr 0x24]
  | .plus | .minus => [signChar c s neg]
  | .cr => if neg then [c.chr 0x43, c.chr 0x52] else [c.space, c.space]
  | .db => if neg then [c.chr 0x44, c.chr 0x42] else [c.space, c.space]
  | _ => []

/-- Editing proper. -/
def editOpt (c : Config) (pic : List ESym) (bwz : Bool) (v s : Int) : Option (List UInt8) := do
  let ps ← classify pic
  if !floatBeforePoint ps then none
  let n := numDigitPos ps
  let f := fracDigits ps
  let i := n - f
  let mag := (rescale .truncation v s f).natAbs % 10 ^ n
  let ds := Digits.toDigits 10 n mag
  let neg := decide (v < 0)
  let zero := mag = 0
  let allSupp := ps.all (fun p => p != .digit none)
  let suppKind : Option ESym :=
    ps.findSome? (fun p => match p with | .digit (some k) => some k | _ => none)
  if bwz && zero then return List.replicate (picWidth pic) c.space
  if zero && allSupp then
    -- all positions suppressed
    if suppKind == some .star then
      -- the whole item, fixed insertion symbols included, except the decimal point
      return (ps.flatMap (fun p => match p with
        | .point => [c.chr 0x2E] | .implied => [] | .fixed k => List.replicate (width k) (c.chr 0x2A)
        | _ => [c.chr 0x2A]))
    else return List.replicate (picWidth pic) c.space
  -- index of the first significant digit
  let firstNine := (ps.filter (fun p => match p with | .digit _ => true | _ => false)).findIdx?
    (· == .digit none)
  let firstNZ := ds.findIdx? (· != 0)
  let k0 := min i (min (firstNine.getD n) (firstNZ.getD n))
  -- produce (byte, isSuppressedFloatPosition), consuming digits left to right
  let rec gen (j : Nat) : List Pos → List (UInt8 × Bool)
    | [] => []
    | p :: rest =>
      match p with
      | .digit k =>
        let b : UInt8 × Bool :=
          if j < k0 then
            match k with
            | some .star => (c.chr 0x2A, false)
            | some .z => (c.space, false)
            | _ => (c.space, true)
          else (c.digitByte (ds.getD j 0), false)
        b :: gen (j + 1) rest
      | .floatHead => (c.space, true) :: gen j rest
      | .insert sym =>
        -- suppressed: part of the string (a digit position, or the floating string's first
        -- symbol, on its left) and left of the first significant digit, or between the last
        -- integer position and the decimal point when no integer digit is significant
        let b : UInt8 × Bool :=
          if j ≤ k0 ∧ (0 < j ∨ ([some .cs, some .plus, some .minus].contains suppKind ∧
                rest.all (· != .floatHead))) ∧
              (j < i ∨ (j = i ∧ 0 < i ∧ rest.any (fun p => p == .point || p == .implied))) then
            match suppKind with
            | some .star => (c.chr 0x2A, false)
            | some .z => (c.space, false)
            | some _ => (c.space, true)
            | none => (symChar c sym, false)
          else (symChar c sym, false)
        b :: gen j rest
      | .point => (symChar c .dot, false) :: gen j rest
      | .implied => gen j rest
      | .fixed sym => (fixedBytes c sym neg).map (·, false) ++ gen j rest
  let out := gen 0 ps
  match floatSym pic with
  | none => return out.map (·.1)
  | some fsym =>
    -- the floating symbol replaces the last suppressed floating position
    let lastIdx := (out.zipIdx.filter (fun (x, _) => x.2)).getLast?.map (·.2)
    let symB := if fsym == .cs then c.chr 0x24 else signChar c fsym neg
    return out.zipIdx.map (fun (x, idx) => if some idx == lastIdx then symB else x.1)

/-- A byte of an edited result under `.chars d m s`: the standard `.`, `,` and `$` become `d`,
`m` and `s` (no other symbol writes those three bytes). -/
def mapChar (c : Config) (d m s b : UInt8) : UInt8 :=
  if b == c.chr 0x2E then d else if b == c.chr 0x2C then m else if b == c.chr 0x24 then s else b

/-- Editing; malformed / unmodelled pictures give `none`. -/
def edit (c : Config) (pic : List ESym) (bwz : Bool) (v s : Int) : Option (List UInt8) :=
  match pic with
  | .chars d m cs :: rest => (editOpt c rest bwz v s).map (List.map (mapChar c d m cs))
  | _ => editOpt c pic bwz v s

end Cobol.Edit
