/-
# `INSPECT`

IBM Enterprise COBOL semantics of `INSPECT … TALLYING / REPLACING / CONVERTING` on the bytes
of the inspected item.  A signed numeric `DISPLAY` item is inspected without its sign (see
`inspView` below); every other item as its bytes.

* Each phrase has a region: from after the first occurrence of its `AFTER INITIAL` delimiter
  (no occurrence: empty region) to before the first occurrence of its `BEFORE INITIAL`
  delimiter (no occurrence: the end of the item), both located in the item before the scan.
  When the first `BEFORE` occurrence lies before the end of the `AFTER` delimiter,
  implementations differ (GnuCOBOL searches the `BEFORE` delimiter after the `AFTER` one) and
  the model reports the statement as unsupported.
* The item is scanned left to right.  At each position the phrases are tried in the order
  written; the first one that matches there (its whole pattern inside its region) counts
  (`TALLYING`) or is replaced (`REPLACING`), and the scan continues after the pattern; if none
  matches, the scan moves one character.  `CHARACTERS` matches any one character; `LEADING`
  only contiguous occurrences from the start of its region; `FIRST` only once.
* `TALLYING … REPLACING …` acts as two statements: the counters are incremented by the
  occurrences (an `ADD`), then the replacements are made.  `CONVERTING src TO dst` replaces
  every character of `src` in the region by the character at the same position of `dst`.
* A figurative constant is one character as a pattern or a delimiter, and as long as the
  pattern as a replacement.
-/
import Cobol.Sem.Arith

namespace Cobol
namespace Sem

/-- Index of the first occurrence of `p` in a byte string. -/
def findSub (p : List UInt8) : List UInt8 → Option Nat
  | [] => if p.isEmpty then some 0 else none
  | b :: bs => if p.isPrefixOf (b :: bs) then some 0 else (findSub p bs).map (· + 1)

/-- The region `lo ..< hi` of a phrase in the item `s`, or `none` when it depends on how the
`BEFORE` delimiter is located: with both delimiters, the standard locates each by its first
occurrence in the item, GnuCOBOL (and other implementations) locate the `BEFORE` delimiter
after the `AFTER` delimiter.  The two agree unless the first `BEFORE` occurrence lies before
the end of the `AFTER` delimiter; that case is reported as unsupported. -/
def inspRegion (s : List UInt8) (before after : Option (List UInt8)) : Option (Nat × Nat) :=
  match after.map (fun a => (findSub a s).map (· + a.length)) with
  | some none => some (s.length, s.length)   -- no AFTER delimiter: empty region
  | lo? =>
    let lo := (lo?.getD none).getD 0
    match before with
    | none => some (lo, s.length)
    | some b =>
      match findSub b s with
      | some i => if after.isSome && i < lo then none else some (lo, i)
      | none => some (lo, s.length)

/-- A phrase ready for the scan: pattern (unused for `CHARACTERS`), replacement (`[]` when
tallying), region. -/
structure InspPh where
  kind : InspKind
  pat : List UInt8
  rep : List UInt8
  lo : Nat
  hi : Nat
  deriving Inhabited

/-- Scan state of a phrase: occurrences so far, next position of a `LEADING` match, `FIRST`
used. -/
structure InspSt where
  count : Nat := 0
  lead : Option Nat := none
  done : Bool := false
  deriving Inhabited

def InspPh.len (p : InspPh) : Nat :=
  match p.kind with
  | .chars => 1
  | _ => p.pat.length

/-- Phrase `p` in state `q` matches at position `i` of `s`. -/
def inspMatches (s : List UInt8) (i : Nat) (p : InspPh) (q : InspSt) : Bool :=
  decide (0 < p.len) && decide (p.lo ≤ i) && decide (i + p.len ≤ p.hi) &&
  match p.kind with
  | .chars => true
  | .all => p.pat.isPrefixOf (s.drop i)
  | .leading => q.lead == some i && p.pat.isPrefixOf (s.drop i)
  | .first => !q.done && p.pat.isPrefixOf (s.drop i)

/-- The first phrase matching at `i`. -/
def inspFirst (s : List UInt8) (i : Nat) : List InspPh → List InspSt → Option Nat
  | p :: ps, q :: qs => if inspMatches s i p q then some 0 else (inspFirst s i ps qs).map (· + 1)
  | _, _ => none

/-- `rep` written over `s` at position `i`. -/
def putAt (s : List UInt8) (i : Nat) (rep : List UInt8) : List UInt8 :=
  s.take i ++ rep ++ s.drop (i + rep.length)

/-- A `LEADING` phrase whose next position the scan has passed can no longer match. -/
def inspExpire (i : Nat) (q : InspSt) : InspSt :=
  match q.lead with
  | some j => if j < i then { q with lead := none } else q
  | none => q

/-- The scan from position `i`: final phrase states and the item after the replacements. -/
def inspScan (s : List UInt8) (ps : List InspPh) :
    Nat → Nat → List InspSt → List UInt8 → List InspSt × List UInt8
  | 0, _, qs, out => (qs, out)
  | fuel + 1, i, qs, out =>
    if s.length ≤ i then (qs, out)
    else
      let qs := qs.map (inspExpire i)
      match inspFirst s i ps qs with
      | none => inspScan s ps fuel (i + 1) qs out
      | some k =>
        let p := ps.getD k default
        let q := qs.getD k default
        let q' := { q with count := q.count + 1,
                           lead := if p.kind == .leading then some (i + p.len) else q.lead,
                           done := q.done || p.kind == .first }
        let out := if p.rep.isEmpty then out else putAt out i p.rep
        inspScan s ps fuel (i + p.len) (qs.set k q') out

/-- Initial scan states (a `LEADING` phrase may match at the start of its region). -/
def inspInit (ps : List InspPh) : List InspSt :=
  ps.map fun p => { lead := if p.kind == .leading then some p.lo else none }

/-- Bytes of an `INSPECT` operand (figurative constants: `len` characters). -/
def inspBytes (c : Config) (st : State) (len : Nat) (o : Operand) : SemM (List UInt8) :=
  cmpOperand c st len o

/-- Prepare the phrases of an `INSPECT` on the item `s`. -/
def inspPhs (c : Config) (st : State) (s : List UInt8) : List InspPhrase → SemM (List InspPh)
  | [] => .ok []
  | ph :: rest => do
    let pat ← match ph.pat with
      | some o => inspBytes c st 1 o
      | none => pure []
    let rep ← match ph.rep with
      | some o => inspBytes c st (max pat.length 1) o
      | none => pure []
    let before ← match ph.before with
      | some o => some <$> inspBytes c st 1 o
      | none => pure none
    let after ← match ph.after with
      | some o => some <$> inspBytes c st 1 o
      | none => pure none
    let (lo, hi) ← match inspRegion s before after with
      | some r => pure r
      | none => throw (.unsupported "INSPECT: BEFORE delimiter located before the AFTER delimiter")
    let rest' ← inspPhs c st s rest
    pure ({ kind := ph.kind, pat, rep, lo, hi } :: rest')

/-- `CONVERTING src TO dst`: the character for `b`. -/
def convByte (src dst : List UInt8) (b : UInt8) : UInt8 :=
  match findSub [b] src with
  | some j => dst.getD j b
  | none => b

/-- `CONVERTING` on the region `lo ..< hi` of `s`. -/
def inspConvert (s src dst : List UInt8) (lo hi : Nat) : List UInt8 :=
  s.zipIdx.map fun (b, i) => if lo ≤ i ∧ i < hi then convByte src dst b else b

/-! ### Signed numeric `DISPLAY` items

IBM (Enterprise COBOL 6.4, INSPECT statement, table 1): a signed numeric `DISPLAY` item is
inspected "as if moved to an unsigned external decimal item of usage DISPLAY with the same
length as the identifier"; "if the sign is a separate character, the byte containing the sign is
not examined and, therefore, not replaced"; the string that results from replacing or converting
is copied back to the item.  The IBM text does not say what becomes of an embedded sign on the
copy back: the model keeps the item's sign, as GnuCOBOL does.  A replacement that leaves a
non-digit in the byte carrying an embedded sign is `unsupported` (GnuCOBOL's result there is an
artefact of its ASCII encoding).  `BEFORE` / `AFTER` delimiters are located in the inspected
bytes. -/

/-- How the bytes that `INSPECT` examines relate to the item's bytes. -/
inductive InspView where
  /-- The item's bytes (alphanumeric, unsigned numeric, numeric-edited and group items). -/
  | bytes
  /-- Separate leading / trailing sign byte: left out, and kept on the copy back. -/
  | sepLead (sign : UInt8)
  | sepTrail (sign : UInt8)
  /-- Embedded leading / trailing sign, removed from its byte; `plain`: that byte held a plain
  digit (a positive sign written as the unsigned digit). -/
  | embLead (neg plain : Bool)
  | embTrail (neg plain : Bool)
  deriving Inhabited

/-- The digit byte of a byte carrying an embedded sign, the sign, and whether it was a plain
digit; `invalidData` when the byte encodes no signed digit. -/
def unsignByte (c : Config) (b : UInt8) : SemM (UInt8 × Bool × Bool) :=
  match c.decSign b with
  | some (neg, d) => .ok (c.digitByte d, neg, (c.decDigit b).isSome)
  | none => .error .invalidData

/-- The bytes `INSPECT` examines in an item of category `k` holding `s`, and how its result is
stored back. -/
def inspView (c : Config) (k : FieldKind) (s : List UInt8) : SemM (InspView × List UInt8) :=
  match k with
  | .num f =>
    if f.usage = .display ∧ f.signed then
      match f.signSep, f.signLead, s with
      | true, true, b :: rest => .ok (.sepLead b, rest)
      | true, false, _ =>
        match s.getLast? with
        | some b => .ok (.sepTrail b, s.dropLast)
        | none => .ok (.bytes, s)
      | false, true, b :: rest => do
        let (u, neg, plain) ← unsignByte c b
        pure (.embLead neg plain, u :: rest)
      | false, false, _ =>
        match s.getLast? with
        | some b => do
          let (u, neg, plain) ← unsignByte c b
          pure (.embTrail neg plain, s.dropLast ++ [u])
        | none => .ok (.bytes, s)
      | true, true, [] => .ok (.bytes, s)
      | false, true, [] => .ok (.bytes, s)
    else .ok (.bytes, s)
  | _ => .ok (.bytes, s)

/-- The byte carrying digit byte `b` again with the item's embedded sign. -/
def resignByte (c : Config) (neg plain : Bool) (b : UInt8) : SemM UInt8 :=
  match c.decDigit b with
  | some d => .ok (if plain then c.digitByte d else c.signByte neg d)
  | none => .error (.unsupported "INSPECT: a replacement leaves a non-digit in the byte carrying the sign")

/-- The item's bytes after an `INSPECT` whose replacements turned its examined bytes into `out`. -/
def inspUnview (c : Config) : InspView → List UInt8 → SemM (List UInt8)
  | .bytes, out => .ok out
  | .sepLead b, out => .ok (b :: out)
  | .sepTrail b, out => .ok (out ++ [b])
  | .embLead neg plain, b :: rest => do
    let b' ← resignByte c neg plain b
    pure (b' :: rest)
  | .embLead _ _, [] => .ok []
  | .embTrail neg plain, out =>
    match out.getLast? with
    | some b => do
      let b' ← resignByte c neg plain b
      pure (out.dropLast ++ [b'])
    | none => .ok out

end Sem
end Cobol
