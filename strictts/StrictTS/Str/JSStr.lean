/-
StrictTS: ECMAScript String values as sequences of UTF-16 code units.
-/

namespace StrictTS

/-- An ECMAScript String value: a finite sequence of UTF-16 code units
(lone surrogates included). `"😀".length = 2` holds in this model as in JavaScript. -/
structure JSStr where
  units : List UInt16
  deriving DecidableEq, Hashable, Inhabited

namespace JSStr

def empty : JSStr := ⟨[]⟩

instance : EmptyCollection JSStr := ⟨empty⟩

/-- `s.length` (number of code units). -/
def length (s : JSStr) : Nat := s.units.length

instance : Append JSStr := ⟨fun a b => ⟨a.units ++ b.units⟩⟩

@[simp] theorem units_append (a b : JSStr) : (a ++ b).units = a.units ++ b.units := rfl

/-- UTF-16 encoding of one Unicode scalar value. -/
def encodeChar (c : Char) : List UInt16 :=
  let n := c.toNat
  if n < 0x10000 then [n.toUInt16]
  else
    let m := n - 0x10000
    [(0xD800 + m / 0x400).toUInt16, (0xDC00 + m % 0x400).toUInt16]

/-- UTF-16 encoding of a Lean string (Lean strings contain no surrogate code points). -/
def ofString (s : String) : JSStr := ⟨s.toList.flatMap encodeChar⟩

instance : Coe String JSStr := ⟨ofString⟩

/-- Decode for display; a lone surrogate becomes U+FFFD. -/
def toLeanString (s : JSStr) : String :=
  String.ofList (go s.units [])
where
  unit (u : UInt16) : Char :=
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xE000 then Char.ofNat 0xFFFD else Char.ofNat u.toNat
  -- (tail recursive: console lines of a long run must not exhaust the interpreter's stack)
  go : List UInt16 → List Char → List Char
  | [], acc => acc.reverse
  | [u], acc => (unit u :: acc).reverse
  | u :: v :: rest, acc =>
    let n := u.toNat
    let k := v.toNat
    if 0xD800 ≤ n ∧ n < 0xDC00 ∧ 0xDC00 ≤ k ∧ k < 0xE000 then
      go rest (Char.ofNat (0x10000 + (n - 0xD800) * 0x400 + (k - 0xDC00)) :: acc)
    else go (v :: rest) (unit u :: acc)

instance : ToString JSStr := ⟨toLeanString⟩
instance : Repr JSStr := ⟨fun s _ => repr s.toLeanString⟩

/-- ECMAScript IsLessThan on strings: lexicographic order on code units. -/
def lt : JSStr → JSStr → Bool
  | ⟨as⟩, ⟨bs⟩ => go as bs
where
  go : List UInt16 → List UInt16 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else go as bs


/-! ## String operations (ECMA-262 §22.1.3) on code units

Arguments that are JavaScript numbers in the source program arrive already converted: the
translator applies the spec's `ToIntegerOrInfinity`, maps `±∞` to any integer beyond the string
bounds, and resolves `undefined` defaults as documented on each function. -/

/-- String literal from a list of code units. -/
def ofUnits (l : List UInt16) : JSStr := ⟨l⟩

/-- `0xD800 ≤ u < 0xDC00`. -/
def isLeadSurrogate (u : UInt16) : Bool := decide (0xD800 ≤ u.toNat) && decide (u.toNat < 0xDC00)

/-- `0xDC00 ≤ u < 0xE000`. -/
def isTrailSurrogate (u : UInt16) : Bool := decide (0xDC00 ≤ u.toNat) && decide (u.toNat < 0xE000)

/-- UTF16SurrogatePairToCodePoint. -/
def surrogatePair (lead trail : UInt16) : Nat :=
  0x10000 + (lead.toNat - 0xD800) * 0x400 + (trail.toNat - 0xDC00)

/-- UTF16EncodeCodePoint for `cp ≤ 0x10FFFF` (lone surrogate code points encode as themselves). -/
def encodeCodePoint (cp : Nat) : List UInt16 :=
  if cp < 0x10000 then [cp.toUInt16]
  else [(0xD800 + (cp - 0x10000) / 0x400).toUInt16, (0xDC00 + (cp - 0x10000) % 0x400).toUInt16]

/-- `s.charCodeAt(i)`; `none` is `NaN` (`i ≥ s.length`; the translator maps negative `i` to `none`). -/
def charCodeAt? (s : JSStr) (i : Nat) : Option UInt16 := s.units[i]?

/-- Code points of a code unit list: surrogate pairs combined, lone surrogates kept. -/
def decodeUnits : List UInt16 → List Nat
  | [] => []
  | [u] => [u.toNat]
  | u :: v :: rest =>
    if isLeadSurrogate u && isTrailSurrogate v then surrogatePair u v :: decodeUnits rest
    else u.toNat :: decodeUnits (v :: rest)

/-- `s.codePointAt(i)` (CodePointAt): `none` is `undefined` (`i ≥ s.length`). -/
def codePointAt? (s : JSStr) (i : Nat) : Option Nat :=
  match s.units.drop i with
  | [] => none
  | [u] => some u.toNat
  | u :: v :: _ => some (if isLeadSurrogate u && isTrailSurrogate v then surrogatePair u v else u.toNat)

/-- `s.charAt(i)`: the code unit at `i` as a string, `""` when out of range. -/
def charAt (s : JSStr) (i : Nat) : JSStr :=
  match s.units[i]? with
  | some u => ⟨[u]⟩
  | none => empty

/-- `s.at(i)`: negative `i` counts from the end; `none` is `undefined`. -/
def at? (s : JSStr) (i : Int) : Option JSStr :=
  let k : Int := if 0 ≤ i then i else (s.length : Int) + i
  if k < 0 then none else (s.units[k.toNat]?).map fun u => ⟨[u]⟩

/-- The substring from `a` (inclusive) to `b` (exclusive); empty when `b ≤ a`. -/
def sub (s : JSStr) (a b : Nat) : JSStr := ⟨(s.units.drop a).take (b - a)⟩

/-- Relative index of `slice`: negative values count from the end, result clamped to `[0, len]`. -/
def relIndex (len : Nat) (i : Int) : Nat :=
  if i < 0 then ((len : Int) + i).toNat else min i.toNat len

/-- `s.slice(start, stop)`; pass `stop := s.length` for an omitted end. -/
def slice (s : JSStr) (start stop : Int) : JSStr :=
  s.sub (relIndex s.length start) (relIndex s.length stop)

/-- `s.substring(a, b)`: both clamped to `[0, len]`, then ordered; pass `b := s.length` if omitted. -/
def substring (s : JSStr) (a b : Int) : JSStr :=
  let a' := min a.toNat s.length
  let b' := min b.toNat s.length
  s.sub (min a' b') (max a' b')

/-- First `i` (counting from `i₀`, where `rest = l.drop i₀`) at which `pat` occurs. -/
def findFrom (pat : List UInt16) : List UInt16 → Nat → Option Nat
  | [], i => if pat.isPrefixOf [] then some i else none
  | c :: t, i => if pat.isPrefixOf (c :: t) then some i else findFrom pat t (i + 1)

/-- StringIndexOf(s, pat, start) for `start ≤ s.length`. -/
def indexOfNat? (s pat : JSStr) (start : Nat) : Option Nat :=
  findFrom pat.units (s.units.drop start) start

/-- `s.indexOf(pat, pos)` (`pos` defaults to `0`; it is clamped to `s.length`); `-1` if absent. -/
def indexOf (s pat : JSStr) (pos : Nat) : Int :=
  match s.indexOfNat? pat (min pos s.length) with
  | some i => i
  | none => -1

/-- Last match position `≤ start`, scanning `rest = l.drop i`. -/
def findLast (pat : List UInt16) (start : Nat) : List UInt16 → Nat → Option Nat → Option Nat
  | rest, i, acc =>
    if start < i then acc
    else
      let acc' := if pat.isPrefixOf rest then some i else acc
      match rest with
      | [] => acc'
      | _ :: t => findLast pat start t (i + 1) acc'

/-- `s.lastIndexOf(pat, pos)`; pass `pos := s.length` for an omitted, `NaN` or `+∞` position. -/
def lastIndexOf (s pat : JSStr) (pos : Nat) : Int :=
  match findLast pat.units (min pos s.length) s.units 0 none with
  | some i => i
  | none => -1

/-- `s.includes(pat, pos)` (`pos` defaults to `0`). -/
def includes (s pat : JSStr) (pos : Nat) : Bool :=
  (s.indexOfNat? pat (min pos s.length)).isSome

/-- `s.startsWith(pat, pos)` (`pos` defaults to `0`). -/
def startsWith (s pat : JSStr) (pos : Nat) : Bool :=
  pat.units.isPrefixOf (s.units.drop (min pos s.length))

/-- `s.endsWith(pat, endPos)`; pass `endPos := s.length` when omitted. -/
def endsWith (s pat : JSStr) (endPos : Nat) : Bool :=
  let e := min endPos s.length
  decide (pat.length ≤ e) && ((s.units.take e).drop (e - pat.length) == pat.units)

/-- WhiteSpace or LineTerminator (§12.2, §12.3): TAB VT FF SP NBSP ZWNBSP, the `Zs` code points
U+1680, U+2000–U+200A, U+202F, U+205F, U+3000, and LF CR LS PS. (U+180E is not included.) -/
def isWhiteSpaceOrLT (u : UInt16) : Bool :=
  let n := u.toNat
  n == 0x09 || n == 0x0A || n == 0x0B || n == 0x0C || n == 0x0D || n == 0x20 || n == 0xA0 ||
  n == 0x1680 || (decide (0x2000 ≤ n) && decide (n ≤ 0x200A)) || n == 0x2028 || n == 0x2029 ||
  n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

/-- `s.trimStart()`. -/
def trimStart (s : JSStr) : JSStr := ⟨s.units.dropWhile isWhiteSpaceOrLT⟩

/-- `s.trimEnd()`. -/
def trimEnd (s : JSStr) : JSStr := ⟨(s.units.reverse.dropWhile isWhiteSpaceOrLT).reverse⟩

/-- `s.trim()`. -/
def trim (s : JSStr) : JSStr := s.trimStart.trimEnd

/-- The first `n` code units of `fill` repeated (`[]` for an empty `fill`). -/
def fillUnits (fill : List UInt16) (n : Nat) : List UInt16 :=
  if fill.isEmpty then [] else ((List.replicate (n / fill.length + 1) fill).flatten).take n

/-- `s.padStart(maxLen, fill)`; pass `fill := " "` when omitted. -/
def padStart (s : JSStr) (maxLen : Nat) (fill : JSStr) : JSStr :=
  if maxLen ≤ s.length ∨ fill.units = [] then s
  else ⟨fillUnits fill.units (maxLen - s.length) ++ s.units⟩

/-- `s.padEnd(maxLen, fill)`; pass `fill := " "` when omitted. -/
def padEnd (s : JSStr) (maxLen : Nat) (fill : JSStr) : JSStr :=
  if maxLen ≤ s.length ∨ fill.units = [] then s
  else ⟨s.units ++ fillUnits fill.units (maxLen - s.length)⟩

/-- `s.repeat(n)` (the translator raises the RangeError for negative or infinite counts). -/
def «repeat» (s : JSStr) (n : Nat) : JSStr := ⟨(List.replicate n s.units).flatten⟩

/-- Parts of `rest` split at the non-overlapping, leftmost occurrences of the non-empty `sep`;
`cur` is the part read so far. `fuel > rest.length` makes the result exact. -/
def splitParts (sep : List UInt16) : Nat → List UInt16 → List UInt16 → List (List UInt16)
  | 0, rest, cur => [cur ++ rest]
  | fuel + 1, rest, cur =>
    match rest with
    | [] => [cur]
    | c :: t =>
      if sep.isPrefixOf rest then cur :: splitParts sep fuel (rest.drop sep.length) []
      else splitParts sep fuel t (cur ++ [c])

/-- `s.split(sep, limit)` for a string separator; `limit = none` is `undefined` (lim = 2³² − 1),
`some n` is `ToUint32(limit)`. An empty separator splits into code units. -/
def split (s sep : JSStr) (limit : Option Nat) : List JSStr :=
  let lim := limit.getD (2 ^ 32 - 1)
  if lim = 0 then []
  else if sep.units = [] then (s.units.take lim).map fun u => ⟨[u]⟩
  else if s.units = [] then [s]
  else ((splitParts sep.units (s.length + 1) s.units []).take lim).map JSStr.mk

/-- `parts.join(sep)` for an array of strings. -/
def join (sep : JSStr) (parts : List JSStr) : JSStr :=
  ⟨List.intercalate sep.units (parts.map units)⟩

/-- GetSubstitution with no captures: `$$`, `` $` ``, `$&`, `$'`; every other `$` is literal. -/
def substitute (matched pre post : List UInt16) : List UInt16 → List UInt16
  | [] => []
  | [c] => [c]
  | c :: d :: t =>
    if c == 36 then
      if d == 36 then 36 :: substitute matched pre post t
      else if d == 38 then matched ++ substitute matched pre post t
      else if d == 96 then pre ++ substitute matched pre post t
      else if d == 39 then post ++ substitute matched pre post t
      else c :: substitute matched pre post (d :: t)
    else c :: substitute matched pre post (d :: t)

/-- `s.replace(pat, repl)` with string pattern and string replacement. -/
def replaceFirst (s pat repl : JSStr) : JSStr :=
  match s.indexOfNat? pat 0 with
  | none => s
  | some p =>
    let pre := s.units.take p
    let post := s.units.drop (p + pat.length)
    ⟨pre ++ substitute pat.units pre post repl.units ++ post⟩

/-- Match positions of `replaceAll`: from `i`, then from `p + max 1 patLen` after each match. -/
def matchPositions (s pat : JSStr) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, i =>
    if s.length < i then []
    else match s.indexOfNat? pat i with
      | none => []
      | some p => p :: matchPositions s pat fuel (p + max 1 pat.length)

/-- `s.replaceAll(pat, repl)` with string pattern and string replacement. -/
def replaceAll (s pat repl : JSStr) : JSStr :=
  let ps := matchPositions s pat (s.length + 2) 0
  let step : List UInt16 × Nat → Nat → List UInt16 × Nat := fun (acc, last) p =>
    let pre := s.units.take p
    let post := s.units.drop (p + pat.length)
    (acc ++ (s.units.drop last).take (p - last) ++ substitute pat.units pre post repl.units,
      p + pat.length)
  let (acc, last) := ps.foldl step ([], 0)
  ⟨acc ++ s.units.drop last⟩

/-- `s.concat(...args)`. -/
def concat (s : JSStr) (args : List JSStr) : JSStr := args.foldl (· ++ ·) s

/-- Every code unit is below 0x80. -/
def isASCII (s : JSStr) : Bool := s.units.all fun u => decide (u.toNat < 0x80)

/-- `toUpperCase` on ASCII letters; other code units unchanged (exact for ASCII strings). -/
def toUpperASCII (s : JSStr) : JSStr :=
  ⟨s.units.map fun u => if decide (97 ≤ u.toNat) && decide (u.toNat ≤ 122) then u - 32 else u⟩

/-- `toLowerCase` on ASCII letters; other code units unchanged (exact for ASCII strings). -/
def toLowerASCII (s : JSStr) : JSStr :=
  ⟨s.units.map fun u => if decide (65 ≤ u.toNat) && decide (u.toNat ≤ 90) then u + 32 else u⟩

/-- `String.fromCharCode(...codes)` with `ToUint16` (reduction mod 2¹⁶). -/
def fromCharCodes (codes : List Nat) : JSStr := ⟨codes.map Nat.toUInt16⟩

/-- `String.fromCodePoint(...cps)`; `none` is the RangeError for a code point above 0x10FFFF
(non-integral or negative arguments are rejected by the translator). -/
def fromCodePoint? (cps : List Nat) : Option JSStr :=
  if cps.all (· ≤ 0x10FFFF) then some ⟨cps.flatMap encodeCodePoint⟩ else none

/-- The code points visited by `for (const c of s)` (lone surrogates as themselves). -/
def codePoints (s : JSStr) : List Nat := decodeUnits s.units

/-- Lexicographic order on code units, consistent with `lt`. -/
def compare (a b : JSStr) : Ordering := go a.units b.units
where
  go : List UInt16 → List UInt16 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else go as bs

/-- `a <= b` on strings. -/
def le (a b : JSStr) : Bool := !lt b a

/-- `a > b` on strings. -/
def gt (a b : JSStr) : Bool := lt b a

/-- `a >= b` on strings. -/
def ge (a b : JSStr) : Bool := !lt a b

end JSStr
end StrictTS
