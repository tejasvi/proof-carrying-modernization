/-
  Jimple/JString.lean

  `java.lang.String` values are sequences of UTF-16 code units, exactly as in the JVM.
  They are modelled as Lean lists of 16-bit vectors, so `length`, `charAt`, `substring`,
  `concat` and `equals` are `List.length`, indexing, `drop`/`take`, `++` and `=`.
-/
import Jimple.Numeric

namespace Jimple

abbrev JChar := BitVec 16
abbrev JStr := List JChar

namespace JStr

def ofChar (c : Char) : JStr :=
  let n := c.toNat
  if n < 0x10000 then [BitVec.ofNat 16 n]
  else
    let m := n - 0x10000
    [BitVec.ofNat 16 (0xD800 + m / 0x400), BitVec.ofNat 16 (0xDC00 + m % 0x400)]

/-- UTF-16 encoding of a Lean string. -/
def ofString (s : String) : JStr := s.toList.flatMap ofChar

instance : Coe String JStr := ⟨ofString⟩

/-- UTF-16 decoding, one code unit at a time (`pend`: a high surrogate awaiting its low
    half), accumulating characters in reverse; lone surrogates become U+FFFD. -/
def decodeAux : List JChar → Option Nat → List Char → List Char
  | [], none, acc => acc.reverse
  | [], some _, acc => (Char.ofNat 0xFFFD :: acc).reverse
  | c :: rest, some hi, acc =>
    let n := c.toNat
    if 0xDC00 ≤ n ∧ n < 0xE000 then
      decodeAux rest none (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (n - 0xDC00)) :: acc)
    else if 0xD800 ≤ n ∧ n < 0xDC00 then decodeAux rest (some n) (Char.ofNat 0xFFFD :: acc)
    else decodeAux rest none (Char.ofNat n :: Char.ofNat 0xFFFD :: acc)
  | c :: rest, none, acc =>
    let n := c.toNat
    if 0xD800 ≤ n ∧ n < 0xDC00 then decodeAux rest (some n) acc
    else if 0xDC00 ≤ n ∧ n < 0xE000 then decodeAux rest none (Char.ofNat 0xFFFD :: acc)
    else decodeAux rest none (Char.ofNat n :: acc)

/-- Decode to a Lean string (for printing and parsing); lone surrogates become U+FFFD. -/
def toLean (s : JStr) : String := String.ofList (decodeAux s none [])

instance : Repr JStr := ⟨fun s _ => repr (toLean s)⟩

/-- `String.hashCode`: `s[0]*31^(n-1) + ... + s[n-1]` in `int` arithmetic. -/
def hashCode (s : JStr) : I32 := s.foldl (fun h c => h * 31 + c.zeroExtend 32) 0

/-- `String.compareTo`: first differing code unit, else length difference. -/
def compareTo : JStr → JStr → I32
  | [], [] => 0
  | [], ys => BitVec.ofInt 32 (-(ys.length : Int))
  | xs, [] => BitVec.ofInt 32 xs.length
  | x :: xs, y :: ys =>
    if x = y then compareTo xs ys else BitVec.ofInt 32 ((x.toNat : Int) - y.toNat)

def isPrefixOf : JStr → JStr → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && isPrefixOf xs ys

/-- `indexOf(String)`: least `i ≥ 0` with `pat` a prefix of `drop i s`, else `-1`. -/
def indexOf (s pat : JStr) : Int :=
  let rec go : JStr → Nat → Int
    | [], i => if pat.isEmpty then i else -1
    | t@(_ :: rest), i => if isPrefixOf pat t then i else go rest (i + 1)
  go s 0

def isAsciiLetterUpper (c : JChar) : Bool := 65 ≤ c.toNat ∧ c.toNat ≤ 90
def isAsciiLetterLower (c : JChar) : Bool := 97 ≤ c.toNat ∧ c.toNat ≤ 122
def isAscii (s : JStr) : Bool := s.all (fun c => c.toNat < 128)
def asciiUpper (s : JStr) : JStr := s.map (fun c => if isAsciiLetterLower c then c - 32 else c)
def asciiLower (s : JStr) : JStr := s.map (fun c => if isAsciiLetterUpper c then c + 32 else c)

/-- `Character.isWhitespace`-free `String.trim`: strips code units `≤ U+0020`. -/
def trim (s : JStr) : JStr :=
  let p : JChar → Bool := fun c => c.toNat ≤ 32
  ((s.dropWhile p).reverse.dropWhile p).reverse

/-- Decimal rendering of an integer (`Integer.toString`, `Long.toString`). -/
def ofInt (i : Int) : JStr := ofString (toString i)

end JStr

end Jimple
