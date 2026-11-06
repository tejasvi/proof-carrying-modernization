/-
  Jimple/Unicode.lean

  Unicode character properties and case mappings as JDK 17's `java.lang.Character` and
  `String.toUpperCase`/`toLowerCase` (root/English locale) have them, for code points
  `0 … 0x10FFFF`: general category (`getType`), the `isUpperCase`/`isLowerCase`/`isWhitespace`/
  `isSpaceChar`/`isAlphabetic`/`isIdeographic` flags, the `toUpperCase`/`toLowerCase`/
  `toTitleCase` mappings, `getNumericValue` and `digit` beyond ASCII, and the string case
  mappings that are not one character to one character (`ß` → `SS`, `İ` → `i̇`, …). The tables
  come from `data/unidata.txt` (`data/UniDump.java`).
-/
import Jimple.UnicodeImport

namespace Jimple
unicode_tables "data/unidata.txt"
end Jimple

namespace Jimple.Unicode

/-- Index of the last entry of the sorted array `keys` that is `≤ x` (`0` if none). -/
def lastLE (keys : Array Nat) (x : Nat) : Nat :=
  go 0 keys.size 40
where
  go (lo hi : Nat) : Nat → Nat
    | 0 => lo
    | f + 1 =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if keys.getD mid 0 ≤ x then go mid hi f else go lo mid f

/-- The value of key `x` in the sorted `keys` with values `vals`. -/
def lookup (keys vals : Array Nat) (x : Nat) : Option Nat :=
  let i := lastLE keys x
  if keys.getD i 0 == x && i < keys.size then vals[i]? else none

/-- General category and flags of a code point (type · 256 + flags). -/
def props (cp : Nat) : Nat := runProps.getD (lastLE runStarts cp) 0

/-- `Character.getType`. -/
def charType (cp : Nat) : Nat := props cp / 256

def flag (cp bit : Nat) : Bool := (props cp / bit) % 2 == 1

def isUpper (cp : Nat) : Bool := flag cp 1
def isLower (cp : Nat) : Bool := flag cp 2
def isWhitespace (cp : Nat) : Bool := flag cp 4
def isSpaceChar (cp : Nat) : Bool := flag cp 8
def isAlphabetic (cp : Nat) : Bool := flag cp 16
def isIdeographic (cp : Nat) : Bool := flag cp 32
/-- `Character.isLetter`: categories Lu, Ll, Lt, Lm, Lo. -/
def isLetter (cp : Nat) : Bool := let t := charType cp; 1 ≤ t && t ≤ 5
/-- `Character.isDigit`: category Nd. -/
def isDigit (cp : Nat) : Bool := charType cp == 9
def isTitle (cp : Nat) : Bool := charType cp == 3

def toUpper (cp : Nat) : Nat := (lookup upperKeys upperVals cp).getD cp
def toLower (cp : Nat) : Nat := (lookup lowerKeys lowerVals cp).getD cp
def toTitle (cp : Nat) : Nat := (lookup titleKeys titleVals cp).getD cp

/-- `Character.getNumericValue` (`-1` none, `-2` not a non-negative integer). -/
def numericValue (cp : Nat) : Int :=
  if cp < 128 then
    if 48 ≤ cp && cp ≤ 57 then cp - 48
    else if 65 ≤ cp && cp ≤ 90 then cp - 55
    else if 97 ≤ cp && cp ≤ 122 then cp - 87
    else -1
  else match lookup numericKeys numericVals cp with
    | some v => (v : Int) - 2
    | none => -1

/-- `Character.digit(cp, radix)`. -/
def digit (cp radix : Nat) : Int :=
  if radix < 2 || radix > 36 then -1
  else
    let v? : Option Nat :=
      if cp < 128 then
        if 48 ≤ cp && cp ≤ 57 then some (cp - 48)
        else if 65 ≤ cp && cp ≤ 90 then some (cp - 55)
        else if 97 ≤ cp && cp ≤ 122 then some (cp - 87)
        else none
      else lookup digitKeys digitVals cp
    match v? with
    | some v => if v < radix then v else -1
    | none => -1

/-- The special (not one-to-one) case mapping of BMP character `c` in a string, if any:
    `kind` 0 upper case, 1 lower case. -/
def specialMap (kind c : Nat) : Option (List Nat) :=
  go 0 (special.size + 1)
where
  go (i : Nat) : Nat → Option (List Nat)
    | 0 => none
    | f + 1 =>
      if i + 2 < special.size then
        let k := special.getD i 0
        let ch := special.getD (i + 1) 0
        let n := special.getD (i + 2) 0
        if k == kind && ch == c then some ((List.range n).map fun j => special.getD (i + 3 + j) 0)
        else go (i + 3 + n) f
      else none

end Jimple.Unicode
