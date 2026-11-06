import EquivLean.Modernize.Cbtrn03c.JavaW.Zoned

/-!
# CBTRN03C → Java: what `edit` returns

`edS`/`edB`: the characters `edit`'s loop appends and its flag, in the loop's order; `editJ`: the
whole result, from `m = |v| % 10 ^ 11`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

def comma : JChar := BitVec.ofNat 16 44

/-- Whether `edit`'s loop has seen a nonzero digit of `D` after `i` steps. -/
def edB (D : JStr) : Nat → Bool
  | 0 => false
  | i + 1 => edB D i || D.getD i 0 != digitJ 0

/-- The characters `edit`'s loop appends in `i` steps: a comma (a space before the first nonzero
digit) before digits 3 and 6, each digit (a space for a leading zero). -/
def edS (D : JStr) : Nat → JStr
  | 0 => []
  | i + 1 => edS D i ++ (if i = 3 ∨ i = 6 then [if edB D i then comma else space] else []) ++
      [if edB D (i + 1) then D.getD i 0 else space]

/-- The sign `edit` writes: `-` for a negative amount, else `+` or a space. -/
def signJ (neg plus : Bool) : JChar :=
  if neg then BitVec.ofNat 16 45 else if plus then BitVec.ofNat 16 43 else space

/-- What `edit(v, plus)` returns, from `m = |v| % 10 ^ 11`. -/
def editJ (neg plus : Bool) (m : Nat) : JStr :=
  if m = 0 then spJ 15
  else signJ neg plus :: (edS (zpadJ m 11) 9 ++
    [BitVec.ofNat 16 46, (zpadJ m 11).getD 9 0, (zpadJ m 11).getD 10 0])

end EquivLean.Modernize.Cbtrn03c.Java
