/-
StrictTS: Unicode default case conversion (`String.prototype.toUpperCase` / `toLowerCase`),
used by `Impl.host` for non-ASCII strings. The semantics leaves non-ASCII case mapping to the
`Impl` parameter (theorems hold for every implementation); this is the runner's
implementation, from the tables of `StrictTS.Str.CaseTables` (generated from Node's ICU by
tools/gen_case_tables.js): full mappings (SpecialCasing's unconditional ones included, e.g.
`ß` ↦ `SS`, `İ` ↦ `i̇`) and the context-dependent Final_Sigma rule of `toLowerCase`. Lone
surrogates are left unchanged.
-/
import StrictTS.Str.JSStr
import StrictTS.Str.CaseTables

namespace StrictTS
namespace CaseTables

/-- The image of `c` under single-code-point runs `(first, last, step, delta)`. -/
def lookupRuns (rs : Array (Nat × Nat × Nat × Int)) (c : Nat) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:rs.size] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, b, st, d) := rs[mid]!
    if c < a then hi := mid
    else if c > b then lo := mid + 1
    else return if (c - a) % st == 0 then some (Int.toNat (c + d)) else none
  return none

/-- The image of `c` in a table of several-code-point results. -/
def lookupMulti (ms : Array (Nat × List Nat)) (c : Nat) : Option (List Nat) := Id.run do
  let mut lo := 0
  let mut hi := ms.size
  for _ in [0:ms.size] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, xs) := ms[mid]!
    if c < a then hi := mid
    else if c > a then lo := mid + 1
    else return some xs
  return none

/-- Membership in a sorted list of ranges. -/
def inRanges (rs : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:rs.size] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, b) := rs[mid]!
    if c < a then hi := mid
    else if c > b then lo := mid + 1
    else return true
  return false

/-- UTF-16 code units to code points (a lone surrogate stands for itself). -/
def decode : List UInt16 → List Nat
  | [] => []
  | u :: v :: rest =>
    if 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF ∧ 0xDC00 ≤ v.toNat ∧ v.toNat ≤ 0xDFFF then
      (0x10000 + (u.toNat - 0xD800) * 0x400 + (v.toNat - 0xDC00)) :: decode rest
    else u.toNat :: decode (v :: rest)
  | [u] => [u.toNat]

/-- One code point (or lone surrogate) to UTF-16 code units. -/
def encode (c : Nat) : List UInt16 :=
  if c < 0x10000 then [c.toUInt16]
  else [(0xD800 + (c - 0x10000) / 0x400).toUInt16, (0xDC00 + (c - 0x10000) % 0x400).toUInt16]

def upper1 (c : Nat) : List Nat :=
  match lookupMulti upperMulti c with
  | some xs => xs
  | none => [(lookupRuns upperRuns c).getD c]

def lower1 (c : Nat) : List Nat :=
  match lookupMulti lowerMulti c with
  | some xs => xs
  | none => [(lookupRuns lowerRuns c).getD c]

/-- Final_Sigma (Unicode §3.13, as ICU decides it): the capital sigma at `i` is preceded by a
cased letter and not followed by one, case-ignorable characters skipped (a character that is
both is skipped). -/
def finalSigma (cs : Array Nat) (i : Nat) : Bool := Id.run do
  let mut before := false
  let mut j := i
  for _ in [0:i] do
    j := j - 1
    let c := cs[j]!
    if inRanges caseIgnorable c then continue
    before := inRanges cased c
    break
  if !before then return false
  let mut k := i + 1
  for _ in [0:cs.size] do
    if k ≥ cs.size then break
    let c := cs[k]!
    if inRanges caseIgnorable c then k := k + 1; continue
    return !inRanges cased c
  return true

end CaseTables

namespace JSStr
open CaseTables

/-- `toUpperCase` with the Unicode default case mapping. -/
def toUpperFull (s : JSStr) : JSStr :=
  ⟨((decode s.units).flatMap upper1).flatMap encode⟩

/-- `toLowerCase` with the Unicode default case mapping (Final_Sigma included). -/
def toLowerFull (s : JSStr) : JSStr :=
  let cs := (decode s.units).toArray
  ⟨((List.range cs.size).flatMap fun i =>
      let c := cs[i]!
      if c == 0x3A3 then [if finalSigma cs i then 0x3C2 else 0x3C3] else lower1 c).flatMap encode⟩

end JSStr
end StrictTS
