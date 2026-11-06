/-
# Resolved data descriptors

`FieldDesc` is what every data reference of the normalized IR carries after resolution: the
byte offset and length of the item in the program's storage and its category.  Descriptors
are computed from the hierarchical data division by `Cobol.Layout` (trusted Lean code), not
by the extractor.
-/
import Cobol.Config

namespace Cobol

/-- `USAGE` of an elementary item. -/
inductive Usage where
  /-- `DISPLAY` (zoned decimal for numeric items). -/
  | display
  /-- `COMP-3` / `PACKED-DECIMAL`. -/
  | packed
  /-- `COMP` / `COMP-4` / `BINARY` (subject to `TRUNC`). -/
  | binary
  /-- `COMP-5` (native binary, full binary range, never `PICTURE`-truncated). -/
  | comp5
  deriving DecidableEq, Repr, Inhabited

/-- Format of an elementary numeric item.  The item's value is `stored * 10^(-scale)`.

* `PIC S9(7)V99` is `{digits := 9, scale := 2, signed := true}`.
* `PIC 99PPP` (scaled left) is `{digits := 2, scale := -3}`.
* `PIC VPP99` (scaled right) is `{digits := 2, scale := 4}`. -/
structure NumFmt where
  digits : Nat
  scale : Int := 0
  signed : Bool := false
  usage : Usage := .display
  /-- `SIGN IS ... SEPARATE CHARACTER` (DISPLAY only). -/
  signSep : Bool := false
  /-- `SIGN IS LEADING` (DISPLAY only). -/
  signLead : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Numeric-editing picture symbols (repetition factors expanded). -/
inductive ESym where
  | nine | z | star | cs | plus | minus | dot | comma | b | zero | slash | cr | db | v | p
  /-- Not a position: the bytes written where the standard `.`, `,` and `$` would be
  (`DECIMAL-POINT IS COMMA`, `CURRENCY SIGN`). Only first in a picture (`Edit.edit`). -/
  | chars (dotCh commaCh csCh : UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- Category of a (resolved) data item. -/
inductive FieldKind where
  /-- Group item: its bytes, never converted. -/
  | group
  /-- Alphanumeric / alphabetic elementary item (`PIC X(n)`, `PIC A(n)`). -/
  | alnum (just : Bool := false)
  /-- Numeric elementary item. -/
  | num (f : NumFmt)
  /-- Numeric-edited item (`PIC ZZ,ZZ9.99-` ...), `BLANK WHEN ZERO` flag. -/
  | numEdited (pic : List ESym) (bwz : Bool := false)
  deriving DecidableEq, Repr, Inhabited

/-- Resolved descriptor: byte offset and length in program storage, and category. -/
structure FieldDesc where
  off : Nat
  len : Nat
  kind : FieldKind
  deriving DecidableEq, Repr, Inhabited

/-- Storage size of a numeric item. -/
def NumFmt.byteLen (c : Config) (f : NumFmt) : Nat :=
  match f.usage with
  | .display => f.digits + (if f.signed && f.signSep then 1 else 0)
  | .packed => f.digits / 2 + 1
  | .binary | .comp5 => c.binBytes f.digits

/-- The item is binary with full binary range (`COMP-5`, or `COMP` under `TRUNC(BIN)`). -/
def NumFmt.fullBinary (c : Config) (f : NumFmt) : Bool :=
  match f.usage with
  | .comp5 => true
  | .binary => c.trunc == .bin
  | _ => false

/-- `2^(8n)`: number of distinct values of an `n`-byte binary item. -/
def binMod (n : Nat) : Nat := 2 ^ (8 * n)

/-- `2^(8n-1)`: bound of the signed range of an `n`-byte binary item. -/
def binHalf (n : Nat) : Nat := 2 ^ (8 * n - 1)

theorem binMod_eq_two_mul {n : Nat} (hn : 0 < n) : binMod n = 2 * binHalf n := by
  unfold binMod binHalf; rw [← Nat.pow_succ']; congr 1; omega

/-- The values an item can hold: the binary range for full-binary items, otherwise
magnitude below `10^digits` (and non-negative when unsigned). -/
def NumFmt.Holds (c : Config) (f : NumFmt) (v : Int) : Prop :=
  if f.fullBinary c then
    (if f.signed then -(binHalf (c.binBytes f.digits) : Int) ≤ v ∧ v < binHalf (c.binBytes f.digits)
     else 0 ≤ v ∧ v < binMod (c.binBytes f.digits))
  else
    v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v)

instance (c : Config) (f : NumFmt) (v : Int) : Decidable (f.Holds c v) := by
  unfold NumFmt.Holds; exact inferInstance

end Cobol
