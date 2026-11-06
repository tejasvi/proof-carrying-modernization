import EquivLean.Demo.Gen.Aeneas.Adler32Rs.Funs
import EquivLean.Demo.XLang.Adler32.Model

/-!
# zlib adler32 → safe Rust: the Rust runs, their inputs and the model's values

The safe Rust translation (`examples/rust/adler32_rs`, extracted by Charon + Aeneas into
`EquivLean.Demo.Gen.Aeneas.Adler32Rs`) is called as the C is.

* `adler32_z(adler, buf, len)` and `adler32(adler, buf, len)`: an input `ZInput` is `adler`, the
  buffer (`none` is `Z_NULL`) and the length passed with `Z_NULL`; with a buffer, `len` is the
  buffer's length (`zLen`).  `zLong x`: `len ≥ 2^28`.  The model's value is `adler32z` on the bytes
  (`Z_NULL` gives 1 whatever `len`; with `len == 1` the C reads `buf[0]`, undefined behaviour).
  `adler32` gets `len` as a `uInt` (exact below `2^28`).
* `adler32_combine` and `adler32_combine64(adler1, adler2, len2)`: every input (`cbLong` is
  `False`); the model's value is `combine`.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Demo.XLang.Adler32

/-- The bytes of a slice, as the model's list. -/
def bytesOf (s : Slice U8) : List Nat := s.val.map (·.val)

/-- An input of `adler32_z` and `adler32`: `adler`, the buffer (`none` is `Z_NULL`) and the length
passed with `Z_NULL` (with a buffer, `len` is the buffer's length). -/
abbrev ZInput := U64 × Option (Slice U8) × Usize

/-- The `len` argument: the buffer's length, or the length passed with `Z_NULL`. -/
def zLen (x : ZInput) : Usize :=
  match x.2.1 with
  | some b => Slice.len b
  | none => x.2.2

/-- The excluded inputs: `len ≥ 2^28`. -/
def zLong (x : ZInput) : Prop := 2 ^ 28 ≤ (zLen x).val

/-- `adler32_z(adler, buf, len)` in Rust. -/
def zRun (x : ZInput) : Result U64 := adler32_rs.adler32_z x.1 x.2.1 (zLen x)

/-- `adler32(adler, buf, len)` in Rust (`len` as a `uInt`). -/
def run32 (x : ZInput) : Result U64 := adler32_rs.adler32 x.1 x.2.1 (UScalar.cast .U32 (zLen x))

/-- The model's value of `adler32_z` and `adler32`. -/
def zModel (x : ZInput) : Nat := adler32z x.1.val (x.2.1.map bytesOf)

/-- An input of `adler32_combine` and `adler32_combine64`: `adler1`, `adler2`, `len2`. -/
abbrev CbInput := U64 × U64 × I64

/-- No input of the combine functions is excluded. -/
def cbLong (_ : CbInput) : Prop := False

/-- `adler32_combine(adler1, adler2, len2)` in Rust. -/
def cbRun (x : CbInput) : Result U64 := adler32_rs.adler32_combine x.1 x.2.1 x.2.2

/-- `adler32_combine64(adler1, adler2, len2)` in Rust. -/
def cb64Run (x : CbInput) : Result U64 := adler32_rs.adler32_combine64 x.1 x.2.1 x.2.2

/-- The model's value of the combine functions. -/
def cbModel (x : CbInput) : Nat := combine x.1.val x.2.1.val x.2.2.val

end EquivLean.Demo.XLang.Adler32
