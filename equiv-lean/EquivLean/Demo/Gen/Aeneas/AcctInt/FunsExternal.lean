-- Hand-written model of the external functions of [acctint], replacing the axioms of the
-- Aeneas template (examples/rust/acctint/FunsExternal_Template.lean).
module
public import Aeneas
public import EquivLean.Demo.Gen.Aeneas.AcctInt.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
open acctint

/-- [core::num::{i128}::abs]: `if self < 0 { -self } else { self }` with the caller's overflow
checks (`#[rustc_inherit_overflow_checks]`), i.e. the checked negation Aeneas uses for `-x`:
`i128::MIN.abs()` panics with an integer overflow. -/
def core.num.I128.abs (x : Std.I128) : Result Std.I128 :=
  if x.val < 0 then -. x else ok x
