-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermLeafA.lean (sha256 5c38de855d8c0789...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunC
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunCT
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH2
import EquivLean.Modernize.TermCommon

/-!
# CBTRN02C → Java, termination: thin VCs of the constructors, `spaces`, `fit`, `padNum`

The thin twins of `ctorAC_vc`, `ctorXR_vc`, `ctorTC_vc` (`JavaRunC`), `ctorTR_vc` (`JavaRunCT`),
`spaces_vc`, `fit_vc` (`JavaRunH1`) and `padNum_vc` (`JavaRunH2`). The constructors have no loop;
`ctorTR`'s cut points 20, 24, 28 are straight-line (variants decreasing along the body). `spaces`
and `fit` count up to `n` (variant `n - i`); `padNum`'s first loop (statement 9) counts `i` up to `n`,
`2^32` above the second (statement 21), which counts `i` down to `-1` (variant `i + 1`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- `ctorTR`'s straight-line cut points 20, 24, 28. -/
def ctorTRVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 20 then 3 else if pc = 24 then 2 else if pc = 28 then 1 else 0

/-- `spaces`: `n - i` (locals `n` 0, `i` 1). -/
def spacesVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `fit`: `n - i` (locals `n` 0, `i` 2). -/
def fitVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 2 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `padNum`: statement 9 `2^32 + (n - i)` (locals `n` 4, `i` 6); statement 21 `i + 1` (local 4). -/
def padNumVs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 9 then
    (match fr.get 4, fr.get 6 with
     | some (.int n), some (.int i) => 4294967296 + (n.toInt - i.toInt).toNat
     | _, _ => 0)
  else if pc = 21 then
    (match fr.get 4 with
     | some (.int i) => (i.toInt + 1).toNat
     | _ => 0)
  else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorAC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorACRef ctorACSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ctorACSpec, setFields, Fields.get_set, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorXR_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorXRRef ctorXRSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ctorXRSpec, setFields, Fields.get_set, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorTC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorTCRef ctorTCSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ctorTCSpec, setFields, Fields.get_set, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorTR_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorTRRef ctorTRSpec ctorTRInv ctorTRVs 40 := by
  jthin [ctorTRSpec, ctorTRInv, ctorTRInv4, ctorTRInv8, ctorTRInv12, setFields, Fields.get_set,
    fields_get_cons, fields_get_nil, narrow_long, narrow_cls, ctorTRVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_thin :
    ThinVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [spacesSpec, spacesInv, Grows, spJ_succ, valueOfArg_char, spacesVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fit_thin :
    ThinVC Gen.prog (fun _ => none) 0 fitRef fitSpec fitInv (fun _ => fitVar) 60 := by
  jthin [fitSpec, fitInv, Grows, fitJ_zero, valueOfArg_char, jchar_rt, fitVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem padNum_thin :
    ThinVC Gen.prog (fun _ => none) 0 padNumRef padNumSpec padNumInv padNumVs 60 := by
  jthin [padNumSpec, padNumInv, Grows, valueOfArg_char, jchar_rt, digit_char3,
    sdiv10_toNat_of_nonneg, sdiv10_nonneg, cmp_zero_nonneg_iff, revD_reverse, revD_length, padNumVs]

end EquivLean.Modernize.Cbtrn02c.Java
