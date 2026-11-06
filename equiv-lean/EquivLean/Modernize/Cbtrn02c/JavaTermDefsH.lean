-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermDefsH.lean (sha256 dd3265ba88f0d0e0...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xb2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5c
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt0
import EquivLean.Modernize.TermCommon

/-!
# CBTRN02C → Java: definitions for the termination of the helpers proved by segments

The thin symbolic executions of `writeTransaction` (`WtThinWP`), `updateAccount` (`UaThinWP`),
`updateTcatbal` (`UtThinWPc`), `postTransaction` (`PtThinWPc`) and `validateTran` (`VtThinWPc`):
the sources' `WtWP`, `UaWP`, `UtWPc`, `PtWPc`, `VtWPc` with calls by `callWPThin` and the
postcondition `True`. Their cut points are straight-line: the variants (`utVs`, `ptVs`, `vtVs`)
decrease along the body. `lookup_map_key_none`: a cut list mapped from the invariants has no entry
where they have none.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The thin symbolic execution of `writeTransaction`'s body (no cut point). -/
def WtThinWP (_args : List Value) (_σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog wtCalleesX.env 0) wtBody [] (fun _ => True) 40 pc fr σ

/-- The thin symbolic execution of `updateAccount`'s body (no cut point). -/
def UaThinWP (_args : List Value) (_σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog uaCallees.env 0) uaBody [] (fun _ => True) 60 pc fr σ

/-- The thin symbolic execution of `updateTcatbal`'s body from `pc` against the cut list `cuts`. -/
def UtThinWPc (_args : List Value) (_σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog utCallees.env 0) utBody cuts (fun _ => True) 80 pc fr σ

/-- The thin symbolic execution of `postTransaction`'s body from `pc` against the cut list `cuts`. -/
def PtThinWPc (_args : List Value) (_σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog ptCallees.env 0) ptBody cuts (fun _ => True) 80 pc fr σ

/-- The thin symbolic execution of `validateTran`'s body from `pc` against the cut list `cuts`. -/
def VtThinWPc (_args : List Value) (_σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog vtCallees.env 0) vtBodyC cuts (fun _ => True) 80 pc fr σ

attribute [irreducible] WtThinWP UaThinWP UtThinWPc PtThinWPc VtThinWPc

theorem WtThinWP_eq (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    WtThinWP args σ0 pc fr σ =
      bodyWP Gen.prog (callWPThin Gen.prog wtCalleesX.env 0) wtBody [] (fun _ => True) 40 pc fr σ := by
  unfold WtThinWP; rfl

theorem UaThinWP_eq (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    UaThinWP args σ0 pc fr σ =
      bodyWP Gen.prog (callWPThin Gen.prog uaCallees.env 0) uaBody [] (fun _ => True) 60 pc fr σ := by
  unfold UaThinWP; rfl

theorem UtThinWPc_eq (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame)
    (σ : State) : UtThinWPc args σ0 cuts pc fr σ =
      bodyWP Gen.prog (callWPThin Gen.prog utCallees.env 0) utBody cuts (fun _ => True) 80 pc fr σ := by
  unfold UtThinWPc; rfl

theorem PtThinWPc_eq (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame)
    (σ : State) : PtThinWPc args σ0 cuts pc fr σ =
      bodyWP Gen.prog (callWPThin Gen.prog ptCallees.env 0) ptBody cuts (fun _ => True) 80 pc fr σ := by
  unfold PtThinWPc; rfl

theorem VtThinWPc_eq (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame)
    (σ : State) : VtThinWPc args σ0 cuts pc fr σ =
      bodyWP Gen.prog (callWPThin Gen.prog vtCallees.env 0) vtBodyC cuts (fun _ => True) 80 pc fr σ := by
  unfold VtThinWPc; rfl

/-- `updateTcatbal`'s straight-line cut points 21, 41, 59 (from 21 to 41 or to 59). -/
def utVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 21 then 3 else if pc = 41 then 2 else if pc = 59 then 1 else 0

/-- `postTransaction`'s straight-line cut points 36, 39, 40. -/
def ptVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 36 then 3 else if pc = 39 then 2 else if pc = 40 then 1 else 0

/-- `validateTran`'s straight-line cut points 11, 17. -/
def vtVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 11 then 2 else if pc = 17 then 1 else 0

/-- A cut list mapped from the invariants, keys kept, has no entry where they have none. -/
theorem lookup_map_key_none {β γ : Type} (G : Nat × β → γ) :
    ∀ (l : List (Nat × β)) (k : Nat), (∀ p ∈ l, p.1 ≠ k) → (l.map fun q => (q.1, G q)).lookup k = none
  | [], _, _ => rfl
  | (a, b) :: l, k, h => by
    have hne : k ≠ a := fun e => h (a, b) (by simp) e.symm
    have hb : (k == a) = false := by simp [hne]
    simp only [List.map_cons, List.lookup, hb]
    exact lookup_map_key_none G l k (fun p hp => h p (List.mem_cons_of_mem _ hp))

end EquivLean.Modernize.Cbtrn02c.Java
