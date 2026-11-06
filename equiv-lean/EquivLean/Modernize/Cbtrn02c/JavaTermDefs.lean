-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermDefs.lean (sha256 2aebefaaf9d19121...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunAsm
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java: definitions for the termination of `run`

The split VC (`Jimple.TermVC.of_thin`) with `run_vcX`'s invariants (`runInvX`) and a variant per cut
point (`runVs`), read from the frame. With `X i = 2^31 - i` for an `int` counter `i`
(`0 < X i ≤ 2^32`):
* the main loop (65: `X next` with `next` local 14, the end-of-file flag `z` local 4; 75, after
  `validateTran`): `2 X + 2` at 65 before the end of the input, `2 X + 1` once `z` is set, `2 X + 3`
  at 75 (the read increments `next`); the exit 83: `0`;
* the straight-line cut points 48, 44, 35: `2^34`, `2^34 + 1`, `2^34 + 2`, above the main loop;
* the category copy loop (22, `i` local 15): `2^34 + 3 + X i`; the account copy loop (12, `i`
  local 15): `2^34 + 3 + 2^33 + X i`, above the category loop.
`RunThinWPcX`: the source's `RunWPcX` with calls by `callWPThin` and the postcondition `True`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The variants of `run`'s cut points 12, 22, 35, 44, 48, 65, 75, 83. Written with `if` on the
    cut point, not by matching on the literals. -/
def runVs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 12 then
    (match fr.get 15 with
     | some (.int i) => 25769803779 + (2147483648 - i.toInt).toNat
     | _ => 0)
  else if pc = 22 then
    (match fr.get 15 with
     | some (.int i) => 17179869187 + (2147483648 - i.toInt).toNat
     | _ => 0)
  else if pc = 35 then 17179869186
  else if pc = 44 then 17179869185
  else if pc = 48 then 17179869184
  else if pc = 65 then
    (match fr.get 14, fr.get 4 with
     | some (.int i), some (.int z) => 2 * (2147483648 - i.toInt).toNat + (if z = 0 then 2 else 1)
     | _, _ => 0)
  else if pc = 75 then
    (match fr.get 14 with
     | some (.int i) => 2 * (2147483648 - i.toInt).toNat + 3
     | _ => 0)
  else 0

/-- The thin symbolic execution of `run`'s body from `pc` against the cut list `cuts`. -/
def RunThinWPcX (_g : G) (_σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog runCX.env 1) runBodyT cuts (fun _ => True) 60 pc fr σ

attribute [irreducible] RunThinWPcX

theorem RunThinWPcX_eq (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    RunThinWPcX g σ0 cuts pc fr σ =
      bodyWP Gen.prog (callWPThin Gen.prog runCX.env 1) runBodyT cuts (fun _ => True) 60 pc fr σ := by
  unfold RunThinWPcX; rfl

theorem runInvX_keys (g : G) (k : Nat) (h : k ∉ [12, 22, 35, 44, 48, 65, 75, 83]) :
    ∀ p ∈ runInvX g, p.1 ≠ k := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [runInvX, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e => h1 e.symm
  · exact fun e => h2 e.symm
  · exact fun e => h3 e.symm
  · exact fun e => h4 e.symm
  · exact fun e => h5 e.symm
  · exact fun e => h6 e.symm
  · exact fun e => h7 e.symm
  · exact fun e => h8 e.symm

end EquivLean.Modernize.Cbtrn02c.Java
