import EquivLean.Demo.Gen.Jimple.AcctInt
import EquivLean.Bridge.Jimple.Behaves

/-!
# `AcctInt.accrue` (Java, through javac + Soot) against a `BigDecimal` reference

The Java rewrite `examples/java/acctint/AcctInt.java` of the COBOL program ACCTINT is compiled
by `javac --release 17`, converted to Jimple by Soot 4.7.1 and imported with `jimple_import`
(`EquivLean/Demo/Gen/Jimple/AcctInt.lean`).  This file proves, on that Jimple, that every
terminating execution of `AcctInt.accrue(type, balance, rate, days)` returns a fresh
`AcctInt$Result` whose fields hold the values of `accrueD` (a reference written over
JimpleLean's `BigDec`, with COBOL-style rounding `Cobol.units`), for a non-null balance
(`accrue_sat`) and for a `null` balance (`accrue_null_sat`, the LOW-VALUES case).

Partial correctness (JimpleLean's `Sat`): see `EquivLean/Bridge/Jimple/Behaves.lean`.
Proof method: JimpleLean's VC generator with two checkpoints (cut points at statements 15 and
31 of the loop-free body; their assertions and the postcondition are kept as opaque
definitions, so that symbolic execution does not drag them through every continuation),
`jvc` on each segment (inlining depth 1 for the `AcctInt$Result` constructor), and one
leaf tactic for the returned objects.
-/

open Jimple EquivLean.Jimple EquivLean.Gen

namespace EquivLean.Demo.AcctIntJava

/-- Daily rate: `rate / 365` rounded half-up to 8 places (written with the decimal `365` so
    that it normalizes like the program's own `BigDecimal.valueOf(365)`). -/
def dailyOf (R : BigDec) : BigDec := ⟨Cobol.units 8 true (R.toRat / (⟨365, 0⟩ : BigDec).toRat), 8⟩

/-- Interest: `balance * daily * days` rounded half-up to 2 places. -/
def interestOf (D R : BigDec) (d : I32) : BigDec :=
  ⟨Cobol.units 2 true ((D.mul (dailyOf R)).mul ⟨d.toInt, 0⟩).toRat, 2⟩

/-- `BigDecimal.abs()` as JimpleLean models it (the receiver itself when non-negative). -/
def absJ (x : BigDec) : BigDec := if x.unscaled < 0 then x.negate else x

/-- Reference result of `accrue(t, D, R, d)`: (new balance, interest, status character). -/
def accrueD (t : I32) (D R : BigDec) (d : I32) : BigDec × BigDec × Int :=
  if d = 0 ∨ (t ≠ 83#32 ∧ t ≠ 67#32) then (D, ⟨0, 2⟩, 90)
  else if 0 ≤ (absJ (interestOf D R d)).compareTo ⟨1000000000, 0⟩ then (D, ⟨0, 2⟩, 69)
  else if 0 ≤ (absJ (D.add (interestOf D R d))).compareTo ⟨100000000000, 0⟩ then
    (D, interestOf D R d, 69)
  else (D.add (interestOf D R d), interestOf D R d, 75)

/-- `v` is a reference to an `AcctInt$Result` whose fields hold the values `q`. -/
def ResultIs (σ : State) (v : Option Value) (q : BigDec × BigDec × Int) : Prop :=
  ∃ c fs b i s B I, v = some (.ref c) ∧ σ.heap c = some (.plain "AcctInt$Result" fs) ∧
    Fields.get fs ("AcctInt$Result", "balance") = some (.ref b) ∧ σ.heap b = some (.dec B) ∧
    Fields.get fs ("AcctInt$Result", "interest") = some (.ref i) ∧ σ.heap i = some (.dec I) ∧
    Fields.get fs ("AcctInt$Result", "status") = some (.int s) ∧
    B.toRat = q.1.toRat ∧ I.toRat = q.2.1.toRat ∧ s.toInt = q.2.2

/-! ## Arithmetic and freshness facts used at the leaves -/

theorem eq_next0_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next1_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next2_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next3_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next4_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next5_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next6_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next7_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next8_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next9_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem eq_next10_false {x : Nat} {σ : State} (h : x < σ.next) : (x = σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False :=
  eq_false (by simp only [State.next] at h ⊢; omega)
theorem next_ne_0_1 (n : Nat) : (n = n + 1) = False := eq_false (by omega)
theorem next_ne_0_2 (n : Nat) : (n = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_3 (n : Nat) : (n = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_4 (n : Nat) : (n = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_5 (n : Nat) : (n = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_6 (n : Nat) : (n = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_7 (n : Nat) : (n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_8 (n : Nat) : (n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_9 (n : Nat) : (n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_0_10 (n : Nat) : (n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_0 (n : Nat) : (n + 1 = n) = False := eq_false (by omega)
theorem next_ne_1_2 (n : Nat) : (n + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_3 (n : Nat) : (n + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_4 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_5 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_6 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_7 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_8 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_9 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_1_10 (n : Nat) : (n + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_0 (n : Nat) : (n + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_2_1 (n : Nat) : (n + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_2_3 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_4 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_5 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_6 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_7 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_8 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_9 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_2_10 (n : Nat) : (n + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_0 (n : Nat) : (n + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_3_1 (n : Nat) : (n + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_3_2 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_4 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_5 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_6 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_7 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_8 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_9 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_3_10 (n : Nat) : (n + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_0 (n : Nat) : (n + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_4_1 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_4_2 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_3 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_5 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_6 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_7 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_8 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_9 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_4_10 (n : Nat) : (n + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_0 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_5_1 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_5_2 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_3 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_4 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_6 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_7 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_8 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_9 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_5_10 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_0 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_6_1 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_6_2 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_3 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_4 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_5 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_7 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_8 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_9 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_6_10 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_0 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_7_1 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_7_2 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_3 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_4 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_5 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_6 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_8 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_9 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_7_10 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_0 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_8_1 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_8_2 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_3 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_4 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_5 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_6 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_7 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_9 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_8_10 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_0 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_9_1 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_9_2 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_3 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_4 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_5 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_6 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_7 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_8 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_9_10 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_0 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n) = False := eq_false (by omega)
theorem next_ne_10_1 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1) = False := eq_false (by omega)
theorem next_ne_10_2 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_3 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_4 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_5 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_6 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_7 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_8 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)
theorem next_ne_10_9 (n : Nat) : (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = False := eq_false (by omega)

theorem not_and_not_of_or {p q : Prop} (h : p ∨ q) : (¬p ∧ ¬q) = False := by
  simp only [eq_iff_iff, iff_false]; intro ⟨hp, hq⟩; cases h <;> contradiction
theorem abs_add_of_not_neg {x y : BigDec} (h : ¬ (x.add y).unscaled < 0) :
    (x.toRat + y.toRat).abs = x.toRat + y.toRat := by
  rw [← BigDec.toRat_add]
  exact Rat.abs_of_nonneg (Rat.not_lt.mp fun hlt => h ((BigDec.toRat_neg_iff _).1 hlt))
theorem abs_add_of_neg {x y : BigDec} (h : (x.add y).unscaled < 0) :
    (x.toRat + y.toRat).abs = -(x.toRat + y.toRat) := by
  rw [← BigDec.toRat_add]
  exact Rat.abs_of_nonpos (Rat.le_of_lt ((BigDec.toRat_neg_iff (x.add y)).2 h))
theorem rat_le_false {a b : Rat} (h : b < a) : (a ≤ b) = False := eq_false (Rat.not_le.mpr h)
theorem natAbs_lt_of_neg {u N : Int} (h1 : u < 0) (h2 : -u < N) : ((u.natAbs : Nat) : Int) < N := by
  omega
theorem natAbs_lt_of_nonneg {u N : Int} (h1 : ¬ u < 0) (h2 : u < N) : ((u.natAbs : Nat) : Int) < N := by
  omega
theorem natAbs_ge_of_neg {u N : Int} (h1 : u < 0) (h2 : N ≤ -u) : N ≤ ((u.natAbs : Nat) : Int) := by
  omega
theorem natAbs_ge_of_nonneg {u N : Int} (h1 : ¬ u < 0) (h2 : N ≤ u) : N ≤ ((u.natAbs : Nat) : Int) := by
  omega
theorem units_zero (s : Int) (rounded : Bool) : Cobol.units s rounded 0 = 0 :=
  Cobol.units_of_eq (by simp) rounded
theorem absJ_of_neg {x : BigDec} (h : x.unscaled < 0) : absJ x = x.negate := by simp [absJ, h]
theorem absJ_of_not_neg {x : BigDec} (h : ¬ x.unscaled < 0) : absJ x = x := by simp [absJ, h]

/-- Leaf tactic: a returned `AcctInt$Result` against `accrueD` (`unfold` adds the reference's
    rounding definitions when the leaf carries the program's own terms). -/
syntax "acct_leaf" (" unfold")? : tactic
macro_rules
  | `(tactic| acct_leaf) => `(tactic| (
      intro t a r d D R hargs ha hr'
      simp only [List.cons.injEq, Value.int.injEq, Value.ref.injEq, reduceCtorEq,
        and_true, true_and] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      try simp_all only [Option.some.injEq, Obj.dec.injEq]
      simp [jsimp, ResultIs, accrueD, absJ_of_neg, absJ_of_not_neg, Fields.get, List.lookup, not_and_not_of_or,
        abs_add_of_not_neg, abs_add_of_neg, Rat.not_lt, eq_next0_false, eq_next1_false, eq_next2_false, eq_next3_false, eq_next4_false, eq_next5_false, eq_next6_false, eq_next7_false, eq_next8_false, eq_next9_false, eq_next10_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9, *]
      all_goals simp_all [Rat.not_lt, rat_le_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9]
      all_goals decide))
  | `(tactic| acct_leaf unfold) => `(tactic| (
      intro t a r d D R hargs ha hr'
      simp only [List.cons.injEq, Value.int.injEq, Value.ref.injEq, reduceCtorEq,
        and_true, true_and] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      try simp_all only [Option.some.injEq, Obj.dec.injEq]
      simp [jsimp, ResultIs, accrueD, absJ, dailyOf, interestOf, Fields.get, List.lookup,
        not_and_not_of_or, abs_add_of_not_neg, abs_add_of_neg, Rat.not_lt, eq_next0_false, eq_next1_false, eq_next2_false, eq_next3_false, eq_next4_false, eq_next5_false, eq_next6_false, eq_next7_false, eq_next8_false, eq_next9_false, eq_next10_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9, *]
      all_goals simp_all [Rat.not_lt, rat_le_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9]
      all_goals decide))

/-- The same leaf tactic for a `null` balance. -/
syntax "acct_leaf_null" (" unfold")? : tactic
macro_rules
  | `(tactic| acct_leaf_null) => `(tactic| (
      intro t r d R hargs hr'
      simp only [List.cons.injEq, Value.int.injEq, Value.ref.injEq, reduceCtorEq,
        and_true, true_and] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      try simp_all only [Option.some.injEq, Obj.dec.injEq]
      simp [jsimp, units_zero, ResultIs, accrueD, absJ_of_neg, absJ_of_not_neg, Fields.get, List.lookup, not_and_not_of_or,
        abs_add_of_not_neg, abs_add_of_neg, Rat.not_lt, eq_next0_false, eq_next1_false, eq_next2_false, eq_next3_false, eq_next4_false, eq_next5_false, eq_next6_false, eq_next7_false, eq_next8_false, eq_next9_false, eq_next10_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9, *]
      all_goals simp_all [Rat.not_lt, rat_le_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9]
      all_goals decide))
  | `(tactic| acct_leaf_null unfold) => `(tactic| (
      intro t r d R hargs hr'
      simp only [List.cons.injEq, Value.int.injEq, Value.ref.injEq, reduceCtorEq,
        and_true, true_and] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      try simp_all only [Option.some.injEq, Obj.dec.injEq]
      simp [jsimp, units_zero, ResultIs, accrueD, absJ, dailyOf, interestOf, Fields.get, List.lookup,
        not_and_not_of_or, abs_add_of_not_neg, abs_add_of_neg, Rat.not_lt, eq_next0_false, eq_next1_false, eq_next2_false, eq_next3_false, eq_next4_false, eq_next5_false, eq_next6_false, eq_next7_false, eq_next8_false, eq_next9_false, eq_next10_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9, *]
      all_goals simp_all [Rat.not_lt, rat_le_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9]
      all_goals decide))

/-- The body of `AcctInt.accrue` as imported. -/
abbrev accrueBody := AcctIntJ.AcctInt.«accrue(char,java.math.BigDecimal,java.math.BigDecimal,int)»
/-- `AcctInt.accrue` in the imported program. -/
def accrueRef : MethodRef := mref AcctIntJ.prog "AcctInt" "accrue"

/-! ## Non-null balance -/

/-- Postcondition: the result holds `accrueD` of the arguments' decimal values. -/
def accruePost (args : List Value) (σ : State) (v : Option Value) (σ' : State) : Prop :=
  ∀ t a r d D R, args = [.int t, .ref a, .ref r, .int d] →
     σ.heap a = some (.dec D) → σ.heap r = some (.dec R) →
     ResultIs σ' v (accrueD t D R d)

/-- Contract of `accrue` for a non-null balance.  `AcctInt$Result` is assumed initialized
    (it has no static initializer; the precondition only rules out a failed initialization
    by naming the state). -/
def accrueSpec : Spec := Spec.of
  (fun args σ => ∃ t a r d D R, args = [.int t, .ref a, .ref r, .int d] ∧
     σ.heap a = some (.dec D) ∧ σ.heap r = some (.dec R) ∧
     σ.initOf "AcctInt$Result" = .done)
  accruePost

/-- Checkpoint at statement 15 (type and day count accepted).  Locals: 1 type, 3 balance,
    4 rate, 5 `zero2`, 8 days. -/
def inv15 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ t a r d D R, args = [.int t, .ref a, .ref r, .int d] →
      σ0.heap a = some (.dec D) → σ0.heap r = some (.dec R) →
      ∃ z, fr.get 1 = some (.int t) ∧ fr.get 3 = some (.ref a) ∧ fr.get 4 = some (.ref r) ∧
        fr.get 5 = some (.ref z) ∧ fr.get 8 = some (.int d) ∧ σ.heap a = some (.dec D) ∧
        σ.heap r = some (.dec R) ∧ σ.heap z = some (.dec ⟨0, 2⟩) ∧
        σ.initOf "AcctInt$Result" = .done ∧ ¬ d = 0 ∧ (t = 83#32 ∨ t = 67#32)

/-- Checkpoint at statement 31 (interest computed and within `S9(9)V99`). Local 4: interest. -/
def inv31 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ t a r d D R, args = [.int t, .ref a, .ref r, .int d] →
      σ0.heap a = some (.dec D) → σ0.heap r = some (.dec R) →
      ∃ i, fr.get 3 = some (.ref a) ∧ fr.get 4 = some (.ref i) ∧
        σ.heap a = some (.dec D) ∧ σ.heap i = some (.dec (interestOf D R d)) ∧
        σ.initOf "AcctInt$Result" = .done ∧ ¬ d = 0 ∧ (t = 83#32 ∨ t = 67#32) ∧
        ¬ (0 ≤ (absJ (interestOf D R d)).compareTo ⟨1000000000, 0⟩)

def accrueInv : Invariants := [(15, inv15), (31, inv31)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem accrue_ok : MethodVC AcctIntJ.prog (fun _ => none) 1 accrueRef accrueSpec accrueInv 80 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [accrueInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨?_, ?_, ?_⟩
  · jvc [accrueSpec, inlineFuel, Fields.get, Fields.set, List.lookup, List.filter, bne]
    all_goals acct_leaf unfold
  · intro fr σ h
    simp only [inv15] at h
    jvc [accrueSpec, inlineFuel, Fields.get, Fields.set, List.lookup, List.filter, bne]
    all_goals first
      | acct_leaf unfold
      | (intro t a r d D R hargs ha hr'
         simp only [List.cons.injEq, Value.int.injEq, Value.ref.injEq, and_true] at hargs
         obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
         try simp_all only [Option.some.injEq, Obj.dec.injEq]
         refine ⟨σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1, ?_⟩
         simp [jsimp, dailyOf, interestOf, absJ, Rat.not_lt, eq_next0_false, eq_next1_false, eq_next2_false, eq_next3_false, eq_next4_false, eq_next5_false, eq_next6_false, eq_next7_false, eq_next8_false, eq_next9_false, eq_next10_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9, *]
         all_goals simp_all [Rat.not_lt, rat_le_false, next_ne_0_1, next_ne_0_2, next_ne_0_3, next_ne_0_4, next_ne_0_5, next_ne_0_6, next_ne_0_7, next_ne_0_8, next_ne_0_9, next_ne_0_10, next_ne_1_0, next_ne_1_2, next_ne_1_3, next_ne_1_4, next_ne_1_5, next_ne_1_6, next_ne_1_7, next_ne_1_8, next_ne_1_9, next_ne_1_10, next_ne_2_0, next_ne_2_1, next_ne_2_3, next_ne_2_4, next_ne_2_5, next_ne_2_6, next_ne_2_7, next_ne_2_8, next_ne_2_9, next_ne_2_10, next_ne_3_0, next_ne_3_1, next_ne_3_2, next_ne_3_4, next_ne_3_5, next_ne_3_6, next_ne_3_7, next_ne_3_8, next_ne_3_9, next_ne_3_10, next_ne_4_0, next_ne_4_1, next_ne_4_2, next_ne_4_3, next_ne_4_5, next_ne_4_6, next_ne_4_7, next_ne_4_8, next_ne_4_9, next_ne_4_10, next_ne_5_0, next_ne_5_1, next_ne_5_2, next_ne_5_3, next_ne_5_4, next_ne_5_6, next_ne_5_7, next_ne_5_8, next_ne_5_9, next_ne_5_10, next_ne_6_0, next_ne_6_1, next_ne_6_2, next_ne_6_3, next_ne_6_4, next_ne_6_5, next_ne_6_7, next_ne_6_8, next_ne_6_9, next_ne_6_10, next_ne_7_0, next_ne_7_1, next_ne_7_2, next_ne_7_3, next_ne_7_4, next_ne_7_5, next_ne_7_6, next_ne_7_8, next_ne_7_9, next_ne_7_10, next_ne_8_0, next_ne_8_1, next_ne_8_2, next_ne_8_3, next_ne_8_4, next_ne_8_5, next_ne_8_6, next_ne_8_7, next_ne_8_9, next_ne_8_10, next_ne_9_0, next_ne_9_1, next_ne_9_2, next_ne_9_3, next_ne_9_4, next_ne_9_5, next_ne_9_6, next_ne_9_7, next_ne_9_8, next_ne_9_10, next_ne_10_0, next_ne_10_1, next_ne_10_2, next_ne_10_3, next_ne_10_4, next_ne_10_5, next_ne_10_6, next_ne_10_7, next_ne_10_8, next_ne_10_9]
         all_goals first | omega | exact natAbs_lt_of_neg ‹_› ‹_› | exact natAbs_lt_of_nonneg ‹_› ‹_›)
  · intro fr σ h
    simp only [inv31] at h
    jvc [accrueSpec, inlineFuel, Fields.get, Fields.set, List.lookup, List.filter, bne]
    all_goals acct_leaf

/-- Every terminating execution of `accrue` on a non-null balance returns `accrueD`. -/
theorem accrue_sat : Sat AcctIntJ.prog accrueRef accrueSpec := methodVC_sat accrue_ok

/-! ## `null` balance (the field held LOW-VALUES) -/

/-- Postcondition for a `null` balance: the result is `accrueD` with the balance `0.00`. -/
def accrueNullPost (args : List Value) (σ : State) (v : Option Value) (σ' : State) : Prop :=
  ∀ t r d R, args = [.int t, .null, .ref r, .int d] → σ.heap r = some (.dec R) →
     ResultIs σ' v (accrueD t ⟨0, 2⟩ R d)

def accrueNullSpec : Spec := Spec.of
  (fun args σ => ∃ t r d R, args = [.int t, .null, .ref r, .int d] ∧
     σ.heap r = some (.dec R) ∧ σ.initOf "AcctInt$Result" = .done)
  accrueNullPost

def inv15N (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ t r d R, args = [.int t, .null, .ref r, .int d] → σ0.heap r = some (.dec R) →
      ∃ z, fr.get 1 = some (.int t) ∧ fr.get 3 = some (.ref z) ∧ fr.get 4 = some (.ref r) ∧
        fr.get 5 = some (.ref z) ∧ fr.get 8 = some (.int d) ∧
        σ.heap r = some (.dec R) ∧ σ.heap z = some (.dec ⟨0, 2⟩) ∧
        σ.initOf "AcctInt$Result" = .done ∧ ¬ d = 0 ∧ (t = 83#32 ∨ t = 67#32)

def inv31N (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ t r d R, args = [.int t, .null, .ref r, .int d] → σ0.heap r = some (.dec R) →
      ∃ z i, fr.get 3 = some (.ref z) ∧ fr.get 4 = some (.ref i) ∧
        σ.heap z = some (.dec ⟨0, 2⟩) ∧ σ.heap i = some (.dec (interestOf ⟨0, 2⟩ R d)) ∧
        σ.initOf "AcctInt$Result" = .done ∧ ¬ d = 0 ∧ (t = 83#32 ∨ t = 67#32) ∧
        ¬ (0 ≤ (absJ (interestOf ⟨0, 2⟩ R d)).compareTo ⟨1000000000, 0⟩)

def accrueNullInv : Invariants := [(15, inv15N), (31, inv31N)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem accrue_null_ok :
    MethodVC AcctIntJ.prog (fun _ => none) 1 accrueRef accrueNullSpec accrueNullInv 80 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [accrueNullInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨?_, ?_, ?_⟩
  · jvc [accrueNullSpec, inlineFuel, Fields.get, Fields.set, List.lookup, List.filter, bne, units_zero]
    all_goals acct_leaf_null unfold
  · intro fr σ h
    simp only [inv15N] at h
    jvc [accrueNullSpec, inlineFuel, Fields.get, Fields.set, List.lookup, List.filter, bne, units_zero]
    all_goals acct_leaf_null unfold
  · intro fr σ h
    simp only [inv31N] at h
    jvc [accrueNullSpec, inlineFuel, Fields.get, Fields.set, List.lookup, List.filter, bne, units_zero]
    all_goals acct_leaf_null

/-- Every terminating execution of `accrue` on a `null` balance returns `accrueD` of `0.00`. -/
theorem accrue_null_sat : Sat AcctIntJ.prog accrueRef accrueNullSpec := methodVC_sat accrue_null_ok

end EquivLean.Demo.AcctIntJava

#print axioms EquivLean.Demo.AcctIntJava.accrue_sat
#print axioms EquivLean.Demo.AcctIntJava.accrue_null_sat
