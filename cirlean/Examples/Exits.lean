import CIR
import Examples.Gen.Exits

/-!
  Program termination (`Examples/cpp/exits.cpp`).

  `exit(n)` ends the program with status `n` (`Exit.halt n`). The call does
  not return, so on that path the outcome is stated with `Calls`, and no
  `Returns` specification holds there (`Calls.not_returns`). In
  `guarded_exit` the exit leaves a `try` block and a cleanup scope: the
  catch-all handler does not see it and the guard's destructor does not run,
  so the final memory still holds the guard's increment. Each proof is
  `cir_start; cir_vcg`.
-/

open CIR Gen.Exits

set_option maxHeartbeats 4000000

namespace Examples.Exits

/-- `int checked(int x)`: `x`, when it is not negative. -/
theorem checked_spec (x : Int) (m : Mem) (hx : 0 ≤ x ∧ x ≤ 2147483647) :
    Returns ctx fn_checked.sym [.int x] m (fun r _ => r = some (.int x)) := by
  cir_start
  cir_vcg

/-- On a negative argument, `checked` ends the program with status 2. -/
theorem checked_exits (x : Int) (m : Mem) (hx : -2147483648 ≤ x ∧ x < 0) :
    Calls ctx fn_checked.sym [.int x] m (fun e _ => e = .halt 2) := by
  cir_start
  cir_vcg

/-- So it does not return then, whatever the postcondition. -/
theorem checked_no_return (x : Int) (m : Mem) (hx : -2147483648 ≤ x ∧ x < 0)
    (post : Option Val → Mem → Prop) : ¬ Returns ctx fn_checked.sym [.int x] m post :=
  (checked_exits x m hx).not_returns

/-- `int guarded_exit(int *live, int x)` with `x ≠ 0`: the program ends with
status 3 inside the `try` block, and `*live` keeps the guard's increment. -/
theorem guarded_exit_exits (bl : Nat) (c x : Int) (kl : BlockKind) (m : Mem)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, .int c⟩) (hbl : bl < m.next) (hkl : kl ≠ .readonly)
    (hc : -2147483648 ≤ c ∧ c < 2147483647) (hx : -2147483648 ≤ x ∧ x ≤ 2147483647) (hx0 : x ≠ 0) :
    Calls ctx fn_guarded_exit.sym [.ptr (.loc bl []), .int x] m
      (fun e m' => e = .halt 3 ∧ m'.blocks bl = some ⟨kl, true, .int true 32, .int (c + 1)⟩) := by
  cir_start
  cir_vcg

/-- With `x = 0` it returns the incremented count, and the guard's destructor
restores `*live`. -/
theorem guarded_exit_returns (bl : Nat) (c : Int) (kl : BlockKind) (m : Mem)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, .int c⟩) (hbl : bl < m.next) (hkl : kl ≠ .readonly)
    (hc : -2147483648 ≤ c ∧ c < 2147483647) :
    Returns ctx fn_guarded_exit.sym [.ptr (.loc bl []), .int 0] m
      (fun r m' => r = some (.int (c + 1)) ∧ m'.blocks bl = some ⟨kl, true, .int true 32, .int c⟩) := by
  cir_start
  cir_vcg

end Examples.Exits
