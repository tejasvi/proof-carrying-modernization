import CIR
import Examples.Gen.Recursion

/-!
  Recursion and mutual recursion (`Examples/cpp/recursion.cpp`).

  A specification of a recursive function is proved by strong induction on a
  measure (here the argument). The induction hypothesis, restated as a local
  hypothesis of the form `∀ …, Returns ctx f.sym args m post`, is used by
  `cir_vcg` as the contract of each recursive call, like a `@[cir_spec]`
  theorem: its preconditions (including that the measure decreases) become
  goals. For mutual recursion, the specifications of all functions of the
  cycle are proved together, as a conjunction.
-/

open CIR Gen.Recursion

set_option maxHeartbeats 4000000

namespace Examples.Recursion
/-- `sum_down(n) = n (n + 1) / 2`, by strong induction on `n`: the induction
hypothesis is the contract of the recursive call. -/
theorem sum_down_spec : ∀ (k : Nat) (n : Int) (m : Mem), n.toNat = k → 0 ≤ n → n ≤ 60000 →
    Returns ctx fn_sum_down.sym [.int n] m
      (fun r m' => (∃ s, r = some (.int s) ∧ 2 * s = n * (n + 1)) ∧ Frame m m' []) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro n m hk h0 h1
  have hrec : ∀ (n' : Int) (m' : Mem), 0 ≤ n' → n' < n → n' ≤ 60000 →
      Returns ctx fn_sum_down.sym [.int n'] m'
        (fun r m'' => (∃ s, r = some (.int s) ∧ 2 * s = n' * (n' + 1)) ∧ Frame m' m'' []) :=
    fun n' m' h0' hlt h1' => ih n'.toNat (by omega) n' m' rfl h0' h1'
  cir_start
  cir_vcg

/-- Mutual recursion: `is_even` and `is_odd` together, by strong induction on
`n`; each hypothesis is the contract of the other function's calls. -/
theorem parity_spec : ∀ (k : Nat),
    (∀ (n : Int) (m : Mem), n.toNat = k → 0 ≤ n → n ≤ 4294967295 →
      Returns ctx fn_is_even.sym [.int n] m
        (fun r m' => r = some (.bool (decide (n % 2 = 0))) ∧ Frame m m' [])) ∧
    (∀ (n : Int) (m : Mem), n.toNat = k → 0 ≤ n → n ≤ 4294967295 →
      Returns ctx fn_is_odd.sym [.int n] m
        (fun r m' => r = some (.bool (decide (n % 2 = 1))) ∧ Frame m m' [])) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  have hodd : ∀ (n' : Int) (m' : Mem), 0 ≤ n' → n'.toNat < k → n' ≤ 4294967295 →
      Returns ctx fn_is_odd.sym [.int n'] m'
        (fun r m'' => r = some (.bool (decide (n' % 2 = 1))) ∧ Frame m' m'' []) :=
    fun n' m' h0 hlt h1 => (ih n'.toNat hlt).2 n' m' rfl h0 h1
  have heven : ∀ (n' : Int) (m' : Mem), 0 ≤ n' → n'.toNat < k → n' ≤ 4294967295 →
      Returns ctx fn_is_even.sym [.int n'] m'
        (fun r m'' => r = some (.bool (decide (n' % 2 = 0))) ∧ Frame m' m'' []) :=
    fun n' m' h0 hlt h1 => (ih n'.toNat hlt).1 n' m' rfl h0 h1
  constructor
  · intro n m hk h0 h1
    cir_start
    cir_vcg
  · intro n m hk h0 h1
    cir_start
    cir_vcg

end Examples.Recursion
