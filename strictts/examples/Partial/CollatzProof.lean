/-
`examples/Partial/collatz.ts`: the Collatz iteration. Whether its loop ends for every positive
integer is the open Collatz conjecture, so the loop has no known variant and `ts_while` does not
apply. The partial-correctness rule (`ts_while_partial`, `evalLoop_partial`) needs only an
invariant: every run of `collatz` that returns, for any `number` argument (negative, fractional,
NaN, ±∞ included), returns a natural number and changes nothing; no run throws or panics.
-/
import Partial.CollatzEx
import StrictTS.Proof.Tactics
import StrictTS.Proof.Partial

open StrictTS JS CollatzEx F64

/-- The double counter saturates: 2^53 + 1 rounds to 2^53 (ties to even). -/
theorem two53_add_one : ofNat (2 ^ 53) + ofNat 1 = ofNat (2 ^ 53) := by decide

/-- `steps + 1` keeps a counter that holds a natural number at most 2^53 (exact below 2^53). -/
theorem counter_succ (k : Nat) (hk : k ≤ 2 ^ 53) : ∃ k', k' ≤ 2 ^ 53 ∧ ofNat k + ofNat 1 = ofNat k' := by
  by_cases h : k + 1 ≤ 2 ^ 53
  · exact ⟨k + 1, h, ofNat_add_one h⟩
  · obtain rfl : k = 2 ^ 53 := by omega
    exact ⟨2 ^ 53, Nat.le_refl _, two53_add_one⟩

/-- **Partial correctness of `collatz`.** Every run that returns leaves the world unchanged and
returns a natural number (at most 2^53, where the double counter saturates). -/
theorem collatz_partial (I : Impl) (n : F64) (w : World TT) :
    ∀ r w', exec (callFun I program collatzRef (.cons (.num n) .nil)) w = some (r, w') →
      w' = w ∧ ∃ k : Nat, k ≤ 2 ^ 53 ∧ r = .ok (.num (ofNat k)) := by
  rw [collatz_call]
  simp only [collatzDef, ts_sym]
  ts_while_partial
    (fun env w₁ => w₁ = w ∧ ∃ (k : Nat) (x : F64), k ≤ 2 ^ 53 ∧ env = .cons (.num (ofNat k)) (.cons (.num x) .nil)),
    (fun env w₁ => w₁ = w ∧ ∃ (k : Nat) (x : F64), k ≤ 2 ^ 53 ∧ env = .cons (.num (ofNat k)) (.cons (.num x) .nil))
  case step =>
    rintro env w₁ ⟨rfl, k, x, hk, rfl⟩
    obtain ⟨k', hk', hsucc⟩ := counter_succ k hk
    -- both arms of `n % 2 === 0 ? n / 2 : 3 * n + 1` keep the invariant
    by_cases hpar : Conv.numEq (x % ofNat 2) (ofNat 0) = true <;>
      simp [ts_sym, hpar, hsucc] <;> exact ⟨fun _ => ⟨k, hk, rfl⟩, fun _ => ⟨k', hk', rfl⟩⟩
  case init => exact ⟨rfl, 0, n, by omega, rfl⟩
  obtain ⟨rfl, k, x, hk, rfl⟩ := hpost
  simp [ts_sym]
  exact ⟨k, hk, rfl⟩

/-- `collatz` never throws or panics, whether or not it terminates (this needs no arithmetic:
the invariant only fixes the shape of the environment). -/
theorem collatz_noFault (I : Impl) (n : F64) (w : World TT) :
    NoFault (callFun I program collatzRef (.cons (.num n) .nil)) w := by
  rw [collatz_call]
  simp only [NoFault, collatzDef, ts_sym]
  ts_while_partial
    (fun env _ => ∃ (k x : F64), env = .cons (.num k) (.cons (.num x) .nil)),
    (fun env _ => ∃ (k x : F64), env = .cons (.num k) (.cons (.num x) .nil))
  case step =>
    rintro env w₁ ⟨k, x, rfl⟩
    by_cases hpar : Conv.numEq (x % ofNat 2) (ofNat 0) = true <;>
      simp [ts_sym, hpar]
  case init => exact ⟨0, n, rfl⟩
  obtain ⟨k, x, rfl⟩ := hpost
  simp [ts_sym]
