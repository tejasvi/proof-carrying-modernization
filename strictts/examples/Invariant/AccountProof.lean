/-
Class invariant for `examples/Invariant/account.ts`: an `Account`'s balance is never negative.
Every method preserves the invariant on every path, including the paths that throw, and the
constructor establishes it for the object it returns.
-/
import Invariant.AccountEx
import StrictTS.Proof.Tactics

open StrictTS JS AccountEx

/-- The object at address `a` is an `Account` with a non-negative balance. -/
def AccOK (w : World TT) (a : Nat) : Prop :=
  ∃ b : Int, w.heap.get? (.obj "Account" [.bigint], a) = some (.cons (some (.bigint b)) .nil) ∧ 0 ≤ b

/-- `deposit` preserves the invariant, whether it returns or throws. -/
theorem deposit_preserves (I : Impl) (a : Nat) (amount : Int) (w : World TT) (h : AccOK w a) :
    ∀ r w', exec (callFun I program Account_depositRef (.cons (.obj a) (.cons (.bigint amount) .nil))) w = some (r, w') →
      AccOK w' a := by
  obtain ⟨b, hb, hpos⟩ := h
  intro r w' hrun
  rw [Account_deposit_call] at hrun
  by_cases hamt : amount ≤ 0
  · simp [ts_sym, Account_depositDef, hamt] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact ⟨b, hb, hpos⟩
  · simp [ts_sym, Account_depositDef, hamt, hb] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact ⟨b + amount, by simp, by omega⟩

/-- `withdraw` preserves the invariant, whether it returns or throws. -/
theorem withdraw_preserves (I : Impl) (a : Nat) (amount : Int) (w : World TT) (h : AccOK w a) :
    ∀ r w', exec (callFun I program Account_withdrawRef (.cons (.obj a) (.cons (.bigint amount) .nil))) w = some (r, w') →
      AccOK w' a := by
  obtain ⟨b, hb, hpos⟩ := h
  intro r w' hrun
  rw [Account_withdraw_call] at hrun
  by_cases hamt : amount ≤ 0
  · simp [ts_sym, Account_withdrawDef, hamt] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact ⟨b, hb, hpos⟩
  · by_cases hgt : b < amount
    · simp [ts_sym, Account_withdrawDef, hamt, hb, hgt] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact ⟨b, hb, hpos⟩
    · simp [ts_sym, Account_withdrawDef, hamt, hb, hgt] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact ⟨b - amount, by simp, by omega⟩

/-- `getBalance` never reports a negative balance. -/
theorem getBalance_nonneg (I : Impl) (a : Nat) (w : World TT) (h : AccOK w a) :
    ∀ v w', exec (callFun I program Account_getBalanceRef (.cons (.obj a) .nil)) w = some (.ok v, w') →
      0 ≤ v.toBig := by
  obtain ⟨b, hb, hpos⟩ := h
  intro v w' hrun
  rw [Account_getBalance_call] at hrun
  simp [ts_sym, Account_getBalanceDef, hb] at hrun
  obtain ⟨rfl, -⟩ := hrun
  simpa using hpos

/-- The constructor establishes the invariant for the object it returns. -/
theorem new_establishes (I : Impl) (init : Int) (w : World TT) :
    ∀ v w', exec (callFun I program Account_newRef (.cons (.bigint init) .nil)) w = some (.ok v, w') →
      AccOK w' v.objAddr := by
  intro v w' hrun
  rw [Account_new_call] at hrun
  by_cases hneg : init < 0
  · simp [ts_sym, Account_newDef, hneg] at hrun
  · simp [ts_sym, Account_newDef, hneg] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨init, by simp, by omega⟩
