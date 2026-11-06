import EquivLean.Bridge.TS.Tactic
import EquivLean.Demo.Gen.TS.PrOld
import EquivLean.Demo.Gen.TS.PrNew

/-!
# Demo: a TypeScript PR diff with loops, proved equivalent with lockstep loops

`examples/ts/pr_old.ts` (before) and `examples/ts/pr_new.ts` (after) were translated by the
pinned StrictTS front end (`node frontend/dist/cli.js --namespace EquivLean.Demo.Gen.TS.Pr… -o
EquivLean/Demo/Gen/TS/Pr….lean examples/ts/pr_….ts`); the IR in `Gen/TS/PrOld.lean` and
`Gen/TS/PrNew.lean` is the translator's output, untouched.

* `sum`: an index loop `for (let i = 0; i < xs.length; i++) s = s + xs[i]` became
  `for (const x of xs) s = s + x`;
* `contains`: an index loop with an early `return true` became a `for … of` loop that sets a
  flag and `break`s.

For every array `xs` stored at address `a` (any contents: NaN, ±0, ±∞ included) and every
world, the old and new functions are equivalent with *equal* outcomes (same result, same
exception or panic, same final world).  Each direction is one lockstep pairing of the two
loops (`ts_lockstep`) with a coupling invariant; no loop variant is needed.  The only
assumption is the JavaScript bound on array lengths, `xs.size < 2^32`.
-/

namespace EquivLean.Demo.TS.PrDiff
open EquivLean EquivLean.TS StrictTS
open EquivLean.Demo.Gen.TS

abbrev TT := PrOld.TT

/-- The common meaning of both `sum`s: the IEEE-754 left fold of `+`. -/
def sumSpec (xs : List (Val TT .num)) : F64 := xs.foldl (fun s x => s + x.toNum) 0

theorem sumSpec_take_succ (xs : Array (Val TT .num)) (i : Nat) (h : i < xs.size) :
    sumSpec (xs.toList.take (i + 1)) = sumSpec (xs.toList.take i) + xs[i].toNum := by
  simp [sumSpec, List.take_add_one, List.foldl_append, h]

theorem take_size (xs : Array (Val TT .num)) : xs.toList.take xs.size = xs.toList :=
  List.take_of_length_le (by simp)

/-- The coupling invariant of the two `sum` loops after `i` iterations: the new loop's state
`((i, [s, xs]), w)`, the old loop's state `([i, s, xs], w)`. -/
def sumJ (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (s₁ : (Nat × Env TT [⟨.num, true⟩, ⟨.arr .num, false⟩]) × World TT)
    (s₂ : Env TT [⟨.num, true⟩, ⟨.num, true⟩, ⟨.arr .num, false⟩] × World TT) : Prop :=
  s₁.2 = w ∧ s₂.2 = w ∧ s₁.1.1 ≤ xs.size ∧
    s₁.1.2 = .cons (.num (sumSpec (xs.toList.take s₁.1.1))) (.cons (.arr a) .nil) ∧
    s₂.1 = .cons (.num (F64.ofNat s₁.1.1)) (.cons (.num (sumSpec (xs.toList.take s₁.1.1)))
      (.cons (.arr a) .nil))

/-- Both `sum` loops leave normally, with `s = sumSpec xs`. -/
def sumR (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (o₁ : Out TT (Completion TT .num × Env TT [⟨.num, true⟩, ⟨.arr .num, false⟩]))
    (o₂ : Out TT (Completion TT .num × Env TT [⟨.num, true⟩, ⟨.num, true⟩, ⟨.arr .num, false⟩])) :
    Prop :=
  o₁ = (.ok (.normal, .cons (.num (sumSpec xs.toList)) (.cons (.arr a) .nil)), w) ∧
  o₂ = (.ok (.normal, .cons (.num (F64.ofNat xs.size)) (.cons (.num (sumSpec xs.toList))
    (.cons (.arr a) .nil))), w)

/-- One lockstep iteration of the two `sum` loops (stated once, used in both directions). -/
theorem sum_step (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) (i : Nat)
    (hi : i ≤ xs.size) :
    Sim (StepRel stepCls stepCls (sumR a xs w) (sumJ a xs w))
        (JS.exec (forOfStep I PrNew.program a
          (.seq (.assign (mvar! 1) (.prim (.numBin .add) args[var! 1, var! 0])) .nil) i
          (.cons (.num (sumSpec (xs.toList.take i))) (.cons (.arr a) .nil))) w)
        (JS.exec (loopStep I PrOld.program
          (.prim (.numCmp .lt) args[var! 0, .builtin (.arrLength .num) args[var! 2]])
          (.seq (.assign (mvar! 1) (.prim (.numBin .add)
            args[var! 1, .builtin (.arrGet .num) args[var! 2, var! 0]])) .nil)
          (.seq (.assign (mvar! 0) (.prim (.numBin .add) args[var! 0, .lit (.num 1)])) .nil)
          (.cons (.num (F64.ofNat i)) (.cons (.num (sumSpec (xs.toList.take i)))
            (.cons (.arr a) .nil)))) w) ∧
    Sim (StepRel stepCls stepCls (fun o₂ o₁ => sumR a xs w o₁ o₂) (fun s₂ s₁ => sumJ a xs w s₁ s₂))
        (JS.exec (loopStep I PrOld.program
          (.prim (.numCmp .lt) args[var! 0, .builtin (.arrLength .num) args[var! 2]])
          (.seq (.assign (mvar! 1) (.prim (.numBin .add)
            args[var! 1, .builtin (.arrGet .num) args[var! 2, var! 0]])) .nil)
          (.seq (.assign (mvar! 0) (.prim (.numBin .add) args[var! 0, .lit (.num 1)])) .nil)
          (.cons (.num (F64.ofNat i)) (.cons (.num (sumSpec (xs.toList.take i)))
            (.cons (.arr a) .nil)))) w)
        (JS.exec (forOfStep I PrNew.program a
          (.seq (.assign (mvar! 1) (.prim (.numBin .add) args[var! 1, var! 0])) .nil) i
          (.cons (.num (sumSpec (xs.toList.take i))) (.cons (.arr a) .nil))) w) := by
  by_cases hlt : i < xs.size
  · ts_step_simp [hw, hlt, sumJ]
    refine ⟨hlt, ?_, ?_⟩ <;> rw [sumSpec_take_succ xs i hlt]
  · obtain rfl : i = xs.size := by omega
    ts_step_simp [hw, hlt, sumR, take_size]

/-- **`sum`: new ≈ old**, with equal outcomes (result and final world). -/
theorem sum_equiv (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) :
    Equiv (· = ·) (call I PrNew.program PrNew.sumRef (.cons (.arr a) .nil) w)
      (call I PrOld.program PrOld.sumRef (.cons (.arr a) .nil) w) := by
  equiv_ts [PrOld.sum_call, PrNew.sum_call, PrOld.sumDef, PrNew.sumDef]
  · -- new ⊑ old
    ts_lockstep sumJ a xs w, sumR a xs w
    case init => exact ⟨rfl, rfl, Nat.zero_le _, by simp [sumSpec], by simp [sumSpec]⟩
    case step =>
      rintro ⟨⟨i, env₁⟩, w₁⟩ ⟨env₂, w₂⟩ ⟨h₁, h₂, hi, h₃, h₄⟩
      dsimp only at h₁ h₂ hi h₃ h₄; subst w₁ w₂ env₁ env₂
      exact (sum_step I a xs w hw hlen i hi).1
    case exit =>
      rintro _ _ ⟨rfl, rfl⟩ hK
      simp only [ts_sym, wp_some] at hK ⊢
      exact ⟨_, hK, rfl⟩
  · -- old ⊑ new
    ts_lockstep (fun s₂ s₁ => sumJ a xs w s₁ s₂), (fun o₂ o₁ => sumR a xs w o₁ o₂)
    case init => exact ⟨rfl, rfl, Nat.zero_le _, by simp [sumSpec], by simp [sumSpec]⟩
    case step =>
      rintro ⟨env₂, w₂⟩ ⟨⟨i, env₁⟩, w₁⟩ ⟨h₁, h₂, hi, h₃, h₄⟩
      dsimp only at h₁ h₂ hi h₃ h₄; subst w₁ w₂ env₁ env₂
      exact (sum_step I a xs w hw hlen i hi).2
    case exit =>
      rintro _ _ ⟨rfl, rfl⟩ hK
      simp only [ts_sym, wp_some] at hK ⊢
      exact ⟨_, hK, rfl⟩

/-! ## `contains`: early `return` versus flag and `break` -/

/-- Loop environments: new `[found, xs, v]`, old `[i, xs, v]`. -/
abbrev CEnv₁ := Env TT [⟨.bool, true⟩, ⟨.arr .num, false⟩, ⟨.num, false⟩]
abbrev CEnv₂ := Env TT [⟨.num, true⟩, ⟨.arr .num, false⟩, ⟨.num, false⟩]

/-- Coupling invariant: after `i` iterations neither loop has found `v` yet. -/
def containsJ (a : Nat) (v : F64) (xs : Array (Val TT .num)) (w : World TT)
    (s₁ : (Nat × CEnv₁) × World TT) (s₂ : CEnv₂ × World TT) : Prop :=
  s₁.2 = w ∧ s₂.2 = w ∧ s₁.1.1 ≤ xs.size ∧
    s₁.1.2 = .cons (.bool false) (.cons (.arr a) (.cons (.num v) .nil)) ∧
    s₂.1 = .cons (.num (F64.ofNat s₁.1.1)) (.cons (.arr a) (.cons (.num v) .nil))

/-- Loop exits: the new loop leaves normally with `found = true` exactly when the old one
leaves with `return true`; otherwise both leave normally, `found = false`. -/
def containsR (a : Nat) (v : F64) (w : World TT)
    (o₁ : Out TT (Completion TT .bool × CEnv₁)) (o₂ : Out TT (Completion TT .bool × CEnv₂)) :
    Prop :=
  (o₁ = (.ok (.normal, .cons (.bool true) (.cons (.arr a) (.cons (.num v) .nil))), w) ∧
    ∃ e₂, o₂ = (.ok (.ret (.bool true), e₂), w)) ∨
  (o₁ = (.ok (.normal, .cons (.bool false) (.cons (.arr a) (.cons (.num v) .nil))), w) ∧
    ∃ e₂, o₂ = (.ok (.normal, e₂), w))

theorem contains_equiv (I : Impl) (a : Nat) (v : F64) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) :
    Equiv (· = ·) (call I PrNew.program PrNew.containsRef (.cons (.arr a) (.cons (.num v) .nil)) w)
      (call I PrOld.program PrOld.containsRef (.cons (.arr a) (.cons (.num v) .nil)) w) := by
  equiv_ts [PrOld.contains_call, PrNew.contains_call, PrOld.containsDef, PrNew.containsDef]
  · -- new ⊑ old
    ts_lockstep containsJ a v xs w, containsR a v w
    case init => exact ⟨rfl, rfl, Nat.zero_le _, rfl, by simp⟩
    case step =>
      clear hs
      rintro ⟨⟨i, env₁⟩, w₁⟩ ⟨env₂, w₂⟩ ⟨h₁, h₂, hi, h₃, h₄⟩
      dsimp only at h₁ h₂ hi h₃ h₄; subst w₁ w₂ env₁ env₂
      by_cases hlt : i < xs.size
      · cases heq : Conv.numEq xs[i].toNum v <;>
          ts_step_simp [hw, hlt, heq, containsJ, containsR]
        · omega
        · exact .inl ⟨_, rfl⟩
      · obtain rfl : i = xs.size := by omega
        ts_step_simp [hw, hlt, containsJ, containsR]
        exact .inr ⟨_, rfl⟩
    case exit =>
      rintro _ _ (⟨rfl, e₂, rfl⟩ | ⟨rfl, e₂, rfl⟩) hK <;>
      · simp only [ts_sym, wp_some] at hK ⊢
        exact ⟨_, hK, rfl⟩
  · -- old ⊑ new
    ts_lockstep (fun s₂ s₁ => containsJ a v xs w s₁ s₂), (fun o₂ o₁ => containsR a v w o₁ o₂)
    case init => exact ⟨rfl, rfl, Nat.zero_le _, rfl, by simp⟩
    case step =>
      clear hs
      rintro ⟨env₂, w₂⟩ ⟨⟨i, env₁⟩, w₁⟩ ⟨h₁, h₂, hi, h₃, h₄⟩
      dsimp only at h₁ h₂ hi h₃ h₄; subst w₁ w₂ env₁ env₂
      by_cases hlt : i < xs.size
      · cases heq : Conv.numEq xs[i].toNum v <;>
          ts_step_simp [hw, hlt, heq, containsJ, containsR]
        · omega
        · exact .inl ⟨_, rfl⟩
      · obtain rfl : i = xs.size := by omega
        ts_step_simp [hw, hlt, containsJ, containsR]
        exact .inr ⟨_, rfl⟩
    case exit =>
      rintro _ _ (⟨rfl, e₂, rfl⟩ | ⟨rfl, e₂, rfl⟩) hK <;>
      · simp only [ts_sym, wp_some] at hK ⊢
        exact ⟨_, hK, rfl⟩

/-! ## The same facts about real JavaScript

In the strict reading (`Strict`, a panic leaves the modelled fragment and is unsafe) the two
versions agree as well: equal outcomes transfer (`Equiv.strict_of_eq`). -/

theorem sum_equiv_strict (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) :
    Equiv (· = ·) (Strict.mk (callFun I PrNew.program PrNew.sumRef (.cons (.arr a) .nil)) w)
      (Strict.mk (callFun I PrOld.program PrOld.sumRef (.cons (.arr a) .nil)) w) :=
  Equiv.strict_of_eq (sum_equiv I a xs w hw hlen)

theorem contains_equiv_strict (I : Impl) (a : Nat) (v : F64) (xs : Array (Val TT .num))
    (w : World TT) (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) :
    Equiv (· = ·)
      (Strict.mk (callFun I PrNew.program PrNew.containsRef (.cons (.arr a) (.cons (.num v) .nil))) w)
      (Strict.mk (callFun I PrOld.program PrOld.containsRef (.cons (.arr a) (.cons (.num v) .nil))) w) :=
  Equiv.strict_of_eq (contains_equiv I a v xs w hw hlen)

end EquivLean.Demo.TS.PrDiff
