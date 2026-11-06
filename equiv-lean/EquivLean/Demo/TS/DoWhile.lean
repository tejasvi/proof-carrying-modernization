import EquivLean.Bridge.TS.Tactic
import EquivLean.Demo.Gen.TS.DigitsOld
import EquivLean.Demo.Gen.TS.DigitsNew

/-!
# Demo: `do … while` refactored into `while (true) … break`

`examples/ts/digits_old.ts` counts decimal digits with
`do { count++; m = Math.floor(m / 10); } while (m > 0)`; `examples/ts/digits_new.ts` uses
`while (true) { count++; m = Math.floor(m / 10); if (!(m > 0)) break; }`.  Both translated by
the pinned StrictTS front end (`Gen/TS/DigitsOld.lean`, `Gen/TS/DigitsNew.lean`).

`digits_equiv`: equal outcomes for every `number` input and every world: NaN and
negative inputs (one iteration), and `+∞`, where both loops diverge (`Equiv` relates the
divergences: neither side is safe).  Each direction pairs the `do … while` loop (`doShape`,
`doTerminates`) with the `while` loop (`loopShape`, `loopTerminates`) in lockstep, with the
coupling invariant "the same environment and world".  No variant is needed, and none exists
for `+∞`.
-/

namespace EquivLean.Demo.TS.DoWhile
open EquivLean EquivLean.TS StrictTS
open EquivLean.Demo.Gen.TS

abbrev TT := DigitsOld.TT
/-- The loop environment `[m, count, n]` of both versions. -/
abbrev E := Env TT [⟨.num, true⟩, ⟨.num, true⟩, ⟨.num, false⟩]

set_option linter.unusedSimpArgs false in
theorem digits_equiv (I : Impl) (n : F64) (w : World TT) :
    Equiv (· = ·) (call I DigitsNew.program DigitsNew.digitsRef (.cons (.num n) .nil) w)
      (call I DigitsOld.program DigitsOld.digitsRef (.cons (.num n) .nil) w) := by
  equiv_ts [DigitsOld.digits_call, DigitsNew.digits_call, DigitsOld.digitsDef, DigitsNew.digitsDef]
  all_goals
    ts_lockstep (fun (s₁ : E × World TT) (s₂ : E × World TT) => s₁ = s₂), (fun o₁ o₂ => o₁ = o₂)
    case init => rfl
    case step =>
      clear hs
      rintro ⟨env, w₁⟩ _ rfl
      cases env with | cons m e => cases e with | cons c e => cases e with | cons k e =>
      cases e
      cases m with | num mx =>
      cases c with | num cx =>
      cases h : (mx / F64.ofNat 10).floor.gt (F64.ofNat 0) <;> ts_step_simp [h]
    case exit =>
      rintro o _ rfl hK
      rcases o with ⟨e | ⟨c, env⟩, w'⟩
      · simp only [ts_sym, wp_some] at hK ⊢; exact ⟨_, hK, rfl⟩
      · cases env with | cons m e => cases e with | cons c' e => cases e with | cons k e =>
        cases e
        cases c <;> simp only [ts_sym, wp_some] at hK ⊢ <;> exact ⟨_, hK, rfl⟩

end EquivLean.Demo.TS.DoWhile
