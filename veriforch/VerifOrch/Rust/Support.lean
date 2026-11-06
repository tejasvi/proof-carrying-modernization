module
public import Aeneas

/-!
# veriforch: Rust support (adapters/rust)

The meaning of the statements veriforch states about Aeneas translations, and the step from compiled evaluation of
a test to its theorem.

* `spec_true_iff`: the no-panic statement `f x ⦃ _ => True ⦄` says exactly that `f x` returns `ok` (no panic, no
  divergence). A test function returns `Unit`, so for it the statement is `t = ok ()`: the test passes.
* `spec_of_reducesTo`: a computation that evaluates to `ok e` (Aeneas's `Result.reducesTo`, decided by
  `native_decide`) satisfies the statement.
* `fail_of_panics`: a computation that evaluates to a panic (`panics`) is `fail e` for some error `e` (the statement
  of a `#[should_panic]` test).
* `vo_bounds`: Rust's integer bounds (`u32::MAX`, `i64::MIN`, ...) rewritten to literals, whose values `step` and
  `scalar_tac` know. Every function module of a Rust build imports this module, so every obligation has it.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace VerifOrch.Rust

theorem spec_true_iff {α : Type _} (m : Result α) : m ⦃ _ => True ⦄ ↔ ∃ v, m = ok v := by
  cases m with
  | ret v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => by simp⟩
  | vis i k =>
    simp only [WP.spec_vis, false_iff]
    rintro ⟨v, h⟩
    have := congrArg Result.match h
    simp at this
  | div =>
    simp only [WP.spec_div, false_iff]
    rintro ⟨v, h⟩
    have := congrArg Result.match h
    simp at this

theorem spec_of_reducesTo {α : Type _} [BEq α] {m : Result α} {e : α} (h : m.reducesTo e = true) :
    m ⦃ _ => True ⦄ := by
  cases m with
  | ret v => simp
  | vis i k => simp [Result.reducesTo] at h
  | div => simp [Result.reducesTo] at h

/-- `true` iff the computation evaluates to a panic. -/
def panics {α : Type _} (m : Result α) : Bool :=
  match m.match with
  | .vis _ _ => true
  | _ => false

theorem fail_of_panics {α : Type _} {m : Result α} (h : panics m = true) : ∃ e, m = fail e := by
  cases m with
  | ret v => simp [panics] at h
  | vis i k =>
    cases i with
    | fail e =>
      refine ⟨e, ?_⟩
      rw [Result.fail_eq_vis]
      congr
      funext x
      exact PEmpty.elim x
  | div => simp [panics] at h

section Bounds

/-! Rust's integer bounds as literals (`core.num.U32.MAX = 4294967295#u32`): Aeneas's `step` and `scalar_tac`
know the value of a literal, not of the named constant. `vo_bounds` rewrites them in the goal and the
hypotheses (a no-op when there are none). `usize::MAX` depends on the platform and stays as it is. -/

theorem U8_MAX_eq : core.num.U8.MAX = 255#u8 := rfl
theorem U8_MIN_eq : core.num.U8.MIN = 0#u8 := rfl
theorem U16_MAX_eq : core.num.U16.MAX = 65535#u16 := rfl
theorem U16_MIN_eq : core.num.U16.MIN = 0#u16 := rfl
theorem U32_MAX_eq : core.num.U32.MAX = 4294967295#u32 := rfl
theorem U32_MIN_eq : core.num.U32.MIN = 0#u32 := rfl
theorem U64_MAX_eq : core.num.U64.MAX = 18446744073709551615#u64 := rfl
theorem U64_MIN_eq : core.num.U64.MIN = 0#u64 := rfl
theorem U128_MAX_eq : core.num.U128.MAX = 340282366920938463463374607431768211455#u128 := rfl
theorem U128_MIN_eq : core.num.U128.MIN = 0#u128 := rfl
theorem I8_MAX_eq : core.num.I8.MAX = 127#i8 := rfl
theorem I8_MIN_eq : core.num.I8.MIN = (-128)#i8 := rfl
theorem I16_MAX_eq : core.num.I16.MAX = 32767#i16 := rfl
theorem I16_MIN_eq : core.num.I16.MIN = (-32768)#i16 := rfl
theorem I32_MAX_eq : core.num.I32.MAX = 2147483647#i32 := rfl
theorem I32_MIN_eq : core.num.I32.MIN = (-2147483648)#i32 := rfl
theorem I64_MAX_eq : core.num.I64.MAX = 9223372036854775807#i64 := rfl
theorem I64_MIN_eq : core.num.I64.MIN = (-9223372036854775808)#i64 := rfl
theorem I128_MAX_eq : core.num.I128.MAX = 170141183460469231731687303715884105727#i128 := rfl
theorem I128_MIN_eq : core.num.I128.MIN = (-170141183460469231731687303715884105728)#i128 := rfl

/-- Rust's integer bounds (`u32::MAX`, `i64::MIN`, ...) as literals, in the goal and the hypotheses. -/
macro "vo_bounds" : tactic => `(tactic| try simp only [VerifOrch.Rust.U8_MAX_eq, VerifOrch.Rust.U8_MIN_eq, VerifOrch.Rust.U16_MAX_eq, VerifOrch.Rust.U16_MIN_eq, VerifOrch.Rust.U32_MAX_eq, VerifOrch.Rust.U32_MIN_eq, VerifOrch.Rust.U64_MAX_eq, VerifOrch.Rust.U64_MIN_eq, VerifOrch.Rust.U128_MAX_eq, VerifOrch.Rust.U128_MIN_eq, VerifOrch.Rust.I8_MAX_eq, VerifOrch.Rust.I8_MIN_eq, VerifOrch.Rust.I16_MAX_eq, VerifOrch.Rust.I16_MIN_eq, VerifOrch.Rust.I32_MAX_eq, VerifOrch.Rust.I32_MIN_eq, VerifOrch.Rust.I64_MAX_eq, VerifOrch.Rust.I64_MIN_eq, VerifOrch.Rust.I128_MAX_eq, VerifOrch.Rust.I128_MIN_eq] at *)

end Bounds

end VerifOrch.Rust
