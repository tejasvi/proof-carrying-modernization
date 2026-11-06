import EquivLean.Demo.XLang.Adler32.Model
import EquivLean.Bridge.Cir.Behaves
import EquivLean.Bridge.Aeneas.Behaves

/-!
# zlib adler32: the Rust translation equals the C wherever the C has no undefined behaviour

The plumbing of jsmn's `Equiv.lean` for a function returning a `uLong` (`adler32_z`, `adler32`,
`adler32_combine64`, `adler32_combine`), generic in the function's inputs: `model x` is the model's value
(`adler32z`, `combine`), `Long x` the excluded large inputs (a buffer of `2^28` bytes or more).

* `CUB x`: the C run on `x` is not safe in cirlean's semantics (undefined behaviour, or no termination).
* `Same`: Rust returns `y` normally and the C returns the `unsigned long` `y`.
* `RSpec`: the Rust run returns normally with the model's value (the Rust side's theorem: no panic).
* `CSpec`: a C run that returns has the model's value (the C side's theorem, partial); `CTotal`: the C run
  returns, with the model's value (total).
* `rust_equiv_c_of`: `EquivOn (fun x => Long x ∨ CUB x) Same rustRun cRun` from `RSpec` and `CSpec`;
  `rust_equiv_c_total_of`: `EquivOn Long Same rustRun cRun` from `RSpec` and `CTotal` (no `CUB` left).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas CIR

namespace EquivLean.Demo.XLang.Adler32

section
variable {Input : Type} (Long : Input → Prop) (model : Input → Nat)
  (rustRun : Input → Result U64) (cRun : Input → CIR.Res (Exit × Mem))

/-- The C run on `x` has undefined behaviour (or does not terminate), per cirlean. -/
def CUB (x : Input) : Prop := ¬ Safe (cRun x)

/-- Same outcome: Rust returns `y` normally and the C returns the `unsigned long` `y`. -/
def Same : Except Error U64 → Exit × Mem → Prop
  | .ok y, (ex, _) => ex = .ret (some (.int (y.val : Int)))
  | _, _ => False

/-- The Rust side's theorem: off the large inputs the Rust run returns normally with the model's value. -/
def RSpec : Prop := ∀ x, ¬ Long x → ∃ y, rustRun x = .ok y ∧ y.val = model x

/-- The C side's theorem (partial): off the large inputs, a C run that returns has the model's value. -/
def CSpec : Prop := ∀ x a, ¬ Long x → cRun x = .ok a → a.1 = .ret (some (.int (model x : Int)))

/-- The C side's theorem (total): off the large inputs the C run returns, with the model's value. -/
def CTotal : Prop := ∀ x, ¬ Long x → ∃ a, cRun x = .ok a ∧ a.1 = .ret (some (.int (model x : Int)))

theorem cspec_of_total (hC : CTotal Long model cRun) : CSpec Long model cRun := by
  intro x a hl ha
  obtain ⟨a', ha', hr⟩ := hC x hl
  rw [ha] at ha'
  cases ha'
  exact hr

/-- Two deterministic computations with known outcomes, related by `R`, are equivalent. -/
theorem equiv_of_ok {o : U64} {a : Exit × Mem} {t : Result U64} {s : CIR.Res (Exit × Mem)}
    (R : Except Error U64 → Exit × Mem → Prop) (ht : t = Result.ok o) (hs : s = .ok a)
    (hR : R (.ok o) a) : Equiv R t s := by
  subst ht hs
  refine ⟨fun _ => ⟨⟨.ok o, rfl⟩, fun ot hot => ⟨a, rfl, ?_⟩⟩,
    fun _ => ⟨⟨a, rfl⟩, fun os hos => ⟨.ok o, rfl, ?_⟩⟩⟩
  · have : ot = .ok o := ofExcept_injective (by rw [ofExcept_ok]; exact hot.symm)
    subst this; exact hR
  · have : os = a := by cases hos; rfl
    subst this; exact hR

/-- **The Rust translation equals the C wherever the C has no undefined behaviour**, off the large inputs: the
same return value; from the two sides' theorems. -/
theorem rust_equiv_c_of (hR : RSpec Long model rustRun) (hC : CSpec Long model cRun) :
    EquivOn (fun x => Long x ∨ CUB cRun x) Same rustRun cRun := by
  intro x hx
  simp only [not_or] at hx
  obtain ⟨hlong, hcub⟩ := hx
  simp only [CUB, not_not] at hcub
  obtain ⟨a, ha⟩ := hcub
  obtain ⟨y, hry, hval⟩ := hR x hlong
  have hret := hC x a hlong ha
  refine equiv_of_ok Same hry ha ?_
  obtain ⟨ex, m'⟩ := a
  simp only at hret
  simp only [Same, hval]
  exact hret

/-- **The Rust translation equals the C, everywhere off the large inputs**, when the C side is total: no
undefined behaviour to exclude. -/
theorem rust_equiv_c_total_of (hR : RSpec Long model rustRun) (hC : CTotal Long model cRun) :
    EquivOn Long Same rustRun cRun := by
  intro x hlong
  obtain ⟨a, ha, hret⟩ := hC x hlong
  obtain ⟨y, hry, hval⟩ := hR x hlong
  refine equiv_of_ok Same hry ha ?_
  obtain ⟨ex, m'⟩ := a
  simp only at hret
  simp only [Same, hval]
  exact hret

end

end EquivLean.Demo.XLang.Adler32
