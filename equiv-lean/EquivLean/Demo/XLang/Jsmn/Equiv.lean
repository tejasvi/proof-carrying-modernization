import EquivLean.Demo.XLang.Jsmn.ModelLemmas
import EquivLean.Demo.XLang.Jsmn.RustDefs
import EquivLean.Bridge.Cir.Behaves
import EquivLean.Bridge.Aeneas.Behaves

/-!
# jsmn: the Rust translation equals the C wherever the C has no undefined behaviour

The plumbing of tiny-regex-c's `Equiv.lean`, for jsmn's observation (`Model.parse`): the return
value of `jsmn_parse` and the first `min (max ret 0) num_tokens` tokens of the array, after one
`jsmn_parse` call on a parser fresh from `jsmn_init`.

* `Long x`: the JSON text has `2^28` bytes or more (`RustDefs`; the bound of the statement, as for
  tiny-regex-c).
* `CUB x`: the C run on `x` is not safe in cirlean's semantics (undefined behaviour, or no
  termination).
* `RSpec`: the Rust run returns normally with the model's observation (the Rust side's
  `rust_spec`).
* `CSpec`: a C run that returns has the model's return value and leaves the model's tokens at the
  start of the token array (the C side's theorem, partial); `cspec_of_pspec` gives it from the C
  side's statement on byte lists.
* `rust_equiv_c_of`: `EquivOn (fun x => Long x ∨ CUB x) Same rustRun cRun` from `RSpec` and
  `CSpec`.

The C run and its token reader are parameters (`cRun`, and `toksOf m k`, the first `k` tokens of
the array in memory `m`), instantiated with the C side's setup when it lands.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas CIR

namespace EquivLean.Demo.XLang.Jsmn

theorem bytes_lt (s : Slice U8) : ∀ b ∈ bytes s, b < 256 := by
  intro b hb
  simp only [bytes, List.mem_map] at hb
  obtain ⟨u, -, rfl⟩ := hb
  have := u.hBounds
  simpa using this

/-- The observation of a Rust result: the return value and the tokens `[0, max ret 0)`. -/
def obsR (y : I32 × Slice jsmn_rs.JsmnTok) : Int × List Tok :=
  (y.1.val, (y.2.val.take (max y.1.val 0).toNat).map toTok)

/-- When the Rust run gives the model's observation for `num_tokens = n`, it gives it without
`n` too (the model's `ret` is at most `n`, or negative). -/
theorem obsR_of_rustObs {js : List Nat} {n : Nat} {y : I32 × Slice jsmn_rs.JsmnTok}
    (h : rustObs n y = parse js n) : obsR y = parse js n := by
  have hr : y.1.val = (parse js n).1 := congrArg Prod.fst h
  have hk : min (max y.1.val 0).toNat n = (max y.1.val 0).toNat := by
    rw [hr]
    rcases parse_cases js n with ⟨he, -⟩ | ⟨he, hn, -, -⟩
    · rcases he with he | he | he <;> simp [he, ERROR_NOMEM, ERROR_INVAL, ERROR_PART]
    · rw [he]
      have e : max (((parse js n).2.length : Nat) : Int) 0 = ((parse js n).2.length : Int) := by
        omega
      rw [e, Int.toNat_natCast]
      omega
  rw [← h]
  simp only [obsR, rustObs, hk]

section
variable (cRun : Input → CIR.Res (Exit × Mem)) (toksOf : Mem → Nat → Option (List Tok))

/-- The C run on `x` has undefined behaviour (or does not terminate), per cirlean. -/
def CUB (x : Input) : Prop := ¬ Safe (cRun x)

/-- Same outcome: Rust returns `y` normally; the C returns the `int` that `y` returns, and its
token array starts with the tokens of `y` that the observation reads. -/
def Same : Except Error (I32 × Slice jsmn_rs.JsmnTok) → Exit × Mem → Prop
  | .ok y, (ex, m') =>
    ex = .ret (some (.int (obsR y).1)) ∧ toksOf m' (obsR y).2.length = some (obsR y).2
  | _, _ => False

/-- The Rust side's theorem (`rust_spec`): on texts shorter than `2^28` bytes the Rust run returns
normally with the model's observation. -/
def RSpec : Prop :=
  ∀ x : Input, ¬ Long x → ∃ y, rustRun x = .ok y ∧ rustObs x.2.val y = parse (bytes x.1) x.2.val

/-- The C side's theorem: on texts shorter than `2^28` bytes, a C run that returns has the
model's return value and leaves the model's tokens at the start of the token array. -/
def CSpec : Prop :=
  ∀ x a, ¬ Long x → cRun x = .ok a →
    a.1 = .ret (some (.int (parse (bytes x.1) x.2.val).1)) ∧
      toksOf a.2 (parse (bytes x.1) x.2.val).2.length = some (parse (bytes x.1) x.2.val).2

/-- Two deterministic computations with known outcomes, related by `R`, are equivalent. -/
theorem equiv_of_ok {o : I32 × Slice jsmn_rs.JsmnTok} {a : Exit × Mem}
    {t : Result (I32 × Slice jsmn_rs.JsmnTok)} {s : CIR.Res (Exit × Mem)}
    (R : Except Error (I32 × Slice jsmn_rs.JsmnTok) → Exit × Mem → Prop) (ht : t = Result.ok o)
    (hs : s = .ok a) (hR : R (.ok o) a) : Equiv R t s := by
  subst ht hs
  refine ⟨fun _ => ⟨⟨.ok o, rfl⟩, fun ot hot => ⟨a, rfl, ?_⟩⟩,
    fun _ => ⟨⟨a, rfl⟩, fun os hos => ⟨.ok o, rfl, ?_⟩⟩⟩
  · have : ot = .ok o := ofExcept_injective (by rw [ofExcept_ok]; exact hot.symm)
    subst this; exact hR
  · have : os = a := by cases hos; rfl
    subst this; exact hR

/-- **The Rust translation equals the C wherever the C has no undefined behaviour**, for every
JSON text shorter than `2^28` bytes and every `num_tokens`, after `jsmn_init` and one
`jsmn_parse`: the same return value and the same tokens; from the two sides' theorems. -/
theorem rust_equiv_c_of (hR : RSpec) (hC : CSpec cRun toksOf) :
    EquivOn (fun x => Long x ∨ CUB cRun x) (Same toksOf) rustRun cRun := by
  intro x hx
  simp only [not_or] at hx
  obtain ⟨hlong, hcub⟩ := hx
  simp only [CUB, not_not] at hcub
  obtain ⟨a, ha⟩ := hcub
  obtain ⟨y, hry, hobs⟩ := hR x hlong
  obtain ⟨hret, htoks⟩ := hC x a hlong ha
  refine equiv_of_ok (Same toksOf) hry ha ?_
  obtain ⟨ex, m'⟩ := a
  simp only at hret htoks
  simp only [Same, obsR_of_rustObs hobs]
  exact ⟨hret, htoks⟩

/-- The C side's statement on byte lists gives `CSpec` for the run on the inputs' bytes. -/
theorem cspec_of_pspec (cRunL : List Nat → Nat → CIR.Res (Exit × Mem))
    (pspec : ∀ (js : List Nat) (n : Nat), (∀ b ∈ js, b < 256) → js.length < 2 ^ 28 →
      ∀ a, cRunL js n = .ok a →
        a.1 = .ret (some (.int (parse js n).1)) ∧
          toksOf a.2 (parse js n).2.length = some (parse js n).2) :
    CSpec (fun x => cRunL (bytes x.1) x.2.val) toksOf := by
  intro x a hlong ha
  simp only [Long, Nat.not_le] at hlong
  exact pspec _ _ (bytes_lt x.1) (by simpa [bytes] using hlong) a ha

end

end EquivLean.Demo.XLang.Jsmn
