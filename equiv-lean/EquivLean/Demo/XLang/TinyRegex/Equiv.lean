import EquivLean.Demo.XLang.TinyRegex.RustFinal
import EquivLean.Demo.XLang.TinyRegex.ModelRange
import EquivLean.Bridge.Cir.Behaves

/-!
# tiny-regex-c: the Rust translation equals the C wherever the C has no undefined behaviour

For every pattern and text that are C strings (no NUL byte, as the interface requires), with the
text shorter than `2^28` bytes, Rust `re_match` equals the C `re_match` wherever the C has no
undefined behaviour: both return normally, with the same return value and the same final
`*matchlength`.

* `Long x`: the text has `2^28` bytes or more (the usize bound of the statement, as in Headline A).
  It cannot simply be dropped: above `Isize.max` Rust's back scan in `matchstar` casts the text
  index to `isize`, which wraps, so Rust returns early where the C scans on, without any UB.
* `NulIn x`: the pattern or the text contains a NUL byte, so it is not a C string (the C
  function takes `const char *`; its contracts take C strings).
* `CUB x`: the C run on `x` is not safe in cirlean's semantics (undefined behaviour, or no
  termination).
* `rust_equiv_c_of`: `EquivOn (fun x => Long x ∨ NulIn x ∨ CUB x) Same rustRun cRun`, from the C
  side's theorem `CSpec` (on C strings, a successful C run has no model UB and returns the model's
  values).  The Rust side is `RustFinal.re_match_spec`; `ModelRange` turns the model's values into
  `int`s.  `cspec_of_pspec` turns the C side's statement on byte lists (`re_match_pspec`) into
  `CSpec`.

The C run and its `*matchlength` slot are parameters here (`cRun`, `mlOf`), instantiated with the
C side's setup (`C.cRun`, `C.mlOf`) when it lands.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas CIR

namespace EquivLean.Demo.XLang.TinyRegex

/-- An input: the pattern and the text bytes (Rust's slices; the C gets them NUL-terminated). -/
abbrev Input := Slice U8 × Slice U8

/-- The bytes of a slice, as the model's list. -/
def bytes (s : Slice U8) : List Nat := s.val.map (·.val)

/-- The Rust side: `re_match pattern text`. -/
def rustRun (x : Input) : Result (I32 × I32) := tiny_regex.re_match x.1 x.2

/-- The text has `2^28` bytes or more. -/
def Long (x : Input) : Prop := 2 ^ 28 ≤ x.2.val.length

/-- The pattern or the text contains a NUL byte (it is not a C string). -/
def NulIn (x : Input) : Prop := 0 ∈ bytes x.1 ∨ 0 ∈ bytes x.2

theorem bytes_lt (s : Slice U8) : ∀ b ∈ bytes s, b < 256 := by
  intro b hb
  simp only [bytes, List.mem_map] at hb
  obtain ⟨u, -, rfl⟩ := hb
  have := u.hBounds
  simpa using this

section
variable (cRun : Input → CIR.Res (Exit × Mem)) (mlOf : Mem → Option Val)

/-- The C run on `x` has undefined behaviour (or does not terminate), per cirlean. -/
def CUB (x : Input) : Prop := ¬ Safe (cRun x)

/-- Same outcome: Rust returns `(r, ml)` normally; the C returns the `int` `r` and leaves the
`int` `ml` in `*matchlength`. -/
def Same : Except Error (I32 × I32) → Exit × Mem → Prop
  | .ok (r, ml), (ex, m') => ex = .ret (some (.int r.val)) ∧ mlOf m' = some (.int ml.val)
  | _, _ => False

/-- The C side's theorem: on C strings, a successful C run has no model UB and returns the model's
values. -/
def CSpec : Prop :=
  ∀ x a, ¬ NulIn x → cRun x = .ok a →
    (reMatch (bytes x.1) (bytes x.2)).2.2 = 0 ∧
      a.1 = .ret (some (.int (reMatch (bytes x.1) (bytes x.2)).1)) ∧
      mlOf a.2 = some (.int (reMatch (bytes x.1) (bytes x.2)).2.1)

/-- Two deterministic computations with known outcomes, related by `R`, are equivalent. -/
theorem equiv_of_ok {o : I32 × I32} {a : Exit × Mem} {t : Result (I32 × I32)}
    {s : CIR.Res (Exit × Mem)} (R : Except Error (I32 × I32) → Exit × Mem → Prop)
    (ht : t = Result.ok o) (hs : s = .ok a) (hR : R (.ok o) a) : Equiv R t s := by
  subst ht hs
  refine ⟨fun _ => ⟨⟨.ok o, rfl⟩, fun ot hot => ⟨a, rfl, ?_⟩⟩,
    fun _ => ⟨⟨a, rfl⟩, fun os hos => ⟨.ok o, rfl, ?_⟩⟩⟩
  · have : ot = .ok o := ofExcept_injective (by rw [ofExcept_ok]; exact hot.symm)
    subst this; exact hR
  · have : os = a := by cases hos; rfl
    subst this; exact hR

/-- **Rust `re_match` equals the C `re_match` wherever the C has no undefined behaviour**, for
every pattern and text that are C strings (no NUL byte, as the interface requires), with the text
shorter than `2^28` bytes: same return value, same final `*matchlength`; from the C side's
theorem `CSpec`. -/
theorem rust_equiv_c_of (hC : CSpec cRun mlOf) :
    EquivOn (fun x => Long x ∨ NulIn x ∨ CUB cRun x) (Same mlOf) rustRun cRun := by
  intro x hx
  simp only [not_or] at hx
  obtain ⟨hlong, hnul, hcub⟩ := hx
  simp only [Long, not_le] at hlong
  simp only [CUB, not_not] at hcub
  obtain ⟨a, ha⟩ := hcub
  have hlen := hlong
  obtain ⟨hub, hret, hml⟩ := hC x a hnul ha
  have hR := Rust.re_match_spec x.1 x.2 hlen
  refine equiv_of_ok (Same mlOf) hR ha ?_
  obtain ⟨ex, m'⟩ := a
  simp only at hret hml
  have hmlr := reMatch_ml_range (bytes x.1) (bytes x.2) hub
  have hretr := reMatch_ret_range (bytes x.1) (bytes x.2)
  have htl : (bytes x.2).length = x.2.val.length := by simp [bytes]
  simp only [Same, bytes] at hret hml hmlr hretr htl ⊢
  refine ⟨?_, ?_⟩
  · rw [hret, Rust.toI32_val_eq]
    · simp only [INT_MIN]; omega
    · simp only [INT_MAX]; omega
  · rw [hml, Rust.toI32_val_eq hmlr.1 hmlr.2]

/-- The C side's statement on byte lists (C strings: every byte in `1..255`) gives `CSpec` for
the run on the inputs' bytes. -/
theorem cspec_of_pspec (cRunL : List Nat → List Nat → CIR.Res (Exit × Mem))
    (pspec : ∀ (p t : List Nat), (∀ b ∈ p, 0 < b ∧ b < 256) → (∀ b ∈ t, 0 < b ∧ b < 256) →
      ∀ a, cRunL p t = .ok a →
        (reMatch p t).2.2 = 0 ∧ a.1 = .ret (some (.int (reMatch p t).1)) ∧
          mlOf a.2 = some (.int (reMatch p t).2.1)) :
    CSpec (fun x => cRunL (bytes x.1) (bytes x.2)) mlOf := by
  intro x a hnul ha
  simp only [NulIn, not_or] at hnul
  refine pspec _ _ (fun b hb => ⟨?_, bytes_lt _ b hb⟩) (fun b hb => ⟨?_, bytes_lt _ b hb⟩) a ha
  · rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; exact absurd hb hnul.1
    · exact h0
  · rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; exact absurd hb hnul.2
    · exact h0

end

end EquivLean.Demo.XLang.TinyRegex

#print axioms EquivLean.Demo.XLang.TinyRegex.rust_equiv_c_of
#print axioms EquivLean.Demo.XLang.TinyRegex.cspec_of_pspec
