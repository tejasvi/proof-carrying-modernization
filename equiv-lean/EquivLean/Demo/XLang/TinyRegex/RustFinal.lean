import EquivLean.Demo.XLang.TinyRegex.RustMatch
import EquivLean.Demo.XLang.TinyRegex.RustTop

/-!
# tiny-regex-c → Rust: the Rust side, closed

`MatchSpec` is the matcher group's `matchpattern_eq` (`RustMatch.lean`), so the top-level
theorems of `RustTop.lean` hold without hypotheses: for every pattern and every text shorter
than 2^28 bytes, `re_match` returns `ok` with the model's return value and matchlength (each as
`toI32`), and `re_matchp` does the same on every regex with `WF` (every `re_compile` result).
-/

open Aeneas Aeneas.Std

namespace EquivLean.Demo.XLang.TinyRegex.Rust

theorem matchSpec : MatchSpec :=
  fun re text pi ti ml mlZ ub hwf hpi hti hlen hml =>
    matchpattern_eq re text pi ti ml mlZ ub hwf hpi hti hlen hml

/-- `re_match` is the model's `reMatch` (return value and matchlength, as `i32`). -/
theorem re_match_spec (pattern text : Slice U8) (hlen : text.val.length < 2 ^ 28) :
    tiny_regex.re_match pattern text =
      .ok (toI32 (reMatch (pattern.val.map (·.val)) (text.val.map (·.val))).1,
        toI32 (reMatch (pattern.val.map (·.val)) (text.val.map (·.val))).2.1) :=
  re_match_eq matchSpec pattern text hlen

/-- `re_matchp` is the model's `reMatchp` on every regex with `WF`. -/
theorem re_matchp_spec (cp : Option tiny_regex.Regex) (text : Slice U8) (ub : Nat)
    (hwf : ∀ re, cp = some re → WF re) (hlen : text.val.length < 2 ^ 28) :
    tiny_regex.re_matchp cp text =
      .ok (toI32 (reMatchp (cp.map absRe) (pat text) ub).1,
        toI32 (reMatchp (cp.map absRe) (pat text) ub).2.1) :=
  re_matchp_eq matchSpec cp text ub hwf hlen

/-- No panic: `re_match` returns normally on every pattern and every text shorter than 2^28
bytes. -/
theorem re_match_no_panic (pattern text : Slice U8) (hlen : text.val.length < 2 ^ 28) :
    ∃ v, tiny_regex.re_match pattern text = .ok v :=
  re_match_ok matchSpec pattern text hlen

end EquivLean.Demo.XLang.TinyRegex.Rust
