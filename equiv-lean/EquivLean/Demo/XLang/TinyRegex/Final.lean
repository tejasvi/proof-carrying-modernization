import EquivLean.Demo.XLang.TinyRegex.Equiv
import EquivLean.Demo.XLang.TinyRegex.CReMatch

/-!
# tiny-regex-c → safe Rust: the equivalence theorem

The C library is kokke/tiny-regex-c (`examples/cir/tinyregex/re.c` @ f2632c6, unmodified; cir2lean of
cirlean 28e2380, `Demo/Gen/Cir/TinyRegex.lean`, checked against cirlean e6ac99a). The Rust crate is
verif-orchestrator's guided LLM translation (`examples/rust/tiny_regex`, lib.rs sha256 5cb11c43…; Charon +
Aeneas, `Demo/Gen/Aeneas/TinyRegex`). Both are proved against one functional model of the C algorithm
(`Model.lean`): the Rust side by `RustFinal.re_match_spec` (with `RustCompile`, `RustMatch`), the C side
by `C.re_match_pspec` (with `C.re_compile_spec`, `C.matchpattern_pspec`, `C.re_matchp_pspec`, the C run
in the hypothesis); `Equiv.rust_equiv_c_of` and `cspec_of_pspec` compose them.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas CIR

namespace EquivLean.Demo.XLang.TinyRegex

/-- The C `re_match(pattern, text, &matchlength)` on the bytes of two slices as C strings, from the
module's initial memory (`C.cRun`: pattern block 26, text block 27, the `int` at block 28). -/
def cRe (x : Input) : CIR.Res (Exit × Mem) := C.cRun (bytes x.1) (bytes x.2)

/-- **tiny-regex-c → safe Rust.** For every pattern and text that are C strings (no NUL byte, as the
interface requires), with the text shorter than 2^28 bytes, the Rust `re_match` equals the C
`re_match` wherever the C has no undefined behaviour (cirlean's semantics): the same return value and
the same final `*matchlength`. -/
theorem re_match_equiv :
    EquivOn (fun x => Long x ∨ NulIn x ∨ CUB cRe x) (Same C.mlOf) rustRun cRe :=
  rust_equiv_c_of cRe C.mlOf (cspec_of_pspec C.mlOf C.cRun C.re_match_pspec)

end EquivLean.Demo.XLang.TinyRegex

#print axioms EquivLean.Demo.XLang.TinyRegex.re_match_equiv
