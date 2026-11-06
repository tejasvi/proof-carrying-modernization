import EquivLean.Demo.XLang.Jsmn.RustGlue
import EquivLean.Demo.XLang.Jsmn.CRun

/-!
# jsmn, C → safe Rust

zserge/jsmn @ 25647e6 (default configuration) and its safe Rust translation (`examples/rust/jsmn_rs`, written by
equiv-lean's agents in an Aeneas-friendly form): after `jsmn_init`, one `jsmn_parse(parser, js, len, tokens,
num_tokens)` gives in Rust exactly what it gives in C, the return value and the filled tokens, for every input
shorter than 2^28 bytes on which the C run has no undefined behaviour in cirlean e6ac99a (the C code's Lean is
cir2lean's output at 28e2380).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas CIR

namespace EquivLean.Demo.XLang.Jsmn

/-- The C run on a Rust input: `jsmn_init`, then `jsmn_parse` on the input's bytes with `num_tokens` its `U32`. -/
def cRunI (x : Input) : CIR.Res (Exit × Mem) := C.cRun (bytes x.1) x.2.val

/-- **jsmn, C → safe Rust.** -/
theorem jsmn_equiv : EquivOn (fun x => Long x ∨ CUB cRunI x) (Same C.toksOf) rustRun cRunI :=
  rust_equiv_c_of cRunI C.toksOf rust_rspec (cspec_of_pspec C.toksOf C.cRun C.jsmn_parse_pspec)

end EquivLean.Demo.XLang.Jsmn

#print axioms EquivLean.Demo.XLang.Jsmn.jsmn_equiv
