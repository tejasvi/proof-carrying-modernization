import EquivLean.Demo.XLang.Adler32.RustSpec
import EquivLean.Demo.XLang.Adler32.CCombineSpec
import EquivLean.Demo.XLang.Adler32.CZSpec

/-!
# zlib adler32, C → safe Rust

zlib v1.3.1's `adler32.c` (tag commit 51b7f2a, unmodified, default configuration, x86_64 LP64) and its safe Rust
translation (`examples/rust/adler32_rs`, written by equiv-lean's agents in an Aeneas-friendly form), one theorem
per function; the Rust never panics, and the C is read in cirlean 28e2380's semantics.

* `adler32_z` and `adler32`: for every `adler` and every buffer of fewer than `2^28` bytes, or `Z_NULL` with
  `len < 2^28`, the Rust returns the C's value unless the C run has undefined behaviour (`adler32_z_equiv`,
  `adler32_equiv`). That happens exactly on `Z_NULL` with `len = 1`, where the C reads `buf[0]` (`C.cub_z_iff`,
  `C.cub_32_iff`); so the two are equal on every input except those (`adler32_z_equiv_explicit`,
  `adler32_equiv_explicit`), and on all of them the C run returns.
* `adler32_combine` and `adler32_combine64`: equal for every `adler1`, `adler2` and `len2`; the C run always
  returns.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas CIR

namespace EquivLean.Demo.XLang.Adler32

/-- **zlib `adler32_z`, C → safe Rust**, off the large inputs and the C's undefined behaviour. -/
theorem adler32_z_equiv : EquivOn (fun x => zLong x ∨ CUB C.cRunZ x) Same zRun C.cRunZ :=
  rust_equiv_c_of zLong zModel zRun C.cRunZ z_rspec C.cspec_z

/-- **zlib `adler32`, C → safe Rust** (`len` a `uInt`), off the large inputs and the C's undefined behaviour. -/
theorem adler32_equiv : EquivOn (fun x => zLong x ∨ CUB C.cRun32 x) Same run32 C.cRun32 :=
  rust_equiv_c_of zLong zModel run32 C.cRun32 run32_rspec C.cspec_32

/-- **zlib `adler32_z`, C → safe Rust, the excluded inputs explicit**: equal except on a buffer of `2^28` bytes or
more (or `Z_NULL` with `len ≥ 2^28`) and on `Z_NULL` with `len = 1`, the only input below `2^28` where the C has
undefined behaviour (`C.cub_z_iff`). -/
theorem adler32_z_equiv_explicit :
    EquivOn (fun x : ZInput => zLong x ∨ (x.2.1 = none ∧ x.2.2.val = 1)) Same zRun C.cRunZ := by
  rintro ⟨a, b, l⟩ hx
  refine adler32_z_equiv (a, b, l) ?_
  rintro (h | h)
  · exact hx (Or.inl h)
  · obtain ⟨hn, h1⟩ := (C.cub_z_iff (a, b, l) (fun hl => hx (Or.inl hl))).mp h
    change b = none at hn
    subst hn
    exact hx (Or.inr ⟨rfl, h1⟩)

/-- **zlib `adler32`, C → safe Rust, the excluded inputs explicit**: as `adler32_z_equiv_explicit`
(`C.cub_32_iff`). -/
theorem adler32_equiv_explicit :
    EquivOn (fun x : ZInput => zLong x ∨ (x.2.1 = none ∧ x.2.2.val = 1)) Same run32 C.cRun32 := by
  rintro ⟨a, b, l⟩ hx
  refine adler32_equiv (a, b, l) ?_
  rintro (h | h)
  · exact hx (Or.inl h)
  · obtain ⟨hn, h1⟩ := (C.cub_32_iff (a, b, l) (fun hl => hx (Or.inl hl))).mp h
    change b = none at hn
    subst hn
    exact hx (Or.inr ⟨rfl, h1⟩)

/-- **zlib `adler32_combine`, C → safe Rust**, for every input (`cbLong` excludes none). -/
theorem adler32_combine_equiv : EquivOn cbLong Same cbRun C.cRunCb :=
  rust_equiv_c_total_of cbLong cbModel cbRun C.cRunCb cb_rspec C.ctotal_cb

/-- **zlib `adler32_combine64`, C → safe Rust**, for every input (`cbLong` excludes none). -/
theorem adler32_combine64_equiv : EquivOn cbLong Same cb64Run C.cRunCb64 :=
  rust_equiv_c_total_of cbLong cbModel cb64Run C.cRunCb64 cb64_rspec C.ctotal_cb64

end EquivLean.Demo.XLang.Adler32

#print axioms EquivLean.Demo.XLang.Adler32.adler32_z_equiv
#print axioms EquivLean.Demo.XLang.Adler32.adler32_equiv
#print axioms EquivLean.Demo.XLang.Adler32.adler32_z_equiv_explicit
#print axioms EquivLean.Demo.XLang.Adler32.adler32_equiv_explicit
#print axioms EquivLean.Demo.XLang.Adler32.adler32_combine_equiv
#print axioms EquivLean.Demo.XLang.Adler32.adler32_combine64_equiv
