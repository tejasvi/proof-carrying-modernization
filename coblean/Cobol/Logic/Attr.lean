/-
# Simp sets

* `cobol_eval`: definitions unfolded by symbolic execution (interpreter and data
  semantics), plus the field-level storage lemmas.
* `cobol_arith`: rounding / truncation / fitting definitions unfolded before `omega`.
* `java_eval`, `rust_eval`: the target-language models (`Java.BigDecimal`, `Rust.Decimal`,
  checked integer operations), unfolded by symbolic execution of a rewrite.
* `cobol_bits`: binary items restated as `BitVec`s (`Cobol.Target.Bits`), before `bv_decide`.
-/
import Lean

register_simp_attr cobol_eval
register_simp_attr cobol_arith
register_simp_attr java_eval
register_simp_attr rust_eval
register_simp_attr cobol_bits
