import CIR
import Examples.Gen.Floats

/-!
  Floating-point test functions checked by the kernel (`Examples/cpp/floats.c`).

  Lean's `Float` has a logical model (`Float.toModel`, a binary64 bit
  pattern) in which arithmetic, comparisons, `sqrt` and conversions from
  integers reduce. The semantics computes everything else exactly from the
  bits (`CIR/Std/Float.lean`): comparisons, conversions to integers,
  `floor`/`ceil`/`round`/`trunc`/`fmod`, rounding to `float`, and `printf`'s
  `%e %f %g` and `scanf`/`strtod` (matched against glibc). So `cir_kernel`
  proves tests that print and parse numbers, with the standard axioms only.
-/

open CIR Gen.Floats

namespace Examples.Floats

/-- 12345 + floor(-2.5) + ceil(2.1) + (int)((float)12345.678 * 10). -/
theorem conv_test : Returns ctx fn_t_conv.sym [] module.initMem (fun r _ => r = some (.int 135801)) := by
  cir_kernel

/-- `0.1` prints as `0.1` with `%1.15g` and reads back exactly: 3 characters. -/
theorem print_number_test :
    Returns ctx fn_t_print.sym [] module.initMem (fun r _ => r = some (.int 397)) := by
  cir_kernel

/-- `"%d|%5.2f|%e"` of 42, 3.14159, 1e-10 is `42| 3.14|1.000000e-10`. -/
theorem printf_test : Returns ctx fn_t_print2.sym [] module.initMem (fun r _ => r = some (.int 21)) := by
  cir_kernel

end Examples.Floats
