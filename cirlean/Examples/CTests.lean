import CIR
import Examples.Gen.CTests

/-!
  Test functions with concrete inputs (`Examples/cpp/ctests.cpp`), proved by
  evaluation from the program's initial memory, with no invariant; the
  statements mention only the test's expected result.
  * `cir_init_mem; cir_eval`: symbolic execution that runs every loop
    iteration by iteration;
  * `cir_kernel`: the kernel evaluates an approximation of the interpreter
    (fast; standard axioms only);
  * `cir_native` (not used here): the same check by `native_decide`.
-/

open CIR Gen.CTests

set_option maxHeartbeats 4000000

namespace Examples.CTests

/-- `int test_loop()` sums 0..9, by symbolic evaluation. -/
theorem test_loop_ok : Returns ctx fn_test_loop.sym [] module.initMem (fun r _ => r = some (.int 45)) := by
  cir_start
  cir_init_mem
  cir_eval

/-- The same by kernel evaluation of the interpreter's approximations
(`CIR/Logic/Kernel.lean`): standard axioms only. -/
theorem test_loop_kernel : Returns ctx fn_test_loop.sym [] module.initMem (fun r _ => r = some (.int 45)) := by
  cir_kernel

/-- `test_count` reads a string literal in a loop: kernel evaluation. -/
theorem test_count_kernel : Returns ctx fn_test_count.sym [] module.initMem (fun r _ => r = some (.int 0)) := by
  cir_kernel

end Examples.CTests
