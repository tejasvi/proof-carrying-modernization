# Crash fixes after the D2 pin (20261025T0300Z)

Each entry is one general fix of a non-verdict failure. No unit of any sample or population is named.

## 20261025T1728Z: kernel "deep recursion" on a signed comparison of a bitwise result

- Symptom: a method whose verification condition branches on the signed value of a bitwise result, for example
  `if ((a ^ b) >= 0)`, also with `&` or `|`, failed when the kernel checked the proof: "(kernel) deep recursion
  detected". Raising `maxRecDepth` does not help. The elaboration itself succeeded.
- Cause: the core simp lemmas `BitVec.toInt_xor`, `BitVec.toInt_and` and `BitVec.toInt_or` rewrote such a condition
  into an `Int.bmod` form, in the symbolic execution's simp call and in the `simp_all` closers. The resulting proof
  sends the kernel into a deep unfolding.
- Fix (Jimple/Tactic.lean): those three lemmas are excluded from the symbolic execution's simp call and from the
  three `simp_all` closers (`closeTriv`, `jauto`, `jautoOn`). The condition stays `0 ≤ (a ^^^ b).toInt`.
- Found by the JDK `Math.floorMod` demo, whose bytecode tests `(mod ^ y) >= 0`. Minimal repros: a body
  `x = mod ^ y; if x >= 0 goto …` and the same with `&`. Both fail on 0300Z and pass with the fix.
- Checks: regression `lake build Jimple Examples`, 132 jobs, 68 theorems, standard axioms only; JVM difftests 41/41
  MATCH (the interpreter is unchanged).

## Model fixes after the D2 pin (not crash fixes)

- `Double.compare` with a NaN operand returned 1 where the JDK returns -1 (`compare(x, NaN)` for any non-NaN x):
  the model took the `dcmpg` result first, which is 1 on NaN. It now orders NaN above every other value and equal
  to itself, then `-0.0 < 0.0`, as `Double.compare` does. Found by the new difftest `FloatSem`, written after the
  mutation run (PREREG_M) showed that the corpus did not check floating-point results; `FloatSem` fails on the
  earlier interpreter and matches the JVM now. Out of the D2 families (java.lang.Double).
