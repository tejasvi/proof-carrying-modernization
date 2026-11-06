/-
  Examples.lean

  Worked examples, each on the Jimple that Soot produced from `javac` output
  (`examples_java/*/jimple`):
  * `Examples.Basics`: integer arithmetic, loops, arrays;
  * `Examples.Exceptions`: `try`/`catch`/`finally` through the trap table;
  * `Examples.Invoice`: `List`, `Iterator`, `BigDecimal`, an interface and dynamic dispatch,
    whole-program contract validity;
  * `Examples.Mainframe`: Java rewrites of COBOL `COMPUTE` statements, proved equal to the
    COBOL semantics;
  * `Examples.ParserTest`: parser, importer and interpreter tests;
  * `Examples.CardDemo`: CardDemo's CBACT02C, CBCUS01C and CBACT03C as translated to Java
    (`examples_java/cbact02c`, `examples_java/cbcus01c`, `examples_java/cbact03c`): the
    contracts of `run` (the displayed lines are the start line, each record's line (twice for
    CBCUS01C and CBACT03C), the end line) from per-method and per-segment proofs
    (`Cbact02cLink.run_sat`, `Cbcus01cLink.cu_run_sat`, `Cbact03cLink.c3_run_sat`), and their
    termination and total correctness (`Cbact02cTermRun`, `Cbcus01cTermRun`, `Cbact03cTermRun`);
  * `Examples.Termination`: `sumTo` terminates.
-/
import Examples.Basics
import Examples.Exceptions
import Examples.Invoice
import Examples.Mainframe
import Examples.Generic
import Examples.Linking
import Examples.Caching.Link
import Examples.Caching.GenericBody
import Examples.Methods.Link
import Examples.ParserTest
import Examples.CardDemo.Cbact02cLink
import Examples.CardDemo.Cbact02cLemmas
import Examples.CardDemo.Cbcus01cLink
import Examples.CardDemo.Cbact03cLink
import Examples.Termination
import Examples.Caching.TermLink
import Examples.CardDemo.Cbact02cTermRun
import Examples.CardDemo.Cbcus01cTermRun
import Examples.CardDemo.Cbact03cTermRun
