import EquivLean.Tactic.LoopAttr
import EquivLean.Core.OptionLoop
import EquivLean.Bridge.Cir.Loops
import EquivLean.Bridge.Aeneas.Loops
import EquivLean.Bridge.TS.Loops
import EquivLean.Bridge.TS.Terminates
import EquivLean.Bridge.Cobol.Loops

/-!
# Registry of loop constructs

Every loop construct of every encoding, with its shape and its termination fact, for
`equiv_loop_auto`: with this file imported, the loop at the head of the goal and the loop at
the head of a hypothesis are paired for any two encodings (C/C++ `for`/`while`/`do`, Rust
`loop`, TypeScript `while`/`for`/`do`/`for…of`, COBOL `PERFORM … UNTIL`/`TIMES`, the reference
`optLoop`) without naming lemmas.
-/

attribute [equiv_loop_shape] EquivLean.optLoop_shape
attribute [equiv_loop_term] EquivLean.optLoop_terminates

-- C/C++ loops are registered by the Cir bridge itself (`Bridge/Cir/Loops.lean`).

attribute [equiv_loop_shape] EquivLean.Aeneas.loop_shape
attribute [equiv_loop_term] EquivLean.Aeneas.loop_terminates

attribute [equiv_loop_shape] EquivLean.TS.loopShape EquivLean.TS.doShape EquivLean.TS.forOfShape
  EquivLean.TS.forOfMapShape EquivLean.TS.forOfSetShape EquivLean.TS.forOfStrShape
attribute [equiv_loop_term] EquivLean.TS.loopTerminates EquivLean.TS.doTerminates
  EquivLean.TS.forOfTerminates EquivLean.TS.forOfMapTerminates EquivLean.TS.forOfSetTerminates
  EquivLean.TS.forOfStrTerminates

attribute [equiv_loop_shape] EquivLean.Cobol.untilShape EquivLean.Cobol.timesShape
attribute [equiv_loop_term] EquivLean.Cobol.untilTerminates EquivLean.Cobol.timesTerminates
