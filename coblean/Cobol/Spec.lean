/-
# Outcome predicates for statements about programs

`Program.run P env fuel st` ends with a `Signal`:

* `.stop k`: normal termination (`STOP RUN`, `GOBACK`, `EXIT PROGRAM`, or the end of the
  procedure division);
* `.fault f`: abend or undefined behaviour (invalid numeric data, subscript out of range,
  division by zero, an unhandled I/O error, `CALL 'CEE3ABD'`, size error without a defined
  result) or a construct outside the model (`unsupported`);
* `.outOfFuel`: the fuel bound was too small (never a real outcome).

Under the IBM default `Config.sizeErrorTruncates = true`, a size error without
`ON SIZE ERROR` truncates (a defined result); only `TRUNC(OPT)` binary receivers and division
by zero fault.
-/
import Cobol.Sem.Exec

namespace Cobol

/-- The signal of a normal termination. -/
def Signal.isStop : Signal → Bool
  | .stop _ => true
  | _ => false

/-- `P` terminates normally from `st`: no abend, no undefined behaviour, no unsupported
construct, enough fuel. -/
def Program.EndsNormally (P : Program) (env : Env) (fuel : Nat) (st : State) : Prop :=
  (P.run env fuel st).1.isStop = true

/-- `P` terminates normally from every initial storage whose numeric fields `fs` hold valid
values (`decodeNum ... = some _`), for the input files `inp`. -/
def Program.EndsNormallyOnValid (P : Program) (env : Env) (fuel : Nat) (fs : List FieldDesc)
    (inp : List (Nat × List (List UInt8))) : Prop :=
  ∀ m : Mem, m.size = P.memSize →
    (∀ d ∈ fs, match d.kind with
      | .num f => (decodeNum P.cfg f (m.field d)).isSome
      | _ => True) →
    P.EndsNormally env fuel (P.initState m inp)

theorem Signal.isStop_iff (s : Signal) : s.isStop = true ↔ ∃ k, s = .stop k := by
  cases s <;> simp [Signal.isStop]

end Cobol
