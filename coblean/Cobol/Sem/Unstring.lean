/-
# `UNSTRING`

IBM Enterprise COBOL semantics of `UNSTRING`:

* The sending item is examined from the `POINTER` position (default 1).  A `POINTER` value
  outside the sending item is an overflow, and nothing is moved.
* For each `INTO` receiver in turn: the characters up to the next delimiter (at each position
  the delimiters are tried in the order written; `ALL` makes contiguous occurrences one
  delimiter) are moved to the receiver as an alphanumeric literal would be; the delimiter
  goes to `DELIMITER IN` (spaces at the end of the sending item) and the number of characters
  moved to `COUNT IN`; examination continues after the delimiter.  Without `DELIMITED BY`, a
  receiver takes as many characters as its length.  When the sending item is exhausted, the
  remaining receivers are not changed.
* `POINTER` ends one past the last character examined and `TALLYING IN` is increased by the
  number of receivers acted upon.  Characters left unexamined after the last receiver are an
  overflow (`ON OVERFLOW`).
-/
import Cobol.Sem.Arith

namespace Cobol
namespace Sem

/-- The first delimiter (in the order written) occurring at position `i` of `s`. -/
def delimAt (s : List UInt8) (i : Nat) : List (Bool × List UInt8) → Option (Bool × List UInt8)
  | [] => none
  | (a, d) :: ds => if !d.isEmpty && d.isPrefixOf (s.drop i) then some (a, d) else delimAt s i ds

/-- The next delimiter at or after position `i`: its position, `ALL` flag and bytes. -/
def nextDelim (s : List UInt8) (ds : List (Bool × List UInt8)) :
    Nat → Nat → Option (Nat × Bool × List UInt8)
  | 0, _ => none
  | fuel + 1, i =>
    if s.length ≤ i then none
    else
      match delimAt s i ds with
      | some (a, d) => some (i, a, d)
      | none => nextDelim s ds fuel (i + 1)

/-- The position past further contiguous occurrences of an `ALL` delimiter. -/
def skipAll (s d : List UInt8) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if !d.isEmpty && d.isPrefixOf (s.drop i) then skipAll s d fuel (i + d.length) else i

/-- One receiver from position `pos`: the data, the delimiter (`none`: end of the sending item
or no `DELIMITED BY`), the number of characters moved, the next position. -/
def unstrPiece (s : List UInt8) (ds : List (Bool × List UInt8)) (len pos : Nat) :
    List UInt8 × Option (List UInt8) × Nat × Nat :=
  if ds.isEmpty then
    let k := min len (s.length - pos)
    ((s.drop pos).take k, none, k, pos + k)
  else
    match nextDelim s ds (s.length + 1) pos with
    | some (q, a, d) =>
      let after := if a then skipAll s d (s.length + 1) (q + d.length) else q + d.length
      ((s.drop pos).take (q - pos), some d, q - pos, after)
    | none => (s.drop pos, none, s.length - pos, s.length)

/-- The receivers in turn: the state, the final position and the receivers acted upon. -/
def unstrRun (c : Config) (s : List UInt8) (ds : List (Bool × List UInt8)) :
    List UnstrInto → State → Nat → Nat → SemM (State × Nat × Nat)
  | [], st, pos, k => .ok (st, pos, k)
  | r :: rs, st, pos, k =>
    if s.length ≤ pos then .ok (st, pos, k)
    else
      match resolve c st r.rcv with
      | .error f => .error f
      | .ok d =>
        let (data, dl, cnt, pos') := unstrPiece s ds d.len pos
        match move c st (.alnum data) [r.rcv] with
        | .error f => .error f
        | .ok st1 =>
          let st2 := match r.delim with
            | some dr => move c st1 (.alnum (dl.getD [])) [dr]
            | none => .ok st1
          match st2 with
          | .error f => .error f
          | .ok st2 =>
            let st3 := match r.count with
              | some cr => move c st2 (.num cnt) [cr]
              | none => .ok st2
            match st3 with
            | .error f => .error f
            | .ok st3 => unstrRun c s ds rs st3 pos' (k + 1)

/-- `UNSTRING` without its phrases: the new state and whether an overflow occurred. -/
def unstring (c : Config) (st : State) (src : DataRef) (delims : List (Bool × Operand))
    (into : List UnstrInto) (ptr tally : Option DataRef) : SemM (State × Bool) := do
  let sd ← resolve c st src
  let s := readBytes st sd
  let ds ← delims.mapM fun (a, o) => do pure (a, ← cmpOperand c st 1 o)
  let p0 ← match ptr with
    | some pr => do
      let v ← evalExpr c st (.ref pr)
      pure (rescale .truncation v (Expr.ref pr).scale 0)
    | none => pure 1
  if p0 < 1 ∨ s.length < p0 then pure (st, true)
  else
    let (st1, pos, k) ← unstrRun c s ds into st (p0 - 1).toNat 0
    let st2 ← match ptr with
      | some pr => (·.1) <$> arith c st1 (.giving (.lit (pos + 1 : Nat))) [{ ref := pr }] false
      | none => pure st1
    let st3 ← match tally with
      | some tr => (·.1) <$> arith c st2 (.addTo (.lit k)) [{ ref := tr }] false
      | none => pure st2
    pure (st3, decide (pos < s.length))

end Sem
end Cobol
