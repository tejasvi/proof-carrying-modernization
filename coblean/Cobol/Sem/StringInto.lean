/-
# `STRING` with delimiters or a pointer

IBM Enterprise COBOL semantics of `STRING src … DELIMITED BY d … INTO r [WITH POINTER p]`:

* Characters go to the receiver from the `POINTER` position (default 1).  A `POINTER` value
  outside the receiver is an overflow, and nothing is moved.
* Each source, in order, contributes its characters up to the first occurrence of its
  delimiter (all of them for `DELIMITED BY SIZE`, or when the delimiter does not occur).  A data
  item contributes its bytes as stored; a figurative constant is one character.
* Characters are moved one at a time; when the receiver is full and characters remain, the
  transfer stops: an overflow (`ON OVERFLOW`).  The receiver is never padded.
* `POINTER` ends one past the last character moved.
-/
import Cobol.Sem.Inspect

namespace Cobol
namespace Sem

/-- A `STRING` source or delimiter as bytes: a data item as stored, a literal or figurative
constant as in a comparison (a figurative constant is one character). -/
def strBytes (c : Config) (st : State) : Operand → SemM (List UInt8)
  | .ref r =>
    match resolve c st r with
    | .error e => .error e
    | .ok d => .ok (readBytes st d)
  | o => cmpOperand c st 1 o

/-- The characters a source contributes: up to the first occurrence of the delimiter. -/
def strPiece (src : List UInt8) : Option (List UInt8) → List UInt8
  | none => src
  | some d => match findSub d src with
    | some i => src.take i
    | none => src

/-- Move bytes into the receiver from position `p` (1-based): the receiver, the next
position, and whether characters remained when it was full. -/
def strPut (dst : List UInt8) : Nat → List UInt8 → List UInt8 × Nat × Bool
  | p, [] => (dst, p, false)
  | p, b :: bs => if dst.length < p then (dst, p, true) else strPut (dst.set (p - 1) b) (p + 1) bs

/-- The sources' characters in turn, until an overflow. -/
def strRun (dst : List UInt8) (p : Nat) : List (List UInt8) → List UInt8 × Nat × Bool
  | [] => (dst, p, false)
  | x :: xs =>
    match strPut dst p x with
    | (d, q, true) => (d, q, true)
    | (d, q, false) => strRun d q xs

/-- `STRING` without its phrases: the new state and whether an overflow occurred. -/
def stringInto (c : Config) (st : State) (srcs : List (Operand × Option Operand))
    (into : DataRef) (ptr : Option DataRef) : SemM (State × Bool) := do
  let pieces ← srcs.mapM fun (s, d) => do
    let sb ← strBytes c st s
    let db ← d.mapM (strBytes c st)
    pure (strPiece sb db)
  let rd ← resolve c st into
  let dst := readBytes st rd
  let p0 ← match ptr with
    | some pr => do
      let v ← evalExpr c st (.ref pr)
      pure (rescale .truncation v (Expr.ref pr).scale 0)
    | none => pure 1
  if p0 < 1 ∨ dst.length < p0 then pure (st, true)
  else
    let (dst', p', ovf) := strRun dst p0.toNat pieces
    let st1 := writeBytes st rd dst'
    let st2 ← match ptr with
      | some pr => (·.1) <$> arith c st1 (.giving (.lit (p' : Nat))) [{ ref := pr }] false
      | none => pure st1
    pure (st2, ovf)

/-- Copy the bytes of each `(from, to)` pair of items of equal length (the arguments and
parameters of a linked `CALL`). -/
def copyBytes (c : Config) : State → List (DataRef × DataRef) → SemM State
  | st, [] => .ok st
  | st, (a, b) :: rest =>
    match resolve c st a, resolve c st b with
    | .ok da, .ok db =>
      if da.len = db.len then copyBytes c (writeBytes st db (readBytes st da)) rest
      else .error (.unsupported "CALL: an argument and its parameter differ in length")
    | .error e, _ => .error e
    | _, .error e => .error e

end Sem
end Cobol
