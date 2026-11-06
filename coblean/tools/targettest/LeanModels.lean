/-
Evaluates the Lean transcriptions `AcctIntJava.accrue` and `AcctIntRust.accrue` on the input
lines of `targettest.py` (same format as the Java and Rust drivers).
-/
import Examples.AcctIntRust
open Cobol

def parseLine (l : String) : Option (Char × Option Int × Int × Nat) := do
  let f := ((l.replace "\n" "").splitOn " ").toArray
  guard (f.size == 4)
  let t ← f[0]!.toList.head?
  let bal ← if f[1]! == "null" then pure none else some <$> f[1]!.toInt?
  let rate ← f[2]!.toInt?
  let days ← f[3]!.toNat?
  pure (t, bal, rate, days)

def main (args : List String) : IO Unit := do
  let stdin ← IO.getStdin
  let target := args.headD "java"
  let mut lines : Array String := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    lines := lines.push l
  for l in lines do
    let some (t, bal, rate, days) := parseLine l | IO.println "parse-error"
    if target == "java" then
      match AcctIntJava.accrue t (bal.map (Java.BigDecimal.valueOf · 2)) (.valueOf rate 5)
          (Int32.ofNat days) with
      | .ok r => IO.println s!"{r.balance.valueAt 2} {r.interest.valueAt 2} {r.status}"
      | .error _ => IO.println "exception"
    else
      match AcctIntRust.accrue t (bal.map Int64.ofInt) (Int64.ofInt rate) (UInt16.ofNat days) with
      | .ok (b, i, s) => IO.println s!"{b.toInt} {i.toInt} {s}"
      | .error _ => IO.println "panic"
