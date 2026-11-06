#!/usr/bin/env python3
"""Write SeqIf_N.lean: the COBOL program of seqif_N.ir.json ≡ a closed-form Java-style result.

usage: mklean.py N [sym]   (`sym`: stop after symbolic execution, print the goal size)
"""
import os
import sys

n = int(sys.argv[1])
sym = len(sys.argv) > 2 and sys.argv[2] == "sym"
P = f"SeqIf{n}"
fs = " ".join(f"f{i}" for i in range(1, n + 1))
hyps = "\n".join(f"    (h{i} : decodeNum {{}} F_{i}.fmt (m.field F_{i}) = some f{i})" for i in range(1, n + 1))
cnt = " + ".join(f"(if 0 < f{i} then 1 else 0)" for i in range(1, n + 1))
tot = " + ".join(f"(if 0 < f{i} then f{i} else 0)" for i in range(1, n + 1))
hs = ", ".join(f"h{i}" for i in range(1, n + 1))
size = 3 * n + 3 + 5
fl = ", ".join(f"f{i}" for i in range(1, n + 1))
tail = "  cobol_sym [obs, javaCount, hm, " + hs + "]\n  trace_state\n  sorry" if sym else \
       "  hb_count cobol_equiv [obs, javaCount, hm, " + hs + "]"
src = f"""import Cobol
open Cobol Lean Elab Tactic

elab "hb_count " t:tactic : tactic => do
  let h0 ← IO.getNumHeartbeats
  evalTactic t
  let h1 ← IO.getNumHeartbeats
  logInfo m!"kHB: {{(h1 - h0) / 1000}}"

/-- Java: `for (int f : fs) if (f > 0) {{ cnt++; total += f; }}` -/
def javaCount (fs : List Int) : Int × Int :=
  fs.foldl (fun acc f => if 0 < f then (acc.1 + 1, acc.2 + f) else acc) (0, 0)

cobol_program {P} from "seqif_{n}.ir.json"

open {P} in
def obs (r : Sem.Res) : Option (Int × Int) :=
  if r.1 = .stop .goback then
    match decodeNum {{}} CNT.fmt (r.2.mem.field CNT), decodeNum {{}} TOTAL.fmt (r.2.mem.field TOTAL) with
    | some c, some t => some (c, t)
    | _, _ => none
  else none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
open {P} in
theorem seqif (m : Mem) (hm : m.size = {size}) ({fs} : Int)
{hyps} :
    obs ({P}.run {{}} 10 ({P}.initState m)) = some (javaCount [{fl}]) := by
  cobol_ranges
{tail}
"""
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f"SeqIf_{n}.lean"), "w").write(src)
