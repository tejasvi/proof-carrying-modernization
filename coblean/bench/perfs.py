#!/usr/bin/env python3
"""Scaling benchmark with paragraphs: MAIN performs N paragraphs P-i, each

    IF F-i > 0  ADD F-i TO TOTAL  ELSE  SUBTRACT F-i FROM TOTAL  END-IF.
    ADD 1 TO CNT.

and the proof compares with a Java-style fold (total of |f_i|, count N).

usage: perfs.py N   (writes perfs_N.ir.json and PerfS_N.lean next to this script)
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
from irjson import *  # noqa: E402,F403

n = int(sys.argv[1])
here = os.path.dirname(os.path.abspath(__file__))
REC, CNT, TOTAL = 1, 2, 3
fields = [item(10 + i, 5, f"F-{i + 1}", pic_9(5, 0, True), usage="packed") for i in range(n)]
data = [item(REC, 1, "REC", children=fields + [
    item(CNT, 5, "CNT", pic_9(4), usage="packed", value=val_fig("zero")),
    item(TOTAL, 5, "TOTAL", pic_9(9, 0, True), usage="packed", value=val_fig("zero"))])]
paras = [para("MAIN", [perform(f"P-{i + 1}") for i in range(n)] + [GOBACK])]
for i in range(n):
    paras.append(para(f"P-{i + 1}",
                      [ite(c_rel(">", o_ref(10 + i), o_num(0)), [add([e_ref(10 + i)], [rcv(TOTAL)])],
                           [{"subtract": {"ops": [e_ref(10 + i)], "rcv": [rcv(TOTAL)], "giving": None,
                                          "onSize": None, "notOnSize": []}}])],
                      [add([e_lit(1)], [rcv(CNT)])]))
json.dump(program("PERFS", data, paras), open(os.path.join(here, f"perfs_{n}.ir.json"), "w"), indent=1)

fs = " ".join(f"f{i}" for i in range(1, n + 1))
hyps = "\n".join(f"    (h{i} : decodeNum {{}} F_{i}.fmt (m.field F_{i}) = some f{i})" for i in range(1, n + 1))
hs = ", ".join(f"h{i}" for i in range(1, n + 1))
fl = ", ".join(f"f{i}" for i in range(1, n + 1))
size = 3 * n + 3 + 5
src = f"""import Cobol
open Cobol Lean Elab Tactic

elab "hb_count " t:tactic : tactic => do
  let h0 ← IO.getNumHeartbeats
  evalTactic t
  let h1 ← IO.getNumHeartbeats
  logInfo m!"kHB: {{(h1 - h0) / 1000}}"

/-- Java: `for (int f : fs) {{ total += f > 0 ? f : -f; cnt++; }}` -/
def javaSum (fs : List Int) : Int × Int :=
  fs.foldl (fun acc f => (acc.1 + 1, if 0 < f then acc.2 + f else acc.2 - f)) (0, 0)

cobol_program PerfS{n} from "perfs_{n}.ir.json"

open PerfS{n} in
def obs (r : Sem.Res) : Option (Int × Int) :=
  if r.1 = .stop .goback then
    match decodeNum {{}} CNT.fmt (r.2.mem.field CNT), decodeNum {{}} TOTAL.fmt (r.2.mem.field TOTAL) with
    | some c, some t => some (c, t)
    | _, _ => none
  else none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
open PerfS{n} in
theorem perfs (m : Mem) (hm : m.size = {size}) ({fs} : Int)
{hyps} :
    obs (PerfS{n}.run {{}} {n + 10} (PerfS{n}.initState m)) = some (javaSum [{fl}]) := by
  cobol_ranges
  hb_count cobol_equiv [obs, javaSum, hm, {hs}]
"""
open(os.path.join(here, f"PerfS_{n}.lean"), "w").write(src)
