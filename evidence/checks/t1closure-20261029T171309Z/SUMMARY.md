RESULT: the import closure of the 12 tier-1 VOEquiv modules has 99 modules outside the toolchain: 53 package modules
(12 VOEquiv, 24 Gen, 14 EquivLean, 3 VerifOrch) and 46 CIR modules of the frozen cirlean c17690c tree; plus 4 toolchain
imports (Lean, Lean.Elab.Tactic.Omega, Std.Data.HashMap, Std.Data.HashSet). 0 unresolved, 0 found in both trees.

Written 2026-10-29T17:14:01Z (date -u). Purpose: the "Modules in closure" cell of the tab:replay2 row for the tier-1 re-proof
(checks/tier1-20261029T164912Z, which replayed each of the 12 VOEquiv modules with leanchecker --fresh, 12/12 rc 0).
- Method: closure_t1.sh (fcf88014) walks the import lines from the 12 roots (VOEquiv/O*.lean of the copy
  ~/fv_paper/replay/tier1-20261029T164912Z/pkg/src), resolving each module to pkg/src or to
  ~/cirlean_frozen/extmodels_c17690c_20261028; Init/Std/Lean names count as toolchain. Output closure.txt (372e8f86).
- One guarded job (pjobs_v3.py, N=1; guard/closure.log: 0.000 core-h). Read-only on the copy and the frozen tree.
- Slip: bash -n of the script ran in the main shell before the guarded job (light, no output).

## Addendum (2026-10-29T17:15:28Z, date -u): EquivLean sources against the tier-0 package
- eqlean_cmp.sh compares each EquivLean/*.lean of the tier-1 copy with the tier-0 copy
  (~/fv_paper/replay/tier0-20261028T214410Z/pkg/src/EquivLean = equiv-lean 5ec2642 + the tier-0 Tactic additions):
  eqlean_cmp.txt (29fd7da3): 11 SAME, ADDED Bridge/Cir/Congr.lean (3280 lines), CHANGED Bridge/Cir/Tactic.lean (-18 +255 diff
  lines), CHANGED Bridge/Cir/ValSwap.lean (-32 +32). One guarded job (guard/eqlean.log).
