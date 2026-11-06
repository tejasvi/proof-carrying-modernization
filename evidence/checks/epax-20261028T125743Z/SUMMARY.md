# EditPoint theorems of coblean snapshot 20261028T1223Z: axioms in a fresh process, closure count (written 2026-10-28T12:58:16Z; by the evidence-owner session, no fork)
Prompted by claims audit v40 (finding 3): the merge-8 check printed the axioms inside the theorem file's own compile.
Here a separate Lean process imports the compiled module EditPointCheck (build of an agent,
~/.claude/jobs/8a4f16ec/tmp/merge8_replay/editpt_lib, Lean v4.35.0) and prints the axioms of all 13 theorems (AxEP.lean,
axep.out): each depends on exactly [propext, Classical.choice, Quot.sound]. Planted controls in a separate file
(AxCtl.lean, axctl.out): a sorry gives [sorryAx], a custom axiom gives [plantedAx].
Closure (CountEP.lean, count.out): 2,416 modules in all, of which 42 are ours (Cobol.* and EditPointCheck); the fork's
single leanchecker --fresh run (checks/merge8-20261028T122832Z/editpoint/fresh.txt, rc 0) replays this whole closure
from an empty environment. Guard logs in guard/ (coreh_guard_v2, ulimit -v 32 GiB).
