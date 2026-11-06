RESULT: equiv-lean's TypeScript relational proofs on ts-esnext 4f5883d (8 pairs, StrictTS a15926a) and ts-repin ae7949d (10 more es-toolkit pairs, StrictTS 6c1f00c) CHECK OUT: copies = the commits, every Gen module regenerates byte for byte, 18/18 and 33/33 theorems print exactly [propext, Classical.choice, Quot.sound] in fresh processes, kernel replay 55/55 and 95/95 modules rc 0 with both controls behaving. One theorem (isStrictlyEqualImplementation) assumes a property of the host oracle; the 10 re-pin theorems need the later translator.

# Check of the equiv-lean TypeScript proof branches ts-esnext and ts-repin (an agent of the evidence-owner session; written 2026-10-28T00:26:06Z)
Copies: ~/fv_paper/replay/tsnext-20261027T2356Z (git archive; 0 symlinks). Producer repo ~/equivlean read-only (no remotes,
no promisor or partialclone config; GIT_ALLOW_PROTOCOL=file, GIT_NO_LAZY_FETCH=1). Method of checks/esdiff-20261027T1415Z.

1. Commits and copies. ts-esnext 4f5883d = ts-esdiff 92f75e6 (already in master) + 7 commits (es-toolkit at 94cf7ff6;
   remeda 4da195bb sortedIndex/sortedLastIndex and drop/unique/take, 8b6f1bc7 _shuffle, 33caa142
   isStrictlyEqualImplementation; README). ts-repin ae7949d = ts-esnext + 11 commits (148d51d re-pins StrictTS
   a15926a -> 6c1f00c, vendored by git archive; 10 es-toolkit proofs). Archives: 2503 files = 4f5883d, 2578 = ae7949d
   (git hash-object vs ls-tree: 0 differ; logs/lstree_*, hashobj_*). StrictTS a15926a (743 files) and 6c1f00c (1048)
   archived from the local ~/strictts equal the vendored pins (diff -rq without .lake/.git: 0 lines).
2. Statements (logs/statements_axioms_{esnext,repin}.out; hypotheses logs/hyps_repin.txt). Every theorem compares the old
   and the new program's callFun on the same arguments from the same world w, for every Impl and every world, with the
   relation Equiv (· = ·): equal outcomes, final world included (difference/intersection keep ArrObs). Instances: the
   agent-written wrappers inst.ts (identical old/new for every pair; logs/inst_wrappers.txt) at T := number (S := number
   for the old isStrictlyEqualImplementation); range/rangeRight are not generic and have none. Hypotheses:
   - at 94cf7ff6, at eb181846: arr and indices are number arrays allocated below w.next; indices.length < 2^32.
   - at c939d973: also arr.length < 2^32 and no index whose integer part is below -2^53.
   - tail 367fc870: the array allocated below w.next, length < 2^32. min/max f38392c4 (for...of -> index loop): the
     array cell exists, length < 2^32. min/max a9e7edde (let x = undefined -> let x: any): the array cell exists.
   - range ed145c50, range 7dbf58a9, rangeRight 9d13669f: none (start any number, end/step any optional numbers).
   - remeda sortedIndex, sortedLastIndex, drop, unique, _shuffle: none (any array reference, dangling included; any
     world, so any sequence of Math.random answers for _shuffle).
   - remeda take: heap cell 1 holds emptyPipe (the module body ran); take_startup_hg proves this after the start-up of
     either version.
   - remeda isStrictlyEqualImplementation: compared through the call-site wrapper isStrictlyEqualNum(data: number,
     other: number), since the signatures differ; hypothesis on the world's oracle: the Object.is answer for argument
     types [unknown, number] equals the answer for [number, number] on the same values. This is a property of the host,
     not of the semantics: in the semantics an oracle may answer differently, and the theorem says nothing then.
3. Study membership and tool verdicts (logs/study_verdicts_es.tsv, study_verdicts_re.tsv, study_lists_es.txt).
   - es-toolkit: all 11 pairs are in the frozen R6 list (415); only at 94cf7ff6 is in the frozen subset (79). R6, L1,
     L2, L3, L4 and L5 all give UNKNOWN for all 11. Commit labels: perf (the three at), test (range ed145c50), refactor
     (range 7dbf58a9, rangeRight, tail), chore (min/max f38392c4), docs (min/max a9e7edde).
   - remeda: all 7 pairs are in the 862-pair list and in the 160-pair subset; L1 to L5 all give UNKNOWN. The commits are
     labelled "fix:" (4da195bb, 8b6f1bc7) and 33caa142, so none is among the 269 refactoring/style/chore pairs.
   - Provenance: every old/new source slice equals the frozen pair file (es-toolkit 23/23 vs prereg/R6/pairs_SHA256SUMS;
     remeda 37/37 vs ~/strictts/scratch/r7/pairs_SHA256SUMS 41e73814). The 10 re-pin meta.json files differ from the
     frozen ones only in "repo" and in inSubset/rules (frozen: false with unsupported, no-loose-eq or unsupported-builtin;
     new: true) (logs/provenance_slices.txt, meta_diffs_es.txt). The pairs were chosen by the producer after the tool
     runs, so these are labelled results, not blind ones.
   - Regeneration (logs/regen_*.txt): the 16 esnext Gen modules regenerate byte for byte with the a15926a frontend and
     with the 6c1f00c frontend; the 24 other Gen modules of ts-repin (incl. difference/intersection) with 6c1f00c.
     node v22.22.1; typescript 5.9.3 copied from ~/strictts/frontend/node_modules (version checked, not a tarball hash).
4. Axioms: esnext 18/18, repin 33/33 (the 18 again, difference_equiv and intersection_equiv, the 13 new) exactly
   [propext, Classical.choice, Quot.sound], fresh processes against my from-source builds. Trust scan of the closures: no
   sorry, native_decide, ofReduceBool, implemented_by, extern, axiom or skipKernelTC (the only hits are the word "unsafe"
   in comments of Bridge/TS/Behaves and Core/Behaves) (logs/trust_scan_*.txt). Compile: no sorry, no error.
5. Build and replay. From source, no lake: StrictTS closure (27 modules at a15926a, 29 at 6c1f00c; roots
   Frontend.Prelude, Proof.Extern, Proof.Tactics) and the EquivLean closure (28 / 66 modules) (compile_*/compile.tsv,
   all rc 0). Kernel replay (tools/leancheck1lp.sh, LEAN_PATH = my builds, pjobs_v3 8/450/150/2, each job guarded):
   esnext 55/55 rc 0, repin 95/95 rc 0 (replay_{esnext,repin}/). No delta reuse: every module replayed here.
   Controls: BadCtl compiles and is rejected (rc 1, declaration type mismatch), GoodCtl rc 0 (replay_controls/).
6. StrictTS versions (logs/strictts_closure_diff.txt, stdiff_*.diff). 6c1f00c (2026-10-27 14:27Z) descends from L4
   (4016a4a) and is an ancestor of L5 (4bef3c4). In the closure, 15 of 27 shared modules changed (Core.Sem 102 diff
   lines: Promise.all/allSettled over tuples, non-index keys of arrays read through unknown give undefined unless
   inherited, in on arrays for such keys; Proof.Numbers 180; Proof.Extern 73; Lib.Prim 39; Num.F64 35), plus
   Str.Case and Str.CaseTables. The esnext and difference/intersection theorems check at both pins with byte-identical
   Gen modules. The 10 re-pin theorems depend on 6c1f00c: the a15926a frontend rejects their slices ("function
   overloads are not supported", "[no-loose-eq] == and !=", "[unsupported-builtin] new Array(n) creates holes")
   (logs/regen_repinprobe-a*.txt). ts-repin also changes EquivLean/Demo/XLang/Crc32/TS.lean (loop conditions), which
   is outside this check's closure.

Proposed paper text (sec-fixes, after the difference/intersection paragraph; labelled):
"LLM agents proved 18 more function changes equivalent in the same way, all labelled results on pairs that every tool
version leaves unknown: eight with the StrictTS version of the study, the at change of es-toolkit 94cf7ff6 and seven
remeda changes (sortedIndex, sortedLastIndex, drop, unique and take, whose helpers moved; _shuffle; and
isStrictlyEqualImplementation), and ten es-toolkit changes of at, range, rangeRight, tail, min and max with a later
StrictTS version, 6c1f00c, whose translator accepts overloads, loose equality and new Array(n). Each theorem states that
the old and the new version have equal outcomes and final worlds on the same arguments from every world, at the number
instance of generic functions. The premises are arrays allocated before the call, lengths below 2^32 for loops over
arrays, for one at change indices with no integer part below -2^53, for take that its module has started, and for
isStrictlyEqualImplementation that the host's Object.is depends only on its arguments' values. The remeda commits are
labelled as fixes, so none of these pairs is among the 269 refactorings, style changes or chores."
Appendix versions: "The further relational proofs: equiv-lean 4f5883d with StrictTS a15926a, and ae7949d with StrictTS
6c1f00c (which also checks difference and intersection)." Replay rows: "at and seven remeda changes & 55 & all &
equiv-lean 4f5883d"; "ten es-toolkit changes at StrictTS 6c1f00c, with the eight and difference/intersection & 95 & all
& equiv-lean ae7949d".

Cost: 0.421 core-h over 156 guarded jobs (guard/). Producer cost not checked. Nothing external; no rm; no sed -i;
sec-ub.tex and the R2/patched-lexer directories not touched.
