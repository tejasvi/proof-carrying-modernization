RESULT: PASS on items 1-6 for #2 t2_unionpun_next3_7c73739 and #5 d2_retslot_next3_7c73739, with two notes on #5. Both packages hash as announced (19/19 and 29/29 OK before and after); each Gen module is the pin's front-end output; #2's three statements and proof files are byte-identical to next2's; #5's two statements differ from the claimed d9ae8e5 statements only by the retslot shape (the result object R as a second pointer argument, hypotheses on R, the value in R instead of the return value, Frame widened by R) and give the same value; every theorem of both packages depends only on propext, Classical.choice, Quot.sound (axiom records and an own walk over the declarations agree), and the closures are kernel-checked (14/14 modules, --fresh 2/2 rc 0, planted controls fire). Notes: (a) the #5 statements do not cover a const (read-only) result object; (b) nmexp_pin7c73739 and p1exp_pin7c73739 list 0132, 0254, 0566 in class (i) but have no claim rows for D2 #38 and #61, only unit-level findings that the tinyxml2 D2 pin Gen has neither deviation's op.

# Check by an agent: re-check packages #2 and #5 at cirlean next3 7c73739 (veriforch, labelled, outside the pre-registrations)
An agent of the evidence-owner session. Check dir: this directory. Replay dir ~/fv_paper/replay/n3pkg25-20261030T111132Z: pkg2/ and
pkg5/ (cp -rL copies), bld2/ bld5/ (my recompile, -DElab.async=false), bld2n/ bld5n/ (my recompile, Lean's default flags),
ctl/ (controls), probe/ (probe files), regen5/ (my cir2lean output). Record of inputs: prereg/T/ADDENDUM_recheck_next3_veriforch.md,
sha256 1d9b867edaa517aa27898f24405554dc6c362d73a1ff38d350d8b4c0ee48be90 (= the brief's). Method of checks/t23next2-20261028T061053Z
and checks/tier1-20261029T164912Z. Every script, lean, leanchecker and cir2lean run, scan and interpreter run went through
pjobs_v3.py with coreh_guard_v2 (cmds_*.txt, pjobs_*.log, guard/).

## 1. Hashes and copy: PASS (sums/, out/w1_copy.out, out/w5_after.out)
- Announced and computed (sha256sum): #2 SHA256SUMS 10d03d31460bd3dc3f9ee11ad429a2d7d8bc0f4f06821c1c61b8c9fde93b92bb, REPORT.md
  672861083621745ad98b5173a323a6ee6c1168cc6c8d3e714c928bceac78f8de; #5 SHA256SUMS fd78b31430f2934076c334ae49e5bcf8c15eebb2c1a7bb7d205797f8917255f1,
  REPORT.md ee2d54f9d56ead77f618ad6253a0f9f266f204de9e800a34ee53c2a121572eb2. All four equal the announced prefixes.
- sha256sum -c: #2 19/19 OK, #5 29/29 OK before the runs (2026-10-30T11:23:57Z, 11:23:58Z), in the copies, and after all runs
  (11:39:56Z, packages and copies). Each package holds exactly its listed files plus SHA256SUMS, no symlinks; the file lists
  are the same after the runs. Copies: 0 symlinks, diff -rq empty. Nothing was written or chmod-ed in the packages.
- The oddity: both logs/leanchecker_fresh.log are empty (e3b0c442...). leanchecker prints nothing when it accepts, so an
  empty log cannot tell an accepted run from no run; my own --fresh runs are in item 5 (they also print nothing, rc 0).

## 2. Pin and Gen: PASS (pin/, gen/, out/w1_pin_before.out, out/w4_pin_after.out, out/w4_pincov2.out)
- ~/cirlean_frozen/next3_7c73739_20261030/.lake/build/bin/cir2lean: sha256 9c75efeada5522b49c647f8404867521cf8343dc6d5267e17e8840423fa1f36d,
  = the build manifest's bin/cir2lean entry and = gentable_next3_pin/bin/cir2lean_pin_7c73739. Manifest
  8d2cc1ff96e4b41ae950ddc3e328b93c79bf0ec9fff7b9857262a848dba1352f: 1017/1017 OK before and after; all 201 .olean files of the
  frozen build (what my LEAN_PATH reads besides the package) are manifest entries. Nothing was built in the frozen tree.
- Gen table SHA256SUMS 6a50093481489b2c9381030755c797e50f80d4e63437b8616eb5c92a9afd323c (= announced): 1857/1857 entries OK.
- #2: both Gen modules are byte-identical to gentable w/T2U_*/pin.lean: binary_protocol d12a0ab327b1ae981b111eade078cd08bc8de1343dfd4b8b370dd9f7272233a0,
  compact_protocol fad3254062970a86adaa79297752e9d10e9406c2309820b4b8addf5e4b96911b. The binary Gen is also next2's; the
  compact Gen differs from next2's (4afdd6db4dbb00c8147d6ac8ef42add44ffa4a8ce86f997eaacfc1ac98c865f8) in one line of
  fn_thrift_compact_protocol_read_varint64 (`.load 48 3 (.int true 32)` becomes `.retLoad 48 3 (.int true 32)`). The
  FuncDecls of the three claim roots are identical in next2's and next3's Gen and contain no call.
- #5: the frozen cir2lean, run in my replay dir on ~/veriforch/runs/prereg_d2_tinyxml2_w1/v0/lib/unit.cir (sha256
  c2146d7b5d9091152d34a33aeea49dfc9efe10e06ba25e2a15289debf856697b, as in REPORT.md; the producer's cir2lean.log names the
  frozen copy veriforch_frozen/D2_20261025T030336Z/..., whose unit.cir has the same sha256): rc 0, 26210 lines, equal to the
  package's src/Gen/v0_lib/Unit.lean (425ff8d85a17aba9e6edbc22be4b9939386f16626f44b9326426d88ced9dc055) except line 2, the
  input path in the header comment.

## 3. Statements (stmt/, gen/fd_*.diff, gen/rec_*, stmt/stmt5_lean.out, probe/stmt5.lean)
#2: PASS. The three proof files are byte-identical to t2_unionpun_next2_424e821's (its SHA256SUMS
59083fd5006162ce128d3e38016f7ac7b01b333ff8e3b4b1df3acb16156d3f19 checks 26/26): 0132 67cfe800e886aca3..., 0254
7e1c11b2352b1147..., 0566 6a1d9624ba287948...; so are the three statements. One theorem per file; no sorry, admit, axiom,
native_decide, implemented_by or extern in either package's VO sources.
#5: the change is the retslot shape and nothing else.
- Old statements = the claimed D2 results: the D2 run's lean_d9ae8e5/VO/v0/lib files (84f3e42343d53c1a58fda524d27c77baa05083da7ef37ba031a9de5159b724fb,
  a44d69eb39b73b40d4fb1179384d9c5a21860129d9a4d8d3ac6c3cf749a9fe75, as in REPORT.md); the run's verify.json has status proved,
  trust kernel, and an obligation whose text (binders : statement) equals the old theorem text (566 and 654 characters).
  New: 947adb672db4c5fc61ca11a381661f21f5b5c7ded7627143621563560462a59c, 41c3239f6ecf943b00da6178d42cb63f008ffa1800d5c7c1d18dc5c06a1c8ad8.
- Side by side, binder by binder (stmt/D2_38_binders.txt, stmt/D2_61_binders.txt):
  - #38 NextSibling: the 20 old binders (b nb k kn p res v0..v7 v9 v10 m hb hh hp) are unchanged. Added: br, kr, oldr,
    hbr : br < m.next, hkr : kr ≠ .readonly, hbrb : br ≠ b, hbrnb : br ≠ nb, hret : m.blocks br = some ⟨kr, true,
    .record "tinyxml2::XMLHandle", .agg [oldr]⟩. Arguments [.ptr (.loc b [])] become [.ptr (.loc b []), .ptr (.loc br [])];
    the post `r = some (.agg [.ptr res]) ∧ Frame m m' []` becomes `r = none ∧ m'.blocks br = some ⟨kr, true,
    .record "tinyxml2::XMLHandle", .agg [.ptr res]⟩ ∧ Frame m m' [br]`.
  - #61 FirstChild: the 7 old binders are unchanged except that hnp gains the conjunct `br ≠ nb ∧` inside its ∃. Added: br,
    kr, oldr, hbr, hkr, hbrb, hret (record tinyxml2::XMLConstHandle). Same argument change; both cases of the post
    (np = .null: [.ptr .null]; np ≠ .null: [.ptr fc]) move from r to R's block, r = none, Frame m m' [br].
  - No hypothesis is dropped. Proofs unchanged except #61's rcases pattern, which names the new conjunct; imports, options and
    the @[cir_spec] attribute unchanged. The four helper proof files are byte-identical to d9ae8e5's.
- The added br ≠ nb hypotheses restrict nothing: E1 and E2 in a fresh process derive each statement with them removed from
  the package theorem (null case: another nb; otherwise R's block holds a handle record and nb's an XMLNode record).
  hbrb : br ≠ b (R is not *this) remains an assumption.
- Gen trace: between the d9ae8e5 Gen (7a29d2eea0116f7b...) and the pin Gen the two root FuncDecls differ exactly by the
  retslot rewrite (a second pointer parameter, ret .void, ssaName %retobj, entry block [0, 12], `.alloca 1 ... "__retval"`
  replaced by `.cast 1 .bitcast 12 ...`, the final `.load 11 1 ...; .ret (some 11)` replaced by `.ret none`); the four callee
  FuncDecls and the records tinyxml2::XMLHandle, XMLConstHandle, XMLNode are identical.
- Does the new statement say as much about the function? Yes, for the result objects it covers. With Returns = evalCall
  ends ok with Exit.ret and Frame m m' mods = m.next ≤ m'.next ∧ ∀ b ∉ mods, b < m.next → m'.blocks b = m.blocks b, the old
  statement says the call returns normally with the value .agg [.ptr res] (#61: [.ptr .null] or [.ptr fc]) and changes no
  existing block. The new one says the call returns normally with no value, R then holds exactly that value with its kind
  kept, alive and typed as before, and no existing block other than R changes.
- What it says about R: R must be a live block below m.next, not read-only, of record type tinyxml2::XMLHandle (#61:
  XMLConstHandle) holding an aggregate of one member with any value, and not this. A fresh non-const local meets this:
  alloca makes a stack block holding ctx.initVal 32 ty, which is .agg [.undef] for both types (#eval and rfl in the probe).
  Not covered: a const result object (allocaConst, a read-only block). cirlean lets its initialization write
  (Memory.lean write?, Basic.lean storeAt), but hkr excludes it; the old statement, whose function built the value in its
  own __retval, gave the value whatever object the caller then initialized. The helper constructor specs carry the same
  restriction (hk : k ≠ .readonly).
- Negative control: the package theorem does not type-check against the #38 statement with .agg [.ptr p] in R (Type
  mismatch, probe line 56, the only error of the probe).

## 4. Axioms: PASS (tables/axioms_summary.txt, tables/axioms_enum.tsv, tables/axioms_print.tsv, ax/, twin/, build/)
- One fresh lean process per module, on my copy and on my recompile: every theorem declared in the module, from its constant
  list (#2: 320 in 6 modules, #5: 207 in 8, auxiliary simp and equation lemmas included), with Lean.collectAxioms (what
  #print axioms calls; Lean 4.35 reads the per-module axiom records of imported declarations) and an own walk over the
  declarations themselves through all imports (types, values, recursor rules; no records). All within {propext,
  Classical.choice, Quot.sound}, records = walk for every theorem, no constant missing. The 9 package theorems (3 verdicts
  of #2; 2 verdicts and 4 helpers of #5) depend on exactly these three by both computations, in the copy and in my build.
  #print axioms of the source theorems: 3/3 and 6/6 exactly [propext, Classical.choice, Quot.sound]; no error lines.
- Planted controls in the same setting (module CtlAx, VOD2.CheckAll2 imported): ctl_from_ax and ctl_indirect [ctl_ax],
  ctl_sorry [sorryAx], ctl_propext [propext], ctl_clean none; records = walk for each.
- Recompile from my copy's sources against the frozen build: all 14 modules rc 0, no error or sorry lines. With Lean's
  default flags 12/14 .olean files are byte-identical to the package's; the two #5 verdict modules differ in bytes but hold
  the same 91 and 92 constants, equal by Expr.equal in type and value, with the same extension entry counts (twincmp.lean).
  With -DElab.async=false the auxiliary lemma names differ and the theorem types are equal.

## 5. Kernel replay in my copy: PASS (tables/leanchecker_*.tsv, lc/, fresh/, control/)
- LEAN_PATH = copy lib + frozen next3 build, LEAN_NUM_THREADS=1, ulimit -v 32 GiB; lean bf8d54e4714cc4b0..., leanchecker
  12c38901cdbfab17... (v4.35.0).
- leanchecker per module: 14/14 rc 0, no output. leanchecker --fresh VOEquiv.CheckAll3: rc 0, 98.4 s, no output;
  --fresh VOD2.CheckAll2: rc 0, 105.2 s, no output (REPORT.md: 99 s and 105 s).
- Controls: BadCtl (a false theorem added with the kernel check skipped) rejected, rc 1; BadUse (imports BadCtl) accepted by
  plain leanchecker (rc 0, own declarations only) and rejected by --fresh (rc 1); GoodCtl rc 0 plain and --fresh.

## 6. Exposure (results files only; sha256 in tables/exposure_files.sha256)
- nmexp_pin7c73739 (gaps7/retslot pass order, the not-modelled return op): T2union#0132, #0254, #0566 in class (i), reason
  NOOP (the unit's pin Gen has no such op).
- p1exp_pin7c73739 (the empty-store pointer check P1): the same three in class (i), reason NODROP (no dropped empty store or
  copy in the unit).
- D2 #38 and #61 have no claim row in either check; both cover the 159 claims T2 102, T2union 3, T3 54. Both READMEs treat
  tinyxml2 D1/D2 at unit level: nmexp, their pin Gen has no such op (txml/); p1exp, no store or copy of an empty type in
  their own-pin Gen (txml/D2_tinyxml2_ops2.tsv is empty). nmexp's txml/D2_tinyxml2/pin.lean (252eeed6d046e360...) equals #5's
  Gen except line 2 and line 26200, the unity file name (prereg_d2_tinyxml2 vs prereg_d2_tinyxml2_w1). In #5's Gen I count 0
  lines with "not modelled" and 0 with .unknown. No class is recorded for D2 #38/#61; the unit-level results leave nothing
  to classify. REPORT.md section 3 of #5 states class (i) from its own reading, not from rows of these checks.

## Deviations and limits
- regen5.sh printed "diff rc=0" for the nmexp comparison: that $? followed a $(sha256sum ...) in the same echo. The diff
  file gen/nmexp_txml_vs_pkg.diff is right (one changed line, 26200).
- axrun.sh ctl CtlAx (rc 1): CtlAx imports no Lean, so the enumeration part failed (9 error lines); its 5 #print axioms
  lines were as expected. Rerun in the package setting by axrunctl.sh (ctlpkg, rc 0).
- Written, never run: scripts/ctl.sh (superseded by ctl2.sh), axprobe.tmpl (by axprobe2.tmpl), pincov.sh (by pincov2.sh, a
  path offset), collect.sh (by collect2.sh, which joins #print axioms lines wrapped at 120 columns).
- stmt.sh's verify.json comparison gave cmp rc 1: a trailing newline only (585 vs 584 bytes; same text by collect2.sh).
- Not done: elaborating #2's statements at next2 (the files are byte-identical); reading the exposure checks' scripts or
  verifying their SHA256SUMS (results files only, as briefed).
- Core-h: 0.2138 (67 guard logs, waves 0-6, tables/coreh_w0_w6.txt), plus the two small jobs of waves 7-8 and the final
  hashing job. No messages sent; nothing external.

Written 2026-10-30T11:44:56Z (date -u) by an agent. Files: scripts/, cmds_*.txt, pjobs_*.log, out/, guard/, sums/, pin/, gen/, stmt/, lc/, fresh/, build/,
ax/, twin/, control/, tables/; SHA256SUMS covers every file here except itself.
Exception: the final hashing job writes guard/w9_sums.log, out/w9_sums.out and pjobs_w9.* while or after it runs; those are not in SHA256SUMS.
