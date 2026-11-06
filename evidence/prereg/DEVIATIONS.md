# Deviations and events after freezing v1 (append-only; dated entries)

- 2026-10-24T09:18Z: veriforch (the orchestrator session) started a feasibility pass on C and D before any run: front-end
  coverage only (zlib/tinyxml2 through cir2lean, commons-lang3 through Soot/JimpleLean, es-toolkit through StrictTS,
  CardDemo through coblean), no LLM, plus a check of the rules against veriforch's CLI and records. Rule sent to the orchestrator session:
  a v2 may fix executability only (commands, status mapping, budgets); populations, samples, seeds and outcome
  definitions stay as frozen, because front-end coverage is part of D's "blocked" outcome. The paper reports the
  numbers of the real run, which re-measures front-end coverage.

- 2026-10-24T09:30Z: veriforch's feasibility pass finished (09:30Z by its log; $0 model spend; front end and
  extraction only; logs ~/veriforch/scratch/prereg/, report ~/veriforch/notes/prereg_feasibility.md). Observed before
  any proof run (the real run re-measures all of these):
  - D front-end scope of the samples: zlib 77 in scope / 23 gap; tinyxml2 53 / 38 gap / 9 not emitted; commons-lang3
    39 in scope / 34 gap / 25 gap via a callee / 2 not found; es-toolkit 29 in the subset / 71 blocked; CardDemo 11 of
    44 extracted, 9 elaborate.
  - C builds: 51 of 58 cJSON commits build on cirlean 88e6008 (7 fail under -std=c89 with the pinned clang); tiny-regex-c
    5 of 5.
- Exploratory CI verdicts on selected C commits, in a non-C1 configuration (unity build, cirlean 87a2905, tests_misc_tests,
  --attempts 0): b2890c8d unknown (finished 07:59Z, before the v1 freeze); a78d9755 unknown (08:39Z, before); 5cc0e39f
  behaviour_changed (08:51-09:12Z, AFTER the v1 freeze). v1's disclosure listed only 349ef187 and f28a468e (both
  unknown); b2890c8d and a78d9755 were not known to the evidence owner at the v1 freeze.
- Tool defects found by the feasibility pass after the samples were frozen: (i) extract_units drops cirscan's missing-call
  column (gap names only "gap:external"); (ii) the jimple scope check misreads model-table headers naming two classes;
  (iii) refutation on linked builds runs cirrun on the first translation unit only; (iv) CI on linked builds compiles only
  the top generated module. DECISION (evidence owner): (i)-(iv) may be fixed before the pin, because they are defects and
  not coverage extensions; no coverage extension aimed at the sample's gaps is allowed before the run, and the sample's
  gap lists are not to be passed to tool owners for that purpose. The fix of (ii) changes the scope record of 15 sampled
  lang3 units; 5 move from blocked to in scope: StringUtils#join([SCII), ToStringBuilder#append(S),
  ToStringStyle#appendSummary(StringBuffer,String,boolean[]), StringUtils#join([ZC), ToStringStyle#appendDetail(StringBuffer,
  String,float[]). The paper adds a sensitivity line for lang3 that leaves out these 15 units.
- v2 of both pre-registrations frozen (PREREG_C_v2.md, PREREG_D_v2.md; SHA256SUMS_v2): executability changes only (C: R1
  library-only targets, --attempts 0, per-commit budget; R2 replay command; R3 C2 commands with --no-equiv; R4 record
  mapping and per-run guard log; R5 jsmn default build; R10 veriforch frozen copy. D: R2; R6 status mapping; R7 per-unit
  command; R8 attempt definition; R9 900 s for generated modules; R10). Populations, samples, seeds, orders and outcome
  definitions unchanged (SHA256SUMS_v1).

- 2026-10-24T09:45Z: JimpleLean's owner (the Java maintainer session) asked how the lang3 sample runs and offered to close general
  gaps before the pin (non-ASCII Character properties, double-to-text, java.text.Normalizer). Answer: method per D v2
  (veriforch bridge, vo verify --only, no JUnit/JVM diff), pin recorded by the orchestrator session at run start (snapshot 20261024T0553Z or
  later), crash-only fixes on a branch from the pin. General improvements before the pin are normal development; the
  sample's membership and gap lists were not shared, and the Java maintainer session was asked not to look them up.

- 2026-10-24T10:12Z: StrictTS wrong-translation defect at the suggested pin b1155cc (not a crash): Number.isInteger/
  isSafeInteger/isFinite/isNaN were constant false on arguments not statically typed number (unknown, unions); affects
  es-toolkit eq, isLength (x2), isFinite, isInteger, isSafeInteger in the checked-dynamic mode. Found by StrictTS's own
  translation validation against Node (276 public functions, 11,372 inputs), independently of the sample. DECISION
  (evidence owner, before D started): D's StrictTS pin is a branch from b1155cc carrying only that fix (~40 lines),
  recorded by the orchestrator session with its hash; same rule as defects (i)-(iv).
- Clarification (v2 did not state the mode): D's es-toolkit part runs in StrictTS's strict subset. The frozen population
  rows are the strict coverage file (es-toolkit.strict.json at a15926a), and the feasibility pass measured strict scope.
  The checked-dynamic mode is not part of D; the defect above (dyn-only) does not touch D's verdicts. The evidence owner
  checked privately that one sampled unit (src/predicate/isLength.ts) is among the functions the defect would affect
  in dyn mode; sample membership was not disclosed to the tool owners.

- 2026-10-24T10:21Z: D's StrictTS pin = ae0eee4b03faf445fef28e8f06a21c551342a856 (branch pin-d), one commit on top of
  b1155cc941eea236358314b1d116bc5bc268bb11. Verified read-only by the evidence owner: git diff --stat b1155cc ae0eee4 =
  frontend/dist/calls.js, frontend/dist/exprs.js, frontend/src/calls.ts, frontend/src/exprs.ts (43+, 8-); no Lean file
  changed. StrictTS reports all 134 corpus/example programs translate byte-identically under both commits.

- 2026-10-24T10:34Z: D executability decisions before the run (veriforch's questions in ~/veriforch/notes/prereg_d_tools.md):
  (1) defect (v): the StrictTS adapter names units by bare function name (794 functions under 512 names; 36 of the 100
  sampled rows would be wrongly "not emitted"). DECISION: es-toolkit extraction uses StrictTS's own coverage mode
  (--coverage --emit-lean) at ae0eee4 over es-toolkit 32f4c8f, mapping each sampled row by file, line, name and kind
  (the tool that defined the frozen population); covered-but-not-emitted rows count as blocked: not emitted.
  (2) R6 additions: a proof that elaborates but fails the kernel replay is not proved; it is an infrastructure error
  "replay failed", reported in two parts: "(kernel) deep recursion" (replay recursion limit) and any other kernel
  rejection, the latter listed unit by unit.
  (3) Pins approved for the run start: coblean 20261024T0803Z (D), JimpleLean 20261024T1029Z or the newest green at
  start (general JDK Unicode tables), StrictTS ae0eee4, cirlean 88e6008; for C equiv-lean 99b598e on cirlean 88e6008.
  Noted: commons-lang3's one-time module compile (~18 core-h) was not in the feasibility price; model $ unchanged.

- 2026-10-24T10:59Z (reported by the orchestrator session): C first start 10:39:50Z crashed at once in the frozen copy (pinned-cirlean
  LEAN_PATH assertion compared a symlinked path with lake's resolved path); the driver mis-recorded C1 order 1 as
  "unknown" and C2 jsmn steps 8-10 as "done"; no model call ($0); stopped by PID 10:41Z. Crash fix only
  (~/veriforch/runs/prereg/C/crashfix_1.diff): resolved-path comparison in lean.py; a vo ci run ending without ci.json is
  recorded as outcome "crash", never as a verdict. New frozen copy ~/veriforch_frozen/C_20261024T104212Z (manifest
  5604c044...), smoke-tested outside the set (cidemo b88e74c..018ebeb). Aborted start archived in
  runs/prereg/C/aborted_20261024T1040Z_leanpath_crash/ (CRASH.md). C1 and C2 restarted from the beginning 10:52Z; pins in
  runs/prereg/C/pins.json. The aborted start's records are not used.
- D started 10:57:49Z (reported by the orchestrator session) from frozen copy ~/veriforch_frozen/D_20261024T105335Z (manifest 871ce181...),
  including defects (i) and (ii), the es-toolkit coverage-mode extraction and the R6 replay split; pins cirlean 88e6008,
  JimpleLean 20261024T1029Z, StrictTS ae0eee4, coblean 20261024T0803Z. A one-unit dry run per population (zlib, tinyxml2,
  es-toolkit, CardDemo) ran from that copy before launch; at the freeze the evidence owner checks which units were used
  and that the official run re-ran them. Observation: veriforch's default "intended contract" call for gap units costs
  ~$0.11 per blocked es-toolkit unit (feasibility estimate $0.04); within the cap; nothing changes after the start.

- 2026-10-24T13:35Z (reported by the orchestrator session): D crash fix 1 (commons-lang3). First lang3 run (10:57-13:30Z) ended with
  70/100 sampled units "infrastructure_error (tool crash: generated module ... does not check)". Cause: Soot prints an
  enum's header as "enum class X" and the Jimple adapter's class regex took "class" as the class name, so the methods of
  all 16 enum classes in the jar collided in one class "class" and their per-method modules clashed. Fix: that regex only
  (~/veriforch/runs/prereg/D/crashfix/crashfix_1.diff); on the pinned jar's 675 class files it changes exactly the 16 enum
  class names. New frozen copy D_20261024T133359Z (manifest 4ca7c314...) = first copy + that diff. lang3 re-run from the
  start (all 100 units) on the new copy; the first run's records kept in runs/prereg/D/crashfix/ (CRASH_1.md) and not
  used. The other four populations have no Java classes and continue on the first copy. At the freeze the evidence
  owner checks the diff is the regex alone and that lang3's reported outcomes come from the re-run.

- 2026-10-24T14:29Z (reported by the orchestrator session; the user via the coordinating session asked to parallelize C1 and D): procedural change, per-unit
  commands, budgets, dispatch order and stop rules unchanged.
  C1 switched 2026-10-24T14:24:23Z to frozen copy C_20261024T142304Z (manifest 44c73e8e...) = C_20261024T104212Z + two
  diffs (runs/prereg/C/crashfix_2_parallel.diff): (a) driver --workers 6, commits dispatched in order_c1.tsv order, each
  in its own VO_CI_RUN_DIR, only atomic .olean caches shared; budget gate: completed spend + B of every in-flight commit
  >= $350 stops dispatching; resource guard (load > 320 or MemAvailable < 150 GB -> wait). (b) a replay defect fix
  (c1_replay_fix.diff): when one theorem of a verdict module failed, Lean wrote no .olean, so an accepted theorem's
  leanchecker replay could not run; the accepted theorem is now re-checked alone in its own module for the replay.
  The orchestrator session: none of the 5 finished records is affected. Order 6 was in flight, stopped by PID and re-dispatched (no record).
  Orders 1-5 kept: 1 and 2 behaviour change shown; 3, 4, 5 unknown.
  D switched 2026-10-24T14:26:21Z for zlib (3 workers), tinyxml2 (2), lang3 (3): copies D_20261024T105335Z_par and
  D_20261024T133359Z_par = running copies + the driver diff only (sha256 1415ad3b...). Units dispatched strictly in
  sample order; a unit waits (never skipped) while its call-graph closure overlaps a running unit's; extra workers have
  their own vo run directories with caches linked to the population's; stop rule ledger + $0.80 x in-flight >= $500.
  Interrupted at the switch and re-dispatched: zlib unit 11, tinyxml2 unit 31, lang3 (still in its one-time compile);
  their pre-stop model spend (at most $0.80 per unit, ~$1.60) is not in the D ledger. es-toolkit and CardDemo had
  finished on the first copy. At the freeze the evidence owner checks (b) against C1 order 1-5 records (the claim that
  they are unaffected) and the interrupted units' final records.

- 2026-10-24T15:14Z (reported by the orchestrator session, found by the StrictTS maintainer session): third StrictTS translator soundness defect at the D
  pin ae0eee4: string indexing s[i] translated with String.prototype.at semantics (s[-1], s[1.5] give characters where
  JS gives undefined). Affected es-toolkit functions per StrictTS's analysis: deburr, dedentImpl (strict), trimEnd,
  trimStart (dyn). D keeps ae0eee4 (the run had started). Checked by the evidence owner: none of the four is in
  D/sample_estoolkit.tsv, and none is in the recorded call-graph closure of any sampled es-toolkit unit
  (records/estoolkit/results.jsonl). The paper reports the defect with the D pin.

- 2026-10-24T18:30Z (reported by the StrictTS maintainer session, master after 63835ca): StrictTS fixed four translator bugs found by its translation
  validation: Number.isX, JSON.stringify, s[i] (above), ?. on a value of type any. Only the Number.isX fix is in the D
  pin ae0eee4. Checked by the evidence owner for the other three, over the 14 claim-bearing es-toolkit units (3
  proved_mechanical, 11 partial) and the 18 functions of their recorded closures, using the unit sources in the run's
  units.json (copy replay/vo-D-20261024T1434Z): no JSON.stringify, no optional chaining, no Number.is* call. The only
  string indexing is in parseHex (closure of hex, unit 84, partial): raw[0], raw[1], raw[2] under raw.length === 3,
  where .at and [] agree (in-bounds integer indices). So none of the three later fixes changes a D claim. Blocked and
  timeout units carry no claim. D stays at ae0eee4; the paper lists the four defects with the D pin.

- 2026-10-24T20:51Z (found by the evidence owner while re-checking D tinyxml2): units 80 (tinyxml2.h:152 StrPair::Set) and 88
  (tinyxml2.h:573 XMLUtil::IsNameStartChar) are recorded infrastructure_error, "no outcome record (status None)", in
  results.jsonl and summary.json. Their vo verify logs (records units/080.log, 088.log) end with "<unit>: stuck
  (negative cache, 3 earlier attempts)" and the JSON result "stuck". The 3 earlier attempts are recorded in
  prereg_d_tinyxml2/v0/lib/units/<unit>.json and are Lean failures:
  - StrPair::Set: cir_loop error, leftover goals;
  - IsNameStartChar: simp maximum recursion depth, leftover goals.
  They were made when the functions were callees of earlier units (both appear in unit 40's closure). Under R6,
  status stuck maps to timeout; infrastructure error is reserved for LLM-error-only attempts or a tool crash, and
  neither applies. The driver did not record the negative-cache result. The paper therefore reports tinyxml2 with R6
  applied to the verify output: timeout 22, infrastructure error 0. It also states the values the driver recorded
  (20 and 2) and the reason. All other outcomes are as recorded (checked with tools/d_outcome_check_v2.py).
  Watch zlib and lang3 for the same pattern.
  Precision (same day): the attempts were made inside earlier units' runs, whose cost they carry: IsNameStartChar
  during unit 40 (ParseAttributes, worker 0, 16:07-16:20Z; its record file is from 16:11Z), StrPair::Set during
  unit 53 (ParseDeep; its record file is from 16:40Z). Both units' logs show the attempts.

- 2026-10-24T21:50Z (reported by the orchestrator session; the user via the coordinating session raised the load rule): procedural change 2 for D, scheduling only. Switched
  2026-10-24T21:48:48Z:
  - zlib and lang3 now run from new frozen copies D_20261024T105335Z_par2 and D_20261024T133359Z_par2, with
    --resume --workers 3 --load-max 450 --free-slots 1 (the first unit of each population is dispatched whatever the
    load; the RAM guard still applies);
  - C2 (no load guard) is unchanged;
  - the order and stop rules are unchanged.
  Interrupted and re-dispatched: zlib's in-flight unit and up to 3 lang3 units, all dispatched less than a minute before
  the stop. Their unledgered model spend is at most $0.80 each.
  Checked by the evidence owner (read-only):
  - each _par2 copy differs from its _par copy only in scripts/prereg_d.py, the added CHANGE_from_*_par.diff and the
    updated SHA256SUMS;
  - both diff files have sha256 7164d9be512d5c68585a761426f3b2a760949b4667e2bd4d7a50dad2321a5ab2 (as reported);
  - the diff changes 7 lines: the dispatch guard (free slots) and the new option. Nothing touches outcome mapping,
    order or budgets.
  At the freeze: check the interrupted units' final records, and that each unit has exactly one final row.

- 2026-10-25T00:49Z (found by the evidence owner re-checking D commons-lang3, finished 2026-10-25T00:14Z): the recorded outcomes are
  blocked 29, timeout 29, infrastructure_error 42 (0 proved). The 42 are two tool crashes:
  - 34 units: TypeError, JimpleAdapter.assemble() got an unexpected keyword argument 'n_lookups'. The Jimple
    adapter's assemble in the frozen copy lacks the parameter the CIR adapter has (D_..._par2 orch/veriforch/adapters/
    jimple/adapter.py:270 vs adapters/cir/adapter.py:149). These units had statuses before the crash: 18 proved with
    replay PASS, 6 conditional, 4 stuck, 4 blocked, 1 partial, 1 budget.
  - 8 units (orders 30, 32, 35, 37, 76, 77, 78, 80): RuntimeError, a generated module (EventCountCircuitBreaker
    StateStrategyClosed.isStateTransition) does not check (scheduler.py:99); no status.
  Recomputation with R6 on the recorded fields (tools/d_outcome_check_v2.py) agrees with the 8 RuntimeError rows and
  the blocked and timeout rows. Its mapping does not apply the crash override, so it disagrees on the 34 crash rows.
  PREREG_D_v2 allows a recorded crash fix and a re-run of the affected units. Reported to the orchestrator session, who decides. If no fix
  and re-run happen before the freeze, the paper reports lang3 as recorded and explains both crashes. The class of
  the 8 generated-module failures (infrastructure error, or blocked as an extraction failure under R6) will be
  recorded here when applied.

- 2026-10-25T00:52Z (reported by the orchestrator session): D commons-lang3 crash fix 2 and a re-run of the 42 crashed units. Causes per the orchestrator session, both
  veriforch bugs:
  (1) JimpleAdapter.assemble lacked n_lookups (34 units);
  (2) a 238-character per-method module name pushed Lean's temporary .olean file name past the 255-byte limit
  ("failed to create file"; the 8 EventCountCircuitBreaker units). So case 2 is a tool crash, not an extraction gap,
  and the class question above is settled as infrastructure error before the fix.
  Fix (runs/prereg/D/crashfix/crashfix_2_lang3.diff, sha256 7d60057e...): assemble accepts and ignores n_lookups;
  module-name components over 160 characters keep a 142-character prefix plus a 16-hex hash.
  New frozen copy D_20261024T133359Z_par3. lang3 resumed 2026-10-25T00:51:09Z (crashfix2_switch_time.txt) with the
  same options, re-running exactly the 42 units.
  Checked by the evidence owner (read-only):
  - _par3 differs from _par2 only in adapters/jimple/adapter.py and adapters/jimple/build.py (the two changes
    above), the added CHANGE_crashfix2_from_par2.diff and SHA256SUMS;
  - lang3_results_before_crashfix2.jsonl equals my copy of the original results;
  - the 58 non-crash records are byte-identical in the current results.jsonl;
  - the 42 crash orders are absent, pending re-run.
  At the freeze: check the 42 re-run records (one each), recompute outcomes, and axioms + replay of claimed theorems.

- 2026-10-25T02:19Z (D2, before any D2 run; decisions by the evidence owner on the fixers' reports):
  1. tinyxml2 external:strchr: cirlean adds a strchr model (8/8 native difftest cases), its commit being the fix.
  2. tinyxml2 not-emitted: cirlean (the C maintainer session) found the general fix outside cirlean, in veriforch: (a) -femit-all-decls in
     the clang -fclangir invocation (61 of 67 units are inline methods of tinyxml2.h that clang never emits); (b) the
     extraction reading the inline loc literal (6 out-of-line members got their in-class declaration's line).
     PREREG_D2_v1 does not require the fix to live in the fixer's repository, so the orchestrator session is asked to make both as the
     recorded fix for this family. If the orchestrator session declines, the family is recorded as declined.
  3. zlib external:lseek64 and external:open: declined by cirlean, with reason. Their results come from the OS, and a
     sound model must leave them open, which cirlean's deterministic semantics cannot express without a broad change.
     No substitute family. zlib runs in D2 with no targeted fix, so its change measures only the other tool changes
     since the D pins.
  4. lang3: JimpleLean (the Java maintainer session) found a D1 measurement artifact. veriforch decides "modelled" from section headers of
     JimpleLean's docs/LIBRARY_MODELS.md that name a class exactly (adapters/jimple/build.py modelled_library). At D's
     pin (JimpleLean 1029Z) two sections had descriptive headers ("Boxed primitives (Integer, Long, Short, Byte,
     Character, Boolean, Double, Float)" and "java.lang.Character: code points and classification"), so methods of
     those classes counted as unmodelled though most are modelled (Character 19 of 22). Part of D1's lang3 "blocked"
     count is therefore this artifact.
     - D1 is reported as run, with a post-hoc, labelled count of sample units blocked only by such already-modelled
       methods.
     - For D2: JimpleLean changes only the two target families: exact  and
        sections, compare/toChars/codePointCount and missing overloads, builder
       subSequence, each difftested.
     - JimpleLean's commit note splits the methods into "already modelled, newly listed" and "newly modelled", and the
       D2 analysis splits lang3's transitions the same way.
     - veriforch's header rule stays as at the D pins until D2 has run, so the other boxed classes are not unblocked
       by a reader change inside D2.

- 2026-10-25T02:22Z (D2 fixes delivered, before any D2 run):
  - tinyxml2 external:strchr: cirlean commit d9ae8e529e4c4c95ef08021d87079678244eb66b (strchr model; 8 difftest cases
    against libc match; Examples build). It is cirlean's D2 pin. Changes since the D pin, 88e6008..d9ae8e5: 18 commits,
    general tool work done before D2 was frozen (loop binders for arrays, pointers and memory; linked lists; cJSON
    trees and cJSON_Delete; string walking; memset/memcpy; frame closers) plus the targeted d9ae8e5.
  - tinyxml2 not-emitted: veriforch made the fix (runs/prereg/D2/d2fix_tinyxml2_not_emitted.diff, sha256
    f6a97874...):
    - prereg_d2_tinyxml2.toml gets cxxflags -femit-all-decls and loc_from_definition = true;
    - adapters/cir/build.py, gated by that option, takes cir.func's inline loc literal (the definition) over the first
      loc(#ref) (the in-class declaration).
    Checked by the evidence owner: the diff names no unit, and both changes are gated per target (C1b's cJSON target
    and all other builds are unchanged). The orchestrator session's front-end-only check on D's pin: 460 units; no re-run row is
    "not emitted" any more. That is emission only, no outcomes.
  - lang3 (JimpleLean): a third label, "already modelled at 1029Z, behaviour fixed": Character's int predicates and
    getType on negative code points, isDefined(-1), and the codePointAt/codePointBefore exception messages, each
    difftested against the JVM. A String/StringBuilder.charAt message defect outside the two families stays as at
    1029Z in the D2 pin.

- 2026-10-25T11:42Z (records of the D2 and C1b runs as reported by the orchestrator session, the TypeScript maintainer session and the Java maintainer session; to be checked from copies):
  - D2 pins:
    - StrictTS 44d6b9b: not-emitted -> 881c69c (covered generic functions emitted at one instance; claims are about
      that instance); subset:unsupported-type -> e2c2d05 (Iterator as a record of method closures). Change list
      ae0eee4..44d6b9b: 197 commits. Whole population (strict): emitted 97 -> 182, not-emitted 139 -> 74,
      unsupported-type 121 -> 92.
    - JimpleLean snapshot 20261025T0300Z. docs/D2_CHANGES.md labels each method listed / fixed / new against the
      1029Z Native.lean. Running veriforch's reader logic on the old and new docs, exactly the 25 population tokens of
      the two families flip to modelled.
    - cirlean d9ae8e5.
  - D2 frozen copy ~/veriforch_frozen/D2_20261025T030336Z (manifest sha256 d8851ecb..., 87 files).
    - veriforch changes inside it: the StrictTS coverage mapping now reads StrictTS's funs.json and records
      generic_instance per unit (needed to map the generic instances); the tinyxml2 not-emitted fix.
    - Started: tinyxml2 03:08:44Z, es-toolkit 03:10Z, lang3 05:11:25Z, zlib 07:22:20Z.
    - Per population, pins.json records the pin and the change list since D's pin.
  - StrictTS performance issue, present at both D's ae0eee4 and D2's 44d6b9b: the @[simp] lemmas F64.min_comm and
    F64.max_comm can spend the whole heartbeat budget in AC ordering in ts_auto's final simp. That makes a cost
    failure (timeout), not a soundness issue. Fixed at StrictTS 0cfa367, which is not in either pin. At the freeze,
    count the D and D2 es-toolkit units recorded as timeout at the heartbeat limit whose Lean log shows acLt, and
    report them as possibly affected.
  - C1b (pass 2), 03:49:39Z-07:13:36Z:
    - frozen copy C1b_20261025T033823Z (manifest sha256 9d4020b6...); pins cirlean ec40522, equiv-lean b171660;
    - build fix (buildfix.diff, sha256 e6ef7bde...): -Wno-error=int-conversion and -D_ISOC99_SOURCE, flags only, the
      same for parent and commit, for orders 12, 14, 27, 46, 48, 53 and 55;
    - result as reported: cJSON blocked -> behaviour change shown 1 (order 14: cJSON_Parse, parse_string,
      print_number, print_value); blocked -> unknown 6; unknown -> unknown 44; tiny-regex-c unknown -> unknown 3;
      new kernel verdicts 0; .40, 13.0 core-h.
  - C2 ended on its budget stop (50.55 of 50; the step in flight finished):
    - jsmn: all 30 rows;
    - tiny-regex-c: 21 of 33 steps, 12 unattempted;
    - cJSON: 50 unattempted.
  - veriforch checker bug, found and fixed 11:03Z: a Lean check that exited non-zero without printing an error (an
    out-of-memory abort) counted as passed. Now success needs exit 0 and the .olean on disk. Scans: 1 cached
    passed-without-olean (quarantined, not a reported result); all 1,372 proved/conditional/partial unit records
    carry the axioms line of a completed check. Pre-registered claims also need the in-run kernel replay.
  - veriforch deleted Lean build products (.lake/build, .olean caches) of finished runs at the VM optimizer's
    request; manifests in ~/veriforch/notes/disk_prune/.
    - Before the deletion I had copied, with oleans: C1 (cert packages for the witnesses), D1 es-toolkit, CardDemo
      and tinyxml2, C2 jsmn.
    - Copied with oleans after the deletion, at 11:4xZ: D1 zlib (still had them), D2 es-toolkit and tinyxml2, C1b,
      C2 tiny-regex-c.
    - D1 lang3 (the crash-fix-2 re-run) has no oleans left. Replaying its claimed theorems needs a rebuild from the
      kept sources and pins, at the freeze.

- 2026-10-25T11:49Z (C1b check by the evidence owner): the 54 outcomes recomputed from the copied records equal veriforch's: 1
  behaviour change shown (order 14), 53 unknown; 76 functions (4 behaviour_changed, 72 unknown); reasons 46 heartbeat,
  17 no distinguishing input, 6 rewrite failed, 3 recursion depth; $2.4043, 13.02 core-h.
  - Order 14 (7ca2c994, "incorporate hooks feature ..."): the 4 behaviour_changed witnesses (cJSON_Parse,
    parse_string, print_number, print_value) were re-run from my copy, with the cert package's Gen modules rebuilt on
    cirlean ec40522 because veriforch had pruned their oleans. Each prints VOW DIFF with the old version returning
    normally and the new version reaching "ub read of an indeterminate or ill-typed value".
  - Cause: the commit adds globals g_cJSON_malloc, g_cJSON_realloc and g_cJSON_free, but the witness runs both
    versions on memory built from the OLD module's initial memory. The new version therefore reads its own hook
    globals where they do not exist.
  - Reading: these witnesses confirm no behaviour difference of the code. Order 14 is reported as unknown in pass 2
    (witness invalid: the new module's globals are absent from the shared initial memory), with this reason. Told to
    The orchestrator session. A recorded harness correction (each version with its own globals) and a re-run of order 14's candidates would
    replace this reading.
  - C1's pass-1 witnesses are unaffected: 10 of 11 have both versions returning normally; order 34's UB comes from
    null hooks in its argument.
  - The build fix matches the PREREG: flags only, a separate target used for the 7 commits, parent and commit alike.

- 2026-10-25T11:51Z (D1 zlib and lang3 checked by the evidence owner from copies; C1 witness harness):
  - D1 zlib (finished 07:20:33Z, copy replay/vo-Dz-20261025T1140Z): the sample hash matches; 100/100 outcomes agree
    with the record; counts and Wilson intervals match summary.json. Recorded: proved_model_stated 10, conditional 4,
    blocked 23, timeout 57, infrastructure_error 6.
    - Of the 6 infrastructure errors, 5 (orders 55, 71, 81, 87, 95) are the negative-cache misrecording: the verify
      logs say "stuck (negative cache, 3 earlier attempts)", and the earlier attempts are Lean failures or budget.
      Under R6 they are timeouts.
    - Order 99 is a genuine tool crash (AttributeError in adapters/cir/adapter.py render: a list in proof.options). It
      stays an infrastructure error unless crash-fixed and re-run.
    - zlib under R6: timeout 62, infrastructure_error 1.
  - D1 lang3 after crash fix 2 (copy replay/vo-Dl3b-...): the 58 earlier records are unchanged. The re-run of the 42
    gave proved_model_stated 19, partial 4, conditional 4, timeout 13, infrastructure_error 2. Totals as recorded:
    proved_model_stated 19, partial 4, conditional 4, blocked 29, timeout 42, infrastructure_error 2.
    - Reading of the wall kill: two units with a recorded status (order 1 proved, order 25 conditional) were killed
      at the 30-minute wall. veriforch's mapping makes them timeouts and so does mine (checker v3, R6 row "killed at
      the 30-min wall").
    - The 2 infrastructure errors (orders 59, 64) are the negative-cache misrecording, so timeouts under R6. lang3
      under R6: timeout 44, infrastructure_error 0.
    - The claimed theorems' oleans were pruned; my independent replay needs a rebuild at the freeze.
  - C1 witness harness (the orchestrator session's fix of 2026-10-25):
    - bug 1: both versions ran on the old module's initial memory;
    - bug 2: voObs compared the first n globals, not the candidate's blocks.
    The 11 pass-1 witnesses all differ in the return value itself, so bug 2 does not matter. For bug 1, the old and
    new globals lists are identical for 8 of the 9 commits (orders 1, 6, 7, 28, 34, 40, 45, 50). Order 2 differs by
    one string literal, so the orchestrator session re-runs its candidates with the fixed render as a recorded check, and I re-run that
    file.

- 2026-10-25T11:53Z: C1 order 2 re-checked with veriforch's corrected witness harness
  (runs/prereg/C/witness_recheck_20261025/PWitness_..._matchrange_1_fixed.lean, sha256 0cfe8ab5...; each version on its
  own initial memory, the candidate's blocks after both modules' globals). Run from my tiny_regex_c_lib cert copy
  (cirlean 88e6008): VOW DIFF, old returns 1 and new returns 0 on the same candidate block. So all 11 C1 witnesses
  stand. zlib D1 order 99: the orchestrator session does not re-run it (the crash is fixed in the live tree only), so it stays an
  infrastructure error with that cause.

- 2026-10-25T12:00Z (D2 and C2 checks by the evidence owner, from copies):
  - D2 outcomes recomputed with tools/d_outcome_check_v3.py: es-toolkit re-run and held-out, and the tinyxml2 re-run.
    All 300 rows agree with veriforch's outcome column; each file has one row per frozen-sample unit (the held-out
    files match D2/heldout_*.tsv); counts and Wilson intervals match each summary.json.
    - es-toolkit re-run vs D1, same units: 7 units leave blocked (5 to proved_mechanical, 1 to proved_model_stated, 1
      to partial), all 7 recorded as generic_instance (claims about that instance); 1 partial -> timeout.
    - tinyxml2 re-run vs D1: 33 leave blocked (24 to timeout, 7 to proved_model_stated, 1 to partial, 1 to
      conditional), plus smaller moves.
      - One unit goes refuted -> proved_model_stated, which shows that a model-stated statement can change between
        runs (D2's statement excludes D1's counterexample).
      - One goes timeout -> refuted: order 91, XMLUtil::ToUnsigned, verdict real_bug. Re-run with cirlean d9ae8e5's
        cirrun on the run's unit.cir (same binary as veriforch's dep), every candidate's outcome equals the recorded
        replay. Convention-respecting decimal inputs out of unsigned range ("999999999999", "-1") reach UB in
        sscanf %u, which ISO C leaves undefined. The hex candidates hit the same generic message, "format outside
        the modelled subset, or a value out of the range of its object", so the paper cites only the decimal
        out-of-range witness.
      - Order 87 (ErrorIDToName) reproduces as in D1.
  - C2 final (copy vo-2-*/c2): tiny-regex-c steps 0-20 recomputed, 0 mismatches. The 12 unattempted steps (21-32)
    have no ci.json, as recorded. Totals over steps 1-20: changed 25, cached 89, rechecked 5, new without the model 3,
    new with the model 17, failed 187, regressions 5, blocked 2; 239 calls, $119.21, 16,657 core-s. C2 total
    $150.55 (cap $150, the step in flight finished); cJSON 50/50 unattempted.

- 2026-10-25T15:06Z (T: Apache Thrift, the user's request via the coordinating session at ~15:00Z): PREREG_T_v1.md frozen (sha256
  be02f96d...), manifest SHA256SUMS_T_v1 (b167d544...): tools thrift_paths.py, select_t3.py, draw_t2.py and the T3 list
  t3_commits.tsv (150 commits: 7 CVE/CVE-class by the repository's own threat model and CHANGES.md, 143 from the last 12
  months; no commit message names a CVE number). Sent to the orchestrator session and the equiv-lean maintainer session. T1 (no model) was running at veriforch when
  frozen. The T2 sample is to be drawn by draw_t2.py from T1's unit list and frozen in T/ADDENDUM_T2_sample.md before
  any T2 run.

- 2026-10-25T15:2xZ (T, clarification before any T2 run or draw): PREREG_T_v1 defines the T1 line denominator (every
  source file) and the strata, but not the file set of the unit frame. Fixed now, as veriforch read it: the T1 unit
  list and the T2 frame are the units in library source files of the supported languages (thrift_paths.lib_source)
  plus the C++ sources under compiler/ (the compiler stratum); tests, tutorials, examples and benchmarks are not in
  the frame (they stay in T1's line denominator). At the pin the TS frame is empty: lib/ts and lib/nodets hold only
  test files and a .d.ts declaration (their libraries are JavaScript), so the TS strata have N_s = 0. T1 lines
  (veriforch, ~/veriforch/notes/thrift/T1_lines.json): total 496,747; supported 258,013 (51.9%); frame lines C++
  112,250, Java 23,297, C 14,802, Rust 11,369, TS 0; untyped JavaScript 22,845 (4.6%).

- 2026-10-25T15:3xZ (D1/D2 lang3 and T: veriforch's jimple adapter skipped every interface, reported by the orchestrator session): the
  class-header regex of adapters/jimple/build.py allowed one space before the class name, and Soot prints interfaces
  as "public interface  X" (two spaces). Every interface .jimple was skipped: calls to its methods were recorded as
  gap:unmodelled:<interface method>, and its default and static methods never became units. The orchestrator session's population-level
  measure for lang3 (D2 pin, read-only re-extraction): 97 of 675 classes skipped; with the fix, in scope 3,823/5,068
  -> 4,153/5,258 units (+190 units, 186 in scope; 144 former gap units in scope). The live tree was fixed at 15:2xZ.
  Decision (evidence owner): D1 and D2 lang3 stay as run (the pre-registrations allow crash fixes only, and both
  passes share the bug, so D2 vs D1 stays like-for-like). The paper reports the bug and its measured impact, and a
  labelled post-hoc count of the sample units whose closure carries an interface-method gap token, and of those blocked
  only by such tokens, computed by the evidence owner from the records and the list of skipped interfaces. For T, the
  fix lands before any T2 draw: T1's Java unit list must come from the fixed adapter, with the fix recorded in T's
  pins (asked of the orchestrator session).

- 2026-10-25T16:0xZ (T, clarification before any T2 draw): T1's C/C++ unit list (~/veriforch/notes/thrift/
  T1_cxx_units.tsv, 5,197 units, sha256 e4c32878...) includes 427 source definitions from the clang AST that no
  translation unit emits (gaps = not-emitted; mostly in the 38 lib/cpp TUs whose CIR cirlean's parser rejects:
  `volatile` on cir.atomic.fetch). They stay in the T2 frame and count as blocked (not-emitted), as in D's
  populations, and as PREREG_T_v1's in-scope definition ("emitted by the front end") implies. The frame is then
  independent of the parser defect; outcomes follow the tool pins recorded when T2 starts.

- 2026-10-25T16:0xZ (T, clarification before any T2 draw): Rust test code inside library files. lib/rs/src holds 187
  #[test] functions in #[cfg(test)] modules. Ruling: every function inside a #[cfg(test)] module (the #[test]
  functions and any helpers there) is test code, not compiled into the library, and is excluded from the T2 frame like
  the test directories (kept in T1's data as kind=test and in its line counts).

- 2026-10-25T16:1xZ (T, clarification before any T2 draw): Java units that the compiler synthesizes (bridge methods,
  access$ accessors, lambda bodies compiled to synthetic methods, <clinit>) are excluded from the T2 frame, as D's Java
  population excluded them ("method with a body (not synthetic/bridge/<clinit>)", PREREG_D_v2). 201 units on the
  preliminary Java list (1,948 -> 1,747). veriforch delivers the final Java TSV with a `synthetic` flag after two
  adapter fixes land (duplicate method keys; a model-table reader bug that hid JimpleLean's boxed/List/Map/Set/Iterator
  models) and T1 Java is re-run; the frame uses that final list.

- 2026-10-25T15:54Z (D2 lang3 and T: veriforch's Java unit index and bridge methods, reported by the orchestrator session at ~15:45Z): veriforch keyed
  Java units by class, method name and parameter types, without the return type, and kept the last declaration with a
  given key. When a class declares a method and the compiler's bridge for it (covariant return: same name and
  parameter types, a supertype as return type), Soot prints the bridge after the method, so `vo verify --only <unit>`
  reached the bridge, not the sampled method. Evidence owner's count from the D run's class-level Jimple cache
  (evidence/tools/lang3_bridge_count.py, sha256 6b4a6ab2...; evidence/checks/lang3bridge-20261025, with a positive and
  a negative control): 74 colliding keys in 50 lang3 classes. Sample units affected: D1 lang3 0 of 100, hence 0 in
  D2's re-run of D1's units (same keys); D2 held-out lang3 2 of 100 (order 50 DiffBuilder$1.getRight(), order 80
  DiffBuilder$8.getLeft()), not run yet. Ruling: a sample unit that the harness did not reach is an infrastructure
  error, as a tool crash is. If orders 50 and 80 run on the D2 pin, they are re-run with the fix as a recorded crash
  fix (gated to colliding keys, taking the non-bridge declaration); if the fix lands before they run, they run once
  with it. T: 11 frame units, fixed in veriforch before T2's frozen copy (the fix is part of T's pins).

- 2026-10-25T15:54Z (correction of three time stamps above): the entries stamped 16:0xZ (not-emitted definitions), 16:0xZ (Rust
  #[cfg(test)]) and 16:1xZ (Java synthetic units) were written before 15:50Z; date -u read 15:50Z when the slip was
  noticed. The stamps were typed, not read from the clock. Content and order are unaffected; no T2 draw has happened.

- 2026-10-25T16:06Z (T and D2 lang3: the bridge fix, from the orchestrator session): veriforch's fix (notes/thrift/jimple_bridge_order_fix_20261025.diff,
  sha256 33585de3351e549413e70962d8870ac6670c6b00e40fc2bef5a075443f4f7b7d, landed 15:58:08Z; copy in
  evidence/checks/lang3bridge-20261025) places the real method last in each shared-name group, so the name index
  resolves to it (adapters/jimple/build.py 13260bea... -> 6a358f61...). The orchestrator session's tests: Thrift's 11 names and lang3's 74
  names now resolve to the real method, units otherwise identical; T1's Java TSV unchanged (908fd092...). It is part of
  T's pins, and it is the crash-fix copy for D2 held-out lang3 orders 50 and 80 (D2 copy + this diff).

- 2026-10-25T16:06Z (T3, implementation details from the orchestrator session before T3 starts; consistent with PREREG_T_v1 T3): (1) C++: `vo ci` runs on
  the TUs whose include closure (clang -MM) contains a changed file; each changed function gets one verdict in a home
  TU (its own .cpp's TU, else the first TU in compile_commands order where it changed). (2) A commit is blocked: build
  if any affected TU fails to build at the parent or the commit (errors kept per TU). (3) B = $0.50 x distinct changed
  functions per language, by symbol. (4) Pins: cirlean at its fix commit (volatile atomics, __throw models), the same
  as T2's, recorded when T3 starts; T1's C/C++ scope numbers stay as measured at T1's pins. (5) Rust: each older
  revision gets its own `cargo vendor`, its Cargo.lock sha256 recorded; build scripts run only in bwrap. (6) Java:
  veriforch has no old/new equivalence step for Java; unless one exists when T3 starts, Java commits end `unknown`
  with that reason, and behaviour-change witnesses are still attempted where the adapter supports them.

- 2026-10-25T16:24Z (D1/D2, all populations: per-slot recompilation, reported by the orchestrator session from T2's dry run): veriforch wrote the worker
  slot's path into generated module text (C/C++: the .cir path in the Gen header of non-modular builds; Java: the
  jimple store path in every Shape/Method module), so each parallel slot recompiled its target's generated modules on
  first use (up to ~250 s for a large C++ TU, ~30 min for a Java target). A unit that was the first in a fresh slot
  could reach the 1,800 s wall partly or wholly through that compile. Ruling: outcomes stay as recorded (a wall kill
  is a timeout). The paper reports a labelled post-hoc count of the timeouts that coincided with a slot's first
  compile, from veriforch's per-unit marking (requested for every D1/D2 timeout), checked by the evidence owner
  against the logs.

- 2026-10-25T16:24Z (T2/T3 pins, from the orchestrator session): cirlean ffab71ea54802c61bcfab3d389f12c94bb85b388 (volatile atomic parser fix, libstdc++
  __throw_*/__glibcxx_assert_fail models; regression 123/123), or cirlean's type-punned-access fix commit if it lands
  before T2's frozen copy. veriforch's path fix (a relative .cir name for cir2lean, one shared jimple store path) goes
  into T2's copy; it changes path strings only. The final pins are recorded when T2 starts.

- 2026-10-25T16:32Z (T, before the T2 draw: Rust list and a count correction): veriforch's final Rust T1 list
  (notes/thrift/T1_rsts_units.tsv, sha256 f6da27f5f3c775dd83e2f5ac085fcd571752fb5d70350b8a2fb24cced092fd92) has 781
  units: 536 frame units (kind fn 31, method 505; in scope 257, 47.9% [43.7, 52.2]) and 245 units inside #[cfg(test)]
  modules (kind=test: 185 #[test] functions and 60 helpers), outside the frame by the ruling above. The earlier entry's
  "187 #[test] functions" was a miscount; the source at the pin has 185 (evidence owner's count of #[test] attributes in
  lib/rs/src). The ruling is unchanged. Rust adapter for T: build.py 146da622... (diff
  notes/thrift/build.py.rsprune_20261025.diff, sha256 1d4c919a...): constructs that abort Aeneas are recorded as gaps,
  Aeneas `sorry` bodies count as gaps, and wrapped definition names are mapped; Charon/Aeneas fdebf20; build scripts of
  vendored crates ran only in bwrap without network. Checked by the evidence owner
  (evidence/checks/thriftT1-20261025/rust_check.out): counts, components and interval equal veriforch's.

- 2026-10-25T16:35Z (all C/C++ studies: cirlean's type-punned access defect; evidence owner's decision): reported by equiv-lean
  (the equiv-lean maintainer session) and confirmed by cirlean (the C maintainer session). At every cirlean commit the paper uses (88e6008, d9ae8e5, ec40522, 28e2380,
  ffab71e), memory is element-typed without bytes, so a scalar load or store of a different width than the element it
  reaches (`*(u32*)p` on a char array; `*(char*)&x` on an int) gets a one-element meaning, which differs from C (for
  example `*(char*)&x = 7` on x = 256 gives 7, natively 263). cirlean's fix (branch `punning`, 2d65713, unmerged) makes
  such accesses undefined ("type-punned access"); it breaks 8 cirlean example proofs whose specifications quantify over
  the block's type, and veriforch's cJSON contracts are written the same way. Decision (option B): the paper's C/C++
  results stay at their pins; the paper states the limitation, and every claimed C/C++ theorem and UB finding is
  checked for such accesses by a static scan of its ClangIR (pointer casts between scalar types of different widths;
  conservative along array paths, record members not affected), with flagged functions run on cirrun at 2d65713. The
  fix merges after the freeze, for the next revision. PREREG_M's cirlean pin is ffab71e. equiv-lean's scan of its 22
  ClangIR files (punscan_v1.py 614835dc...) found no such cast.

- 2026-10-25T16:38Z (T3, from the orchestrator session before T3 starts): (1) veriforch's Java CI now has an old/new equivalence step through
  equiv-lean's `equiv_jimple` (751764f, JimpleLean 0149Z), so T3's 34 Java commits get verdicts; T3's Java front end
  is JimpleLean 0149Z (T2's is 0300Z), recorded in T3's pins. (2) The hook's fifth verdict `unchanged` (class file
  byte-identical, only Soot's local names differ) maps to `unknown` with the reason "bytecode identical; no verdict
  theorem", since PREREG_C_v2 has four verdicts and a claim needs a replayed theorem. T3 pins so far: cirlean ffab71e,
  equiv-lean b171660 rebuilt on it (cert_pin_t3.env sha256 221e4dae...). H part one: builds and one smoke input per
  harness now, the corpus sweep after T3 launches (the user's ordering via the coordinating session); pins cirlean ffab71e and a frozen script
  copy with a manifest.

- 2026-10-25T16:41Z (N, before any coblean NIST run; decisions on two questions from coblean, the COBOL maintainer session): (D1) "one file directory per
  module that persists from program to program, as EXEC85 does" is read as GnuCOBOL's cobol85 harness does it: the
  XXXXX* files are removed before each main program, and only SUBPRG follow-on programs keep the files of their
  producer. Under the literal reading, GnuCOBOL itself fails or loses 29 tests in 9 programs (SQ129A, SQ130A, SQ141A,
  SQ142A, SQ225A, IX111A, IX216A, IX217A, IX218A) that need those files absent; with the harness rule its per-program
  counts equal GnuCOBOL's published SQ.txt and IX.txt (coblean's report). The same rule applies to both systems.
  (D2) At the paper's coblean pin (snapshot 20261024T2306Z), the front end turns WRITE ... ADVANCING into an
  unsupported statement, and every NIST program writes its report that way, so every program the front end accepts
  would stop at its first report line. Decision: the NIST run uses a front end that treats WRITE ... ADVANCING as a
  plain WRITE (the record bytes are the same; printer spacing is not modelled). The change is limited to
  tools/cobolfe (diff and sha256 in N/ADDENDUM_N_inputs.md), the semantics (Cobol oleans) is unchanged, and the
  verdict vectors do not depend on spacing. The paper states both: at 2306Z every program stops at its first report
  line (unsupported), and the results with this front end, labelled. Also recorded: GnuCOBOL's generated C is compiled
  with -std=c17 (GCC 15 defaults to C23 and rejects IC235A and IC401M); extract.py applies EXEC85's column-7 option
  processing (manifest f639c71d...).

- 2026-10-25T16:41Z (H, before part one; readings on veriforch's corpora, the orchestrator session): (1) bzip2/bzip2_compress_target has no public seed
  corpus (OSS-Fuzz packs seeds only for bzip2_decompress_target; the upstream at f5dfc960 has no corpus directory),
  so its part-one outcome is "no public corpus". It is not a part-two candidate: "whose corpus inputs all run" needs at
  least one input that ran, not a vacuous all. Part two's ranking among the remaining candidates is then
  yajl-ruby/json_fuzzer, cgif/cgif_file_fuzzer, cgif/cgif_rgb_fuzzer, subject to part one. (2) The cgif corpora are
  produced, as OSS-Fuzz does, by building and running the upstream test programs with OSS-Fuzz's seed-writing wrapper
  (veriforch: own gcc lines, no meson, in a sandbox without network); 43 of the 55 seeds are checked against the
  upstream fuzz/seeds.sha256, and the other 12 are generated the same way and reported as unchecked.

- 2026-10-25T16:41Z (T3 pins and dry run, from the orchestrator session): T3's Java pins are JimpleLean 0149Z and equiv-lean 751764f (equiv_jimple),
  pin file cert_pin_t3_v2.env (sha256 4036b59b...); C/C++ and Rust pins unchanged (cirlean ffab71e, equiv-lean b171660
  rebuilt on it). T3's last dry run uses list commits (orders 1-3, and Rust orders 21 and 46) for build and front end
  only (materialize, build, extract, module checks), with no verdict obligation and no model call, in separate dry-run
  directories.

- 2026-10-25T16:41Z (cirlean heap typing, from the C maintainer session, for the type-punning decision of 16:35Z): malloc, calloc, operator new and
  realloc(NULL, n) return untyped storage; the first bitcast of the returned pointer to T* types the block (T[n/sizeof
  T] when that divides, else one T); later casts never retype; realloc keeps the type; memcpy/memset into untyped
  storage is UB. So a malloc-to-T* cast is benign when it is the block's first cast and later accesses use T (or the
  same width). The fix at 2d65713 checks element types along array paths only: a punned access into a record member
  keeps the one-element meaning there too. The C maintainer session is building a flow-aware, interprocedural scanner (cirpun) over the
  frontend's parse, with categories FLAG, RECORD, SIGN and CHAR and controls, by ~20:00Z; it replaces the per-cast
  greps (punscan_v1, punscan_fv) for the final check.

- 2026-10-25T16:55Z (T3, implementation detail from the orchestrator session, consistent with PREREG_C_v2): proof and olean caches are shared per library
  target across commits, as in C1 and C1b; every claimed verdict theorem is still checked and kernel-replayed. A cost
  projection against the Tue 03:00Z stop follows T3's dry run; the pre-registered order and stop rule decide what is
  left unattempted.

- 2026-10-25T16:57Z (T4 start and pins, from the equiv-lean maintainer session; a ruling on library contracts): T4 started 2026-10-25T16:57Z at equiv-lean master
  8a77ffd (no .lean file differs from 751764f; checked by git diff). Pins: C++ cirlean 28e2380 (equiv-lean's vendor
  copy of cir2lean), clang upstream-4955d32b, libc++ headers from cir2c-eb2a332, instantiation TCompactProtocolT and
  TBinaryProtocolT over TTransport; Java JimpleLean 20261025T0149Z, Soot 4.7.1, javac 17 --release 8 (T1's jar); Rust
  Charon 0.1.293 and Aeneas fdebf20; Lean v4.35.0. Generated modules from veriforch's T4 delivery
  (scratch/t4gen/deliver/T4_MODULES.tsv sha256 60300769..., SHA256SUMS 89ab0669...; copies in
  evidence/checks/T4-20261025). Budget stops: spec $120, each language $400, total $1.4k (cap $1.5k). Gaps declared
  before any proof: C++ glibc htons/htonl/ntohs/ntohl and libc++ basic_string; Java String.getBytes, new
  String(Charset) and ByteBuffer; Rust varint-rs VarintWriter (opaque in Aeneas), the Cursor io::Write transport
  module and byteorder's blanket impls. Ruling: PREREG_T_v1 accepts transport contracts; any other library function may
  get a contract model only if it is marked and listed, and a function pair proved under such a contract is reported
  as "proved under library contracts" with the list, apart from "proved" (transport contracts only). Otherwise the pair
  is "not finished".

- 2026-10-25T16:59Z (H part one, readings before the corpus sweep; from veriforch's builds and smoke runs at cirlean ffab71e):
  (1) Locations: cirlean's UB results carry no source location. veriforch adds a locator (a scratch copy of cirlean's
  interpreter that only tags each UB with its function, call site and loop); its outcome and message must equal the
  pinned cirrun's byte for byte on the input, otherwise the input is reported without a location. (2) Not every UB
  report of the semantics is undefined behaviour in C: some are limits of the model (for example "memcpy: byte-level
  access not modelled" when cgif's harness copies 2 input bytes into a uint16 field, and "realloc: not a live heap
  block" after cJSON's malloc(1) is typed as a scalar). Each distinct report is classed as (i) UB in C, confirmed by a
  sanitizer report or by reading with the clause of the standard cited, (ii) a model limit, with the code and the C
  rule that makes the operation defined, or (iii) unconfirmed. An entry point is "UB found" only with at least one
  location of class (i); an entry point whose inputs stop only at model limits is "blocked", with the limit named, as
  PREREG_H_v1 defines blocked; class (iii) is listed apart. (3) cJSON: all 14 seeds end in a newline, so the harness
  returns at its first check (`data[size-1] != '\0'`) on every one; its part-one result is reported with that note.
  The cJSON harness theorem of veriforch is about a parse-only variant of cjson_read_fuzzer with locales off
  (Theorem's build has ENABLE_LOCALES, and cirlean does not model localeconv); the paper states this next to any
  comparison with Theorem's proofs. (4) The pin stays cirlean ffab71e for all of H (no re-pin during the study).

- 2026-10-25T17:02Z (T3, disclosure by the orchestrator session; ruling): a veriforch worker testing the new equiv_jimple hook ran `vo ci` on T3 list
  order 41 (1311cf3619^..1311cf3619, Java library target) with --attempts 0 --budget 0 at about 16:54-16:56Z, before
  the real run: no model call, but the commit's verdicts were computed early, which the dry-run rule does not allow.
  Result as reported: 9 changed functions, 2 behaviour_changed, 4 unknown, 3 unchanged (mapped to unknown); ci.json
  sha256 cd65f1f038e125e7e83f4f9350eae2623f83bea2fb86ae2fb4e90b1687ad1699 (copy and guard log in
  evidence/checks/T3-early-order41). Handling: the scratch directory stays untouched and nothing in T3 or its caches
  reads it; the real run recomputes order 41 from T3's frozen copy; the paper reports the real run and says whether it
  equals this early result. Ruling on T3 order 2 (a 2017 C++ commit whose TJSONProtocol TU fails with clang and boost
  1.90 under -std=c++11): the commit-level rule stands (PREREG_T_v1; the strict reading recorded at 16:06Z): the whole
  commit is "blocked: build", with the error.

- 2026-10-25T17:04Z (T2 and T3, full disclosure by the orchestrator session of early runs by its Java worker; no model calls in any): the worker read
  "outside the frozen order's first 10" as "order > 10". T3 list order 41 (1311cf36194ec3f860016f424b545866c43c193e):
  two smoke runs of tools/eqj_smoke.py (16:17:59-16:21:20Z and 16:23:58-16:25:10Z; 9 verdicts; smoke_1311cf3.json
  f713b9505ca6dc5b..., smoke2_1311cf3.json df0b3afccc08165c...), vo ci runs 1 (16:25:40-16:36:48Z, crashed on long
  names, no verdicts) and 2 (16:42:30-16:42:53Z, crashed), and run 3 (16:53:43-16:55:54Z, rc 0, --attempts 0 --budget
  0; the ci.json recorded at 17:02Z). T2: while testing the long-name fix, the worker ran `vo verify --no-llm` on the
  whole Thrift Java target (16:40:59Z and 16:53:41Z) and `--only NonblockingSaslHandler.<init>` (17:00:05Z, not a
  sample unit), leaving template-only outcomes for all 1,936 Java units, T2 sample units included: stuck 603, blocked
  933, gap 400, no proof (runs/thrift_java_lntest/v0/jar/verify.json, sha256
  e889cc07534fe1a6040b4a8c945febd09832eb1145df4e83a1b08e0357518a5a; my count of its statuses agrees; copies in
  evidence/checks/T2-early-lntest and T3-early-order41). Handling: these directories stay untouched and unread; T2's run
  directories and caches are fresh and read none of them (veriforch to confirm at T2's start); T2 and T3 outcomes come
  from the real runs only. Assessment: no model call, no proof and no verdict theorem was produced early; the T2 early
  run shows template failures and scope, which T1 already published, and served to test a general crash fix that is
  part of T2's pins.

- 2026-10-25T17:07Z (M, StrictTS, from the TypeScript maintainer session): the population drive runs 2 workers instead of the frozen configuration's 3, under the
  shared VM's standing rule of at most 2 mutation runs in parallel. No frozen file changes: the drive reads a copy,
  scratch/mutation/config_w2.json, that differs from config_strictts.json (afceac98...) only in "workers": 2 (its sha256
  to follow). Verdicts are unaffected: run_m.py settles the first 30 non-stillborn candidates of order.tsv whatever the
  worker count, and the time limits (60 min build, 1,800/900 s suite steps) are far above the ~11 min per mutant seen in
  the controls; every step still runs one core under the guard. The three controls, already running with the frozen
  configuration, finish as they are.

- 2026-10-25T17:10Z (M, cirlean and coblean semantics: readings before their first population mutant):
  (1) Baseline control. PREREG_M_v1's control "the unmutated copy passes the whole suite" is read together with its kill
  criterion ("... where the unmutated copy passes that test"): tests that fail or are declined at baseline count as
  neither kill nor survival and are reported as excluded. cirlean: t_gap_emplace (extra.cpp:59; UB "invalid memory
  read" where native prints 4, a documented model gap at every pin since it was added), so 174 of 175 cases count.
  coblean: the 2 TRUNC(BIN) mismatches of V.dt_bin and the 14 declined cases (V.ct, V.ct_fe). (2) coblean: the 4 Prop
  definitions and 3 Decidable instances (Codec.BinRange, Round.Exact, Round.FitsDigits, Data.NumFmt.Holds) count as
  proofs and are not mutated; the semantics' conditionals use the Bool functions (rescaleExact, quotExact, inBinRange)
  instead, and the Props are used computationally only in Cobol/Logic/Bounds.lean (a tactic, out of scope, not in
  cobolrun's build). A test row stops at its first killing case (which rows kill is still recorded). The test
  executable imports Cobol.Frontend.Load instead of Cobol (23 modules, all 14 in-scope files; its baseline equals the
  evidence run), so sorry counts cover those modules. (3) cirlean's scope readings (tool docstring): Prop-valued proof
  predicates (Mem.WF, Module.RoGlobals) are not mutated; signed-to-unsigned means a signedness argument replaced by
  false and .toInt replaced by .toNat; bit widths include roundBin's precision and exponent bounds (53/-1074/971,
  24/-149/104), which are not mutated; the 48 pattern rows `_ + 1` -> `_ - 1` stay and are stillborn if drawn. (4) Both
  run at most 2 mutants at a time (the shared VM's standing rule for mutation runs), each step on one core under the
  guard.

- 2026-10-25T17:12Z (N, ruling on the NIST runner's absent-file handling, before any in-scope NIST run): coblean's semantics takes
  OPEN errors as environment input (env.openError, Cobol/IR.lean:480 at the pin, default none, documented "e.g. 35:
  file not found"; fileOpen, Cobol/Sem/File.lean:136-145, returns what it gives). The NIST runner's CobolRun change
  fills this hook for files that have no input data and are flagged as required. Ruling: this supplies the
  environment, as input files do, and is accepted as a harness change, on three conditions: (1) the addendum lists the
  flagged files and the codes; (2) the codes follow COBOL 85: 35 when a non-OPTIONAL file is absent at OPEN INPUT or
  I-O; an absent OPTIONAL file opens as an empty file with status 05. If the semantics cannot express the OPTIONAL case
  through the hook, the programs that need it are reported with that limit named, never forced to agree. (3) The
  Cobol/*.lean oleans are byte-identical to the pin's. The paper says that the runner supplies open errors for absent
  files through the semantics' environment hook.

- 2026-10-25T17:14Z (M, StrictTS: harness bug, from the TypeScript maintainer session): the three controls on the frozen harness (c833c55) gave the recorded
  verdicts (manifest scratch/mutation/controls_SHA256SUMS, sha256 2f4e2703...). The first two population results
  (Num/F64.lean:57:8:ROR and 241:53:AOR) were classed "stillborn: theorem statement broken", but both mutants only make
  adjacent `example ... := by decide` proofs fail: run_m.py handled one build's errors in a single loop, each sorry
  inserted a line, and the next error in the file then pointed at the inserted line and read as a broken statement.
  The frozen rule says such proofs get sorry and the build is repeated, so both should have been built and tested.
  Handling: the drive is stopped; runs started under c833c55 stay as records in results/population_c833c55/ and do not
  count; the harness gets a minimal fix (map errors to commands in the unedited source, handle each command once,
  treat an error in an already-sorried proof as a broken statement) with a gate that fails on c833c55, unit checks and
  the three controls re-run; the population restarts from order position 1 with 2 workers after the fix's commit,
  run_m.py sha256 and diff sha256 are recorded here.

- 2026-10-25T17:21Z (T4, readings and interim notes from the equiv-lean maintainer session; nothing here is a result yet): (1) The C++ binary protocol's writeI16/
  I32/I64, their readers and the i32 length prefix pass an integer's object representation as `(uint8_t*)&net` to
  TTransport::write/readAll. C and C++ define such character access, but cirlean at 28e2380 has no byte-level memory
  (the type-punning finding of 16:35Z), so these pairs are reported "not finished" with that reason (a semantics gap,
  not a library contract), in line with the type-punning decision. The compact pairs do not pun. (2) First checkpoint
  reported: writeVarint32 (E) proved in C++ under the C++ transport contract (eq-cir, t4-cpp 2a404af, standard axioms).
  (3) A candidate discrepancy, not yet established: Rust's write_field_header (lib/rs compact.rs:555) takes the short
  form only for 0 < delta < 15, so a delta of 15 gets the long form where the specification, C++ and Java use the short
  form; the i16 delta can overflow (Aeneas panics, release builds wrap). PREREG_T_v1 requires the byte sequence run on
  each language's semantics before it is reported as a discrepancy; the Rust helper models io::Write for this function
  as a marked library contract.

- 2026-10-25T17:37Z (several items, recorded together):
  (a) T3 (the orchestrator session): with the commit-level rule, a blocked commit gets no verdicts for its other TUs
  (`--blocked-verdicts skip`); its outcome is "blocked: build" either way. Accepted. T3's Java pin stays JimpleLean
  0149Z (equiv-lean's jimple build needs it), so the 1728Z deep-recursion fix does not reach T3; such errors are
  reported with that reason. T3 driver changes before launch: per-run wall and core-hours scale with the run's verdict
  count; the budget stop counts finished spend, not reservations; outer cap 800 core-h.
  (b) T2 before launch (the orchestrator session): (A) Rust only: deterministic Lean failures of generated modules (exit 1 with messages,
  never timeouts or kills) are cached under the same content key, as successes are; without it most Rust units would
  time out on tool cost (the final dry run: 212 failing Lean runs, 3.4 min of a 10-min wall). New frozen copy =
  T2_20261025T170117Z + the recorded diff; C and Java paths unchanged. (B) Java start pin: JimpleLean 20261025T1728Z
  instead of 0300Z (the Java maintainer session's crash fix for "(kernel) deep recursion" on branches over signed bitwise results; only
  Jimple/Tactic.lean differs, the interpreter is unchanged); T2 has not started, so this is its start pin.
  (c) D1 lang3 order 59 (ArrayUtils.insert(int,double[],double[]); infrastructure_error with four "(kernel) deep
  recursion" messages): under D's rule a tool crash is an infrastructure error until its crash fix and re-run. Ruling:
  re-run it once with D1's pins plus only the crash fix (the Jimple/Tactic.lean diff applied to D1's JimpleLean), as a
  recorded crash fix; if the diff does not apply to D1's JimpleLean, or the re-run still fails, it stays an
  infrastructure error with the reason. A re-run on 1728Z as a whole is not allowed, since 1728Z also carries D2's
  fixes. (The fix addresses one cause of the message only, the Java maintainer session.)
  (d) H (the orchestrator session): to time the new file-input runner (needed because 23 cgif seeds exceed the argv limit), one corpus input
  ran early (cgif_file_fuzzer/noise256_large.seed, 0.76 s); its outcome is not used, and the sweep re-runs every input
  from frozen copy v2 (scratch/theorem/frozen_H2_20261025T1732Z). Runner change: h-cirrun = vo-cirrun with argument
  parsing changed only; vo-cirrun re-runs all 37 inputs of at most 16 KB as a byte-equality check; the locator is
  checked against h-cirrun.
  (e) M, coblean semantics (the COBOL maintainer session): two harness check defects. V.stm counted a verdict ending in "AGREE" as passing, and
  "DISAGREE" ends with it; V.hand counted only equal lines (differing lines are marked "!! "). Reading, per PREREG_M's
  kill criterion (the suite's own comparison): V.stm kills when the last word of its verdict is not AGREE; V.hand kills
  on any "!! " line, a missing program table, an equal-line count other than 28, or a column-header line (GnuCOBOL rc,
  model signal) that differs from the baseline's (the "== <path>" line excluded). Every mutant's raw outputs are
  kept; the analysis recomputes both rows from them for all 30, harness status and final status side by side;
  controls of the corrected rules passed (same-output runs survive; four synthetic one-edit failures are killed).
  Effect so far: mutant 9 (StringInto.lean:80:10:CND) moves from survived to killed (V.stm DISAGREE).
  (f) M part FE (the COBOL maintainer session): the old suite has the same V.hand blind spot. Ruling: the headline keeps the old suite as it was
  (the design measures the suite as it is, before and after added tests), and the corrected V.hand reading is reported
  next to it, labelled, for both sets, from the kept raw outputs.
  (g) N (the COBOL maintainer session): post-step abend_status_v2.py (sha256 b59349369ffe2b90...) applies the same-abend status rule after the
  frozen runner (final.json next to results.json), tested on synthetic programs; launcher launch_v1.sh (05ab3906...).
  Classification: the frozen classes stand (decided before any result): a Lean resolver exception inside cobolrun
  (9 IX programs) is "error", a Python exception in the front end (IX108A) is "unsupported"; the results add a column
  naming the mechanism, and the paper gives both readings where they differ.

- 2026-10-25T17:39Z (H, disclosure by the orchestrator session): before the sweep, veriforch's worker used yajl-ruby/json_fuzzer's only corpus input
  (seed.json) as its smoke input: vo-cirrun at 16:50Z; native builds at 16:55Z (clang 24, plain and UBSan) and 17:11Z
  (clang 20, all four builds, in bwrap); locator and runner checks at 17:14Z, ~17:19Z and 17:30Z; sweep-driver tests at
  17:20Z, 17:21Z and 17:31Z. Every run ended normally, on the semantics and natively; recorded in
  notes/theorem/H_part1.md with logs kept. Its outcome was therefore known before the sweep; the sweep re-runs it from
  frozen copy v2, and the paper says that this input's outcome was seen early. From now on only synthetic inputs run
  before the sweep. (bzip2's part-two status was ruled at 16:41Z: not a candidate.)

- 2026-10-25T17:39Z (M, cirlean, disclosed by the run's owner via the C maintainer session): the per-process build cap was raised from 32 GiB address
  space (draft section 4) to 256 GiB address space plus a 24 GiB RSS watchdog, after order 1's build failed to create
  threads under the 32 GiB cap (Lean reserves about 1 GiB per thread); suite cap unchanged at 32 GiB; transient
  resource failures are retried up to 2 times; order 1 re-run (its infrastructure row stays in results_cirlean.tsv,
  marked superseded); order 2 (built and survived under the old cap) stands; no outcome affected. New driver files:
  tools/build_cirrun_v4.sh b92667cb..., tools/run_mutant_m_v3.py aea36217..., tools/drive_m_v4.py 0baa790e...,
  drive_config_cirlean_v4.json cf778998.... Still at most 2 at a time, same order and stop rules.

- 2026-10-25T17:40Z (N, correction of PREREG_N_v1's disclosure; M part FE): PREREG_N_v1 says coblean left out IF "because it models no
  intrinsic function". That reason, as coblean gave it then, was wrong: at the pin the resolver models ABS, INTEGER,
  INTEGER-PART, MOD, REM, MIN and MAX (Cobol/Frontend/Resolve.lean:150-160), and CURRENT-DATE through the clock;
  CBTRN03C's FUNCTION MOD runs through it. The module rule did not depend on that reason. Part FE: under the corrected
  V.hand reading, set 1 on the old suite is unchanged, 18/30 (the same 5 V.hand kills: orders 1, 6, 7, 14, 27; checker
  hand_check.py 30ac492b..., results s1old_handcheck.tsv e2e81f5b..., with controls).

- 2026-10-25T17:44Z (T3 launch record, from the orchestrator session; a reading): T3 launched 2026-10-25T17:42:03Z from frozen copy
  ~/veriforch_frozen/T3_final_20261025T173358Z (SUMS 32320da92b2c05ba..., 208 files = the 17:25Z candidate + driver diff
  49e34f0b...); pins.json sha256 502514b178807a515d4b75bf595259b36f5a5b236caefa6fda6854c917b93913 (C/C++ cirlean ffab71e
  + equiv-lean b171660; Java JimpleLean 0149Z + equivlean-751764f-jimple-0149Z; Rust Aeneas fdebf20 +
  equivlean-7e1aaf0-aeneas with 8 vendor sets, sets.json c54526c3...; Lean v4.35.0; clang 4955d32b). START_DIRS.txt
  (be493901...): all 24 planned cache directories absent before launch, none of the early-run directories named;
  START_DIRS_post.txt (8f13817c...): every directory created at or after 17:42:07Z, no cache link outside
  runs/prereg/T3. A first attempt at 17:41:24Z exited at the driver's argument check before doing anything; relaunched
  with the identical command plus `--out runs/prereg/T3`, frozen code unchanged (LAUNCH_NOTES.txt). 12 gated workers,
  --blocked-verdicts skip, stop Tue 03:00Z. Reading (order 8, a Java formatting commit with no changed function): a
  commit with no changed function in a supported language has no kernel verdict, so its outcome is "unknown" with the
  reason "no changed function"; the census lists such commits apart, and none counts as certified (PREREG_C_v2's
  "certified equivalent: all equivalent" is not read vacuously).

- 2026-10-25T17:47Z (D1 lang3 order 59, the crash-fix re-run plan from the orchestrator session; precedence of two readings): D1's own par3 re-run of order
  59 never ran the tool: its log says "stuck (negative cache, 3 earlier attempts)", and those 3 cached attempts are the
  kernel deep-recursion crashes. Under the negative-cache reading it counted as a timeout in my D1 lang3 recount (44
  timeouts); under the crash reading it is an infrastructure error until its crash fix and re-run. Because the cached
  attempts were crashes, not failed proofs, the crash reading takes precedence for this unit: it is re-run once, and
  the re-run's outcome replaces the timeout, labelled as a crash-fix re-run. Plan (accepted): new copy
  D_20261024T133359Z_par3_cf3o59 = par3 + a 3-line recorded diff (new OUT dir, bridge dir with suffix -deeprec, target
  renamed so the run dir is new); the bridge = D1's JimpleLean + only the Tactic.lean diff 0300Z -> 1728Z; the run dir's
  cache = a copy of D1's without that one negative entry, no --retry-stuck; a fresh prepare; order 59 in slot 0 with D's
  wall (1,800 s) and budget ($0.80), one run. D1's directories stay untouched. If the diff does not apply to D1's
  Tactic.lean, or the re-run fails again, the unit is an infrastructure error with the reason.

- 2026-10-25T17:49Z (D1 lang3 order 59, outcome): the crash-fix re-run was not performed. The Java maintainer session's fix
  (runs/prereg/D_crashfix3_o59/crashfix_3_deeprec_Tactic.diff, sha256 66742c44..., 0300Z -> 1728Z, Tactic.lean only)
  does not apply to D1's Tactic.lean (1029Z, 313050a1...): patch -F0, default fuzz and git apply --check all fail;
  hunk 2 edits a symbolic-execution simp call that D1's file does not have (evidence apply_check_D1_Tactic.txt). Per
  the 17:47Z condition, the unit is an infrastructure error (a kernel deep-recursion crash without a fix that applies
  to the run's version); no hand-adapted hunk. D1 lang3 by R6 is now 19 proved, 4 conditional, 4 partial, 29 blocked,
  43 timeout, 1 infrastructure error (order 64 stays a timeout under the negative-cache reading).

- 2026-10-25T18:00Z (M, StrictTS: the harness fix, completing the 17:14Z and 17:07Z entries): fix commit 0003ada (branch modular),
  run_m.py only (+49/-42; sorry edits planned on the unedited source, applied bottom-up), run_m.py sha256
  a42c50b234346a753c2bae03c39bb95c9a669c5f67eba0beb094c4be9c307c90, diff c833c55 -> 0003ada sha256 dafed603...
  (both checked by the evidence owner). Gate: on c833c55 candidates #3 (Num/F64.lean:57:8:ROR) and #4 (241:53:AOR) were
  recorded stillborn; on 0003ada both build after sorrying the failing examples and are killed (separate check dir;
  manifest gate_SHA256SUMS 890d546d...). Unit checks test_plan_sorries.py (689d7dfe...): 0003ada 4/4, c833c55 1/4.
  Controls on 0003ada give the recorded verdicts (manifest controls_fix_SHA256SUMS 3d006902...). config_w2.json sha256
  c9e4b3617abffa96b79d7bf62b7d6caebdf64ec0d5e81e3fb17affba0dc48036 differs from config_strictts.json only in "workers":
  2 (checked). The c833c55 population records #1-#5 (2 false stillborn, 3 stopped without a verdict) stay as
  non-counting records. The population restarts at order position 1 with 0003ada and config_w2.

- 2026-10-25T18:02Z (V, before the first sample program; from cirlean's runner smoke test): (1) the runner records a signal death as
  the shell's $? (128 + signal), so abort is 134 as PREREG_V_v1 says (the core-hour guard itself reports 256 minus the
  signal). (2) An infinite loop in cirrun grows memory (about 14 GB in 120 s), so it ends as TIMEOUT or as an
  out-of-memory CRASH (16 GiB cap) depending on machine speed. The primary kinds stay as frozen; a secondary column
  `resource` (timeout | oom | none) is recorded, and the analysis adds, as a descriptive figure next to the primary
  shares, TIMEOUT and out-of-memory CRASH together as "resource limit".

- 2026-10-25T18:10Z (V start, from the C maintainer session; a deviation in the secondary triage): V started about 18:10Z with the frozen runner
  ~/cirlean_work/llvmsub/tools/run_prereg_v5.py (sha256 0d16897bba742916...), which checks PREREG_V_v1, the sample, the
  manifest, cirrun and clang before launch and fails closed on a mismatch; steps on cores 120/121 (at most 2 programs at
  a time), each under its own guard; outer cap 15 core-h, no new program after 14.5 core-h or Tue 03:00Z. The pinned
  clang has no compiler-rt, so -fsanitize builds do not link; the sanitizer triage (secondary; it does not change
  cir_kind) uses the system gcc 15.2 (/usr/bin/gcc, sha256 86471103...): -std=gnu17 (g++ -std=gnu++17) -O0 -w
  -fsanitize=undefined,address, the same includes, -lm; build and run limits 60 s each; ASAN_OPTIONS=detect_leaks=0.

- 2026-10-25T18:11Z (coblean follow-ups decided by the coordinating session; two later measurements designed here, before they run): coblean fixes its
  front end in the live tree only (", -n" in function argument lists; link.py's EXIT PROGRAM of a linked callee; every
  construct the front end drops that can change behaviour becomes unsupported), as declared later changes; pins,
  snapshots and the pinned Cobol oleans stay untouched, and the paper's results stay at their pins.
  (N2) A second NIST measurement, labelled and reported next to run (b), never replacing it: run_nist.py (6635004c...),
  abend_status_v2.py (b5934936...) and launch_v1.sh (05ab3906...) unchanged, the same six modules and programs, the
  file-directory and open-error rules of the addendum, on the new coblean snapshot plus the NIST pin's two diffs. Before
  it runs, N/ADDENDUM_N2.md records the new snapshot's name, the sha256s of its front-end files and of every Cobol olean
  (which must equal the pin's), and the runner's hashes.
  (M-coblean set 2, mirroring part FE) coblean builds an extended suite for the features where set 1's survivors sit:
  GnuCOBOL-differential tests only, exact comparisons, on the same 2306Z pin and narrowed cobolrun; it is frozen
  (commands, inputs, baseline, sha256) and sent to the evidence owner. Then the evidence owner releases the secret S2M,
  committed now by its sha256 3bd54091bd5dadf03b6d4873a1c58b979e8bc20cd52999f48fbe0f63be52065a, and set 2 is
  `draw_m.py candidates_m_coblean.tsv coblean order2.tsv --seed S2M --exclude <the 30 ids attempted for set 1>`, the
  first 30 tested in that order. Runs: set 2 on the old suite and on the extended suite (the headline: the same mutants,
  old against extended), and set 1 on the extended suite (labelled as not independent). Set 1's 15/30 stays reported
  as is; #4's equivalence label stays apart. Budget within the bridge's 20 core-hours. No set 2 mutant is drawn or run
  before the extended suite's freeze and the release of S2M.

- 2026-10-25T18:26Z (T2 launch record, from the orchestrator session; checked by the evidence owner): T2 launched 2026-10-25T18:25:08Z from frozen copy
  ~/veriforch_frozen/T2_20261025T180210Z = T2_20261025T170117Z + the Rust fail-cache v2 diff (29a502fb...), manifest
  sha256 8342d3464fc5263f9aed17fab98dc36c9292ac9daf1baa8095050d995a518c6e (the intermediate copy T2_20261025T173609Z,
  fail-cache v1, is unused). pins.json (runs/prereg/T2/pins.json) sha256
  a4ca958fb5327eaa0a079f09a8f7636849c4c88b2bb44e1ea1ca18ddbbf3a1fa: cirlean ffab71e, JimpleLean snapshot 20261025T1728Z,
  Aeneas fdebf20, every fix diff, Lean/clang/Soot/JDK; it records sample 83a361fc..., addendum 281dfc00... and
  SHA256SUMS_T_v1 b167d544... (checked against the frozen files). START_DIRS.txt (0f4e5494...): 259 run, cache and
  store directories absent before launch, none present; nothing read from the early-run directories. Final dry run
  from this copy on three non-sample units (--no-llm). 1,000 units, workers gated by load and memory, stop at $500 or
  Tue 03:00Z.

- 2026-10-25T18:27Z (M, JimpleLean: misclassified stillborn candidates; ruling): the run (results
  M_jimplelean_v2_20261025T1625Z.jsonl, sha256 7b595fb14c7337aa..., ids = order positions 1-33, checked) attempted 33:
  17 killed, 13 survived, 3 marked stillborn. All three labels are wrong under PREREG_M_v1's rule (stillborn = the
  mutated definition does not elaborate, or a build failure other than a broken proof): Numeric:260:58:LIT:275 and
  Numeric:204:14:CND:235 never reached their mutation (Lean could not create threads while building Jimple.Tactic,
  exit 134: infrastructure); Numeric:64:18:LIT:58 breaks only proofs, and run_mutants_v2.py's sorry step mishandled it
  (top-down replacements with stale lines; a `let ... :=` inside a statement taken as its end), validated earlier on 18
  proofs although the build covers the library's 421. Ruling, as for StrictTS: the three are re-run with the fixed
  runner run_mutants_v3.py (sha256 ed6f27f355fd5d7d...; bottom-up replacements, statement-internal `:=` skipped, two
  retries for builds that fail without a located error, 64 GB address space; validated by replacing all 421 proofs) on
  the frozen copy. The final set is the first 30 in order that build and are tested; if all three build, attempts
  31-33 (Numeric:127:24:AOR:177, Numeric:124:42:LIT:168, Semantics:93:40:AOR:321) drop out and are reported apart as
  non-counting records. The other 27 tested records stand (all with no sorry, except Numeric:47:47:LIT:33 with one
  replacement, which cannot drift).

- 2026-10-25T18:38Z (V: results recorded; a crash-fix ruling; a cirlean front-end finding): the run (18:10:37-18:30:00Z, 200/200,
  results.tsv ac02a5a3..., results.jsonl 034c4d9e..., my recount) gives cir_kind MATCH 95, UNSUPPORTED 52, UB 25,
  EXIT 13, TIMEOUT 8, MISMATCH 5, CRASH 2, and native_kind NATIVE_OK 177, NATIVE_FAIL 21, REF_DIFF 2. Crash fix: the two
  CRASH programs (fib2, Perm) overflow cirrun's default 8 MB stack. The fix is a uniform rule, cirrun runs with an
  unlimited stack for every program; a larger stack cannot change a run that did not overflow, so only the two are
  re-run, recorded as a crash fix, their first records kept. Finding: cirlean's front end reads every hexadecimal
  floating-point constant as a 64-bit double bit pattern, so float and long double constants printed in hex (infinity,
  NaN, values without a short decimal form) get wrong values (ieee/inf-1); none of the claimed theorems' ClangIR in the
  evidence owner's copies contains a hexadecimal floating-point constant (grep over D1/D2 zlib and tinyxml2, C1, C2, B,
  TRX and the cJSON files: 0 files), so no claim is affected; the fix goes after the freeze.

- 2026-10-25T18:44Z (M, StrictTS: a third harness fix, found by static scan before any result hit it; from the TypeScript maintainer session): the sorry step
  takes a theorem's proof to start at its first depth-0 `:=`; in a proof by equation arms whose arms contain `obtain
  ... :=` or `have h :=`, that `:=` lies inside an arm, so the cut would drop the later arms and end in a false
  "statement broken" stillborn. At the pin 9 of 927 theorem, lemma and example commands are affected (3 in the
  population build: Proof/Extern.lean:109, :125, Proof/AsyncRace.lean:36; 6 more only in the survivors' library build).
  Fix: an equation arm at the command's indentation before the first `:=` marks where the proof starts (it changes
  exactly those 9 cuts at the pin). Gate: sorry every theorem of the pin with the planner and build the library and the
  suite targets; it must fail on 0003ada and pass on the fix; unit cases and the controls re-run on the fix. A wrong cut
  can only produce a stillborn, never a killed or survived verdict, and no stillborn has occurred in this run, so the
  results so far stand; the drive pauses (running mutants finish) and resumes from where it stopped once the fix's
  commit, run_m.py sha256, diff and gate output are recorded here.

- 2026-10-25T18:46Z (M, StrictTS: configuration for the cap rule, from the TypeScript maintainer session; formula fixed now, numbers when the extended suite
  starts): the harness's cap check used placeholders (1.5 core-h, 45 min per validation) and counted only its own
  result and validation files, while the frozen rule (draft lines 105-107, 113) uses the reference run's measured
  core-hours and minutes and counts all mutants, controls and validations. Fix: config_w2v.json = config_w2 with
  per_validation = the reference's measured core-hours rounded up to 0.1 and its minutes rounded up to the next 5, and
  coreh = 20 - H, where H is the guard-metered core-hours of every StrictTS M run the harness cannot see (controls, gate
  runs, base jobs, aborted runs; listed line by line from the guard logs, wall-time estimates labelled where no log
  exists), rounded up to 0.1. Before the first survivor validation, config_w2v's sha256, its diff against config_w2 and
  the H tally are recorded here; validations start after that.

- 2026-10-25T18:50Z (T2 crash fix before any unit, from the orchestrator session): T2 paused at 18:49:21Z with 0 units dispatched and $0 spent (front end
  95+/122 libraries done). A driver bug in prereg_t2.py's prepare step (the Java/Rust phase used slot 0 without taking
  it off the free list) let two C/C++ prepares run at once in runs/t2_thrift_c_glib and race on a shared support
  module; 2 TUs failed ("does not check: lean reported no error but wrote no .olean"): thrift_c_glib_thrift and
  thrift_c_glib_protocol_thrift_multiplexed_protocol. Without a fix their units would be recorded as blocked by the
  front end, which would be wrong. Fix (driver only, about 4 lines): correct slot accounting; on --resume, a library
  whose prepare record has rc != 0 is prepared again (old record moved to prepare/superseded/). The race can only
  cause failures, so the rc-0 prepares stand. New copy = T2_20261025T180210Z + the diff, resumed from the same run
  directories and records, with a check of the shared module's cached .olean; the resume time, copy and diff sha256s
  and pins_resume are recorded when T2 resumes.

- 2026-10-25T18:53Z (T2 resume record, from the orchestrator session): T2 resumed 2026-10-25T18:52:01Z (--resume, same run directories; 0 units before)
  from copy ~/veriforch_frozen/T2_20261025T185110Z = T2_20261025T180210Z + the driver diff (only scripts/prereg_t2.py
  changed, 04db12b3 -> 5a124e76), manifest sha256 69201f10e97b2b49...; diff
  notes/thrift/prereg_t2_crashfix1_20261025.diff sha256 115e33833999a74b...; pins_resume_20261025T185203Z.json sha256
  16fe616322e94af0... (both checked). Re-prepared: thrift_c_glib_thrift and
  thrift_c_glib_protocol_thrift_multiplexed_protocol, both rc 0 (old records in prepare/superseded/thrift_c_glib/). The
  shared module's cached .olean in that target equals the copies every other C/C++ target built (sha256 371a74ee...).

- 2026-10-25T18:56Z (V crash fix, round 2, from the C maintainer session): `ulimit -s unlimited` did not help; fib2 (order 43) and Perm (order 84) still
  crash ("Stack overflow detected"; re-run records runV/rerun_crashfix.jsonl 72a50d4f..., .tsv 9ed8daa4..., runner v6
  daad142b...; first records kept). Cause, shown on cirlean's own drivers only: cirrun evaluates on a Lean thread whose
  stack comes from LEAN_STACK_SIZE_KB, which ulimit -s does not reach; 4 GiB fixes the reproducer (1 GiB does not).
  Accepted uniform rule for every program: `ulimit -s unlimited; ulimit -v 20971520; export LEAN_STACK_SIZE_KB=4194304`
  (a 4 GiB evaluator stack and 4 GiB more address space, so every run keeps the same heap headroom as under the 16 GiB
  cap). A deeper stack with the same heap headroom can only remove stack overflows, so only orders 43 and 84 are re-run;
  their new records go into a new file, and the first and round-1 records are kept.

- 2026-10-25T18:59Z (H part two and the cJSON stretch, from the orchestrator session): (1) H part two (yajl-ruby json_fuzzer): veriforch's scheduler never
  attempts units with a gap and would record yajl_do_parse (gap:external strtol, __errno_location, reachable only
  through the yajl_integer/yajl_double callbacks, which this harness leaves unset) as an assumption. An opt-in
  `vo verify --attempt-gaps <unit>` (about 5 lines in the scheduler, recorded diff; behaviour unchanged with the flag
  off, tested) lets a named gap:external unit be attempted. It adds no axiom: cirlean evaluates a call to an external
  without a model as undefined behaviour (Eval.lean:984/990), so a proof must show such calls unreachable. Each unit
  attempted this way is marked in its record. It is part of part two's start pins (part two had not started). Phase
  1 budget $150 of yajl's $450. (2) The user, through the coordinating session, asked for the full cjson_read_fuzzer like-for-like with
  Theorem's build (cJSON 1.7.18 at acc76239, harness unmodified, -DNDEBUG -DENABLE_LOCALES), on cirlean 266d1ed plus two
  model changes (realloc of single-object blocks; localeconv returning the C locale); cutoff Mon 2026-10-26 18:00Z. It
  is an extension, not part of PREREG_H; if it lands and passes the evidence owner's checks, the paper states it with
  its pin, otherwise the paper states the parse-only, locales-off theorem and names the blocker. The parse-only theorem
  stands as is.

- 2026-10-25T19:14Z (V crash fix round 2, records; from the C maintainer session, checked by the evidence owner): runner v7 run_prereg_v7.py
  982b23d319c9e578... = v5 plus exactly the 18:56Z environment and an --orders filter (diff read). Orders 43 (fib2,
  through the main(int, char**) harness) and 84 (Perm) now end TIMEOUT at 120 s ("resource timeout", max RSS 6.48 and
  2.97 GB), both NATIVE_OK; runV_crashfix2/results.tsv 18bfdfce..., results.jsonl 53a7a24d... (copied to
  checks/V-20261025/crashfix2). First and round-1 records kept. Final V counts with the crash fixes (my recount,
  final_counts_crashfix2.txt): CRASH 0, TIMEOUT 10, all else unchanged; among NATIVE_OK 177: MATCH 95, UNSUPPORTED 31,
  UB 25, EXIT 13, TIMEOUT 10, MISMATCH 3; MATCH among verdicts 95/123.

- 2026-10-25T19:14Z (M-coblean set 2 released; record): coblean froze the extended suite (manifest MANIFEST_reads.sha256 005257d2...,
  810 files, every line re-hashed by the evidence owner; harness mut_one_v3 cd2204c4..., run_order_v2 63381fdb...,
  analyze_v3 cfcd6d0f...; baseline rows.json 446b0eec..., 9 new rows 100/100 ok). S2M released in
  M/ADDENDUM_M_coblean_set2.md (frozen 19:07:15Z, sha256 4056056513066596f8b85de201abe48865cc2bfc2ecc15717adb911f6f27ad05);
  its sha256 equals the 18:11Z commitment. order2.tsv 8e8d5f9a... (1,081 ids, none from set 1), recomputed
  independently by the evidence owner and by coblean. coblean started set 2 (old and extended suite) and set 1 on the
  extended suite on the 2306Z pin, at most 2 jobs, stop at 7.5 core-h or 4 h (coblean, 19:1xZ).

- 2026-10-25T19:14Z (H part two start record, from the orchestrator session; partly checked): phase 1 (model, $150 hard of yajl's $450) started
  2026-10-25T19:07:30Z: vo verify targets/h_yajl_ruby_json_fuzzer.toml --only <45 reachable units> --attempts 4 --refine
  --budget 150 --jobs 4 --check-timeout 1800 --attempt-gaps yajl_do_parse, nice 19, cirlean ffab71e. The flag (18:59Z)
  was applied at 19:03:36Z: live orch/veriforch/scheduler.py 5965ce3a..., cli.py 43f988f7... (hashes checked), diff
  scratch/theorem/part2/patch/attempt_gaps.diff b5dd878a... (read: opt-in list, gap:external units only, a note in each
  attempted unit's record, no axiom); flag-off test NOOP_RESULT.txt 56374a76... (jsmn_lib 9/9 and yajl 8/8 records
  identical, --no-llm, fresh dirs).

- 2026-10-25T19:14Z (T2 crash fix 2, from the orchestrator session; not yet checked): Rust units in worker slots k>0 rebuilt the Rust library for their
  whole 10-minute wall because the slot copies got per-slot crate namespaces (adapter derives the namespace from the
  target name; build.py:1198). Driver-only fix: slot() writes crate_name = "t2_thrift_rs" into the Rust slot copies; new
  copy = T2_20261025T185110Z + that diff; pause by verified PID, --resume in the same dirs. Outcome-blind rule fixed
  before outcomes were read: every Rust unit that ran in a slot k>0 under the old copies (so far 4, 13, 22, 25, plus any
  that finish before the pause) moves to superseded/ and re-runs after the fix. The evidence owner checks the new copy,
  the diff and the superseded list when the resume record arrives.

- 2026-10-25T19:14Z (N2 results and three COBOL semantics defects; from the COBOL maintainer session and nist-runner, checked by the evidence owner): N2 ran
  18:51-18:57Z (launch_n2.log) on the ADDENDUM_N2 tree. My recount of the six final.json/results.json (copied to
  checks/nist-20261025/cln2; n2_recount.txt): 309 programs, pass 85, fail 13, unsupported 193 (61 program-level drops),
  undefined 1, timeout 0, error 17 (resolver rejections, run b's E1 and E2); per test 2,687 of 2,767 over 98 programs
  (run b, recounted the same way: 2,419 of 2,525 over 130). Files final_census_n2.txt 8285fab0..., transition_b_n2.md
  924c7768..., triage_n2_v1.md 6b9c246f..., triage/theorem_paths_v2.txt 1a804058.... Fails: C1 x7, C9 x1 (new, NC175A,
  Cobol/Edit.lean:138-143), C2 x1, C5 x2, producer x2. Defects of the 2306Z semantics, none on a theorem path: C9,
  M-syncsub (SYNC alignment relative to the subgroup, Layout.lean + datadiv.py) and M-pos (indexed-file read position
  after inserts/deletes while open, File.lean); coblean's walk defect_paths_v1.txt b83344b0... (script 7072169a...),
  15 IRs, 0 flagged; my independent regex and file-use walk agree (checks/cobdefects-20261025). The coordinating session decided: the three
  are fixed in coblean's live tree as declared later changes (helper sem-fixes; M-pos only if the fix stays inside
  File.lean's position handling); no equiv-lean re-pin before the freeze; the paper states the pins carry the defects,
  none on a theorem path, and that the new snapshot fixes them with coblean's theorems re-checked; M set 2 stays on 2306Z.

- 2026-10-25T19:22Z (H part two pins, from the orchestrator session): start 2026-10-25T19:07:30Z, cirlean ffab71ea54802c61bcfab3d389f12c94bb85b388; live
  veriforch (not a frozen copy): scheduler.py 5965ce3a, cli.py 43f988f7, cir adapter 7f4cf09c, build.py ef679367,
  compdb 8c41325e, lean.py 72cf2438, llm.py baad59aa; snapshot of the 64 orch .py files
  scratch/theorem/part2/veriforch_orch_snapshot_20261025T1918Z (SHA256SUMS 5d36ea09...); only scheduler.py and cli.py
  changed since the --attempt-gaps patch. Resource watchdog v2 from 19:18Z (SIGSTOP after 5 min of load > 450 or < 150
  GB free; kill only below 100 GB). Ruling (evidence owner): a check paused past its 1800 s wall is an infrastructure
  artefact, not a proof failure; part two's outcomes are per entry point, so such units may be re-run after the pause,
  each re-run marked in its record.

- 2026-10-25T19:22Z (lang3 population figure dropped; evidence owner): the counts 3,823/5,068 -> 4,153/5,258 were per-unit scan scopes
  printed by an unsaved script (no saved before/after lists; the orchestrator session), and 4,153 = 3,823 + 144 (former own-interface gaps) +
  186 (new interface units in scope), not D's closure definition. The paper keeps only the evidence owner's sample count
  (2 of the 29 blocked D1 lang3 units blocked only by own-interface calls).

- 2026-10-25T19:22Z (JimpleLean model fix, declared later change; from the Java maintainer session, claims checked by the evidence owner): a new tester
  (difftest/src/FloatSem.java, exact float observation) found that the library model of Double.compare(x, NaN) returns 1
  where the JDK returns -1 (the model took dcmpg first); fixed in snapshot 20261025T1918Z (regression 129 jobs / 68
  theorems std; corpus 42/42), listed as a model fix, not a crash fix. Raw NaN bit patterns differ by design (JVMS
  leaves them open). Claims check (checks/dcompare-20261025, tools/jcompare_claims.py; positive controls MutableDouble.
  compareTo and CompareToBuilder.append flagged, negative control MutableDouble.intValue not): none of the 55 claimed
  lang3 units of D1 and the D2 re-run reaches Double.compare or Float.compare in its lang3 call closure; A's 8 Java
  translations contain no float type. T2's Java claims (JimpleLean 1728Z, before the fix) get the same check at
  analysis. Asked of the Java maintainer session: whether Float.compare and compareTo/equals share the fault, and which snapshots carry it. A
  labelled post-hoc FloatSem count on the 9 float survivors of M set 1 was allowed (not independent; headline unchanged).

- 2026-10-25T19:29Z (cJSON full-harness extension, statement bound; finding by the orchestrator session, ruling by the evidence owner, the coordinating session informed): in
  the C model, "no UB for every input of fewer than 2^63 bytes" is false for the full cjson_read_fuzzer (cJSON 1.7.18).
  print_string_ptr computes output_length = L + escape_characters in size_t, and a string of L raw bytes below 0x20 (other
  than \b \f \n \r \t; parse_string accepts them) needs 6L. The ensure() call with 6L + 3 wraps, then passes ensure's
  INT_MAX check exactly for L in [3,074,457,345,618,258,603; 3,074,457,345,976,172,543] (357,913,941 values; my
  arithmetic, checks/cjfull-bound-20261025/arithmetic.txt), and the escape loop writes about 6L bytes past a small
  buffer. Such inputs (~3.07e18 bytes, about 2^61.4) are within ReadableBuf's bound and reachable in the model only
  because its malloc never fails; no real machine can hold them. Ruling: (a) the extension's statement uses
  size < 2^61, fixed now by the rule "the largest power of two P with 6(P-1) + 3 < 2^64" (the only size_t multiplier on
  the print path); if the proof meets another wrap below 2^61, the owner reports it before any further change of bound.
  (b) The paper states the theorem with this bound and discloses the counterexample class with its line-level trace at
  acc76239, as found by inspection unless a kernel-checked refutation lands. The parse-only theorem keeps 2^63 (it never
  prints). Any comparison with Theorem's proofs states both bounds (theirs: inputs on which the plain build is never
  refused memory beyond 2 GiB for ASan, 16 GiB for UBSan); the finding is not a flaw in their proofs. No upstream report
  before publication and the user's go. H part two keeps PREREG_H's bound unless a disclosed class of the same kind
  appears; the owner reports it before changing the bound.

- 2026-10-25T19:33Z (full-harness bound note, trace checked): the orchestrator session sent line references at cJSON.c acc76239 (sha256 75c51de8...):
  parse_string 781 (scan 798, copy 833), print_string_ptr 911 (escape count 939-959, +5 at 957; output_length 962;
  ensure call 964; write loop 984), ensure 447 (INT_MAX check 463, before the offset is added at 468). All checked by
  the evidence owner on a copy (checks/cjfull-bound-20261025/lines.txt); with arithmetic.txt they back the paper's
  "by inspection" statement.

- 2026-10-25T19:39Z (JimpleLean float model: scope of the fault, and a labelled post-hoc count; from the Java maintainer session, checked by the evidence
  owner): probes over {NaN, 0.0, -0.0, 1.0, -1.0, +inf, -inf, 4.9e-324}^2 against the JVM (difftest/probe_cmp/):
  Double.compare had 9 wrong cases (compare(NaN, NaN) = 1, JDK 0; compare(x, NaN) = 1 for the 7 non-NaN x, JDK -1),
  identical code in 1029Z (D1), 0149Z (A), 0300Z (D2) and 1728Z (T2), fixed in 1918Z (64/64). Float.compare,
  Double.compareTo and Float.compareTo have no model in any snapshot (a call goes wrong, so no proof can rely on them);
  Double.equals and Float.equals are correct (64/64 on 0300Z and 1918Z). Post-hoc count, labelled as tests written after
  the survivors were seen (not independent; the 16/30 headline stands): FloatSemCases.java 4baffdcd... (6,038 cases;
  FloatSem.java 62780e6b...), inputs posthoc_float_v1 SHA256SUMS e0b2a86f... (sha256 -c OK on my copy), runner
  posthoc_floatsem_v1.py, command 550fa8d7... under coreh_guard_v2 (0.169 core-h, my read of the guard log). Baseline at
  the M pin (0300Z, clean rebuild): 19 cases fail and are dropped (the Double.compare NaN cases), 6,019 kept pass. The 9
  float survivors of M set 1 (all in M_jimplelean_final's 14 survivors; the 5 others are not float code, e.g. Numeric:47
  is lcmp): 8 killed (Semantics:108 fcmpg->fcmpl 58 differing cases, Numeric:73 16, :192 269, :199 137, :201 18, :204
  1,670, :210 7, :260 436), 1 survived (Numeric:241, dcmpl's NaN result -1 -> -2, which only sign tests read); no
  sorries, all exits 0. Records posthoc_float_20261025T1926Z.jsonl 18622e61... (copied to checks/Mjimplelean-20261025/
  posthoc_float; my recount agrees).

- 2026-10-25T19:39Z (T2 crash fix 2, resume record; from the orchestrator session, checked by the evidence owner): paused 19:12:28Z, resumed 19:36:30Z from
  ~/veriforch_frozen/T2_20261025T191617Z (SHA256SUMS 837eaa6e..., 154/154 OK on my check; versus T2_20261025T185110Z only
  scripts/prereg_t2.py differs, 5a124e76... -> 9ef65fef...). Diff prereg_t2_rustns_20261025.diff 8c266ec4... (read: Rust
  slot copies get crate_name = the target name). Second part: VO_EQUIVLEAN_AENEAS_DIR set to the immutable pin directory
  so Rust cache keys no longer contain the copy's path; the Rust library prepared under the old copy is superseded and
  re-prepared before any Rust unit. pins_resume_20261025T193631Z.json 56095f80.... Superseded by the outcome-blind rule
  (superseded/cf2_20261025T193123Z, MOVES.tsv): units 4 and 13 (both Rust, workers 3 and 12, timeout, $0); in-flight
  units 16, 22, 23, 25 re-run (partial guard logs kept). Ledger note: the killed attempts of units 16 and 23 spent $0.37
  that ledger.json does not carry; T2's spend is taken from the usage logs.

- 2026-10-25T19:42Z (T2/T3 Rust: live Lean packages; from the orchestrator session, guard code read by the evidence owner): Rust units read mathlib and
  Aeneas's other dependencies in place from equiv-lean's live workspace (~/equivlean/.lake/packages; adapters/rust/
  build.py:62-65), not from an immutable copy; only Aeneas (deps/aeneas-fdebf20) and the bridge
  (deps/equivlean-7e1aaf0-aeneas) are immutable. Fail-closed guards (read in the T2_20261025T191617Z copy): lean_dirs
  raises unless every package revision in that workspace's lake-manifest equals Aeneas's manifest (:136-150), and the
  cache fingerprint includes the sha256 of Mathlib.olean (:282-288). A change during the run would show as
  infrastructure errors. The orchestrator session asked the equiv-lean maintainer session not to touch the directory until Tue 03:00Z. Same for T3's Rust.

- 2026-10-25T19:42Z (H part two, yajl-ruby json_fuzzer: statement bound and refutations; finding by the orchestrator session's worker from the code, nothing
  run; ruling by the evidence owner before any yajl result): with PREREG_H's bound (the cJSON harness statement's,
  inputs below 2^63 bytes) "no UB" is false for this harness by inspection. The harness's own arrayLevel++
  (json_fuzzer.c:65) overflows a signed int at array depth 2^31 (e.g. 2^31 bytes of '['), and yajl_lex.c:398 (numRd++)
  at 2^31 digits after a decimal point (e.g. "0." and 2^31 digits). The harness passes the length to yajl_parse as an
  unsigned int (size mod 2^32). yajl_buf's growth (yajl_buf.c:92-137) is safe for every size; objectLevel++
  (json_fuzzer.c:54) cannot reach 2^31 because each object costs at least 4 bytes. Ruling:
  (1) Pre-registered outcome at 2^63: such inputs cannot be run on the semantics. "Refuted" is read as also admitting a
  kernel-checked refutation (a Lean theorem that the semantics reaches the undefined behaviour on a described input),
  checked by the evidence owner like any claim. Without one, the outcome is "not finished", with the inspection finding
  and its line references reported next to it.
  (2) A labelled second result, not replacing (1): the same statement for inputs below 2^31 bytes, the largest power of
  two below the smallest counterexample class, by the rule of the cJSON full-harness ruling. If the proof meets another
  failure below 2^31, the owner reports it before any further change of bound. Outcome categories as PREREG_H.
  (3) Reporting: the two overflows are source-level undefined behaviour for inputs of at least 2 GiB, reported as outside
  the scope of Theorem's proofs, never as a flaw in them. Any comparison states Theorem's bound for this harness as the
  evidence owner reads it from their statement at the pinned commit.

- 2026-10-25T19:43Z (yajl ruling, lines checked): on copies of yajl-ruby @ 6501652d1135 (json_fuzzer.c d1962e79..., yajl_lex.c
  0285ff9f...): json_fuzzer.c:27 int arrayLevel, :65 arrayLevel++, :90-93 both counters start at 0, :100 yajl_parse(parser,
  data, size) with yajl_parse taking an unsigned int length (api/yajl_parse.h:148-150); yajl_lex.c:392 int numRd = 0,
  :398 numRd++ in the fraction digit loop (checks/yajl-bound-20261025/NOTE.md).

- 2026-10-25T19:47Z (T3 status and an announced Rust crash fix; from the orchestrator session, not yet checked): at 19:45Z, 33 of 150 commits recorded, no
  crashes in the driver, $11 spent. In order 33, 75 of 91 changed functions were unknown because the pair package
  holding both revisions fails to build: Lean rejects a duplicate auto-generated instance name between the old and new
  Types modules ("environment already contains 'instDiscriminantShutdownIsize' from Old.default.T3_thrift_rust.Types").
  This is a tool crash, so per PREREG_T those functions are infrastructure errors until the crash fix and re-run. Plan:
  fix adapters/rust/equiv.py so the old revision's names cannot clash; new frozen copy = copy + diff; pause, resume.
  Affected set by an outcome-blind rule fixed now: every Rust commit whose equivalence step logged "environment already
  contains"; those records are superseded and re-run, the others stand. Conditions set by the evidence owner: on list
  commits (order 33) the fix is tested at build level only (the pair package builds; no verdicts computed outside the
  driver); verdict invariance (byte-identical) is tested on an unchanged pair and on commits outside the T3 list. Before
  the resume, the affected list comes from a recorded grep (command and output sha256), and the superseded records move
  with per-file sha256s. Analysis reading, fixed before the census: promoted Rust test units (adapter verdict "test") are
  listed apart, as Java's synthetic methods are.

- 2026-10-25T19:51Z (T3 Rust crash fix, wider scope; from the orchestrator session, not yet checked): Aeneas's discriminant attribute emits a root-scope
  instance named after the enum (instDiscriminant<Enum>), and the pair package's old modules import the new shared
  FunsExternal and through it the new Types, so every Rust commit whose CI builds a pair package (any changed library
  function) hits the clash; orders 21, 25 and 36 built none. The affected-set rule recorded above (the logged message)
  still applies unchanged. Fix (equiv.py, about 40 lines): in the old Types only, attributed enums are renamed N ->
  N_vo_old, with abbrev N := N_vo_old and constructor aliases; old code and shared externals untouched. Reported tests:
  order 33 build-only (the pair package builds), byte-identical verdicts on an unchanged pair and on an outside-list
  Rust commit, and the test fails on old code. Dispatch paused (dispatcher stopped by verified PID); in-flight jobs
  finish under the old copy. Open with the evidence owner: what the invariance tests compared, given that old code
  crashes on every pair package, and how statements relate old and new values of a renamed enum type.

- 2026-10-25T19:51Z (coblean semantics fixes, scratch result; from the COBOL maintainer session, partly checked): C9 (Edit.lean, 3 changed lines; diff
  505accdc...) and M-syncsub (Layout.lean 92, datadiv.py 41; diffs 18484c24..., 39f8ca85...) fixed in a scratch tree
  (hashes and changed-line counts checked by the evidence owner; th0 axiom lines identical to 2306Z's, my diff). C9's
  repro now agrees except two GnuCOBOL quirks (***.**- with -0.001 / 0.004); M-syncsub's synctest_sub 60/60 (43/60
  mismatched before), the M suite's synctest 100/100; a SYNC binary item inside a group with OCCURS is now unsupported
  (fail-safe; GnuCOBOL's placement irregular, IBM's rule not established). M-pos is not fixed: its fix needs a field in
  FileSt (Cobol/IR.lean), which the theorem invariants spell out, so the coordinating session's condition excludes it; it stays documented,
  off every theorem path. Scratch re-check (coblean): build 115 jobs, 25 axiom lines identical, no proof touched,
  47/48 evidence rows identical (V.hand new format, same 28/0), 9 CardDemo IRs identical; Cobol.olean unchanged; Edit,
  Layout, Logic/Alnum and Logic/Summary oleans change. Merge into live and the snapshot follow fe-fixes' tester batch;
  the paper's sentence waits for that snapshot and its re-check.

- 2026-10-25T19:52Z (T2 crash fix 3 announced; from the orchestrator session, not yet checked): Rust units 4, 13 and 22 were proved in their re-run after
  crash fix 2 (one model attempt each, about $0.05 each), but kernel_replay.sh then failed on each with "Could not find
  any oleans for: VO.default.<unit>": it runs lake env leanchecker in the package directory, and Rust packages have no
  lakefile (Lean runs with an explicit LEAN_PATH). So every proved Rust unit was recorded as infrastructure_error, with
  the cause mislabelled kernel_rejection. The Rust replay path had never run before (no Rust unit was proved in any dry
  run); C, C++ and Java replays pass. Fix: the replay uses the package's explicit LEAN_PATH for Rust, and an
  olean-not-found is labelled "replay could not run" (an infrastructure error, never a kernel rejection). Planned tests:
  replay passes on a proved Rust unit; C/C++/Java replay output unchanged; the test fails on old code; a negative
  control. Then pause, new copy + diff, resume. Affected set by an outcome-blind rule fixed now: every Rust unit whose
  replay log contains "Could not find any oleans"; superseded (MOVES.tsv) and fully re-run, as for the earlier crash
  fixes. No unit is counted as kernel-rejected on account of this.

- 2026-10-25T19:56Z (cJSON full-harness extension, pin progression; from the orchestrator session): the final pin will be cirlean 266d1ed plus exactly three
  model changes, not the two of 18:59Z: 90b9c2f (realloc of single-object blocks; localeconv returning the C locale) and
  one more commit, cir.signbit (glibc's isinf compiles to it in print_number; parsed with its operand and modelled as C's
  signbit; no new Op constructor; Logic/Tactic statements unchanged). Without it, print_number is undefined behaviour in
  the model for every non-NaN double; it was the only unmodelled operation in the full harness's generated code. Proof
  definitions agreed with cirlean (CJPrint v4 8ab370f0..., CycleSpecsP2 f3d742fc...) are used inside the proof, not in the
  harness statement (to be checked). The three model changes enlarge the trusted base of this extension only; the paper
  names them with the pin. Status: parse_number (1.7.18) proved, conditional only on get_decimal_point; compare_double
  proved; cutoff Mon 2026-10-26 18:00Z.

- 2026-10-25T19:57Z (cJSON full harness, how the 2^61 bound enters; from the orchestrator session, diff read by the evidence owner): the bound is a
  mechanical binder from a target option. adapters/cir/adapter.py (live, b8a90c7d...) gains harness_size_log2; with
  targets/cjson_full.toml's harness_size_log2 = 61 (the only target that sets it), the entry contract appends
  (hsmall : size < 2 ^ 61) after ReadableBuf; without the option the text is unchanged (diff
  notes/stretch_cjson/fh/cir_adapter_sizebound_20261025.diff 476c39f5..., read). CJPrint and CycleSpecsP2 appear only in
  callee contracts (the orchestrator session); the evidence owner checks the harness statement at claim time. Model-change tests (realloc,
  localeconv, signbit) asked of the C maintainer session via the orchestrator session.

- 2026-10-25T20:02Z (T2 crash fix 3, resume record; from the orchestrator session, checked by the evidence owner): paused 20:00:12Z, resumed 20:00:48Z from
  ~/veriforch_frozen/T2_20261025T195945Z (SHA256SUMS f7a77db6..., 154/154 OK on my check; versus T2_20261025T191617Z only
  the driver differs, 9ef65fef... -> cffc7446...). Diff prereg_t2_rustreplay_20261025_v2.diff 5337136c... (Rust replays
  get the package's explicit LEAN_PATH via --extra-lean-path; a module that cannot load gets cause not_run).
  pins_resume_20261025T200049Z.json 48cc873f.... Affected list: the recorded /usr/bin/grep -l -F over the 23 replay logs
  (superseded/cf3_20261025T200040Z/affected_grep.argv, output ddb357e4...): units 4, 13 and 22, superseded, their cause
  corrected to "replay could not run" in NOTES.txt; in-flight units 31, 32, 33, 35, 36 re-run. Test
  test_crashfix3_v2.out bd15f178... (read): Rust unit 4 old FAIL, new PASS; C++ 15 and Java 2 PASS under both with
  identical replay commands; a copy with an added false theorem under debug.skipKernelTC fails as a kernel rejection,
  the unaltered copy passes; a broken olean path fails as not_run. Re-runs of units 4 and 13 (proved_model_stated, replay
  PASS) reused the proof scripts that the superseded runs had put in the orchestrator's proof cache (same key: body,
  callee contracts, library version), so they cost $0.00 and their model spend is counted once. Killed in-flight attempts
  across the two pauses spent $1.23 that ledger.json lacks; T2's spend comes from the slots' usage logs.

- 2026-10-25T20:08Z (M, StrictTS deviation 3, record and resume; from the TypeScript maintainer session, checked by the evidence owner): fix commit
  c5cfd0358792c97561406de139f7a301b00186be (branch mutation-m; tools/mutation/run_m.py only, +18/-8; its message lists
  the 9 changed cuts: Proof/Extern.lean:109, :125, Proof/AsyncRace.lean:36, Str/Lemmas.lean:158, :177, :273, :304,
  Proof/Summarize.lean:1169, :1838). From git, read-only: run_m.py at c5cfd03 sha256
  2efcfe3ecf4bfe547d25753a1a90681865f008ae09bb0a396f9995646911ff7d, diff 0003ada..c5cfd03 26e0a6d7.... Gate gate_d3.py
  5d3d13af... (manifest gate_d3_SHA256SUMS 5d7182b6..., 26/26 OK on my check): all 927 commands sorried by each planner
  (927 edits, 0 plan failures each); 0003ada fails (rc 1, 10 errors in StrictTS.Str.Lemmas and StrictTS.Proof.AsyncRace),
  c5cfd03 builds (rc 0, 0 errors). Unit cases unit_d3.txt af680349...: c5cfd03 7/7; 0003ada fails c5 and c7. Controls
  on c5cfd03 (manifest controls_d3_SHA256SUMS 362fa058..., 33/33 OK): baseline passes, no-op survives, the Format.lean
  edit is killed. The 8 results finished under 0003ada stand (copied to checks/Mstrictts-d3-20261025): 5 killed, 2
  survived, 1 stillborn; their sorries (21 and 2, all examples in Num/F64.lean) touch none of the 9 commands. The
  stillborn (#7, F64.lean:44:62 LOG, finished 18:46:09Z, after the 18:44Z entry) failed in the mutated definition itself
  (F64.lean:45:25, application type mismatch; 0 sorries), so it is genuine. The drive resumes with c5cfd03 and config_w2,
  skipping the 8 settled results. The 18:46Z condition stands: config_w2v's sha256, its diff and the H tally are recorded
  before the first survivor validation.

- 2026-10-25T20:10Z (cJSON full harness, final semantics pin and its tests; from the orchestrator session/the C maintainer session, checked by the evidence owner): cirlean
  c4ef58d4ee9934f6b05a9e2915a6b7bd2b5e6590 = 266d1ed + 90b9c2f (realloc of single-object blocks; localeconv returning
  the C locale) + c4ef58d (signbit). Package ~/cirlean_work/deliver/fuzzer_pin_c4ef58d (SHA256SUMS b9618845..., 14/14
  OK on my copy, checks/fhpin-c4ef58d-20261025): patches 100d3383... (Frontend/Recognize, Logic/WFGlobal, Model,
  Std/Models, tests) and 696f546f...; before_after.txt: t_realloc_one, t_realloc_struct, t_localeconv end in undefined
  behaviour or "no model" at ffab71e and give 12, 39, 50 at 90b9c2f and c4ef58d; t_signbit (3 cases) is "unsupported
  operation cir.signbit" at 90b9c2f and gives 63, 62, 63 at c4ef58d; each equals the native result (difftest output
  lines, MATCH). Full difftest at c4ef58d: MATCH 177, MISMATCH 0, 1 other (t_gap_emplace, a C++ library gap case);
  floats MATCH 1,118, MISMATCH 0. The full-harness checks run on c4ef58d.

- 2026-10-25T20:14Z (correction to the StrictTS deviation-3 record above; from the TypeScript maintainer session, checked against M/strictts/order.tsv): order
  position 7 is StrictTS/Core/Sem.lean:1212:28:ARM (killed, 0 sorries) and position 8 is StrictTS/Num/F64.lean:44:62:LOG
  (stillborn, genuine; error at F64.lean:45:25 in the mutated definition). The record above calls the stillborn "#7";
  read "#8". Verdicts and reasons unchanged. The drive resumed at 20:13:11Z on c5cfd03 (positions 9 and 10 running), as
  one chain: drive, then the reference run (tripwire 3.0 core-h), then the H tally and config_w2v, stopping before any
  survivor validation.

- 2026-10-25T20:16Z (T2 driver crash and crash fix 4 announced; from the orchestrator session, not yet checked): the driver died at 20:15:17Z with a
  JSONDecodeError in ledger_total(): the dispatch loop read ledger.json without the lock while a worker thread rewrote it
  (truncate, then write). No T2 process left (the guard ended the tree); ledger.json valid ($14.01 over 62 unit runs =
  57 results + 5 superseded); results.jsonl 57 valid lines. Fix (driver only): ledger_update() writes a temporary file
  and replaces ledger.json atomically. Test: a writer/reader race on a scratch ledger (old code raises, new code clean,
  final total = the sum of the writes). New copy = T2_20261025T195945Z + diff, then --resume; units in flight at the
  crash have no result and run again (no outcome-based superseding needed). Evidence owner's conditions: their partial
  logs are kept and listed at resume, and their killed attempts' spend comes from the usage logs.

- 2026-10-25T20:17Z (D2: the same latent ledger race; from the orchestrator session, ruling by the evidence owner): D2's frozen driver
  (~/veriforch_frozen/D2_20261025T030336Z/scripts/prereg_d2.py:242-264) reads ledger.json without the lock while
  ledger_update() rewrites it in place under flock; the zlib and lang3 drivers share that ledger. No D2 crash in about 17
  hours. Ruling: option (a). D2 stays untouched ("crash fixes only"; a pause now would itself interrupt running units).
  If a D2 driver crashes this way, the same atomic-write change is applied as a recorded crash fix, the units in flight
  run again (partial logs kept), and the resume record lists them; the driver's exit is watched so that little wall time
  is lost before the stop.

- 2026-10-25T20:18Z (cJSON print length obligation in a 32-bit build; analysis by a session relayed and hash-checked by the coordinating session, arithmetic
  re-done by the evidence owner): with ILP32 (size_t, ptrdiff_t, int and pointers 32 bits; cJSON.c compiles with gcc
  -m32 and with cirlean's clang -fclangir), the obligation at cJSON.c:962/964 (acc76239) fails for string lengths L in
  [715,827,883; 1,073,741,823] (357,913,941 values; about 683 MiB to 1 GiB); input plus parsed copy (about 1.33 GiB) fit
  a 32-bit address space, so unlike the 64-bit class this one is within physical limits on 32-bit targets. ensure's own
  sum (line 469) cannot wrap given the INT_MAX check (line 463). The bound rule gives 2^29 for a 32-bit size_t (2^61 for
  64 bits). Files: arithmetic_32bit.txt 9d323499... (copied) and my recomputation arithmetic_32bit_mine.txt
  (checks/cjfull-bound-20261025); the next window needs about 2.67 GiB of input and copy. The same computation is in the
  newer cJSON used elsewhere in the paper (v1.7.19-6-g6d9f244: lines 1000, 1005, 1007; INT_MAX check 506). Our
  semantics, our statements and Theorem's proofs all use the 64-bit data model. Paper: stated in obligation/bound form
  next to the 64-bit disclosure, only with the full-harness result. Whether cJSON's maintainers hear of it privately
  before publication is put to the user (a reachable instance on 32-bit targets); until then nothing leaves the machine.

- 2026-10-25T20:20Z (coblean tester strengthening, declared later change; from the COBOL maintainer session, checked by the evidence owner): snapshot
  ~/coblean_snapshots/coblean-20261025T2014Z (hash list snapshot2_sha256.txt 76190935...). My cmp: all 44 Cobol oleans
  and all 9 CardDemo IRs identical to 2306Z, so the semantics and the theorem programs are unchanged. Testers: INSPECT and
  UNSTRING counters start non-zero; difftest records one trace byte per IF or SIZE ERROR outcome (OTRACE) and splits its
  statuses (ok-negzero, ok-packed-fc, mismatch-bytes); filetest compares a per-statement trace, also before an abend;
  stricter evidence and stm checks; controls show each new check rejecting a fault the old one accepted. New measurement
  against 2306Z (docs/EVIDENCE_live_vs_2306Z_20261025T2014Z.md 3f8a8607..., hash checked): every VAL row equal except the
  status split and dt_bin with 3 mismatches instead of 2 (case 130, exposed by OTRACE: the TRUNC(BIN) out-of-PICTURE class,
  where the model follows IBM). Paper: one sentence in sec-limits; the fidelity table stays at 2306Z. Next: sem-fixes
  merges C9 and M-syncsub on top of this snapshot.

- 2026-10-25T20:20Z (T2 crash fix 4, resume record; from the orchestrator session, checked by the evidence owner): the dispatch thread died at 20:04:28Z;
  the worker threads finished their units and wrote their results, and the process exited at 20:15:17Z (so no killed
  attempts and no unit to re-run; superseded/cf4_20261025T201745Z holds only notes). Resumed 20:19:01Z from
  ~/veriforch_frozen/T2_20261025T201745Z (SHA256SUMS 87a46913..., 154/154 OK on my check; only the driver differs,
  cffc7446... -> 8a1cab58...). Diff prereg_t2_ledger_20261025.diff 56f5317b... (temporary file + os.replace; reader
  unchanged); pins_resume_20261025T201902Z.json 827ccde1... (crash fixes 1-4). Race test test_ledger_race.out c681e2b9...
  (read): old code raises on its first read; new code 0 errors in 1,087,034 reads against 63,214 writes, final total equal
  to the sum. results.jsonl: its first 57 lines hash to fb54028c..., the value reported for the file at the crash, so the
  resume only appended.

- 2026-10-25T20:33Z (T4 interim and its commit; from the equiv-lean maintainer session, not yet checked): three cross-language discrepancies proved on both the C++
  and the Rust semantics on the spec's named inputs (spec t4-spec f93f948, e6c5d2f9...): (1) field-header write with
  delta 15: C++ writes the spec's [F5], Rust [05 1E] (compact.rs:555 field_delta < 15), both decode in both readers;
  (2) write with an i16 delta overflow (last 32767, id -32768): C++ writes the spec's long form, Rust panics on Aeneas'
  semantics (a debug build); (3) read of [15] after id 32767: C++ returns id -32768 where the spec rejects
  (DeltaIdOverflow), Rust returns a protocol error. C++ and Rust agree on four malformed inputs the spec rejects.
  Contracts: C++ rows transport contracts only; Rust rows transport plus marked library contracts listed per pair.
  Rust column 11/11 (fed0c3b, $63); C++ and Java in progress. Ruling on the commit (evidence owner): T4's Lean files go on
  their own frozen commit(s), not merged into equiv-lean master before Tue 06:00Z, so the migration study's freeze tree
  stays the checked content (no re-pin before the freeze, the coordinating session); T4 is reported with its own pins; merging after the freeze
  is fine. Each claimed T4 row: commit, theorem names, axioms printed and kernel replay by the evidence owner, contracts
  listed as hypotheses.

- 2026-10-25T20:34Z (H part two, yajl: phase-2 plan; from the orchestrator session, plan file notes/theorem/H_part2_phase2_plan.md 01a218ac...): phase 1 (the
  autonomous run) continues untouched (93 calls, $22.66, 1.95 core-h at 20:29Z; projected end about 02:00-04:00Z Mon); its
  model-written contracts do not compose, so phase 2 restates contracts top-down, with proof engineers (three agents), for the labelled second result only: a target copy h_yajl_ruby_json_fuzzer_lt2p31 with
  harness_size_log2 = 31 (the pre-registered target stays at 2^63). Run of record by Mon 20:00Z at the latest, unfinished
  units as named assumptions; a second run only if it fits before Tue about 01:30Z. Estimates: phase-2 model spend
  $10-60 (hard cap $60), 40-60 core-h. At 2^63 a kernel-checked refutation is attempted only after the < 2^31 work.
  Reporting (evidence owner): as for the cJSON harness, proof lines by role (owner, engineers, model, generated) and
  statement origins; cost all-in, i.e. the usage-log model spend plus the agents' own token spend from their transcripts,
  stated separately; the phase-1 (autonomous) outcome reported on its own.

- 2026-10-25T20:42Z (H part two, yajl: scope; from the orchestrator session): no kernel-checked refutation will be attempted at 2^63. The pre-registered
  outcome there is "not finished", reported with the two line references (json_fuzzer.c:65, yajl_lex.c:398), per the
  ruling above; phase 2 works only on the labelled < 2^31 theorem.

- 2026-10-25T20:45Z (T3 Rust fix: the two answers, and a generator limit now visible; from the orchestrator session/w-thrift-rsts, partly checked): the diff
  (notes/thrift/equiv.py.discrfix_20261025.diff, b3cfa65d...) touches only orch/veriforch/adapters/rust/equiv.py (read).
  Invariance: the pair rust_exp2 aa3b937..7cdfa7c has no attributed enum, so old code does not crash there; its ci.json
  under the old and the new equiv.py differ only in timing keys (my diff of both files: seconds, seconds_base,
  seconds_head; verdicts 2 equivalent, 1 behaviour_changed in both; checks/t3fix-20261025). The outside-list commit
  42d0b717 only shows that the crash is gone (it crashed under the old code). Statements: Equiv (. = .) (<crate>.f args)
  (<crate>_vo_old.f args), the same arguments to both versions and = on results, with no mapping between old and new
  crate types; the generator also writes argument types as crate-relative names that do not resolve in the VOEq
  namespace. So every Rust obligation with a crate type among its arguments or result ends unknown ("Unknown
  identifier ..."; e.g. 2 of 42d0b717's 95 obligations); no Rust verdict theorem can involve a renamed enum, and in T3
  only functions over primitive argument and result types can get Rust verdicts. Not fixed mid-run (a type mapping
  between revisions is a design change). Census reading, fixed now: these unknowns are grouped as "statement not
  well-formed: crate types in the signature". T3 resumes from T3_cf1_20261025T204341Z (93e06462...) after the drain.

- 2026-10-25T20:47Z (cJSON parse-only theorem, engineers' own token spend; from the orchestrator session, recomputed by the evidence owner): veriforch's
  three proof-engineer agents, from their first message to 2026-10-25T18:53:18Z (the run of
  record's end): $112.96 (737 calls; $55.20, $38.94, $18.82), AGENT_COST.md af3ec804..., script 97fce800.... My
  recomputation with tools/transcript_spend.py on snapshot copies of the three transcripts
  (checks/E-20261025/cjh_agentcost, SHA256SUMS_snapshot) gives the same calls, tokens and dollars per agent. With the
  model spend (usage logs, $40.30) and 31.5 core-h, the veriforch side is about $154.5; not yet included: cirlean's
  attributable work (the parse_array/parse_object/parse_string bundles, CJTree and the other added library modules; asked
  of the C maintainer session) and the coordinating sessions. The paper states no cost for this theorem unless it is all-in.

- 2026-10-25T20:53Z (cJSON parse-only theorem, cirlean's attributable token cost; from the C maintainer session, recomputed by the evidence owner): to
  2026-10-25T18:53:18Z, attributed helpers $240.91 (pobj 79.00, lookup 70.41, optim 66.42, a Sonnet string-walk helper
  17.62 at Sonnet prices, floatnan until 17:29Z 3.93, rog 2.25, cjlemmas 1.28); shared tooling on its own line $66.80
  (vcgspeed until 17:29Z 35.03, wfglobal 16.12, cirstd 9.52, cirparser 6.13); the lead session $810.39, not attributed
  (cJSON work interleaved with general semantics work and other bridges' requests); excluded other work. Script
  token_cost_v1.py 3e5780de.... My recomputation on snapshot copies of all transcripts (checks/E-20261025/
  cirlean_cjh_cost, SHA256SUMS_snapshot) with tools/transcript_spend.py (Opus) and a Sonnet-priced pass for the one Sonnet
  helper gives every figure exactly. Paper (sec-ub): attributable LLM tokens about $394 (orchestrator model $40,
  its engineers $113, the semantics maintainers' helpers $241); shared tooling and coordinating sessions excluded and
  said so.

- 2026-10-25T20:58Z (cirlean memcpy model: no overlap check; from the C maintainer session, claims checked by the evidence owner): cirlean's memcpyModel
  (every pin up to c4ef58d) copies overlapping ranges, which C leaves undefined (memmove is the defined one; memset and
  memcmp are unaffected). Check (checks/memcpy-20261025, tools/memcpy_claims.py; closures from cirpun --print-closure;
  controls: StrPair::SetStr flagged, XMLNode::ToDocument not): of 281 claimed C/C++ closures (B, C1, C2, D1, D2 tinyxml2
  re-run and held-out, TRX, the cJSON harness), 16 contain a memcpy; every site was read in the source: the destinations
  are fresh allocations (cJSON parse_number, ensure, cJSON_strdup, create_reference; tinyxml2 StrPair::SetStr) or the
  print buffer copied from a separate string block, or the source is a local array (StrPair::GetStr); zlib's
  inflateCopy (conditional) has 3 sites, but its theorem covers only the failure paths, which return before any memcpy.
  B rows are UB findings, which the gap cannot create. No claimed theorem depends on the gap; equiv-lean's 22 ClangIR
  files contain no memcpy (the equiv-lean maintainer session). Paper: one sentence in sec-limits. The same scan runs on D2 zlib and the held-outs,
  T2, T3, H and the full harness before their claims enter. Fix after the freeze (cirlean).

- 2026-10-25T21:00Z (two later results on their own commits; planning): (a) equiv-lean's musl item (user via the coordinating session) is complete on branch
  musl, head 65c47df2f99065418c74442f79ff52307d2ffeb3 (from 751764f, cirlean 28e2380; not merged): partial-correctness
  theorems that musl 1.2.5's strlen and memcpy (gpg-verified tarball, files byte-identical to src/string) refine
  cirlean's models under stated hypotheses, plus counterexamples where the models differ from musl (non-char elements
  in strlen; one-element punning, signed bytes, indeterminate bytes and overlapping ranges in memcpy). The evidence
  owner's check runs from a hard-linked copy of the 751764f replay copy plus the commit's 17 new files (all Lean files and
  examples equal the commit's blobs; only HANDOFF and README differ, from the later master commit of the base copy):
  build of the 9 new modules with lean -o into new files, the equiv-lean maintainer session's Axioms.lean (11 lines expected), leanchecker replay
  (checks/eqmusl-20261025T2100Z). (b) JimpleLean starts termination support (total-correctness VC with variants and its
  soundness proof); termination theorems for the CardDemo Java programs may enter only as a separate, labelled result
  on their own commit if they land by Mon 2026-10-26 18:00Z and pass the evidence owner's replay before Tue 06:00Z; the
  Java headline stays partial correctness on the current pins.

- 2026-10-25T21:05Z (M, coblean's front end, part FE final; from the COBOL maintainer session, recounted by the evidence owner): END 20:59:59Z. My recount of
  the 90 run records (checks/Mcobolfe2-20261025, recount.txt): set 2, the first 30 candidates of order_set2.tsv (all
  tested, none stillborn): old suite 21/30 = 0.700 [0.521, 0.833]; extended suite 23/30 = 0.767 [0.591, 0.882]; killed
  only by the extended suite: orders 19 (parser.py:2111 LOG) and 27 (parser.py:235 STMT), both by X.hp; killed only by the
  old suite: none. Set 1 on the extended suite, labelled as not independent of the added tests: 25/30 = 0.833 [0.664,
  0.927] (old suite 18/30). Of set 2's 7 survivors on the extended suite, order 28 is labelled equivalent (on every
  program the original front end accepts; reason in FE_ANALYSIS_v1.md 3ffe5d42...), reported in its own column; orders 1
  and 18 survive on the statically laid-out STRING path, which no extended test reaches (a design miss found after the
  runs, the suite still frozen). Cost of the phase 7.79 core-h; part FE total 10.364 of 20 core-h.

- 2026-10-25T21:07Z (cJSON 32-bit instance: the user's decision, relayed by the coordinating session): the user has prepared a private report to cJSON's
  maintainers (not yet sent). Nothing public about the 32-bit instance until a fix or 2027-01-23; obligation/bound
  wording only. At the user's request cirlean (the C maintainer session) is producing a kernel-checked refutation of the ILP32 instance on
  6d9f244 (for L = 715,827,883 the size passed to ensure at cJSON.c:1007 is 5, and ensure returns the 256-byte buffer
  without growing it), mainly as evidence for the report; if it lands and checks before the freeze it sits with the
  32-bit bound sentence under the same rule. Evidence owner's note: the 64-bit counterexample trace in the full-harness
  text transfers to 32-bit builds by the same arithmetic, so it is held under the same rule in any public version unless
  the user decides otherwise (asked via the coordinating session).

- 2026-10-25T21:17Z (coblean semantics fixes merged; declared later change; from the COBOL maintainer session, checked by the evidence owner): snapshot
  ~/coblean_snapshots/coblean-20261025T2114Z, manifest manifest_coblean-20261025T2114Z.sha256 13b53de1... (281 entries,
  281/281 OK on my check). Against 2014Z the sources differ only in Cobol/Edit.lean, Cobol/Layout.lean and
  tools/cobolfe/datadiv.py (plus HANDOFF and the new evidence TSV); their changed lines equal the scratch diffs
  505accdc..., 18484c24..., 39f8ca85... (my diff). Against 2306Z only Cobol/Edit.olean and Cobol/Layout.olean change (44
  Cobol oleans compared; Cobol.olean still be3132eb...); the 9 CardDemo IRs are identical. File.lean unchanged: M-pos
  stays unfixed and documented. coblean's re-check: TH0 from source 115 jobs, 24 standard + 1 bv_decide; 25 axiom lines
  identical to 2306Z's; new TSV EVIDENCE_carddemo_live_20261025T2113Z.tsv f1aaa37d... (174 rows; 171 identical to 2014Z,
  3 line counts differ: T4, E4, T7). The evidence owner's own re-run of TH0, all TH*.ax/.st rows and T4/E4/T7 on a full
  copy (replay/cobE5-20261025T2117Z; checks/cobE5-20261025T2117Z) is running.

- 2026-10-25T21:20Z (M, coblean semantics set 2 final; from the COBOL maintainer session, recounted by the evidence owner): set 2 ran 19:09:31-20:31:31Z and set 1
  on the new rows 20:36:28-21:14:23Z, on the 2306Z pin (mut_one_v3). My recount (checks/Mcoblean2-20261025,
  recount_set2.txt): set 2 = orders 1-30 of order2.tsv (ids checked), none stillborn: old suite 19/30 = 0.633 [0.455,
  0.781], extended suite 21/30 = 0.700 [0.521, 0.833]; killed only by the extended suite #15 Edit.lean:134:37:ROR
  (X.edsize) and #17 File.lean:264:59:ROR (X.file2); families tested/old/extended AOR 6/4/4, CND 2/2/2, LIT 12/9/9, LOG
  1/1/1, ROR 8/2/4, STS 1/1/1; 8 sorries in 6 mutants; 8,903 core-s. Equivalence labels with Lean proofs: #1
  (wrapBinMut_eq) and #23 (decZonedMut_eq); each mutant definition equals the pin's with exactly the candidate's token
  changed, and both proofs compile against the 2306Z oleans with [propext, Quot.sound] (my run, eqcheck/). Set 1 on the
  extended suite (not independent): set 1's 15 old-suite kills plus the new rows' kills give 26/30 = 0.867 [0.703,
  0.947]; killed by new rows only: 2, 6, 7, 8, 12, 17, 18, 22, 24, 28, 29. Paper: the mutation paragraph in sec-stack
  (all bridges but StrictTS, which follows). Also from the COBOL maintainer session: the trust items' engineering agents cost $304.73 from 16:00Z
  to 21:18Z (cost.py; NIST's share with all of main counted 138.68 against its $200 model cap); the measurements
  themselves made no model call.

- 2026-10-25T21:35Z (T3 resume record after the Rust crash fix; from the orchestrator session, checked by the evidence owner): dispatcher stopped at 19:51:06Z;
  the 12 in-flight commits finished by 21:15:04Z. A switch-script deviation (it waited 15 minutes instead of stopping)
  let the old driver dispatch orders 48-63 under the old copy. Orders 51 (C++), 52 (C), 53 (C++) and 56 (Java, no
  changed function) finished with records; per t3_commits.tsv none involves Rust, and the copies differ only in the Rust
  equivalence adapter, so they stand (evidence owner's ruling). The others (48-50, 54, 55, 57-63) were stopped by
  verified PIDs without records and are re-run. Affected list: the recorded grep (affected_command.txt) over the Rust
  logs, output affected_logs.txt 0c53a5d2... = order 33 only; superseded/cf1_20261025T213157Z/MOVES.tsv ef984c5f....
  Crash fix 1 copy T3_cf1_20261025T204341Z (SHA256SUMS 93e06462...; equiv.py diff b3cfa65d...; tests SUMS f9049f5d...,
  18/18 OK on my check). Crash fix 2 (the driver's resume check compared the Rust pin directories through a symlinked
  path; now resolved paths; diff b632635f...): copy T3_cf2_20261025T213312Z (SHA256SUMS c9b2977c..., 208/208 OK on my
  check; versus cf1 only scripts/prereg_t3.py differs, 009f97d2... -> c363d360...). Resumed 21:33:21Z; pins.json
  b45a9a8a... (resumed entry appended); 50 records, $26.02, 100 commits to dispatch, order 33 first.

- 2026-10-25T21:44Z (coblean fixed semantics, independent re-check done): on a full copy of coblean-20261025T2114Z
  (replay/cobE5-20261025T2117Z, diff -rq empty) the evidence owner re-ran TH0 (rebuild from source: "Build completed
  successfully (115 jobs). | standard: 24 | bv_decide: 1", 1,563 s), all 50 TH*.ax/.st rows (each theorem's axioms and
  statement hash) and T4, E4, T7 with tools/cob_evidence_run.py under the guard: 54/54 match the TSV f1aaa37d...'s expected
  values, whose TH rows equal 2306Z's. Paper (sec-limits): a later version fixes C9 and M-syncsub, the COBOL package's own
  theorems still build from source with the same axioms and statements there, and M-pos remains as described.

- 2026-10-25T21:44Z (veriforch tool fix in the live tree; from the orchestrator session): the proof-cache key (body, callee contract keys, pin, kind) did
  not include a unit's given statement, so a changed given statement could reuse a cached proof of the older one (the
  record then showed the statement actually proved: no false claim, but not the intended one). Fix: live
  orch/veriforch/scheduler.py -> 2ec92745... (diff scheduler_givenstmt_20261025.diff ba785194...); stored proposals and
  cycle proofs count only if they prove the current given statement. Impact on the cJSON parse-only theorem: none (its
  given units came from their given candidates; the 6 model units have no given statement). The frozen T2, T3 and D2
  copies do not use the live scheduler. Open: H part two phase 1 runs live veriforch (started with scheduler.py
  5965ce3a...); asked of the orchestrator session whether the running process or its workers can load the changed file.

- 2026-10-25T21:45Z (H part two phase 1 and the live scheduler change; from the orchestrator session, partly checked): phase 1 (pid 3165512, started
  19:07:30Z) imported veriforch.scheduler once at start (5965ce3a...); its parallelism is threads sharing the module;
  its subprocesses (run1.sh, the guard, timeout, lean, cir2lean, cirscan) do not import veriforch. My grep of orch/*.py:
  no importlib.reload, multiprocessing or ProcessPoolExecutor; sys.executable appears only in modules the C verify path
  does not use (per the orchestrator session: c2rust/, modernize/). So phase 1 runs entirely on 5965ce3a, as its snapshot records. Phase 2
  records its scheduler and adapter hashes at its run-of-record start.

- 2026-10-25T21:46Z (T4 Java: a class-hierarchy hypothesis; from the equiv-lean maintainer session, ruling by the evidence owner): the Java field-header theorems use
  their callees' proved contracts. JimpleLean's modular call rule lets an instance-method contract cover every
  override, so these open-world statements (any program containing the protocol classes) take one program hypothesis,
  NoRedecl: no application subclass of TCompactProtocol redeclares the called methods (readByte, readVarint32 via
  readI16, readFieldId, getTType; writeVarint32, writeByteDirect, writeI16). It is neither a transport nor a library
  contract. Ruling: if a corollary proves NoRedecl by kernel computation (no native_decide) for the exact class set of
  the Thrift jar that T4's Java inputs come from (277 classes; its only subclass TTupleProtocol redeclares none), the row
  is "proved" for that program, with the open-world statement and its NoRedecl hypothesis noted on the row. Without
  that corollary by the freeze, the row is marked separately, "proved under the program assumption NoRedecl", and the
  assumption is listed with the transport contracts.

- 2026-10-25T21:47Z (T4 NoRedecl: the class set; from the equiv-lean maintainer session, checked by the evidence owner): jar
  ~/veriforch/scratch/thrift_java/thrift-java-f0eb8b84.jar (sha256 d7b84d85...) has 262 .class entries, equal to
  jar_classes.txt; the Java Gen module's 277 classes are those 262 plus 15 lambda classes Soot generates for
  invokedynamic sites (gen-only 15, jar-only 0; checks/t4-noredecl-20261025). The corollary will also prove
  prog.classes.length = 277 by kernel computation, so the program the theorems quantify over misses no class.

- 2026-10-25T21:57Z (T2 status at 22:00Z and properties of the frozen procedure, for the analysis; from the orchestrator session): 233/1000 units in sample
  order: blocked 96, timeout 87, proved_model_stated 44, partial 4, conditional 2, infrastructure_error 0; 44/44 kernel
  replays pass. C 33 (18/5/10), C++ 117 (57/18/39, 3 partial), Java 62 (12/14/35, 1 conditional), Rust 21 (9/7/3, 1
  partial, 1 conditional). Model $61.23 (ledger) + $1.23 killed attempts (usage logs); 5.72 core-h; projected about
  $270 and an end near 05:30Z Mon (the $500 cap will not bind). Properties to state in the analysis: the per-unit budget
  is checked before each call, so 112 units overshot it (max $1.26, total $24.56); 12 wall kills (Java 9, C++ 3), each
  one CPU-bound check past the 10-minute wall, read as timeouts (R6); the ledger's core-h omits the last check of a
  wall-killed unit (guard logs are complete and are used); the first Rust unit in each fresh slot runs the Rust front end
  (60-90 s) inside its wall (Rust timeouts are to be listed with this mark); dispatch waits while a long unit holds
  shared closure members (no effect on outcomes).

- 2026-10-25T22:09Z (T2: the first refuted unit is a model false positive; from the orchestrator session, reading by the evidence owner): unit 254 (C,
  protocol) thrift_bitwise_cast_gdouble (lib/c_glib thrift_binary_protocol.c) is refuted (real_bug) under the frozen
  mapping: it writes a union's guint64 member and reads its gdouble member, which C11 defines (6.5.2.3, footnote 95),
  while cirlean ffab71e makes the other member indeterminate, so every replay ends in "read of an indeterminate or
  ill-typed value". The finding's model-written text calls it a tool gap, but the mechanical verdict does not use it.
  Reading: the R6 outcome stays as recorded (nothing excluded after the fact); the analysis lists every refuted T2 unit
  with the evidence owner's re-run and classification (UB in C, a precondition the library's callers always meet, or
  a model limit with the C clause), as for D. The callers on that path (e.g. thrift_binary_protocol_read_double) are
  listed by the orchestrator session in a "known model false positive" table. A stricter model can only refute or block falsely; it cannot
  make a no-UB proof unsound, so claimed proofs are unaffected.

- 2026-10-25T22:16Z (JimpleLean termination framework; from the Java maintainer session, not yet checked): new module Jimple/Termination.lean. Soundness
  Jimple.TermVC.mterm and Jimple.AllTermVC.term (a valid table whose methods satisfy the termination VCs with ranked
  callees gives ContractTerm for every method); Jimple.total_of_sat_mterm (partial correctness Sat plus MTerm gives
  existence of an execution and the postcondition on every execution); Jimple.MTerm.run. MTerm (mutual with VTerm,
  RTerm, BTerm): every execution terminates over every nondeterministic choice and callee outcome, and one exists.
  Reported axioms std for all four; JimpleLean regression 135 jobs (22:14Z). First example: CBACT02C run_term and
  run_total (JimpleLean's own CardDemo example). Snapshot name by about 01:00Z; the evidence owner checks it then, and
  termination results enter the paper only under the conditions recorded above (by Mon 18:00Z, own commit, replayed).

- 2026-10-25T22:16Z (T3 census note; from the orchestrator session, to be checked at the census): orders 66-69 (THRIFT-6177..6180, WebSocket fixes) are
  "unknown: no changed function": each changes only TWebSocketServer.h, a header-only template that no library source
  file includes, so the built library contains none of the changed code. Scope fact for the paper: T3 sees only code
  compiled into the library's translation units. Status: 58 commits done, $27.41, no crashes.

- 2026-10-25T22:17Z (Java termination: deadlines and form; ruling by the evidence owner, asked by the equiv-lean maintainer session): the migration headline stays
  the 16 theorems on 751764f (Java partial correctness; no re-pin before the freeze, the coordinating session). Total-correctness Java theorems
  enter only as a separate, labelled result on their own commit, with the partial theorems kept unchanged beside them.
  Packages by Mon 2026-10-26 18:00Z; the clean build of that commit green by Mon 22:00Z, frozen afterwards, so the
  evidence owner's delta replay ends before Tue 06:00Z. Per-program rows: total where proved, partial otherwise, marked
  per row (no all-or-nothing).

- 2026-10-25T22:23Z (veriforch live scheduler, two more fixes; from the orchestrator session): scheduler.py -> 12d39ff6... (diff scheduler_givenimports_20261025.diff
  5fc6fd0c...). (1) A unit with a given statement and no candidate tried is assumed by its callers through that
  statement ("given contract assumed (no proof tried)"); callers become conditional instead of blocked; no axiom.
  (2) The imports a given statement needs reach every module where it appears. Frozen T2, T3 and D2 copies and yajl
  phase 1 are unaffected. For the full-harness and yajl labelled results, the evidence owner reads assumed.json: any
  assumed contract makes a result conditional, listed by name, never "proved".

- 2026-10-25T22:29Z (M, StrictTS: population complete; deviation 4 configuration acknowledged; from the TypeScript maintainer session, checked by the evidence owner):
  drive exit 0 at 22:13:41Z (run_m.py c5cfd03). My recount of the 32 result.json files (order positions 1-32, checked
  against M/strictts/order.tsv; copied to checks/Mstrictts-final-20261025): 30 tested, 20 killed, 10 survived = 0.667
  [0.488, 0.808]; 2 stillborn, both the mutated definition failing to elaborate (position 8 F64.lean:44:62:LOG at
  45:25; Core/Sem.lean:1420:15:AOR, an invalid match pattern at 1420:12). Reference validation 527 rows, 0.393 core-h,
  12.8 min. config_w2v.json 00516269... differs from config_w2.json (c9e4b361...) exactly in coreh 20 -> 17.7,
  per_validation_coreh 1.5 -> 0.4 and per_validation_min 45 -> 15, as the 18:46Z formula requires. H tally
  H_tally_final.txt 19e65732...: 34 lines, each with its source; my parse gives metered 2.0570 + estimated 0.1495 =
  2.2065, rounded up 2.3 (so coreh 17.7); spot check: the 21 base_ff30e09 guard logs sum to 0.127 as listed.
  Survivor validations may start.

- 2026-10-25T22:35Z (musl model-to-implementation theorems checked; evidence owner): equiv-lean branch musl 65c47df (from 751764f,
  cirlean 28e2380), checked on a hard-linked copy of replay/eq-20261025T1449Z plus the commit's 17 new files
  (checks/eqmusl-20261025T2107Z): all tracked Lean and example files equal the commit's blobs (only HANDOFF and README
  differ, from the base copy's later master commit); the 9 new modules built with the lakefile's options
  (Elab.async=false, autoImplicit=false, relaxedAutoImplicit=false; Memcpy 4,885 s; earlier attempts without those
  options aborted with "failed to create thread", copies eqmusl-20261025T2100Z kept apart); Axioms.lean prints 11 lines,
  all [propext, Classical.choice, Quot.sound]; leanchecker replays 9/9 rc 0; the closure has 62 modules, the other 53 all
  replayed or reused in the C-to-Rust check on byte-identical files; 1.446 core-h. Paper: a paragraph in sec-trust
  (two models refined by musl's code under stated conditions; five differences shown as theorems).

- 2026-10-25T22:37Z (cJSON 32-bit refutation, embargoed; from a session for the coordinating session, partly checked): ~/fvreview_20261023/m32test/CJSON32Refute.lean
  (SHA256SUMS_refute: 5/5 OK on my check): kernel-checked theorems on cJSON 6d9f244 built for i686 (ClangIR
  cJSON_6d9f244_i686.cir 3e4e26e0..., Gen.CJSON32): ensure returns the unchanged 256-byte buffer for needed <= 255 at
  offset 0; for every L in [715,827,883; 715,827,924] on a string of L bytes 0x01, print_string_ptr computes
  output_length = 6L - 2^32 and needed = 6L - 2^32 + 3 and ensure returns the unchanged buffer; the specialization at
  L = 715,827,883 (needed = 5); reported axioms std, no sorry. Under the user's embargo (nothing public about 32-bit
  until a fix or 2027-01-23). The evidence owner replays it once the cirlean version and build command are known (asked).

- 2026-10-25T22:44Z (cJSON 32-bit refutation, embargoed: independent replay done; disclosure evidence, not a paper claim): from a copy
  (checks/cj32refute-20261025) over the frozen cirlean ~/cirlean_frozen/c4ef58d_20261025: leanchecker replays all 172
  modules of the closure rc 0 (128 generated Gen.CJSON32 modules, 43 CIR modules at c4ef58d, CJSON32Refute); the five
  theorems print [propext, Classical.choice, Quot.sound]; no sorry in the file. Nothing public until a fix or
  2027-01-23 (the user's rule).

- 2026-10-25T22:55Z (D2 zlib re-run finished; held-out started; from the orchestrator session): re-run 100/100 at 22:54:07Z (summary.json 65ca82e5...,
  outcomes.tsv d3b2ac29...): proved_model_stated 19, conditional 1, partial 4, blocked 23, timeout 53, no refuted or
  infrastructure error; model $98.71, 52,762 core-s. The zlib held-out driver started at 22:54:08Z from the same chain
  (front end 152 s, rc 0); watcher re-armed on both remaining drivers. D2 ledger $336.19 of $500; at about $1 per zlib
  unit the stop rule (ledger + $0.80 x units in flight >= $500) may bind near the end of zlib held-out; unattempted
  units are reported per the pre-registration. The evidence owner's check of the re-run runs from a copy (vo2zr).

- 2026-10-25T23:12Z (D2 zlib re-run checked; evidence owner, via a fork): copy replay/vo-Dz2r-20261025T2256Z (summary and outcomes hashes
  = veriforch's); checks/vo2zr-20261025T2256Z: 100/100 rows = the frozen sample, outcomes and Wilson = summary.json
  (proved 19, 0.125-0.278); 5 wall kills counted as timeouts; 24/24 claimed units with checked theorems, standard axioms
  throughout their closures; kernel replay 364/364 package modules rc 0, 38 cirlean modules reused on byte-identical
  files; cirpun: 12 clean, 9 clean except opaque-handle casts typed by the statements, 3 non-clean only on paths their
  statements exclude (gzclearerr, gz_reset: gz_error's message path with no message; inflateBack: only a null stream);
  the only memcpy (infback.c:334) is on that excluded path; no hexadecimal FP constant. D -> D2 transitions: 8 stay
  proved, 2 become timeouts, 8 timeouts + 2 conditionals + 1 infrastructure error become proofs. Paper: tab:sample row and
  a paragraph reading zlib as the control (its gain is as large as the fixed populations', so the D2 gains cannot be
  credited to the fixes alone).

- 2026-10-25T23:12Z (JimpleLean termination snapshot; from the Java maintainer session, manifest checked): ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z
  (SHA256SUMS c1808513..., 144/144 OK on my check; source only, no build): Jimple/Termination.lean 04ab1dd3...,
  Jimple/TermSplit.lean d956902f... (Jimple.TermVC.of_thin reuses a method's partial-correctness VC with a thin
  variant VC). Reported: regression 142 jobs, 0 sorryAx, std axioms; total correctness for CBACT02C, CBCUS01C, CBACT03C in
  JimpleLean's examples; equiv-lean packages done for CBTRN01C and CBACT01C, others in progress. The evidence owner builds
  and replays it with the separate equiv-lean commit (deadlines Mon 18:00Z / 22:00Z).

- 2026-10-25T23:19Z (veriforch live scheduler, bundle change; from the orchestrator session, hashes checked): scheduler.py -> 30758b71... (diff
  scheduler_unitbundle_20261025.diff ca9c364e...): owners' multi-module proof bundles can serve single units (cirlean's
  ensure_spec and update_offset_spec share one file importing a shared tactic module), and bundle modules are checked
  once per run and reused by name after a text-hash comparison (a same-name module with different text is refused).
  What is proved and how it is checked are unchanged; frozen T2/T3/D2 copies and yajl phase 1 unaffected. The
  full-harness check replays every module of the final closure itself, so reuse inside the run does not matter there.

- 2026-10-25T23:28Z (cJSON 32-bit refutation v2, embargoed; from a session, checked by the evidence owner): CJSON32Refute.lean extended to 11
  theorems at the user's request (ebc059f5..., olean a3923c8e...; Gen.CJSON32 oleans unchanged against my v1 copy).
  From a copy (checks/cj32refute-20261025/v2): leanchecker CJSON32Refute rc 0 (the other 171 closure modules unchanged
  and replayed in v1); elaboration rc 0 prints 11 theorems, all [propext, Classical.choice, Quot.sound]; no sorry.
  Disclosure evidence only; nothing public until a fix or 2027-01-23.

- 2026-10-25T23:36Z (Java total correctness for all eight programs, reported; from the Java maintainer session, not yet checked): CBACT02C, CBCUS01C, CBACT03C in
  JimpleLean snapshot T2312Z (Examples.CardDemo.run_total, cu_run_total, c3_run_total); CBTRN01C, CBACT01C, CBTRN03C,
  CBACT04C, CBTRN02C as equiv-lean packages (EquivLean.Modernize.<Prog>[.Any].Java.run_term and run_total), built against
  the 751764f freeze build with the T2312Z termination modules; reported axioms std. The equiv-lean maintainer session integrates them on branch
  java-total pinned to T2312Z (build running). Manifests ~/jimplelean_work/termpk/manifests/. At the commit check the
  evidence owner reads each total statement and confirms it is about the same Java program as the headline theorem
  (the proved translation) and how it composes with the partial refinement; the three in JimpleLean's examples count only
  if they are stated over those same programs.

- 2026-10-25T23:38Z (Java total correctness: programs and statement form; from the Java maintainer session, partly checked): the three JimpleLean examples are
  over the same programs: my comparison of JimpleLean-20261025T2312Z/examples_java/{cbact02c,cbcus01c,cbact03c}/jimple
  with equiv-lean's EquivLean/Demo/Gen/Jimple/mod_<prog> at 751764f: 10/10 files byte-identical. On java-total
  (49e9a3a) the termination files are imported with import_jl.py, so they are typechecked over the headline programs'
  Gen.prog. Statement form for all eight: run_total : forall args s, S.pre args s -> (exists o, MExec Gen.prog runRef
  args s o) /\ forall o, MExec Gen.prog runRef args s o -> S.post args s o, with S equiv-lean's runSpec (the contract that
  statement_of_sat consumes; glue lemmas for the three JimpleLean ones). Composition with the headline Sim (partial on
  the Java side): run_term adds that a Java outcome exists and no execution diverges; the equiv-lean maintainer session states the total version
  through a Total Behaves instance (Safe = no wrong outcome and MTerm). The evidence owner checks these statements and
  replays the java-total build at the deadline.

- 2026-10-26T00:29Z (T3 disk prune, approved with conditions; requested by the orchestrator session after a VM disk report): only .lake/build and per-run
  olean caches inside finished commit directories may be deleted (veriforch's prune tool: allowlist, manifest, in-use and
  60-minute recency guards); records, logs, ci.json, prepass and shared caches stay. Complete directories are kept for
  every commit where any changed function has a verdict other than unknown (equivalent, changed_only_where_old_unsafe,
  behaviour_changed with a witness), decided from the records, and for order 2 (blocked: build). The deletion manifest
  (per commit: files, bytes) and its sha256 come to the evidence owner. T2 and D2 untouched until they end.

- 2026-10-26T00:31Z (M, StrictTS: survivor validations; rulings by the evidence owner on the TypeScript maintainer session's two problems): the extended-suite chain
  ended 00:26Z. (1) Deviation 5: two survivors (Prim.lean:37:31:LIT, F64.lean:403:40:ROR) are "not validated (build)"
  because Lean aborted at module start with "failed to create thread: Resource temporarily unavailable" (exit 134),
  an environment failure (cgroup pids never at max; the same modules built for the reference and 8 survivors). They are
  re-run under the frozen procedure; if the failure recurs, with synchronous elaboration (Elab.async=false), recorded
  exactly as the crash fix (it does not change what is proved). (2) The frozen extended-suite criterion ("killed when a
  row, status and counts, differs from the reference's") marks all 8 validated survivors killed, but 60-75 rows per
  survivor differ only in counts (inputs_compared), which the time-budgeted drivers (validate.js 624/642/696) make
  load-dependent. Ruling: the pre-registered outcome is reported exactly as defined, with this caveat; added, labelled
  post hoc: (a) a second unmutated reference run compared row by row with the first (noise calibration), (b) a
  status-level table (match <-> MISMATCH per survivor) judged against (a), status flips also seen between the two
  references counting as noise; and whether the drivers' inputs are seeded. The population result (20/30) is unaffected.

- 2026-10-26T00:32Z (T3 prune done; from the orchestrator session, checked by the evidence owner): keep-list t3_keep_orders_v1.txt (22d07247...) = orders 2,
  11, 24, 29, 30, 32, 41, 57, 71, 77, 79; my recomputation from every finished commit's ci.json (verdicts equivalent,
  changed_only_where_old_unsafe or behaviour_changed) gives exactly these orders plus order 2; orders whose only
  non-unknown verdicts are unchanged or test (3, 4, 21, 28, 31, 36, 73) carry no claim. Prune roots
  t3_prune_roots_v1.txt (16432307...): 63, none in the keep-list; 9 skipped by the recency/in-use guards, 54 pruned.
  Deletion manifest manifest.tsv 5d6d8e37... (every path under .lake/build; my check) and per_commit.tsv cd137950...;
  103,504 files, 11.68 GiB; tool prune_build_v4.py 4fcf3711.... Records, logs, ci.json, prepass and shared caches kept.
  Also from the TypeScript maintainer session: StrictTS validate.js seeds each target's inputs from a hash of its absolute path and line, so every copy
  directory draws a different deterministic input sample (a second noise source besides the time budget); the second
  reference run uses a fresh copy at a new path.

- 2026-10-26T00:32Z (T4 discrepancy set, reported; from the equiv-lean maintainer session, not yet checked): commits C++ t4-cpp b3b5f35, Java t4-java 26f42c6, Rust
  t4-rust fed0c3b; each row proved on all three semantics on the spec's named bytes; std axioms; transport contracts
  only, plus NoRedecl for Java. W1 delta 15: C++ and Java write the spec's F5, Rust 05 1E (both decode). W2 i16 delta
  overflow: C++ and Java write the spec's long form, Rust panics (debug build). R1 15 after id 32767: spec rejects; C++
  and Java return id -32768, Rust an error. R2 byte 10 after 0: spec rejects; C++ and Rust read STOP, Java reads
  TField(STOP, id 1). R3 an out-of-range id varint: all three accept what the spec rejects. V1 an overlong varint32:
  C++ ends in the transport's end-of-input, Java and Rust raise protocol errors; C++ also accepts 6-10-byte varints
  modulo 2^32. Agreement on exVarint32Exceeds and on 05 1E after 0. NoRedecl corollary: thrift_fh_hyps and
  thrift_classes_length in EquivLean/Demo/Thrift/Java/ThriftProg.lean (decide +kernel and rfl). Open: exNegSize, a
  Java getMinSerializedSize UUID candidate. Then t4-final from 751764f with a clean build and a per-row table; the
  evidence owner checks every row (axioms, replay, statements, the named bytes) there.

- 2026-10-26T00:51Z (T4 additions; from the equiv-lean maintainer session, not yet checked): V2, the bytes 80 80 80 80 80 00: C++ reads six bytes and returns 0
  (readVarint32_overlong6, t4-cpp 64c9183); Java throws TProtocolException after five bytes (rv32_exVarint32Overlong, any
  continuation, t4-java 14956e7); Rust returns InvalidData (rust_exVarint32Overlong, fed0c3b); the spec says overlong:
  C++ accepts what the others reject. exNegSize (F5 80 80 80 80 08) proved for C++: TProtocolException(NEGATIVE_SIZE)
  (readListBegin_exNegSize), running the real exception constructors with the message string on cirlean's built-in
  model, so this M row is "under library contracts"; it agrees with Rust. The C++ column is final; Java list/set pending;
  t4-final (from 751764f, all columns merged) follows with the per-row table and a clean build.

- 2026-10-26T00:53Z (T4: the user's rule on native confirmation, relayed by the coordinating session): before any outside report, every T4 discrepancy row
  (W1, W2, R1, R2, R3, V1, V2) is run against the real C++, Java and Rust Thrift libraries; a native result that differs
  from a model's prediction is a model gap, not a Thrift bug. The equiv-lean maintainer session delivers a per-row native table before Tue 2026-10-27
  03:00Z. Paper: until a row has native confirmation it is described as a difference between the language models, not
  as a Thrift interoperability bug; a row whose native behaviour differs from its model becomes a model-gap entry in the
  limitations. Outward handling of the parser differentials stays with the user (FREEZE_PLAN 24).

- 2026-10-26T00:55Z (D2 lang3 held-out finished; from the orchestrator session): 100/100 at 00:53:29Z (summary.json 7484d746..., outcomes.tsv a3611d1a...):
  driver counts proved_model_stated 14, conditional 7, partial 6, blocked 31, timeout 41, infrastructure_error 1 (order 84,
  DurationFormatUtils$Token.increment(), "stuck (negative cache, 3 earlier attempts)": a timeout under the recorded
  reading). Orders 50 (blocked) and 80 (partial) carry the bridge-collision names; veriforch establishes from the records
  whether the bridge or the method was verified and, if either was hit, re-runs both from a crash-fix copy gated to the
  colliding keys, with a record. D2 ledger $356.94; only zlib held-out remains. The evidence owner's check runs from a
  copy (vo2l3h).

- 2026-10-26T01:01Z (D2 lang3 held-out orders 50 and 80: bridge collision hit, crash-fix re-run; from the orchestrator session, per the 15:54Z ruling):
  units.json lists two units per name (the real method, then the compiler's bridge); the driver's match_unit took the
  first (the real method) to map outcomes, while vo verify --only <name> verified the scheduler's last unit (the bridge),
  whose own contract entered the context; the Lean statement (vo_mref without return type) resolved to the first
  declaration, the real body. So 50 was proved (kernel PASS) and then mapped "blocked" from the real method's scope gap,
  and 80 ended partial: both infrastructure errors until re-run. Re-run: copy ~/veriforch_frozen/D2_20261025T030336Z_bridgefix
  (D2's copy + jimple_bridge_order_fix_20261025.diff, new manifest), run dir runs/prereg_d2_lang3_bridgefix (cache linked),
  records runs/prereg/D2/lang3/heldout_bridgefix/, D2 pins (JimpleLean 0300Z), D2's exact command, replay and the frozen
  map_outcome. One recorded adaptation: rows are matched by name and descriptor return type (after the reorder the frozen
  first-by-name match would pick the bridge), which selects the same frame unit as before. Model at most $1.60, kept out
  of D2's ledger (so the zlib held-out stop rule is unchanged) and reported on its own line in D2's cost.

- 2026-10-26T01:23Z (D2 lang3 held-out checked; evidence owner, via a fork): copy replay/vo-Dl3h-20261026T0056Z (summary and outcomes
  hashes = veriforch's; JimpleLean 0300Z dependency 133/133 = the pin); checks/vo2l3h-20261026T0056Z: 100 rows = the
  frozen sample; 99 agree, order 50 differs (record proved, driver blocked: the bridge collision). R6 counts with the
  recorded readings: proved 14 (0.085-0.221), conditional 7, partial 5, blocked 30, timeout 42 (order 84 negative-cache
  stuck after three ordinary failures; 7 wall kills), infrastructure 2 (orders 50 and 80, pending the crash-fix re-run).
  26/26 claims standard axioms; 687 modules replayed rc 0; no claim reaches Double.compare (controls pass; order 56's
  flag is an overload match, its body has no call); interface defect, labelled post hoc: 3 of the 30 blocked units carry
  an own-interface gap token, 1 (order 10) is blocked only by them. Paper: tab:sample row and one clause on the
  interface count; the row is updated when 50 and 80 come back.

- 2026-10-26T01:28Z (D2 lang3 held-out orders 50 and 80 re-run; from the orchestrator session, checked by the evidence owner): copy
  ~/veriforch_frozen/D2_20261025T030336Z_bridgefix (SHA256SUMS 8a930d75..., 87/87 OK on my check; versus D2's copy only
  adapters/jimple/build.py differs, c1685952... -> da3e0329...; diff jimple_bridge_order_fix_20261025.diff 33585de3...),
  JimpleLean 0300Z, run dir runs/prereg_d2_lang3_bridgefix, records heldout_bridgefix/results.jsonl 3343f0f8... (read):
  order 50 DiffBuilder$1.getRight() resolves to the real method, status gap, outcome blocked
  (gap:unmodelled:java.lang.Boolean.valueOf/1), $0.0135; order 80 DiffBuilder$8.getLeft() resolves to the real method
  (closure of 5 units), budget exhausted, outcome timeout (was partial), $0.99. Neither has a claimed theorem. Model
  $1.0046 on its own line, outside D2's ledger. Final R6 counts for the held-out sample: proved 14, conditional 7,
  partial 5, blocked 31, timeout 43, infrastructure 0 (tab:sample updated). Side finding (post-freeze tool list): the
  per-unit proposal cache is keyed by unit name, so same-named units can share proposals; here only a free attempt
  replayed the bridge's old proposal and got stuck, without effect on the outcome.

- 2026-10-26T01:28Z (D2 lang3 orders 50/80: resolution confirmed; from the orchestrator session): records d13a5056... (50) and b70d3724... (80); in the
  re-run's package, vo_mref for DiffBuilder$1.getRight resolves to return type java.lang.Boolean and for DiffBuilder$8.getLeft
  to Double[] (the real methods; the bridges return Object), and the scheduler processed exactly those units
  (scratch/thrift_java/d2_check/ResolveCheck.lean, rc 0). Closure replay of 80's proved lambda <init>: PASS.

- 2026-10-26T01:32Z (M, StrictTS: deviation 5 and the post-hoc additions done; from the TypeScript maintainer session, to be checked against RESULTS_M.md): Prim
  37:31 built normally; F64 403:40 aborted in thread creation again and was validated with the crash fix
  (weakLeanArgs = ["-DElab.async=false"], recorded). Pre-registered extended outcome: 10/10 validated survivors "killed by
  the extended suite", with the caveat. Post hoc (a): the second unmutated reference differs from the first in 54 rows,
  52 count-only, the same scale as the survivors (60-75 rows). Post hoc (b), input by input: mutation-specific
  differences in 3 of 10 survivors (#6, #12, #32, all from the mutated exponentiation case); the rest noise (pow last
  place, median sort order, === on records inside unknown, latent Kosaraju bugs). Correction: #18 (F64 129:42 NEG) is
  equivalent for program behaviour (F64.epsilon is read only by proofs; the translator inlines Number.EPSILON). Two
  validation findings on the unmutated semantics: exponentiation can differ from V8 in the last place (ECMA-262 allows an
  implementation approximation; F64Diff has no pow), and sorting with an inconsistent comparator (NaN entries) orders
  differently from V8 (implementation-defined). Total 10.8 of 20 core-h.

- 2026-10-26T01:34Z (M, StrictTS final; from the TypeScript maintainer session, checked by the evidence owner): RESULTS_M.md 48c7f89e... (271 lines, branch mutation-m,
  harness c5cfd03) and tables ref1_vs_ref2.txt 711d92c6..., survivors_vs_ref1.txt 483f6d13..., status_table.txt
  1bdcedb3... (copied to checks/Mstrictts-final-20261025; hashes checked). My reading: the second unmutated reference
  differs from the first in 54 of 527 rows (2 status, 52 count-only); the 10 survivors differ in 60-75 rows each (0-11
  status); the input-level reading in RESULTS_M.md names mutation-specific differences for #6, #12 and #32 (all in the
  exponentiation case, pow absent from F64Diff). Population 20/30 = 0.667 [0.488, 0.808], 2 stillborn (#8, #13), 30
  sorries in 7 built mutants; pre-registered extended outcome 10/10 "killed" with the caveat; post-hoc equivalence labels
  by argument: #1 (likely), #9, #18, #31 (fuel limit only). 10.8 of 20 core-h. The paper's numbers match.

- 2026-10-26T02:03Z (T4 rows on the real Thrift libraries; from the equiv-lean maintainer session, partly re-run by the evidence owner): at Thrift f0eb8b84e, all 24
  cells of rows W1, W2, R1, R2, R3, V1, V2 (and the new L1) behave as the models predict: no model gap.
  NATIVE_TABLE.md 077daaed.... New row L1 (readListBegin on 0D, an empty UUID list): C++ returns T_UUID size 0, Java
  throws TTransportException "unrecognized type code", Rust returns (Uuid, 0); the spec accepts. Evidence owner's re-run
  from copies (checks/t4native-20261026): the C++ drivers rebuilt with the same g++ flags from lib/cpp sources that equal
  f0eb8b84e's blobs (except the declared minimal config.h) give output identical to theirs (they append rc to the file);
  the Java drivers compiled against the released jar (d7b84d85...) give identical output, main and L1; the Rust debug
  build from a copy (offline, -j 1, toolchain 1.99.0, no auto-install) is running. Note from the equiv-lean maintainer session: a Rust version query
  inside the Thrift tree let rustup download the pinned toolchain (download only).

- 2026-10-26T02:04Z (T4 native re-run complete; evidence owner): the Rust debug build from my copy (offline, -j 1, toolchain 1.99.0, no
  auto-install; checks/t4native-20261026/rust) gives output identical to the equiv-lean maintainer session's apart from the panic line's thread id and
  my appended exit-code line, for rows W1-V2 and for L1. With the C++ and Java re-runs, every native cell of the T4
  discrepancy rows is reproduced from copies. The rows are confirmed as behaviour of the real libraries at f0eb8b84e
  (the user's rule): the paper may describe them as differences between Thrift's implementations; outward handling
  stays with the user (FREEZE_PLAN 24).

- 2026-10-26T02:08Z (Java total correctness: java-total green, frozen; from the equiv-lean maintainer session, check started): commit 9f0e5fb068b8eefe7f79c7134ac44946e0f459dc
  (751764f + JimpleLean re-pin to snapshot 20261025T2312Z + the termination proofs + README); clean build 1024/1024, 0
  failed, 7.19 core-h (run dir freeze_kit/runs/9f0e5fb-jtotal-20261026T001117Z); 46 named rows reported std; the 16
  headline statements unchanged and re-checked there. Eight run_total theorems (and run_term companions), statement form
  forall args s, runSpec.pre -> (exists o, MExec ...) /\ (forall o, MExec ... -> runSpec.post), each total_of_sat_mterm of
  the headline's run_sat and run_term (via sat_runSpec_of_J for CBACT02C, CBACT03C, CBCUS01C). Provenance per the Java maintainer session's
  manifests. Inside the 22:00Z deadline (the build was green before 03:00Z). The evidence owner's check runs from a
  hard-linked copy (eqjt); the equiv-lean maintainer session keeps the worktree unchanged until then.

- 2026-10-26T02:23Z (H part two, yajl phase 1 outcome; from -49, checked by the evidence owner): the autonomous run (19:07:30Z to
  01:42:50Z, rc 0) gives no harness theorem: LLVMFuzzerTestOneInput is stuck after 4 attempts (assuming yajl_alloc,
  yajl_do_parse, yajl_free). Of the 45 reachable units, 23 proved, 7 partial, 1 conditional, 14 stuck (my cross-check of
  phase1_summary.txt fcf86dbd... against verify.json d975a8bd...: 45/45 statuses agree; verify.json holds 61 units
  because --refine also ran the 16 unreachable ones). Model $61.12 over 204 calls (my sum of usage.jsonl 84bfea57...:
  188 end_turn, 11 max_tokens, 5 refusal), of which $10.38 on the unreachable units; 8.083 core-h; no watchdog pause.
  Where it stuck: the lexer's symbolic switch (recursion and time limits), yajl_do_parse under --attempt-gaps with a
  lexer contract too narrow for its caller, yajl_parse proved only for states 1-3 while the harness calls it from state
  0. Phase 1 is reported on its own as the autonomous outcome; the pre-registered outcome at 2^63 stays "not finished".
  Files copied to checks/hyajl-phase1-20261026 (SHA256SUMS).

- 2026-10-26T02:29Z (Java total correctness checked; evidence owner, via a fork): copy replay/eqjt-20261026T0209Z (hard links of
  ~/equivlean_freeze_9f0e5fb-jtotal plus full vendor copies); checks/eqjt-20261026T0209Z: 1,322 tracked files = 9f0e5fb;
  JimpleLean 2312Z vendor sources = the snapshot manifest (144/144); against 751764f 181 files added, the 30 changed
  JimpleLean proof copies differ only in their provenance comment (2312Z for 0149Z), otherwise only docs and the three
  version pointers; no headline statement or proof file changed. Termination files = the Java maintainer session's manifests (179 entries) under
  the declared rename; the other JimpleLean copies pass import_jl.py --check (36/36). Each run_total is
  total_of_sat_mterm of the same run_sat as the headline java theorem (via sat_runSpec_of_J for CBACT02C, CBACT03C,
  CBCUS01C). Axioms: 32 theorems (8 run_total, 8 run_term, 16 headline) [propext, Classical.choice, Quot.sound]. Kernel
  replay of the 655-module closure: 578 replayed rc 0, 77 reused on byte-identical files, 2 import-only; 0.75 core-h.
  Paper: a paragraph in sec-migration (a separate result on a later version of the Java semantics), sec-limits wording,
  appendix pin and replay rows. The worktree may be released.

- 2026-10-26T03:21Z (T2 complete; from veriforch, check started): 1,000/1,000 units at 03:18:58Z: proved_mechanical 3, proved_model_stated
  194, conditional 10, partial 22, refuted 1 (unit 254, the union false positive), blocked 468, timeout 302,
  infrastructure 0; all 197 proved units passed the driver's kernel replay; C 127, C++ 520, Java 230, Rust 123; model
  $234.85 (records and ledger) + $1.23 from killed attempts (usage logs); 16.23 core-h. Files: summary.json a7612ce8...,
  summary.md 501883b6..., outcomes.tsv 9995f45c..., results.jsonl 3cc25e54..., ledger.json 483ab6d7..., driver.log
  7f45a3e1..., T2_known_false_positives.md 266b8f0f..., T2_driver.md 41d7aa59.... The evidence owner's check (outcomes,
  the pre-registered stratified analysis, refuted re-run, axioms and replay of every claim, C/C++/Java scans) runs from
  copies (t2-<stamp>).

- 2026-10-26T04:09Z (T2 final checked; evidence owner, via a fork; one mapping ruling): checks/t2-20261026T0321Z (copies
  replay/t2-20261026T0321Z): all 8 file hashes match; 1,000 records = the frozen sample in order. My recount agrees with
  the driver on 991 units; 9 (35, 65, 489, 523, 599, 770, 867, 890, 997) were killed at the 10-minute wall with no status
  and the driver mapped them "blocked" from their static gap scope. Ruling: the pre-registered reading applies ("a wall
  kill is a timeout whatever status was recorded"), so the paper's counts are blocked 459 and timeout 311 (driver 468 /
  302); proved counts are the same. Proved share (mechanical + model-stated), stratified [95%]: all 18.7% [16.3, 21.1],
  C 16.0% [9.2, 22.8], C++ 13.9% [10.9, 16.8], Java 25.6% [20.0, 31.2], Rust 42.1% [32.8, 51.4] (= summary.json). Spend:
  usage logs $236.21 over 1,784 calls (ledger $234.98; records $234.8451); per-unit median $0.159, mean $0.235; overshoot
  450 units, max $1.2647, $90.18; compute 30.36 core-h by the guard (records 16.23). Wall kills by detail line 27, by the
  killed flag 36 (the 9 above). Unit 254 re-run on cirlean ffab71e: UB on every input tried; C11 6.5.2.3 footnote 95
  defines the access: a model limit. Claims: 229 (258 theorem modules compiled from hard-linked copies), axioms 258/258
  std, closure replay 879/879 rc 0. Scans: Java Double.compare 2 flags explained; cirpun 91/102 clean, the rest typed
  void* parameters, unresolved indirect or virtual calls, and libstdc++ atomic refcounts; one memcpy (claim 54, distinct
  objects required by its statement); hex FP only double infinities. Fork slip: one unguarded python3 -m py_compile.
  Paper: the T2 paragraph in sec-thrift.

- 2026-10-26T05:15Z (cJSON 32-bit refutation v3, embargoed; from a session, checked by the evidence owner): CJSON32Refute.lean
  c2bee213... (olean 61cb09b6...), 22 theorems, now also over a patched build (cJSON_6d9f244_patched_i686.cir 1089a91a...,
  Gen.CJSON32Patched): whole-function undefined behaviour of print_string_ptr, print_string, print_value,
  cJSON_PrintPreallocated and print_object (key path); the guard and wrap facts; and that the proposed FIX.diff makes
  every L in [715,827,883; 858,993,459] return 0 before ensure and leaves no 32-bit wrap below the bound. From a copy
  (checks/cj32refute-20261025/v3): Gen.CJSON32 oleans unchanged from v1 (its 171-module closure replayed then);
  leanchecker on the patched fn_print_string_ptr module and on CJSON32Refute rc 0; elaboration rc 0 (my first attempt
  ran under the 0.05 core-h one-liner guard, which killed it at the cap; the empty output is kept and was no verdict);
  23 axiom lines, all standard ([propext, Classical.choice, Quot.sound], one with [propext, Quot.sound]); no sorry.
  Disclosure materials in ~/fv_disclosure/cjson_20261025 (EMAIL.txt, FIX.diff, BOUNDS.md, CVE_REQUEST_DRAFT.md) are the
  user's; nothing sent by the evidence owner; embargo until a fix or 2027-01-23.

- 2026-10-26T05:25Z (D2 complete: zlib held-out finished; from veriforch, check started): 52/52 at 05:22:40Z, no stop (stopped_at
  null): proved_model_stated 9 (0.094-0.297), conditional 1, partial 1, refuted 0, blocked 14, timeout 26,
  infrastructure_error 1 (order 24 inflate_fast: status stuck, detail "LLM: model declined the request", a model
  refusal). Model $41.57; 6.42 core-h in records (7.779 core-h by the guard over the whole zlib driver run). D2 ledger
  $384.73 of $500, plus $1.0046 for the lang3 bridge-fix re-run. Files: summary.json 9891f37e..., outcomes.tsv
  7651f6f6..., results.jsonl ec3e9e35..., zlib.out 106c3a29..., zlib.guard.log e4ffb0f8..., ledger.json 227dbe9f....
  The evidence owner's check runs from a copy (vo2zh); the refusal's mapping is ruled after reading its record.

- 2026-10-26T05:40Z (D2 zlib held-out checked; ruling on the model refusal; evidence owner, via a fork): copy replay/vo-Dz2h-20261026T0526Z;
  checks/vo2zh-20261026T0526Z: 52 rows = the frozen heldout_zlib.tsv; hashes and the cirlean d9ae8e5 pin match; 51 rows
  agree with the driver. Order 24 (inflate_fast): 3 model proposals, each with stop reason refusal (01:56:30Z, 01:56:46Z,
  01:57:33Z), 0 proof checks, $0.4009, no negative-cache line. Ruling: the unit used its attempt budget without a proof,
  so under R6 it is a timeout (ran out of attempts), not an infrastructure error (no tool crash, nothing to fix or
  re-run); the paper notes that the model declined all three requests. Final R6 counts: proved 9 (0.094-0.297),
  conditional 1, partial 1, refuted 0, blocked 14, timeout 27, infrastructure 0; 6 wall kills counted as timeouts. Claims
  (9 proved, gz_error partial, _tr_flush_bits conditional; all model-stated; 7 reused cached proofs from the re-run):
  53 theorems std; 391 modules replayed rc 0; cirpun 11/11 clean apart from opaque-handle casts typed by the statements;
  no memcpy; no hex FP. D2 is complete; tab:sample has all rows.

- 2026-10-26T05:59Z (T4 final green, frozen; from the equiv-lean maintainer session, check started): commit ac65118b46a1fcc891709ab551c61aa85dff1734 (branch t4-final;
  751764f + t4-spec f93f948, t4-rust fed0c3b, t4-cpp 64c9183, t4-java 14956e7, t4-java-rt ce981c6, t4-java-coll bdc58ab,
  a README section and the bwi16* rename); clean build 1531/1531, 0 failed, 6.74 core-h; 54/54 named rows reported std
  (17 headline, 9 C-to-Rust, 28 T4); the all-modules sweep passes (sorryAx 0). Per-row table EquivLean/Demo/Thrift/ROWS.md
  (byte literals Spec.lean l.910-956, hypotheses per theorem, NoRedecl corollaries, jar d7b84d85...). Native status:
  all 24 cells confirmed (table 077daaed, reproduced by the evidence owner). The evidence owner's row-by-row check runs
  from a hard-linked copy (eqt4); the equiv-lean maintainer session keeps the worktree unchanged until then.

- 2026-10-26T06:22Z (veriforch prune of T2 and D2 build products, after the evidence owner's checks; from veriforch): prune_build_v4.py
  removed only .lake/build and cache/olean* in runs/t2_* and runs/prereg_d2_* directories untouched for over 60 minutes
  (sources, proof JSON, records, logs and transcripts kept; 292,367 files, 67.14 GiB; manifest
  notes/disk_prune/t2_d2_t3_del_20261026T062033Z/manifest.tsv 0d37909b...; runs/prereg_d2_zlib skipped by the recency
  guard). The evidence owner's replay copies keep their compiled files (copies or hard links; checked); their w1 'cache'
  entries are symlinks into veriforch's cache, which the checks did not use.

- 2026-10-26T06:27Z (T4 final checked; evidence owner, via a fork): copy replay/eqt4-20261026T0559Z (hard links of the clean build plus
  vendor copies); checks/eqt4-20261026T0559Z: 2,109 tracked files = ac65118; against 751764f 968 added files, all under
  Thrift paths, plus HANDOFF and README edits; no headline or C-to-Rust file changed. All 25 row theorems exist in the
  modules ROWS.md names; their statements (fresh process) use the Spec's named byte literals or the listed bytes and
  conclude what the native table shows. Hypotheses equal ROWS.md's except that the Java L1 (rlb_uuid) and negative-size
  (rlb_exNegSize) theorems also take NoRedeclL, which thrift_coll_hyps proves (with NoRedeclS) for Thrift's program; ROWS.md
  under-describes that corollary (documentation only; the commit stays frozen). NoRedecl corollaries by decide +kernel
  and rfl, class count 277 (no axioms); 277 Jimple files present. Axioms 890/890 std (836 public Thrift theorems + 54
  named rows), no sorryAx. Kernel replay of the 990-module closure: 721 replayed rc 0, 269 reused (byte-identical to the
  1449Z replay). 1.12 core-h. Paper: the T4 paragraph in sec-thrift (pair counts per language from the README table;
  eight differences, natively confirmed), appendix pin and replay rows.

- 2026-10-26T06:28Z (T4 ROWS.md correction, documentation only; from the equiv-lean maintainer session): their statement scan matched NoRedecl names with word
  boundaries and missed NoRedeclL and NoRedeclS. Corrected: rlb_D, rlb_uuid, rlb_exNegSize take tContracts, Contains,
  NoRedeclL, CPAt; rsb_D, rsb_exNegSize take tContracts, Contains, NoRedeclS, CPAt; wcb_E takes tContracts, Contains,
  NoRedeclW, CPAt; thrift_coll_hyps proves Contains + NoRedeclL + NoRedeclS + NoRedeclW (consistent with my check).
  Fixed on master after the freeze; ac65118 unchanged. The equiv-lean maintainer session removed its freeze worktree; my copy holds the links.

- 2026-10-26T07:20Z (second veriforch prune, checked by the evidence owner): 221,064 regenerable files (12.42 GiB) from
  runs/prereg_d2_zlib and finished unknown-only T3 commit directories. Keep-list t3_keep_orders_v2.txt 53e49346... equals my
  recomputation from the 127 finished commits' ci.json verdicts plus order 2 (2, 11, 24, 29, 30, 32, 41, 50, 57, 58, 71, 77,
  79, 89, 111, 115, 116, 118, 119); the 92 T3 prune roots (t3_prune_roots_v2.txt 6278f906..., 104 dirs in all) do not overlap
  it; every manifest row (7c47f67a...) is under .lake/build or cache/olean.

- 2026-10-26T08:42Z (yajl: the numRd overflow is reachable on 64-bit; from veriforch): yajl_parse and yajl_lex_number take an unsigned int
  length, and the lexer scans the fraction digits in place, so for size = 2^31 + 2 ("0." and 2^31 digits) numRd reaches
  INT_MAX after 2^31 - 1 digits and the next numRd++ (yajl_lex.c:398) overflows a signed int on LP64. R3's bound size <
  2^31 is therefore exactly the threshold. A local 64-bit UBSan reproduction and a disclosure note with a one-line fix go
  to ~/fv_disclosure/yajl_20261026, embargoed: outward handling is the user's (raised by the evidence owner).

- 2026-10-26T08:50Z (prior art: CVE-2026-16554, verified from CERT Polska's advisory): the 32-bit wrap in cJSON's print_string_ptr is public
  (published 2026-07-27, cJSON 1.7.19, escape_characters wraps for ~858,993,460+ control characters; vendor unreachable; AFINE
  Team). Ours is only the exact threshold 715,827,883 and the window below the advisory's threshold, where output_length or
  needed wraps without escape_characters wrapping, machine-checked, plus the fix covering it. Recorded in
  prior_art/LEDGER_addendum_20261026_cve.md (binding). The user's embargo premise changed; the question goes to the user.

- 2026-10-26T08:51Z (R5 jsmn: C-side scans; evidence owner): equiv-lean branch r5-c 675dedc, examples/cir/jsmn/jsmn_run.cir (98defaed...;
  jsmn.h c04533e9... = jsmn @ 25647e6) from a JSMN_STATIC harness (jsmn_init, one jsmn_parse): cirpun from jsmn_run, 7
  functions, FLAG 0, CHAR 0, SIGN 0, AGG 0, NOOBJ 0, ASSUME 0; no memcpy; no hexadecimal FP constant
  (checks/r5jsmn-scan-20261026).

- 2026-10-26T08:51Z (yajl 64-bit reproduction, embargoed; from veriforch, files checked): ~/fv_disclosure/yajl_20261026 (SHA256SUMS ff177a8e...):
  UBSan (-fsanitize=signed-integer-overflow) on LLVMFuzzerTestOneInput with size 2^31 + 2 reports "signed integer overflow:
  2147483647 + 1 cannot be represented in type int" at yajl_lex.c:398:18; with FIX.diff (numRd unsigned) the run returns 0.
  Outward handling is the user's.

- 2026-10-26T09:08Z (R2-32 pin; ruling by the evidence owner): a minimal cirlean branch from c4ef58d may change only the data-layout
  parameters for the 32-bit target (pointer size and alignment in Ctx.sizeAlign and what follows from them), tested
  against native i686 runs, commit and diff recorded; it is a labelled pin for that one embargoed result only and changes
  no pin of the paper's other results.

- 2026-10-26T09:16Z (R6 inputs frozen; evidence owner): ADDENDUM_R6_inputs.md 8733b38d... with copies in R6/ (testable 415 pairs
  408069f7..., provable 79 pairs f2f81a47..., pairs_SHA256SUMS bf561176... checked 3,642/3,642); tool commit 10ec829 (master
  f6a4ec0 plus difftool changes only). Not pre-registered; first look on 31 pairs disclosed there.

- 2026-10-26T09:19Z (coblean: survivor-feature tests and a DISPLAY validation gap on theorem paths; from the COBOL maintainer session, partly checked): cov-tests on a
  scratch copy of 2114Z (COV_REPORT.md 5c817809...): GnuCOBOL-differential testers for the M survivors' features all ok at two seeds;
  each survivor planted back is now caught; two new GnuCOBOL deviations excluded by name. Gap: 7 DISPLAY operands of the
  theorem programs (CBACT01C 5, CBTRN03C 2) are signed zoned items; the model prints stored bytes with an overpunched sign
  (IBM default DISPSIGN(COMPAT), confirmed from IBM's Enterprise COBOL 6.4 documentation), GnuCOBOL a separate sign, so no
  differential test checks them (display_paths_v1.txt e2a49b72..., read: 7 uncompared operands). Paper: one sentence in
  sec-limits. Slip reported by coblean: one rm -f of two own test data files without a delete record.

- 2026-10-26T20:01Z (cJSON private report sent; relayed by a session, user confirmation 2026-10-26T19:59Z): the private
  report in ~/fv_disclosure/cjson_20261025/ went to the cJSON maintainers on 2026-10-26. Embargo unchanged in kind: nothing public
  about the 32-bit print-length obligations, the lower window or FIX.diff until an upstream fix or the embargo date. Date: the user's
  10-25 ruling says 2027-01-23; 90 days from the 10-26 send is 2027-01-24; the earlier date binds unless the user says otherwise.
  The prior-art split (CVE-2026-16554 for the cJSON.c:1000 obligation at the advisory's threshold; ours = the obligations at lines
  1005/1007 below it, and the patched bound) is as recorded 08:50Z (prior_art/LEDGER_addendum_20261026_cve.md). The R2-32 result
  (~/fvreview_20261023/r2_32) stays an embargoed record, checked by the evidence owner before any use.

- 2026-10-26T20:05Z (T3 driver fix cf3, labelled; requested by veriforch 20:1xZ after an inspection at the user's request; approved by the
  coordination session and by the evidence owner with conditions): units 072 (C++), 090 and 103 (Rust) only. (a) ci.py checks each
  (unit, old_body_hash, new_body_hash) once per commit and checkpoints per-unit verdicts, matching T3_DRIVER.md l.132 (one home TU and
  one verdict per changed function); 072 touched a header seen by 12 TUs (392 (TU, function) pairs for 227 functions) and later TUs
  could overwrite lean_cert/VOEquiv.<eid>.lean. (b) 072's remaining distinct functions run at VO_CI_EQUIV_JOBS=6 under its guard.
  (c) the scheduler reserves $0.00 for Rust units under --attempts 0 (no LLM calls on the 17 finished Rust commits); the $300 cap
  stays on metered spend. Conditions (evidence owner): verdicts only from the home TU that prereg_t3.py reads, never from a
  non-home TU; 072 pre-seeded only with home-TU verdicts, each of the 16 equivalent certs sha-matched to its home-TU check or
  regenerated, list of the 142 (function, home TU, TU checked, verdict, cert sha) before the resume; per-check budgets, timeouts
  and LLM settings unchanged; Rust $0 reservation only with a fail-closed guard (an LLM call under --attempts 0 aborts the run as
  infrastructure); 072's old log, records and lean_cert state moved aside, not deleted; cf3 diff sha256, driver commit and the
  affected units sent to the evidence owner; cf3 records marked in the census; units unfinished at 03:00Z follow the stop rule.

- 2026-10-26T20:10Z (rally deliveries 09:20Z-19:51Z; evidence owner, recovered after the d0 restart; checks running): R1, R2-64, R2-32, R3,
  R5 (r5-final 373874f), R6 (53f98fcd), R7 (t4-java-total 613c77c) and coblean's live snapshot coblean-20261026T1055Z
  (later changes M-pos and C5) are recorded with paths and hashes in notes/DELIVERIES_20261026.md; each enters the paper only
  after its check. cirlean cut branch ilp32 e00113f (parent c4ef58d; 5 files, +35/-7; ptrBytes from the data layout),
  per the 09:08Z ruling: a pin for R2-32 only. Producer process notes as disclosed: JimpleLean's helper wrote 4
  scratch files into the t4-java-coll worktree at 09:26Z and moved them out within a minute (status clean); equiv-lean's
  rusttrn made one edit by python heredoc, one sed -i on its own scratch file and one shell append to its job notes, and
  cir-repin ran one stray no-op python call (none touched 373874f); coblean's pos-fix ran a stray no-op python3 -c 1
  outside its guard at ~09:10Z and left an empty /tmp/null_unused_diff at 10:55Z. R4 fallback (i) (COBOL-only CBSTM03A+B
  theorem) no-go at ~10%; fallback (ii) (survivor-feature tests, 09:19Z entry) is coblean's contribution.

- 2026-10-26T21:22Z (NIST triage classes settled; evidence owner, from coblean's reading of IBM Enterprise COBOL 6.4, checked by my fork): C1 (NOT ON SIZE
  ERROR without ON SIZE ERROR; 6 fails in run (b), 7 in N2) -> class (iii): GnuCOBOL/CCVS85 depart from IBM's documented truncation rule,
  which coblean models. C2 (INSPECT of a signed numeric DISPLAY item, NC216A) -> class (ii): a coblean semantics defect, off every
  theorem path (no theorem IR or source uses INSPECT), unfixed at the paper's versions; coblean's fix waits until after the freeze.
  The 1055Z snapshot is the paper's "later version" (checks/cob1055-20261026T2004Z).

- 2026-10-26T21:57Z (pre-registered cost and gap analyses; evidence owner): cost per unit (model $ and core-seconds: median, IQR, mean,
  total) and gap names with frequencies for D, D2 (re-run and held-out) and T2, and gap names for the CardDemo census, computed
  from my copies of the unit records (checks/dcost-20261026T2151Z) and reported in the paper's appendix (tab:costgaps). Not reported
  in this draft: the per-library front-end and extraction cost (PREREG_D_v2 l.54); per-unit core-seconds miss compute outside
  the units (T2: 14.4 of 30.4 metered core-hours), stated in the caption.

- 2026-10-26T22:13Z (T3 census and scan rulings; evidence owner, after my check checks/t3-20261026T2147Z): (1) Per-language rows count each
  language's own functions (PREREG_C_v2 rules applied to that language's verdicts); the total counts each commit once by its overall
  outcome. veriforch's summary put a multi-language commit's overall outcome under every language it touches; the only change is the
  C row (order 101's C side is unknown): C 3 / 0 / 23 instead of 3 / 1 / 22. (2) The type-width scan of the 54 equivalence verdicts
  flags one access of another width: libstdc++'s shared_ptr _M_release loads its two 32-bit counters as one 64-bit value
  (shared_ptr_base.h:336), reached by the verdicts for TEvhttpServer::complete (11 commits) and ~TFileTransport (order 142):
  12 of 54. Under decision B (16:35Z 10-25) these are reported as holding only under the semantics' one-element reading of that
  access; 8 of the 9 partly certified commits (32, 57, 79, 89, 101, 105, 116, 138) have no other verdict. DEVIATION from B: the
  flagged functions were not run on cirrun 2d65713 before the freeze (no harness for them tonight); next revision. (3) Witness
  facts (prereg T3 analysis): all 38 reproduce; per-witness input facts in the check's witness/ dir; the paper says which rest
  on unmodelled calls, uninitialized class state, layout changes, a null vptr or receivers no constructor produces.

- 2026-10-26T22:45Z (paper text of the whole-harness theorem; evidence owner, after the claims audit): the full-harness ruling (b) asked the text to
  give the reason for the statement's size bound. Under the user's embargo (10-25 ruling; report sent 10-26), the paper states the bound
  only and gives no reason until the embargo ends; this supersedes (b) for that sentence. Comparisons with Theorem's proofs state
  their memory budgets next to our bound (claims audit #6).

- 2026-10-27T00:18Z (M JimpleLean set 2, a labelled second measurement; evidence owner, on JimpleLean's proposal after the user lifted the
  freeze): same design as M coblean set 2. JimpleLean extends the Java difftest suite where set-1 survivors sat (the bit-exact
  float tester and tests aimed at Semantics:108 FUN, :320 LOG, :403 LIT, :520 LIT), freezes it and sends its sha256. The evidence
  owner then releases the secret S2J (sha256 of the string without newline, committed now: 1ea2fe5fa2e9860972e2828972cf06955c5f4bfac4865c27c529b5ced8206b0d) in an addendum,
  draws the order with M/draw_m.py --seed S2J --exclude set 1's attempted ids, and freezes it. JimpleLean runs the first 30
  tested candidates on the old suite and on the extended suite (headline: old vs extended on these mutants), on the set-1 pin.
  Labelled: after PREREG_M's stop (Tue 03:00Z), not pre-registered; set 1's 16 of 30 stays reported as is.

- 2026-10-27T00:20Z (M JimpleLean set 2: paused by JimpleLean pending the user's word, before any suite extension, manifest, draw or run): the seed
  S2J committed above stays unreleased; no set-2 number enters the paper unless the design above is followed from the start.

- 2026-10-27T00:31Z (rally R6 erratum from StrictTS, checked by the evidence owner): the tool draws inputs from implementation signatures,
  which for overloaded functions admit more than the public overloads; 10 of the 86 counterexamples are calls outside the public
  types (checks/r6erratum-20261027T0027Z). The paper reports 76 of 86 as type-valid and four (not six) perf/style commits with
  behaviour changes on type-valid calls. No count of PROVED, REFUTED or UNKNOWN changes.

- 2026-10-27T01:14Z (labelled new result, scope frozen before any proof; equiv-lean's proposal, accepted by the evidence owner): "zlib adler32, C -> safe
  Rust". C: zlib 1.3.1 tag 51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf, adler32.c unmodified (sha256 9cd1443a...), default
  configuration, x86_64 LP64. Functions: adler32_z (every adler, every buffer with len < 2^28, and buf == Z_NULL), adler32,
  adler32_combine64 / adler32_combine (all inputs). Statement per function: EquivOn Bad (Same ret) rustRun cRun, Bad = len >= 2^28 or
  C UB in cirlean; C and Rust totality reported only if proved. Rust written by equiv-lean's agents (labelled). Evidence as for R5
  plus a re-runnable native gcc-vs-rustc differential. Not pre-registered.

- 2026-10-27T01:30Z (M JimpleLean set 2 resumed through a separate agent of the evidence owner, at the user's request relayed by JimpleLean):
  steps (a)-(c) done in replay/jset2-20261027T0100Z (manifest 5e21e3e8..., baseline 0155c455..., verified); seed S2J released and the
  order drawn: prereg/M/ADDENDUM_M_jimplelean_set2.md (69c00a3d...), M/jimplelean_set2/order2.tsv 70390558... (419 candidates;
  independent recomputation equal). An unused first exclude file without a header (set1_attempted_ids.tsv) stays in that dir,
  outside its SHA256SUMS; the tool read set1_attempted.tsv. Runs (step e) follow by the same agent.

- 2026-10-27T02:20Z (M JimpleLean set 2 result, labelled): order2 positions 1-30, all built; old suite 20/30, extended suite 24/30 (4 extra kills
  by the float testers), 6 not detected; controls as set 1 (no-op not detected; known-bad detected). One suite program outside
  the design (ConcatConst, the concatenation constant path next to :403) was frozen with the suite and is disclosed in its README.
- 2026-10-27T02:26Z (M JimpleLean set 2, run order): the two controls (no-op edit, known-bad Native.lean edit) ran after the 30 altered versions,
  at the evidence owner's request; PREREG_M runs controls before the first altered version, and the set-2 addendum does not say.
  The no-op edit was not detected and the known-bad edit was detected (22 old programs, as in set 1, plus 6 new), so the order
  does not change any count.
- 2026-10-27T02:34Z (T2, labelled re-check outside PREREG_T_v1): units 132, 254, 566 re-run by veriforch at cirlean next e6ac99a, which reads
  same-size union members bit for bit except NaN patterns; proved for all non-NaN inputs (checked: checks/t2union-20261027T0208Z).
  The pre-registered census stays as recorded; the re-check spent $3.26 over 12 calls, above the per-unit budget, and is
  reported as a separate, labelled result.
- 2026-10-27T02:34Z (R6r, remeda refactoring study by StrictTS, labelled, not pre-registered): inputs and tool fixed before the run and
  recorded in prereg/ADDENDUM_R6r_remeda_inputs.md (sha256 e19195aa4e36028de301c42691fb3602c73d6e3d4cb94097f556ed7d2f22d423); list hashes recomputed and equal.
- 2026-10-27T02:35Z (R6r): StrictTS reports the run started on master bbe90b4, whose tool code it says equals 2ea47b8 (the commit in the addendum),
  dist hash dbe5a9c2... as for R6b; clone ~/strictts/scratch/projects_hist/remeda at d02c3bdb. To be verified at the check (diff of
  the tool sources between 2ea47b8 and bbe90b4; dist hash).
- 2026-10-27T02:39Z (R6b, labelled re-run of the frozen R6 inputs with StrictTS 43132a8, not pre-registered): checked (checks/r6b-20261027T0150Z);
  R6 stays the reported study; R6b is reported beside it with its qualifications (all 9 changes outside the frozen 79-pair list;
  endsWith/startsWith only on the old parameter types; three confirmation files outside the delivery manifest).
- 2026-10-27T03:06Z (T3 decision B, labelled): the run of the 12 flagged verdicts on a later C semantics, recorded earlier as not done, was made
  by veriforch at cirlean e6ac99a (not 2d65713) after the census; checked (checks/t3sp-20261027T0244Z): same verdicts, same
  statements, condition unchanged (record members keep the one-element reading). The census stays as recorded.
- 2026-10-27T04:05Z (R6r remeda, labelled, not pre-registered): checked (checks/r6r-20261027T0333Z); in the paper beside R6/R6b with its limits (81 of 160 provable pairs without target; 35 one-instance proofs; 7 test helpers). The same no-target kind affects 1 of es-toolkit's 79 provable pairs (UNKNOWN), now stated.
- 2026-10-27T04:10Z (R6c, R6rb, labelled re-runs with StrictTS const-arrow 9e54bdb): inputs recorded before the runs in prereg/ADDENDUM_R6c_R6rb_inputs.md (sha256 6ecf67c4097cc911a965a096752f202f02608ec5b70439a2fe89aa0043eac626); first looks on 8 R6 pairs disclosed there.
- 2026-10-27T06:38Z (R6c, R6rb): checked (checks/r6c-20261027T0601Z); reported in the paper as labelled re-runs with the third tool version; the six es-toolkit additions are not blind (first looks).
- 2026-10-27T06:56Z (outside the pre-registrations, labelled): the coblean 0518Z NIST DECLARATIVES run (outside PREREG_N/N2; the 43 programs are coblean's list) and the T4 Java nibbles 14/15 package (a9c8e23) are reported as labelled later results; both checked (checks/cob0518-20261027T0520Z, checks/t4nib-20261027T0520Z).
- 2026-10-27T07:02Z (R6d, labelled re-run with StrictTS master 25790c3, incl. the weaker statement kind old-no-panic): inputs recorded before the run in prereg/ADDENDUM_R6d_inputs.md (sha256 7c9230e1fbe8d3a6ec947bdc7f8ddad3967c365ef04942698ff8f18f103bbe32); first looks disclosed there.
- 2026-10-27T09:04Z (R6d, labelled): checked (checks/r6d-20261027T0825Z); old-no-panic pairs reported apart, never as equivalences; changed verdicts are first looks (not blind).
- 2026-10-27T10:26Z (R6e, labelled re-run with StrictTS master 4016a4a): inputs recorded before the run in prereg/ADDENDUM_R6e_inputs.md (sha256 5e82684023527e7ad1141361eba0966f6d6f0b0dccc1b770a23c78bb30776976); extensive first looks disclosed; last re-run of the series for this revision.
- 2026-10-27T12:13Z (R6e, labelled): checked (checks/r6e-20261027T1138Z); changed verdicts are first looks (not blind); last re-run of the series for this revision.
- 2026-10-27T14:33Z (R4 CBSTM03B translations, labelled): checked; not pooled into the 92-run statistics; evidence-owner check slip: 3-4 parallel Lean jobs for 1,179 s against the 2-job rule (guarded, no cap reached).
- 2026-10-27T16:11Z (V, labelled re-run at cirlean e6ac99a): inputs recorded before the run in prereg/V/ADDENDUM_V_rerun_e6ac99a.md (sha256 72c9ff4e0d657ce5a863f2ceb5776d0c4e7c1dee478bfdacd0becc634c4f02c9).
- 2026-10-27T16:39:14Z (R6f, labelled re-run with StrictTS master 4bef3c4): inputs recorded before the run in prereg/ADDENDUM_R6f_inputs.md (sha256 4e3af7f3c3555f72c8f25f214d4590e279a6d22facd5882f340cc6508466b3cd); first looks disclosed there (155 pairs). Change of plan: R6e's addendum called R6e the last re-run of the series for this revision; R6f was registered after the user's 00:13Z instruction to include all improvements, within the producer's strong-model window; no R6-R6e result changes.
- 2026-10-27T16:40Z (V, labelled re-run at cirlean e6ac99a): checked (checks/Vnext-20261027); one verdict changes (inf-1 MISMATCH -> MATCH); reported beside V, the pre-registered V numbers unchanged.
- 2026-10-27T17:13:59Z (M2, labelled cirlean mutation re-runs: M2a same 30 mutants, area-informed; M2b next 30 from order 35): inputs recorded before the run in prereg/M/ADDENDUM_M2_cirlean.md (sha256 bf94540c35b4174f88cdce4598412c8833021cc0b415a679e62c1efa9124baaf); ub_* lines excluded by the evidence owner at registration; blinding record and baseline classes verified.
- 2026-10-27T17:28:15Z (IBM-variant tester run, labelled, coblean 2306Z): plan recorded before the run in prereg/ADDENDUM_IBMVAR_coblean.md (sha256 3853d1b41bf7cc50abf2d8cb96677c2f9c90df6295e58906b5b1573f84a50d3f).
- 2026-10-27T17:35:40Z (M2 blinding record): re-sealed by the C maintainer session as SHA256SUMS 8649f149 (10 files; earlier 0ca32c19, d67f219b kept): rog statement v2 and access-record addendum. One recursive grep for four cJSON print names, run from ~/cirlean_work on 2026-10-25T20:32:52Z (before the blind rule), covered mutation/ and printed 14 paths, none under mutation/. The frozen M2 addendum (bf94540c) names 0ca32c19; this entry supersedes that hash for the delivery check.
- 2026-10-27T17:36Z (re-pin at cirlean e6ac99a, labelled): checked (checks/repin-20261027T1552Z); statements of the C ports and the Thrift rows byte-identical, auxiliary and musl statements restated as declared; checker slip: six steps under 20 s each ran without the core-hour guard.
- 2026-10-27T17:55:58Z (labelled results without an earlier entry; added after a claims audit): the CBSTM03B theorem (checked 2026-10-27, checks/cbstm03b-20261027T0113Z; snapshot coblean-pin2306Z-cbstm03b-20261027T0112Z), the CBSTM03A+B theorems (checked 2026-10-27, checks/stm03ab-20261027T1252Z; snapshot coblean-pin2306Z-cbstm03ab-20261027T1251Z) and the es-toolkit difference/intersection relational proofs (checked 2026-10-27, checks/esdiff-20261027T1415Z; equiv-lean 92f75e6) are labelled results outside every pre-registration. No inputs were recorded before them; each was reported in the paper only after its check. The dates are those of the checks, not of these entries.
- 2026-10-27T18:02:00Z (IBM-variant tester run, labelled): pre-run list ~/coblean_runs/ibmvar/prerun/PRERUN_LIST_v1.txt (sha256 baff99bbbf00a7a85185881fbf0808cf2e36c65ce3b2e4d598f94e209e82832f) received before any tester run. Declared changes against prereg/ADDENDUM_IBMVAR_coblean.md (3853d1b4), made before running: class hv (HIGH-VALUE byte 0xFF = X DF under CP037) with a second verdict; filetest seeds 101 and 102 (the tab:fidelity seeds); labelled extras E1 (CBSTM03A+B on the sample data with the IBM-profile IR) and E2 (4 hand cases); controls CTL-B (C/D zones swapped) and CTL-C (corrupted table) besides CTL-A. Probe: GnuCOBOL prints a separate sign under every flag set, so the 7 DISPSIGN(COMPAT) operands stay untested as DISPLAY output (stored bytes compared only). Translation table cp037_v1.ttbl a99f6bfb; runner ibmvar_run_v1.py 8625598f; testers = 2306Z files unchanged; 840 programs (7 configs x 2 seeds x 60).
- 2026-10-27T18:08Z (coblean 1730Z, labelled): checked (checks/cob1730-20261027T1734Z); INITIALIZE defects fixed in that version, SELECT OPTIONAL and index items modelled; the CardDemo representations unchanged; the theorems pin 2306Z.
- 2026-10-27T18:23Z (IBM-variant tester run, labelled): checked (checks/ibmvar-20261027T181928Z); 964 programs, 0 mismatch; controls exact; reported in sec-limits with its untested items.
- 2026-10-27T19:04Z (M2, labelled): checked (checks/m2-20261027T185803Z); reported beside M (M unchanged); order 37 counted as a kill under the verbatim criterion, the count without it given.
- 2026-10-27T19:05:58Z (M2 blinding, note): at 19:05Z, after M2 was sealed, the cirlean lead told the test author (rog) the kill counts; rog is no longer blind to M results, so a future registered mutation run needs tests from a fresh helper. M2 unaffected.
- 2026-10-27T19:31Z (R6f es-toolkit, labelled L5): checked (checks/r6f-20261027T1859Z); all 28 added proofs are first looks (not blind); checker slip: rm -f of two own temporary files in the check dir.
- 2026-10-27T19:42:51Z (V, labelled re-run at cirlean next2 424e821; next revision): inputs recorded before the run in prereg/V/ADDENDUM_V_rerun_next2.md (sha256 ed2f75df81b35a4667ee85730e560d730a55eaa58b72750d0ad9d5c1390ca73a).
- 2026-10-27T20:13Z (V, labelled re-run at cirlean next2): checked (checks/Vnext2-20261027T201054Z); reported beside V; three new UB verdicts flagged as untriaged.
- 2026-10-27T20:20Z (CSUTLDTC, labelled): checked (checks/csutl-20261027T201400Z); pinned on the later COBOL semantics (2008Z), not the theorem pin of the migration study.
- 2026-10-27T20:22:19Z (IBM-variant tester repeat on coblean 2008Z, labelled; next revision): pre-run list ~/coblean_runs/ibmvar/live/prerun/PRERUN_LIST_live_v1.txt (sha256 1e3625d2c491b9848bb9be6795fad22ea9c3522f4d0dbb6b33290a10947c432c) received before any tester run; 66 seeded runs (3960 programs), table a99f6bfb, flag classes and controls CTL-A-live, CTL-W-live as listed.
- 2026-10-27T20:44Z (coblean 2008Z, labelled): checked (checks/cob2008-20261027T2011Z); collating sequences and ODO modelled in that version; the linker defect has no exposure in our corpus.
- 2026-10-27T21:03Z (R6f remeda, labelled L5): checked (checks/r6fre-20261027T2032Z); all 56 added proofs are first looks (not blind). Correction to ADDENDUM_R6f_inputs.md: report.js does read a provable list (provable column and reason text only); the copies used equal R6e lists.
- 2026-10-27T21:17:50Z (A3 mutation test, labelled addition): equiv-lean's Lean refutations of the three timeout mutants' statements (47d9ce3/b46c478) checked (checks/mutref-20261027T205650Z) and reported beside A3; the A3 counts (97 with an error, 3 timeouts) are unchanged; the refutations were written after the A3 runs and are not part of the A3 protocol.
- 2026-10-27T22:13:23Z (A/C/T4 re-check, labelled): all headline theorems build together at equiv-lean unified 04d2599 (checks/unified-20261027T2059Z, SHA256SUMS 394f9bbb): 146 rows std, 2,063 modules replayed or reused rc 0 incl. the 17 AeneasMeta modules; reported as a later build, not as the versions of the claims.
- 2026-10-28T00:08:57Z (IBM-variant repeat on 2008Z, labelled): checked (checks/ibmvar2-20261027T2355Z, SHA256SUMS 301ddcea); reported in sec-limits beside the first IBM-variant run; the front-end sign control did not run its table (stated).
- 2026-10-28T00:28:26Z (coblean 2231Z, labelled): checked (checks/merge4-20261027T2355Z); reported in sec-limits. (TS relational proofs ts-esnext/ts-repin, labelled): checked (checks/tsnext-20261027T2356Z); reported in sec-fixes; pairs outside the study counts.
- 2026-10-28T00:44:36Z (R2-64, R2-32 and the changed yajl_lex_number, labelled; text by the session the user assigned to this topic, not the evidence-owner session): the user lifted the paper embargo on these three results (via the coordinating session, 2026-10-27T18:10Z) and assigned their paper text to this session (2026-10-27, ~23:4xZ), in proof-status terms only. Checked: checks/fh-r264-20261026T2003Z, checks/r232-20261026T2007Z and checks/yjpatch2-20261027T2352Z (fresh check; the partial check yjpatch-20261027T1820Z, stopped at 18:22Z, is superseded); parent of the 32-bit pin e00113f: checks/ilp32parent-20261028T0035Z. In the paper from the next freeze on: one paragraph in sec-ub (statements, bounds, axioms, replays), a versions sentence and three replay rows in the appendix; with them, two existing replay rows corrected to name their import-only root (parse-only 246 + 1, whole harness at c4ef58d 284 + 1). Claims audit ub1 and de-AI rounds ubr1a/ubr1b: records in ~/fv_ub_20261027.
- 2026-10-28T01:43:12Z (coblean 0109Z, labelled): checked (checks/merge5-20261028T0112Z); reported in sec-limits and sec-migration.
- 2026-10-28T01:47:07Z (CBSTM03A to Rust, labelled): equiv-lean a50f10e checked (checks/r4a-20261028T0107Z); reported in sec-migration; the runs are outside the translation statistics.
- 2026-10-28T04:12:51Z (coblean 0336Z, labelled): checked (checks/merge6-20261028T0339Z); a row in tab:snapshots.
- 2026-10-28T04:35:20Z (CBSTM03A to Java, labelled): equiv-lean 8ed869e checked (checks/r4ajava-20261028T0213Z); reported in sec-migration; the runs are outside the translation statistics.
- 2026-10-28T05:38:19Z (R2-64/R2-32 prior-art citation; by the session assigned to sec-ub): added citation cve202616554 (CERT Polska advisory CVE-2026-16554, 2026-07-27, print_string_ptr 32-bit size_t wraparound; prior_art/LEDGER_addendum_20261026_cve.md) to sec-ub.tex and refs.bib.
- 2026-10-28T06:10:03Z (COBSWAIT all-input theorem, labelled): pin coblean-pinM7-cobswait-20261028T0554Z checked (checks/cobswait-20261028T060011Z); reported in sec-migration; with it 12 of the 14 CardDemo batch programs have a COBOL-side theorem.
- 2026-10-28T06:25:05Z (coblean 0551Z, labelled): checked (checks/merge7-20261028T0554Z); a row in tab:snapshots (app:later).
- 2026-10-28T06:28:54Z (T2/T3 at cirlean next2 424e821, labelled): checked (checks/t23next2-20261028T061053Z); reported in sec-thrift with both conditions; appendix rows.
- 2026-10-28T06:50:15Z (NIST census N3 of coblean 0551Z, labelled): plan recorded before the run in prereg/ADDENDUM_NIST3_coblean.md (sha256 0a5fcca5...); go sent to the COBOL maintainer session after this entry.
- 2026-10-28T07:01:04Z (NIST census N3, labelled): pre-run summary received before any module run (~/coblean_runs/nist3/prerun_summary.txt, sha256 df1facb4...; tree manifest bf1403be...). One difference from ADDENDUM_NIST3_coblean.md's wording, recorded before the runs: COB_SWITCH_1=ON COB_SWITCH_2=OFF is set in every module run's environment (as gc_ref.py sets it for every GnuCOBOL reference), not only for NC211A; per the COBOL maintainer session it reaches the front end and only NC108M, NC174A, NC211A and NC254A name SWITCH-1/2. The census reports this with the declared differences.
- 2026-10-28T07:28:35Z (NIST census N3, labelled): delivered sealed (~/coblean_runs/nist3/sealed_20261028T072609Z, SHA256SUMS 729f32ff...). Timing deviation disclosed by the COBOL maintainer session: the NC module job ran 07:00:22-07:00:42Z, about 20 s before the pre-run summary reached the evidence owner; the plan itself (ADDENDUM_NIST3_coblean.md) was fixed and logged at 06:50:15Z, before any run, and the job's command equals the summary's. Switch effect: without COB_SWITCH, NC174A, NC211A and NC254A fail (labelled control outside the census). Independent check by an agent launched.
- 2026-10-28T07:40:01Z CORRECTION to the entry of 2026-10-28T07:01:04Z (NIST census N3): that entry says the pre-run summary was 'received before any module run' and the switch scope 'recorded before the runs'. Both are inaccurate: prerun_summary.txt was written at 06:59:57Z, the NC module job ran 07:00:22-07:00:42Z and the SQ job started at 07:01:03Z, before that entry (checks/nist3-20261028T072837Z, item 7). The plan itself (ADDENDUM_NIST3_coblean.md) was logged at 06:50:15Z, before any run; every outcome reproduces in the independent re-run.
- 2026-10-28T07:41:02Z (NIST census N3, labelled): checked (checks/nist3-20261028T072837Z); reported in sec-stack and Appendix app:later; the per-snapshot NIST column of tab:snapshots is replaced by the census.
- 2026-10-28T07:45:58Z (three later COBOL defects, session's reports with our JUSTIFIED IR scan): added to app:later; Limitations counts updated (seven after our checks; four rest on the session's report; all but four fixed or stopped).
- 2026-10-28T08:43:22Z (whole cJSON harness R1 at cirlean next2 424e821, labelled; checked by the sec-ub session): veriforch's package ~/veriforch/runs/postfreeze/r1_cjson_next2_424e821 (SHA256SUMS 4747bb88, 493/493) on frozen pin next2_424e821_20261027 checked in checks/r1next2-20261028T0803Z (an agent, SUMMARY.md 54552ac4, SHA256SUMS 8e4b728d 336/336): entry statement byte-identical to e6ac99a's; 32 unit theorems + FHEntry.entry_main std; 288/288 modules of RESOLUTION.tsv (45 CIR.* + 243 lib/) replay rc 0 and leanchecker --fresh on the entry rc 0 (BadCtl rc 1, GoodCtl rc 0); 31/32 unit statements byte-identical to e6ac99a's, 1 (cJSON_cJSON_New_Item_spec) adds hpunm (ctx.punnedMember ... = false), discharged inside the composition. Added to sec-ub.tex and sec-appendix.tex.
- 2026-10-28T09:00:26Z (StmCore v2 pin: CBSTM03A with CBSTM03B, three sorted-abort corollaries abortPost_sorted, stm_run_abort_cust_sorted, stm_run_abort_acct_sorted; labelled, not pre-registered): pin coblean-pin2306Z-cbstm03ab-v2-20261028T0658Z delivered by the COBOL maintainer session at 07:06Z (1251Z plus Examples/StmCore/SortedAbort.lean); checked by an agent (checks/stmcor2-20261028T084846Z, SUMMARY.md d8c5f188, SHA256SUMS 59/59): diff vs 1251Z = SortedAbort only, std axioms x3 with planted controls, leanchecker --fresh rc 0 with the 1251Z closure reused (71 byte-identical), prebuilt 29/29. In the paper: one sentence in sec-migration (sec:cbstm03), Appendix A item, replay row (72, all).
- 2026-10-28T10:41:27Z (defect E, COBOL front end, reported by the COBOL maintainer session ~10:3xZ before any fix): a picture string beginning with ',' loses the comma in all snapshot front ends up to 0551Z and the pins. Our exposure scan checks/picscan-20261028T104013Z (SUMMARY 2bdcb71c): 0 leading-comma PICTURE strings in CardDemo (109 files, 9,143 clauses) and NIST (510 files, 58,366 clauses); plant 3/3. Paper: App. F paragraph; sec-limits counts 'another eight', 'four of the eight', 'all but five', COBSWAIT scans.
- 2026-10-28T10:44:58Z (C1 attribution run of N3, coblean; exploratory, not pre-registered): plan recorded BEFORE the run in prereg/ADDENDUM_C1ATTR_coblean.md (sha256 prefix b677baab8c83d205): variant tree = N3 recipe + c1var_resolve.diff b740d599 (Resolve.lean: trap when either SIZE ERROR phrase present), frozen N3 runner, all 309 programs, expected exactly the 55 listed FAIL entries -> PASS (10 programs), NC107A stays fail, nothing else changes (census 235 -> 245).
- 2026-10-28T10:51:13Z (C1 attribution run, coblean; exploratory): built variant tree recorded in prereg/ADDENDUM_C1ATTR_coblean_tree.md (sha256 prefix 60553303768036a9): manifest 387a13c0 (2,165 lines), diff vs N3 ab5e42de = Resolve.lean + 22 build outputs, Resolve.lean dd5de241. Sent by the COBOL maintainer session before the first module; recorded here shortly after the NC module started.
- 2026-10-28T11:05:56Z (C1 attribution run, coblean; exploratory): delivered sealed by the COBOL maintainer session (c1var/sealed_20261028T110243Z, SHA256SUMS 4b8c115d, 2,424 entries): as predicted, the 55 listed entries FAIL -> PASS (10 programs pass), NC107A unchanged; NOT predicted: NC251A undefined (divByZero under NOT ON SIZE ERROR alone, line 768) -> unsupported (36 more entries pass, stops at DIV-TEST-F5-21, DIVIDE REMAINDER into a non-numeric item); run-time values only otherwise (NC214M ACCEPT TIME; WHEN-COMPILED in IF142A/IF403M front-end JSON). Census 235/11/61/1/1 -> 245/1/62/0/1. Under check by an agent.
- 2026-10-28T11:14:44Z (C1 attribution run): checked by an agent (checks/c1var-20261028T110556Z, SUMMARY.md 623765f6, SHA256SUMS 62/62): seal 2,424/2,424; independent rebuild of the variant (cobolrun 8b0a88db = producer's); full 309-program re-run identical; own per-test parser: 91 entry changes = 55 predicted + 36 new NC251A PASS; nothing else. In the paper: App. F paragraph after the N3 census; sec-stack sentence (ten of 11 failing programs and the one undefined stop traced to the size-error rule; NC107A the JUSTIFIED defect).
- 2026-10-28T11:29:44Z (correction to the 10:51 C1 entries): the built-tree record (10:51:13Z) preceded the start of the NC module (10:53:56Z by the producer's launch log and guard logs, per audit v38), not 'shortly after' it. And the NC251A change (undefined -> unsupported) was NOT predicted by the plan, which says any other difference counts against the attribution; the paper now labels it as unpredicted and attributes the stop to the semantics' treatment of a division by zero without ON SIZE ERROR, not to the truncation rule.
- 2026-10-28T12:42:16Z (coblean merge 8 = snapshot 20261028T1223Z; labelled, not pre-registered): delivered by the COBOL maintainer session ~12:2xZ (fixes A editpoint, D editlead, B JUSTIFIED, C DISPLAY decimal literal onto 0551Z). Checked by an agent (checks/merge8-20261028T122832Z, SUMMARY.md 72465cbf, SHA256SUMS 119/119): no theorem IR changes; EditPoint.lean 13 theorems std axioms + fresh replay; fixes A-D present on 1223Z, absent on 0551Z (probes + testers); NIST N3 commands on 1223Z, all 309 re-run: only NC107A fail -> pass, census 236/10/61/1/1. Paper: tab:snapshots row + 'seven later snapshots', App. F fix sentences, EditPoint theorems sentence, N3 sentence, sec-stack NC107A sentence, sec-limits 'all but one'.
- 2026-10-28T14:04:39Z (coblean arithmetic defect notes F1-F6, G, R1 from the COBOL maintainer session, before any fix): departures from IBM's intermediate-place rules found during ifn2 (exponents). Session's exposure: F1 one theorem statement (CBACT04C 1300-COMPUTE-INTEREST, model 2 places vs IBM 4, stored value equal by truncation, provided IBM truncates intermediates) and one NIST statement (NC252A); F2, F3, F5, F6 none; F4 4 NIST statements (passing programs); G NC250A one test (unsupported in N3). Session plan: fix F2/F3/F6/G now, F1 in an equivalence-keeping form (CBACT04C IR and proofs unchanged), F4/F5 later, R1 after a reading; d0: no objection; no re-proof asked. An agent started (own scan of theorem IRs, Lean truncation lemma, probes).
- 2026-10-28T14:13:15Z (arithmetic departures F1-F6, G): checked by an agent (checks/arith-20261028T140509Z, SUMMARY.md a2863d43, SHA256SUMS 59/59): own scan of the theorem IRs: one division in a theorem program (CBACT04C 1300-COMPUTE-INTEREST; model 2 places, IBM 4; lone quotient truncated into V99), none of F2/F3/F5/F6/G; Lean trunc_comp (std axioms); probes reproduce. Paper: App. F paragraph; sec-limits now says CBACT04C reaches F1 in one statement whose stored value is equal (provided IBM truncates intermediates), 'all but eight' open, COBSWAIT covered by the arithmetic scan.
- 2026-10-28T14:32:56Z (coblean merge 9 = snapshot 20261028T1421Z; labelled): defect E fix (lexer.py, one condition) on 1223Z. Checked by an agent (checks/merge9-20261028T142433Z, SUMMARY.md f37481f5, SHA256SUMS 85/85): only lexer.py + testers/docs changed, 68 oleans identical, theorem IRs regenerate byte for byte, probe ,ZZ9 keeps its comma on 1421Z (not on 1223Z), lctest 60/60, NIST 309 re-run identical to merge 8 (236/10/61/1/1). Paper: tab:snapshots row, 'eight later snapshots', App. F defect E fixed, App. A list, sec-limits 'all but seven, the seven departures'.
- 2026-10-28T16:58:23Z (coblean merge 10 = snapshot 20261028T1636Z; labelled): close-fix (CLOSE REEL/UNIT/NO REWIND/LOCK, OPEN INPUT REVERSED) + ifn2 (integral exponents) on 1421Z. Checked by an agent (checks/merge10-20261028T164108Z, SUMMARY.md dd09c702, SHA256SUMS 90): manifest 619/619, nothing under Examples/, theorem IRs regenerate byte for byte, FuelMono +2 arms with fresh-process axioms (5 FuelMono theorems std, ioFinishU_mono propext; TH0 24/25 std + bincnt_equiv's bv_decide native axiom = producer's 25 lines), closetest/powtest = producer's, NIST 309 re-run: census 246/11/50/1/0/1 = producer's; vs merge 9 only the 11 listed changes (10 pass; NC250A unsupported -> fail, only IF--TEST-28 = defect G). Paper: tab:snapshots row, nine later snapshots, App. A list, App. F NC250A sentence, ninth-snapshot axioms sentence, sec-limits count.
- 2026-10-28T17:25:31Z (coblean arithmetic departure F7 from the COBOL maintainer session, before any fix): in conditions, function arguments get dmax 0 (IBM: at least the argument's own operands under either reading of R1); probe r1probe1.cob R04 (model false, GnuCOBOL true); exposure 0 by the session's runs; our arith scan has 0 divisions in conditions of the theorem IRs. Not fixed now (with R1 later). Paper: App. F sentence; sec-limits counts (eight departures; F7 on the session's report, supported by our division scan; COBSWAIT six of eight).
- 2026-10-28T17:47:49Z (equiv-lean unified-next2 fac6c38 on cirlean 424e821 + coblean 0109Z; labelled): after the producer's rebuild, CONFIRMED by an agent re-check (checks/next2-20261028T161321Z section 7, SUMMARY.md 82a4de0b): all 176 claimed theorems' closures (2,362 modules) replay rc 0, axioms std, statement texts unchanged, meaning follows the pins; recompiles byte-identical. Paper: sec-trust paragraph after the joint build; sec-limits member-strict clause and memcpy-overlap clause.
- 2026-10-28T18:26:03Z (cirlean pointer-stride defect, reported by the C maintainer session before any fix): cir.ptr_stride/ptr_diff move by elements of the containing array, not sizeof(T), when the sizes differ (revised e6ac99a and member-strict 424e821); cast-back dereference gives a defined wrong value (minimal cases ~/cirlean_work/scratch/stridecheck/s.c). Fix planned in next3 (bytes). Exposure scan of the claimed closures requested (same set as cirpun); paper text after our check.
- 2026-10-28T18:31:15Z d0 check stride-20261028T182920Z: pointer-stride defect CONFIRMED at all 10 frozen cirlean builds (wrong defined values on cast-back strides and pointer differences; false out-of-bounds and ill-typed reports; same-size controls match). Exposure scan by the C maintainer session pending.
- 2026-10-28T18:39:16Z (cirlean core soundness audit, the C maintainer session/rog, frozen 424e821, 73 minimal cases; ~/cirlean_work/scratch/soundaudit_core/FINDINGS.md sha16 29898c7fd89cf9ed): 21 cases where cirrun gives a defined value and C gives another value, UB or an indeterminate value: G5 (9) scalar access whose path designates a whole aggregate is not type-checked, a scalar store replaces the aggregate, 64-bit store/load over two ints defined (incl. atomics); G4 (1) aggregate copy through another struct type defined; G2 (2) strtol/strtod end-pointer store bypasses the typed store; G3 (5) va_arg (3, fixed on next3 vastruct) and sscanf (2, pedantic) type mismatches; U1 (2) union member activated at member-pointer formation, stale member through earlier-formed pointers; U2 (2) bit-field unit in a union reads 0 for bits of the previous member. Also 24 false UBs. The C maintainer session: G5/G4/G2 inside cirpun FLAG/AGG/CHAR categories (existing scan bounds them); U1/U2 not seen by cirpun. Fixes on next3 branches bytes (G5/G4 + stride), modelstore (G2), unionact (U1/U2). Our checks: own reproduction probe + exposure classification (pending); paper text after them.
- 2026-10-28T18:41:50Z d0 check coresnd-20261028T183958Z: G5 and G4 reproduced at all 10 frozen builds, G2 at f107f53/424e821 (first strtol model), U1/U2 from 90b9c2f; controls match. Exposure classification next.
- 2026-10-28T18:44:29Z d0 checks extended to cirlean 88e6008, d9ae8e5, ec40522 (replay-copy interpreters): stride, G5, G4 at all 13 versions; G2 at f107f53/424e821 only; U1/U2 at all but 266d1ed/28e2380 (union stores reported invalid there).
- 2026-10-28T18:44:54Z (cirlean library-model soundness audit, the C maintainer session/cjlemmas, 130 runs at 424e821; ~/cirlean_work/scratch/soundaudit/FINDINGS.md sha 4742f16c): 35 gap lines in 12 causes where C leaves the behaviour undefined and cirrun gives a value: printf-family argument types unchecked; sprintf/snprintf overlap check misses the format string as source and an unterminated %.Ns source; fprintf with a NULL stream; memcpy/memmove/memset/memcmp with NULL and n = 0; va_list lifecycle misuses and int as long through a function pointer; negative VLA size converted and allocated; writes to const-qualified objects succeed; invalid atomic memory orders ignored; recursive __cxa_guard and never-written sibling bit-field (documented). 2 mismatches (handler registered during exit never runs; %lc of a non-ASCII wint_t); 10 false UBs. Fixes on next3 branches modelstore, vafmt, constobj. Our reproduction + exposure check pending.
- 2026-10-28T18:46:19Z d0 check libsnd-20261028T184506Z: library gaps reproduced: mem* null with size 0 and const-local stores defined at all 10 builds; sprintf format overlap, %d with long, va_arg after va_end defined from 90b9c2f; controls match.
- 2026-10-28T18:49:35Z SLIP: glob sec-*.tex included sec-ub.tex in one grep (no content displayed; filtered). Logged in PROGRESS.
- 2026-10-28T18:51:20Z (sec-ub exposure check for the pointer-stride defect and the core-memory gaps; by the sec-ub session): checks/ub-stride-coresnd-20261028T1846Z (SUMMARY.md 6d4c7c84, SHA256SUMS bd34c1c3 23/23): cirpun --stride reports STRIDE 0 across both UB findings (matchstar, cJSON_SetValuestring; UNKNOWN 0) and all six harness/unit closures (cjh UNKNOWN 0; r1/r264/r232 UNKNOWN 1 on localeconv's char[2]; yjr3/yjpatch2 UNKNOWN 96 on the unresolved indirect-call allocator pointers); core gaps G5/G4/G2/G3/U1/U2 have zero exposure in the two UB findings and the four cJSON closures, and in yajl-ruby are bounded by the same unresolved allocator/callback indirect-call pointers. Added to sec-ub.tex.
- 2026-10-28T18:55:57Z d0 observation (to be checked by a fork before any text): T3 unit 142's equivalence verdict for TFileTransport::~TFileTransport (D2, one of the 12 shared_ptr verdicts) begins with cir.vtt.address_point (unit.cir:3465 ff.), then byte strides on the vptr (-24) and on this (unit.cir:3474/3478). A d0 probe (checks/stride-20261028T182920Z/vbase: class with a virtual base, destroyed and read as a base subobject) stops with 'unsupported operation cir.vtt.address_point' at c4ef58d, ffab71e, e6ac99a and 424e821 (native 6 and 2; a plain destructor matches). If the theorem semantics treats this as going wrong, every execution of that destructor goes wrong at its first step on both versions, and the verdict relates no execution (fork A found the same prologue via the strides).
- 2026-10-28T19:04:12Z the C maintainer session stride exposure scan sealed: ~/cirlean_work/scratch/stridescan (SHA256SUMS 0aed7171e4aad5f1; cirpun2 25a5f5c from f365f63; 560 jobs; controls 21/21 incl. d0's probe 7/7 flagged + 3 same-size clean). STRIDE on claimed paths: T3 142 TFileTransport D2 (virtual-base adjustment; refused = UB), musl strlen word loop (10 rows), musl memcpy (130 rows, WordFree-excluded), T2 409 (offset 0 by the statement); UNKNOWN: C1 x4 + FH R1 (offset 0), T4 borrowed[rsize] (u8 by contract), T3 TSocket x6 (std::string), yajl r3 96; UB findings: none an artefact. Independent screens (d0 forks): coreexpA (8412eb48: no G5/G4/G2/G3 on claimed paths), coreexpB (3f58347a: stride agrees on D2, strlen, memcpy, 409; ALSO flags T3 notify pos += ret, TNonblockingServer.cpp:1337, in breakLoop's closure, which the C maintainer session's scan counts 0: discrepancy asked of the C maintainer session and of fork B; unions: kept member pointers in std::string (9 T2 units, 5 T3 verdicts incl. TSocket cached address), T4 libc++ string bit-fields), coreexpC (208499ca: no library-gap condition can hold on claimed paths).
- 2026-10-28T19:06:36Z d0 an agent (checks/vacuity-20261028T185625Z, SUMMARY fc2b3fb5): 6 of the 54 T3 equivalence verdicts relate no execution: TFileTransport D2 (order 142; first op cir.vtt.address_point -> .ub unsupported at ffab71e/e6ac99a/424e821; Equiv = Sim both ways, Sim needs Safe = .ok) and 5 deleting destructors (D0) of abstract classes with cir.trap bodies (orders 50, 58, 72x3; never called in C++); the other 48 not shown vacuous (straight-line screen); T2 claims use Returns (.ok required): none vacuous this way. Told the orchestrator session (T3 owner). The C maintainer session V triage at next2 (vtriage_next2 SHA256SUMS 3d300612): 13 real UB, 13 false alarms of 26 UB rows; an agent checking (due 20:00Z).
- 2026-10-28T19:12:48Z d0 an agent (checks/vtriage-20261028T190635Z, SUMMARY ed8a5a7e): 26/26 agree with the C maintainer session's V triage at next2 (13 real UB under ISO incl. 7 shifts/overflows confirmed by own UBSan builds at the producer's line; 13 false alarms; GNU reading 11/15). Paper: sec-stack LLVM paragraph (full triage replaces the three-row triage).
- 2026-10-28T19:15:47Z the C maintainer session stride scan v2 sealed: ~/cirlean_work/scratch/stridescan_v2 (SHA256SUMS 0bce58a8ae73244d; cirpun2 796ac42 fixes strideElem for non-element objects; controls 26/26 incl. stride_obj.c; v1 unchanged). Only change: STRIDE row for notify:1337 in both T3 142 breakLoop units (never reached in the semantics: poll without a model first). Now agrees with fork coreexpB on all stride sites.
- 2026-10-28T19:20:40Z d0 an agent deep (vacuity-.../deep/DEEP.md 290e7f3f): 19 of 54 T3 equivalence verdicts relate no execution at ffab71e (11 TEvhttpServer::complete via evhttp_add_header without model/body; D2; breakLoop; setCurrentThreadHighPriority; 5 D0); the 12 shared_ptr verdicts also at e6ac99a and 424e821; 35 with a safe path. Paper: sec-thrift T3 paragraphs rewritten (19 vacuous; 8 of 9 partly certified commits only vacuous verdicts; order 142 keeps 3 TSocket setters); sec-limits shared_ptr sentence and stride places (4, incl. breakLoop callee). Told the orchestrator session (T3 owner) with 20:30Z for objections.
- 2026-10-28T19:23:04Z d0 an agent (checks/nonvac-20261028T191944Z, SUMMARY b3e653f5): jsmn (28e2380, e6ac99a, 424e821), musl memcpy and strlen (e6ac99a, 424e821) each complete on inputs inside their hypotheses with the native result (memcpy n=7 outside WordFree stops at a type-punned access, as predicted); drivers add only a caller (function CIR identical). Paper: sec-limits sentence.
- 2026-10-28T20:08:25Z d0 check t3arity-20261028T200633Z (SUMMARY 559d752a): 16 of 54 T3 verdict statements pass one argument fewer than the root's params (bool dropped) -> bindArgs .ub at ffab71e; same 16 as the C maintainer session's t3args_v1 scan. T3 vacuity now 22/54; no verdict of the 9 partly certified commits relates an execution; 32 others in behaviour-change commits 50, 72, 77. Paper: sec-thrift T3 paragraph (22), shared_ptr paragraph (12 of the 22), sec-limits TSocket/union sentences.
- 2026-10-28T20:18:44Z audit v48 findings 1-5 applied (notes/agent_v48_report_summary.md); correction to vacuity deep/DEEP.md: pthread_self is declared with model none and body none (not absent); same consequence.
- 2026-10-28T21:10:07Z the COBOL maintainer session MERGE 11 sealed: coblean-20261028T2106Z (manifest 3588a630, 632 entries; TSV 1a540954; d0 files 2613eefd): fixes G (VALUE ALL repeated to size), F2 (conditions dmax; EVALUATE per-side relOwn), F3 (numeric-edited COMPUTE receivers in dmax), F6 (integer functions outer dmax 0), F1 (IBM quotient scale except a one-division COMPUTE with numeric receivers and no ROUNDED: CBACT04C 1300-COMPUTE-INTEREST and NC252A COMP-TEST-32 keep the old scale); producer: same resolved IR for the 15 theorem IRs; TH0 25 axiom lines same; NIST 247/10/50/1/1 (only NC250A fail->pass vs merge 10); open: R1+F7, R2, R3, F4, F5. An agent launched (due 22:15Z).
- 2026-10-28T21:27:34Z d0 an agent (checks/merge11-20261028T211008Z, SUMMARY 006b0196): merge 11 CONFIRMED (manifest, d0 files, only front-end modules changed, theorem oleans and IRs unchanged, DmaxResolve 15/15, TH0 axioms, dmaxtest, census 247 = producer, only NC250A changes; F1 exception matters exactly at CBACT04C 1300-COMPUTE-INTEREST and NC252A COMP-TEST-32). Paper: App A list, App F later snapshots (ten; tenth: front end only), tab:snapshots row, arithmetic paragraph (five of eight departures fixed), sec-limits (three departures left; quotient rule except CBACT04C's form; ten snapshots).
- 2026-10-28T21:44:09Z the orchestrator session tier-0 package (post-freeze, exploratory): t3_tier0_tsocket_424e821 (SHA256SUMS faf97918; REPORT bbe829d4; replay log 5219e9f1): TSocket setNoDelay/setKeepAlive/setLinger with the bool passed, equivalent + changed_only_where_old_unsafe + nonvacuous (Safe witnesses) at 424e821, std axioms. An agent checking (due 22:45Z). Tier 1 (extmodels c17690c) for the 11 complete + breakLoop in progress at VO.
- 2026-10-28T21:57:55Z d0 an agent (checks/tier0-20261028T214410Z, SUMMARY 87ae92c5): tier-0 TSocket package CONFIRMED (hashes, arity, statements = T3 + bool, same program terms, std axioms, replays); witnesses use the early return (socket_ = -1); setsockopt unmodelled. Paper: sec-thrift sentence (exploratory re-proof) + App A item; audit after tier-1 or by ~23:30Z.
- 2026-10-29T00:40:13Z audit v51 applied (notes/agent_v51_report_summary.md). SLIP (an agent, disclosed): a grep over the glob sec-*.tex read sec-ub.tex; output filtered by name, nothing shown. Briefs will name the files explicitly from now on.
- 2026-10-29T01:14:41Z the COBOL maintainer session READINGS MEMO R1-R3: ~/coblean_runs/inr/READINGS_MEMO.md (318c6205): R1 settled (inner dmax over all arguments; fixes F7; NIST exposure 5 statements, said to keep PASS), R2 not an IBM question (no ROUNDED MODE in Enterprise COBOL 6.4/6.5; model's modes = COBOL 2014 extension; lone-quotient lowering to DIVIDE GIVING), R3 not settled (assumption wording memo 5(c); same stored values as 'always carry' for plain ROUNDED). An agent checking (due 01:45Z); merge 12 to follow.
- 2026-10-29T01:23:50Z d0 an agent (checks/readings-20261029T011442Z, SUMMARY 974299d9): 76/76 quotes match the cached pages (own script, planted control); R1 settled in direction (both earlier readings excluded; inner dmax with one interpretive step; no IBM digits; NIST tests do not separate it from the statement-dmax reading; hand evaluations of the 5 agree); R2 absence confirmed; R3 memo 5(c) correct (exhaustive 2,911,104 cases). Paper: App F R1 and F7 sentences rewritten; no R2/R3 wording in d0's files needs a change.
- 2026-10-29T02:52:59Z the C maintainer session notice (before exposure analysis): by-value parameters of call-non-trivial class types (shared_ptr, std::string, RAII) are passed as values in pre-lowering CIR at every cirlean pin: the callee gets a bitwise second object; C++ has one object destroyed by the caller. Effects in a shared_ptr repro: libc++ one wrong defined value (use_count 1 vs 2), else spurious UB from the extra release; libstdc++ only UB (through _M_release's counter load). Scope: such parameters in 384/558 T2 and 346/530 T3 units, 46/357 census files. Fixed in next3 (byval, b0e046f: pass by reference to the caller's temporary). Exposure check of all claimed C++ closures (T2, T3 incl. tier-0, T4, D1/D2 tinyxml2) requested; our own screen to compare.
- 2026-10-29T02:53:37Z d0 check byval-20261029T025320Z: by-value deviation CONFIRMED with an own RAII probe (moved-from parameter: -1 vs native 0 at six builds; untouched parameter and trivial record match). Exposure: the C maintainer session/optim check requested; own screen after.
- 2026-10-29T04:16:12Z the C maintainer session deviation (all pins): a global that is only declared (extern; defined in another unit or a library) is zero-initialised as if defined, so reads give zeros. The C maintainer session/mutant exposure: cJSON none; T3: __libc_single_threaded in the 12 vacuous closures (11 complete + D2), reads give 0 vs glibc's 1, atomic refcount path computes the same counts; census 16/1218 (iostream). Fix in next3 (externglob: UB except modelled stdin/stdout/stderr, typeinfo, __libc_single_threaded = 1). Asked to extend the scan to all claimed closures (T2, T4, C ports, musl, D1/D2, re-check and tier-0 packages); own screen to compare.
- 2026-10-29T04:16:37Z d0 check extglob-20261029T041624Z: declared-only globals read as zero CONFIRMED (own probe: extern scalar and array give 0 at five builds; a defined global matches). Exposure scan of all claimed closures requested from the C maintainer session; own screen after.
- 2026-10-29T04:58:31Z the C maintainer session by-value exposure scan sealed: ~/cirlean_work/scratch/byvalscan (SHA256SUMS 5375c61a; cirpun --byval 9be6d9d on 796ac42): 0 BYVAL rows in all 307 claimed jobs (T2 incl. partial, T3 54 old/new incl. 32 relating and tier-0, t3sp, T4 ac65118 and fac6c38, D1/D2 tinyxml2); 4 read-only root parameters of 3 T2 claims; by-value calls behind indirect calls only in T2 858 (excluded by hneed_not_executing); controls 35/35. Asked for a return-value exposure check at the claims' pins now (T3 unit 50 getPath returns std::string by value; libstdc++ _M_local_buf self-reference).
- 2026-10-29T04:59:01Z d0 byval check addendum: a self-referential class returned by value reads through a pointer into the callee's ended buffer on cirrun (UB report at four builds; native defined); trivial record return matches. Return-value exposure check requested from the C maintainer session (T3 unit 50 getPath).
- 2026-10-29T07:09:33Z the C maintainer session return-value scan (retscan SHA256SUMS 1198adc7; cirpun --retval 07c0135; controls 40/40): no SELFREF/KEPT return slot or EXPOSED receiving call in the 307 claimed jobs; T3 50 getPath at ffab71e returns through the strCopyCtor model (model value, no pointer); 2 EXPOSED rows only in T2 858 behind hneed_not_executing. Declared-only globals scan (sealscan_20261029T055225Z, SHA256SUMS 0339317d): none in T2union, T4, C ports, musl, D1 zlib; 45/521 claims read one in the over-approximated closure, 0 writes, none on a non-vacuous verdict path. next3 statement shapes: byval (T2 130/463/549) and retslot (T3 50 getPath, T2 74/338/483, D2 38/61) need regenerated statements for re-checks at next3. An agent checking all three scans (due 07:50Z).
- 2026-10-29T07:18:07Z d0 an agent (checks/cxxscans-20261029T070934Z, SUMMARY 91ee4f77): byvalscan, retscan, sealscan CONFIRMED for the claimed closures (hashes; own screen agrees per study; getPath via strCopyCtor; 10 sampled declared-only hits keep their reasons). Retscan gap (NRVO-elided user copy ctor, no dtor: our ret.cpp probe not flagged) reaches no claimed closure. Own screen did not cover t3sp/t23next2/tier-0, T4 fac6c38, C1/C2/VO2 (same program terms for the first three). Paper: three deviations to sec-limits and App F next.
- 2026-10-29T08:18:47Z RECORDED (before any run) the draft inputs of the labelled V re-run at cirlean next3: prereg/V/ADDENDUM_V_rerun_next3_DRAFT_v2.md (sha16 33e1057a3f60bcf3, = the C maintainer session's draft): sample d0f38820; runner run_prereg_v10.py (8150b519c92016f9; v9 + --cirrun/--cirrun-sha256 checked before any write + required --stop-utc); declared expectations from vtriage_next2 (11 false alarms gone at the triaged sites, 139 partial, 80 depends on intptr, 13 real stay UB, 179 moves to :71, 158 flagged, oom and externglob notes). PIN fields (cirrun path + sha, PIN-UTC, --stop-utc) and the next3 item list to be filled at the pin; the FINAL addendum must be recorded here before the run starts.
- 2026-10-29T08:59:55Z SLIP (an agent, 10-28 19:11Z): vtriage SUMMARY line 7 typed a wrong hash tail for the producer's SHA256SUMS (found by the C maintainer session); erratum appended with the computed hash 3d30061213a151ddd96c8b741e26a0ec681871bf564e09a3f300be0dc7c8be3f; SUMMARY now 2782bb22.
- 2026-10-29T09:00:10Z the COBOL maintainer session MERGE 12 sealed: coblean-20261029T0854Z (manifest 3be9a8c2, 667 entries; TSV c2d91158; d0 files bd1738c2): fixes F4, F5, F7, R1 (inner dmax), R2 (c), Z0, C30; R3 an assumption; named-unsupported stops at three in-argument 30-digit paths; producer: TH0 axioms same, DmaxResolve/Ar2Resolve old==new on 15 theorem IRs + pins, census unchanged 247; D0_EVIDENCE.md da111dc9. An agent launched (due 10:30Z).
- 2026-10-29T09:43:50Z d0 an agent (checks/merge12-20261029T085953Z, SUMMARY 5fc361b1): merge 12 CONFIRMED (inputs; IRs/pins; resolvers old==new; own build 115 jobs, 6 changed oleans byte-equal; TH0 axioms; testers; census 247 = merge 11 row by row; TSV 293/7/25 re-run; D0_EVIDENCE 37/37 quotes, scans, bound 29; stops and nested-REM probes). Paper: App A, App F later snapshots (eleven), tab:snapshots row, arithmetic paragraph (remaining departures fixed, Z0, C30, three stops, R3 assumption), sec-limits (every defect fixed or stopped; eleven snapshots).
- 2026-10-29T16:49:07Z the orchestrator session tier-1 package (post-freeze, exploratory): t3_extmodels_c17690c (SHA256SUMS 3ab57abc; REPORT f3785471; replay log b52f0789): 12 T3 verdicts (breakLoop + 11 complete) with extmodels models and bool passed: 12/12 nonvacuous; 10/12 equivalent + changed_only_where_old_unsafe; 2/12 (complete 072, 105) proved refuted on counterexample memories (buffer pointers into record members / a vtable record). An agent checking (due 18:15Z), incl. whether those memories are reachable and which model assumptions become trusted.
- 2026-10-29T17:22:23Z tier-1 re-proof (exploratory, post-freeze, outside the pre-registration) checked (checks/tier1-20261029T164912Z, SUMMARY 7ba1301f) and entered in the paper as exploratory (sec-thrift, App A, tab:replay2); the T3 counts stay as pre-registered. Exposure check by an agent pending before audit v56.
- 2026-10-30T02:39:38Z labelled re-run of sample V at cirlean next3 (7c73739): inputs recorded before the run in prereg/V/ADDENDUM_V_rerun_next3.md (231bc40a); not a pre-registration; reported beside V like the next2 re-run.
- 2026-10-30T05:07:39Z (cirlean next3 7c73739 FH bundles check, labelled; by the sec-ub session): checks/fhnext3-20261030T0432Z (an agent, SUMMARY.md b5fe9173, SHA256SUMS 0efa553c 561/561): all 19 announced hashes in FREEZE_NOTICE_next3_7c73739.md (14694e8f) and MANIFEST_build.sha256 (8d2cc1ff, 1017/1017 in next3_7c73739_20261030) verify; all 10 *_next3 bundle manifests verify; all 20 .lean bundle source files are byte-identical to next2_v4/next2 (0 statement changes, no maxHeartbeats fallback or parse_array closer used); all 5 conditions for GhostNat12.lean:77 (3M -> 6M, diff 90de2bf8) hold; all 34 theorem names print subsets of [propext, Classical.choice, Quot.sound]; per-module leanchecker 259/259 rc 0 and leanchecker --fresh 10/10 root bundle modules rc 0 under ulimit -v 32 GiB. Whole-harness R1 assembly at 7c73739 requested from the orchestrator session.
- 2026-10-30T05:43:45Z labelled re-check of claimed C/C++ verdicts at cirlean next3 7c73739 (the orchestrator session): inputs recorded before the runs in prereg/T/ADDENDUM_recheck_next3_veriforch.md (five packages: R1 whole harness [the harness-study session's], T2 union-punning 3, T3 54, T2 102, D2 2; regenerated byval/retslot statements; runner run1.sh cd3a5728); not a pre-registration; reported beside the original runs.
- 2026-10-30T08:56:53Z next3 re-check record prereg/T/ADDENDUM_recheck_next3_veriforch.md (1d9b867e), R1 item: superseded for parse_array, parse_object and cJSON_Delete by cirlean's announced FH specification restatement CycleSpecsP2N v4 -> v5 (h_new gains the premise hrel; v5 step statements imply v4's); R1 and its paper text belong to the harness-study session; the record itself is unchanged (read-only).
- 2026-10-30T08:57:01Z next3 re-check record, R1 item: also a wrapper-layer restatement in veriforch's R1 (cJSON_skip_utf8_bom.lean: input buffer block typed as a byte array of the input's length instead of a free type), announced by the C maintainer session before the R1 package; top-level spec and 30 other unit signatures unchanged per veriforch. R1 belongs to the harness-study session.
- 2026-10-30T11:57:14Z (CycleSpecsP2N v5 FH bundles at cirlean next3 7c73739, labelled; checked by the sec-ub session): checks/fhnext3v5-20261030T1146Z (SUMMARY.md 041ce9c5dd6b9b04, SHA256SUMS 2c08c8af83b55418 27/27): parse_array_strong_next3_v5 (790e46ef, 11/11), parse_object_strong_next3_v5 (7946ff56, 19/19), and cJSON_Delete_next3_v5 (1db06365, 9/9) plus SPEC_v5.sha256 (0c5e9e53 / 371b7033, 4/4) and 238/238 RESOLUTION_v5.tsv rows verify; DeleteSpecTheirsP, ParseArrayStepSpecP, and ParseObjectStepSpecP typecheck against CycleSpecsP2N v5 in a fresh Lean process with standard axioms; 12/12 rebuilt v5 modules pass per-module leanchecker rc = 0 and 3/3 root modules pass leanchecker --fresh rc = 0 under ulimit -v 32 GiB.
- 2026-10-30T14:38:54Z (whole cJSON harness R1 at cirlean next3 7c73739, labelled; checked by the sec-ub session): veriforch's package ~/veriforch/runs/postfreeze/r1_cjson_next3_7c73739 (SHA256SUMS 13ef1e65, 499/499) on frozen pin next3_7c73739_20261030 checked in checks/r1next3-20261030T1407Z (an agent, SUMMARY.md d336e0b6, SHA256SUMS de921b52 639/639): entry statement byte-identical to 424e821's; 32 unit theorems + FHEntry.entry_main std; 300/300 modules of RESOLUTION.tsv (54 CIR.* + 246 lib/) replay rc 0 and leanchecker --fresh on the entry rc 0 (BadCtl rc 1, GoodCtl rc 0); 30/32 unit statements byte-identical to 424e821's, 2 change (cJSON_cJSON_New_Item_spec adds hrel = ctx.memberRelated ... (.record "internal_hooks") = true; cJSON_skip_utf8_bom_spec types the input buffer block bc as .array (.int false 8) xs.length), both discharged inside the composition. Added to sec-ub.tex and sec-appendix.tex.
- 2026-10-30T14:41:58Z (r1next3-20261030T1407Z final manifest hashes): SUMMARY.md 1047f089, SHA256SUMS a3fed15e (642/642).
- 2026-10-30T19:04:04Z (cirlean next3.1 e0b4d64 FH bundles check, labelled; by the sec-ub session): checks/fhnext31-20261030T1834Z (an agent, SUMMARY.md a66c7186, SHA256SUMS e694fbda 558/558): all 18 announced hashes in FREEZE_NOTICE_next31_e0b4d64.md (c27b8af3) and MANIFEST_build.sha256 (01ad8503, 1032/1032 in next31_e0b4d64_20261030) verify; all 10 *_next31 bundle manifests verify; all 21 .lean bundle source files are byte-identical to *_next3 (7 bundles) and *_next3_v5 (3 bundles) (0 source or statement changes); DeleteSpecTheirsP, ParseArrayStepSpecP, and ParseObjectStepSpecP typecheck against CycleSpecsP2N v5 and all 34 theorem names print subsets of [propext, Classical.choice, Quot.sound]; per-module leanchecker 260/260 rc 0 and leanchecker --fresh 10/10 root bundle modules rc 0 under ulimit -v 32 GiB. Whole-harness R1 assembly at e0b4d64 requested from the orchestrator session.
- 2026-10-30T19:06:12Z (fhnext31-20261030T1834Z final manifest hashes): SUMMARY.md 125e368e, SHA256SUMS b9fe6829 (558/558).
