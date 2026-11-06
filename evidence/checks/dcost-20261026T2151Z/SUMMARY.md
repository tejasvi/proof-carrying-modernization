# Pre-registered cost-per-unit and gap-name analyses (checks/dcost-20261026T2151Z; fork of the evidence owner; 2026-10-26T21:56Z)

RESULT: computed for D (es-toolkit, tinyxml2, zlib, commons-lang3), D2 re-run and held-out (all four), the CardDemo
census (gap names only) and T2 (overall and per language), from my existing copies of the records. Blocked counts equal
the paper's tables for all 12 D/D2 rows, CardDemo (35) and T2 (459); T2 cost equals checks/t2-20261026T0321Z (median
$0.159, IQR 0.036-0.359, mean $0.235, total $234.85).

Required by: PREREG_D_v2.md l.88-90 (CardDemo counts only; cost per unit, model $ and core-seconds: median, IQR, mean,
total; gap names with frequencies), PREREG_D2_v1.md l.104 (gap names before and after; cost per unit), PREREG_T_v1.md l.74.

## Sources (copies; the same records the checks behind each table row use)
- D: replay/vo-D-20261024T1434Z/records/estoolkit, replay/vo-Dtx-20261024T2047Z/records/tinyxml2,
  replay/vo-Dz-20261025T1140Z/records/zlib, replay/vo-Dl3b-20261025T1149Z/records/lang3; CardDemo:
  replay/vo-D-20261024T1434Z/records/carddemo.
- D2 re-run: replay/vo-2-20261025T1141Z/prereg/D2/{estoolkit,tinyxml2}/rerun, replay/vo-Dz2r-20261025T2256Z (zlib),
  replay/vo-Dl3r2-20261025T1735Z (lang3). Held-out: replay/vo-2-20261025T1141Z/prereg/D2/estoolkit/heldout,
  replay/vo-Dtxh2-20261025T1813Z (tinyxml2), replay/vo-Dz2h-20261026T0526Z (zlib, 52 units), replay/vo-Dl3h-20261026T0056Z
  (lang3) with orders 50 and 80 from veriforch's heldout_bridgefix/results.jsonl (copied to inputs/, sha256 3343f0f8...,
  = the paper's comment): outcome and gap from the re-run, cost from the main run (the re-run's $1.00 stays on its own line).
- T2: checks/t2-20261026T0321Z/T2records/results.jsonl (costs) with the 'mine' column of t2_outcomes_mine.tsv (the frozen
  reading the paper uses: 459 blocked, 311 timeout).
- Outcome reading for D/D2: a copy of tools/d_outcome_check_v3.py mine(). Every record has model_usd and core_s.

## Definitions
- Gap name = the blocked unit's scope string (detail after "gap:"), "not emitted by the front end", or the tool's error
  class (PREREG_D_v2 R6 table); gap_names.tsv lists every distinct name with its unit count.
- Gap items = the comma-separated entries of a scope string (bracket-aware; kinds external, unmodelled, unsupported,
  subset), counted once per blocked unit naming them (gap_items.tsv); the table shows the three most frequent items.
- Quartiles: statistics.quantiles(method="inclusive") (linear interpolation); median of all units in the run.

## Results
- cost_per_unit.tsv (per row: units; model $ median, Q1, Q3, mean, total, units at $0; core-s median, Q1, Q3, mean,
  total, units at 0), gap_names.tsv, gap_items.tsv, summary_rows.json (+ outcome counts per row), tab_cost_gaps.tex
  (14 rows; compiles in a plain article test, textest/t2.pdf; uses \code from main.tex and booktabs).

## Caveats
- Per-unit core-seconds come from the unit records. Units that stop before any Lean check record 0 (es-toolkit 86, 86
  and 94 of 100; T2 285 of 1,000, of which C 103/127, Rust 73/123). The per-unit field does not cover all of a run's
  compute: T2's units sum to 51,822 core-s = 14.4 core-h, while the guard metered 30.36 core-h for the T2 driver.
- commons-lang3 D: 50 of 100 units record $0 of model calls (median $0.006).
- The records cut some long gap names (e.g. tinyxml2's "XMLDeclaration::XMLDeclaration(tinyxml2::XMLDocume"); the table
  marks such names with "...". Counts are unaffected.
- Not computed (not asked): PREREG_D_v2 l.54 front-end and extraction cost per library.

## Plain summary (for the paper)
Per unit, the model calls cost a median of $0.014 for es-toolkit, $0.11 to $0.88 for tinyxml2, $0.87 to $1.00 for
zlib and $0.006 to $0.30 for commons-lang3 across D and D2, and $0.16 in the Thrift sample, with long upper tails
(means up to $0.99). The most frequent gaps are the TypeScript subset's rules on any-typed values, C library functions
without a model (strchr in tinyxml2; strerror, errno and read/write in zlib), tinyxml2's own constructors and
destructors outside a unit's closure, single Java library methods without a model in commons-lang3, the CICS
copybooks and ACCEPT/ENTRY statements of the CardDemo programs, and, in the Thrift sample, functions the front end does
not emit and calls into GLib's type system.

## Slips
- One command ran an empty `python3 -` heredoc outside the guard (no input, no effect).
- No Lean runs; all analysis python ran as python3 -I under tools/g1.sh; nothing written outside this dir.
