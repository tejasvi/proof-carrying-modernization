# Pre-registration D2: before and after fixing the most frequent blockers, on the D samples and on held-out samples

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25. No D2 fix had landed at that time. The
files listed in SHA256SUMS_D2_v1 are part of this pre-registration. Later changes go to DEVIATIONS.md, which is
append-only; this file is never edited.

D2 is a declared second measurement. D (PREREG_D_v2) stays the primary pre-registered result and is reported as run.
D2 is reported apart and labelled as a measurement taken after targeted tool changes.

## Question

If each bridge fixes the one or two blocker families that hold back the most functions of its whole population, how do
the outcome proportions change? Measured on the same frozen D samples, and on fresh held-out samples, to show whether
the gain generalizes beyond the units measured before.

## Populations

The D populations, unchanged: `D/pop_zlib.tsv` (C, 152), `D/pop_tinyxml2.tsv` (C++, 395), `D/pop_lang3.tsv` (Java,
3,901) and `D/pop_estoolkit.tsv` (TypeScript, 794). CardDemo is excluded: its blockers are CICS, IMS and DB2, which no
fix in scope addresses.

## Fix targets (frozen; whole population, not the sample)

- Data: the front-end output of the D run for each population (`units.json`, copied to `D2/inputs/units_<pop>.json`).
  For every population unit, `tools/blocker_freq.py` finds its front-end unit with the matching rules of veriforch's
  `prereg_d.py` and collects the gap tokens of every unit in its call-graph closure.
  - A unit with no front-end unit gets the token `not-emitted`.
  - Tokens group into families. An external function, a subset rule or `not-emitted` is its own family; an
    unmodelled Java library method belongs to the family of its Java class.
  - Output: `D2/freq/freq_<pop>.tsv`, plus per-unit tokens.
- Rule (`tools/select_fix_targets.py`): a unit is fully unblocked by a set of families when every gap family in its
  closure is in the set. Per population, the chosen set is the pair of families that fully unblocks the most population
  units. If a single family reaches at least 90% of that pair's count, only that family is chosen. Ties go to the
  larger carrying frequency (units whose closure carries the family), then to the name.
  - Why not plain carrying frequency: families that often occur together unblock nothing on their own. In zlib the two
    most frequent families (`__errno_location`, `strerror`, 27 units each) fully unblock 0 units.
  - Both rankings are kept in `D2/freq/`.
- Result (`D2/fix_targets.tsv`):

| population | fixer | families to fix | population units fully unblocked |
|---|---|---|---|
| zlib | cirlean | `external:lseek64`, `external:open` | 9 of 152 (38 blocked) |
| tinyxml2 | cirlean | `external:strchr`, `not-emitted` | 131 of 395 (202 blocked) |
| commons-lang3 | JimpleLean | `unmodelled:java.lang.CharSequence`, `unmodelled:java.lang.Character` | 202 of 3,901 (2,245 blocked) |
| es-toolkit | StrictTS | `not-emitted`, `subset:unsupported-type` | 163 of 794 (699 blocked) |

- What a fix may be:
  - one general change per family: a model of the external function; support for the type, rule or library class;
    or making the front end emit the units it skipped;
  - it must not mention any sample, held-out or population unit by name;
  - each fix is recorded with its commit and the family it addresses;
  - a fixer may decline a family that has no general fix, giving the reason; no substitute family is chosen.
- es-toolkit specifics:
  - StrictTS reports that most of its `not-emitted` functions are generic functions left out because the IR is
    monomorphic. A fix that emits each generic function at fixed type arguments is allowed. Every claim about such a
    function is then about that instance and is reported as such.
  - es-toolkit keeps the strict mode of D. Switching to the checked-dynamic mode is not a D2 fix: it changes what a
    proof states.

## Samples

- Re-run sample: the frozen D samples `D/sample_<pop>.tsv` (100 each), in their order.
- Held-out sample: `tools/draw_heldout.py` with seed `fv-paper-prereg-D2-2026-10-25`. It draws min(100, remaining)
  units without replacement from the population minus the D sample.
  - Files: `D2/heldout_<pop>.tsv`, frozen here: zlib 52 (all remaining units, shuffled), tinyxml2 100, lang3 100,
    es-toolkit 100.
  - Their order is the processing order.

## Tool pins

- Recorded when the D2 run starts, after the fixes are pinned:
  - cirlean (zlib, tinyxml2), JimpleLean (lang3) and StrictTS (es-toolkit), each at a commit or snapshot that contains
    its fixes;
  - Lean v4.35.0;
  - veriforch as a frozen copy with a SHA256 manifest.
- The D2 pins also contain every other change made since the D pins. The changes between the D and D2 pins are listed
  (commit log or snapshot diff) and reported with the results.
- No re-pin during the run. Crash fixes only, each recorded, and the affected units are re-run.

## Procedure and outcomes

- Per unit: the procedure of PREREG_D_v2 (R7 to R9), unchanged:
  - front end and extraction once per library;
  - `vo verify --only` over the unit and its callee closure, `--attempts 3 --check-timeout 600 --budget 0.80`;
  - the 30-minute wall;
  - the counterexample step where the bridge has one;
  - kernel replay of every claimed theorem.
- Outcomes: the R6 mapping of PREREG_D_v2, unchanged, with the readings already recorded in DEVIATIONS.md (2026-10-24
  and 2026-10-25): a negative-cache "stuck" is a timeout; a tool crash is an infrastructure error until its crash fix
  and re-run.
- Order: per population, the re-run sample first, then the held-out sample. Populations may run in parallel.
- Budget: model spend for all of D2 at most $500 (veriforch's usage logs). If the budget runs out, processing stops at
  the current position in every population. Unattempted units are reported and left out of the denominators.
- Compute is reported (core-seconds per unit, from the guard logs). It is not part of the cap.

## Analysis

- Per population and sample, the counts and proportions of every outcome, with Wilson 95% intervals.
- Re-run sample, paired with D:
  - the number of units that move between each pair of outcomes (a transition table);
  - in particular, how many units move from blocked to proved, partial or conditional.
- Held-out sample: proportions with Wilson intervals, set next to D's proportions on its sample. The comparison is
  descriptive (different units); no test is pre-specified.
- Gap names with their frequencies before and after; cost per unit (median, IQR, mean, total).
- No pooling across languages in the headline numbers. Nothing is excluded after the fact.

## Known before the run

- D's results for these populations (zlib still running at the freeze of this document; tinyxml2, es-toolkit and
  commons-lang3 finished, commons-lang3 with 42 units being re-run after crash fix 2).
- The fix targets above and the whole-population blocker data. Nothing from the D samples' outcomes was used to choose
  them.
