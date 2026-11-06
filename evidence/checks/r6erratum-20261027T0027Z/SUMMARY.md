RESULT: R6 erratum confirmed. My re-run of tscheck_cex.js from copies is byte-identical to tscheck.tsv (1dbd9852...): of the 86
counterexample calls, 76 type-check against the public declarations in both versions (all 9 Lean-confirmed, 67 of 77 Node-only)
and 10 in neither (all Node-only, exactly the erratum's list). Of the six perf/refactor/style highlights, four keep a type-valid
counterexample (uniq([-0]), toPath(".."), toPath("]"), areObjectsEqual, the last an internal function); zip() and
zipWith([], 8, undefined) are calls outside the public overloads. The three docs/test/bench highlights all stay valid.

# R6 erratum check (fork of the evidence owner; written 2026-10-27T00:30Z by date -u)

## Inputs (copies)
- StrictTS master 6ac88b4 (worktree ~/strictts; read with --no-optional-locks): from_commit/R6_ERRATUM_20261027.md 5b4e93137c7df386...,
  tscheck.tsv 1dbd9852f2f141f2..., tscheck_cex.js 32d7b04d765aa0ad... (commit blobs = worktree files).
- Chunk records: my copy ~/fv_paper/replay/r6-20261026T2004Z/scratch_r6/chunks (15 lists): 86 changed functions with verdict REFUTED
  (refuted_ids_from_chunks.txt; ids all match ^date_sha8_name$) = the 86 ids of tscheck.tsv.
- Pair slices: the 86 pairs copied with cp -rL from ~/strictts/scratch/hist_es/scan2_{rpsc,other}/<id> into pairs/ (0 symlinks);
  all 820 files match ~/fv_paper/prereg/R6/pairs_SHA256SUMS (the frozen sums; pairs_expected.sha256).
- TypeScript 5.9.3 (~/strictts/frontend/node_modules/typescript, required read-only, as the script does), Node v22.22.1.

## Re-run
- node tscheck_cex.js <chunks copy> pairs work > tscheck_mine.tsv under coreh_guard_v2 (0.010 core-h, rc 0; ulimit -v 16 GiB);
  tscheck_mine.tsv byte-identical to the erratum's tscheck.tsv.
- Joined with r6_table.tsv (category column): REFUTED (Lean-confirmed) 9 valid; REFUTED (Node only) 67 valid + 10 invalid; no pair
  valid in one version only (refuted_with_validity.tsv).

## The 10 invalid calls (invalid10.tsv; cex_inputs.tsv; declarations read in the old and new slices)
- zip() (0f26a676 perf; b51351f2 feat): public overloads take 1 to 4 arrays; only the variadic implementation admits 0.
- zipWith([], 8, undefined) (e37b2957 perf) and zipWith([0]) (a46806bb fix): every overload needs an array and a combine function
  (2 to 5 arguments); 8 is neither, and one argument is too few.
- delay(0, { signal: {} }): the single declaration types signal as AbortSignal; {} is not one.
- repeat(false, ...): public overload repeat(str?: string, n?: number); boolean is not a string.
- random({}) and random(undefined, -47.67): no overload of the four ((floating?), (max, floating?), (min, max, floating?), (min,
  index, guard)) admits them under strict checking.
- template("", {...}, {}): the public overload takes at most 2 arguments (the third, guard, is implementation-only).
- orderBy({ constructor: undefined, type: null }, {}): no overload matches ({} is not an iteratee of the declared types).
- areObjectsEqual (5cb0b788 style) is not exported in es-toolkit's source (src/predicate/isEqual.ts:78, plain function; no export
  in the public indexes); the R6 slice appends export { areObjectsEqual } and its declaration takes (a: any, b: any, stack?), so
  the call checks against its own declaration, as the erratum says.

## Highlights (highlights.tsv)
- perf/style: uniq([-0]) valid (Lean-confirmed); toPath("..") valid; toPath("]") valid; areObjectsEqual valid (internal);
  zip() invalid; zipWith([], 8, undefined) invalid -> four of six.
- docs/test/bench: trimEnd("", "") valid (Lean-confirmed), takeRight([8, 8], -1) valid (Lean-confirmed), divide(0, 1) valid.

## Paper implications (for the evidence owner)
- "86 shown to differ" stays a count of refutations; add that 76 of them are calls the public types admit (all 9 Lean-confirmed).
- "Six commits typed as performance or style changes alter behaviour" becomes four with type-valid counterexamples, one of them in
  an internal function; the zip() example must go (its counterexample is outside the public overloads); toPath stays.
- PROVED counts unaffected (statements quantify over the implementation signature's inputs, a superset).
- Not checked here: the erratum's es-toolkit HEAD and lodash statements (a disclosure-draft matter, not a paper number).
