RESULT: R5 agrees with the delivery: equiv-lean r5-final 373874f6236a, EquivLean.Demo.XLang.Jsmn.jsmn_equiv proved with exactly [propext, Classical.choice, Quot.sound]; kernel replay of its 340-module closure (92 replayed rc 0, 248 reused); tracked files = commit; C and Rust inputs regenerate byte-identical; proof-line total 6,076 equal (role split differs by 31 lines); two wording notes, no proof-status discrepancy.

# R5: jsmn C -> safe Rust (checks/eqr5-20261026T2004Z; copy replay/eqr5-20261026T2004Z; checked 2026-10-26 20:04-20:30Z)

## Copy and commit
- Copy: hard-link base from my 751764f copy (replay/eq-20261025T1449Z), then `rsync -rlD --checksum --delete` from
  ~/equivlean_freeze_373874f-r5final (read only; .git, .tmp, .lake/tmp excluded) and from the live vendor pins
  JimpleLean-20261025T0149Z, coblean-20261024T2306Z, strictts-a15926a, cirlean-28e2380 and the Aeneas backend
  (no change against my 751764f copy for any pin). Worktree HEAD 373874f, git status clean (equivlean.META). Symlinks in
  the copy: 5, all relative and inside it. lake-manifest.json and lakefile.toml identical to 751764f's.
- Tracked files: 1190/1190 equal their blobs at 373874f (git hash-object vs ls-tree); no untracked and no missing file
  outside .lake. `lake build --no-build` of the six jsmn theorem modules: all targets up to date (1887 jobs).
- 751764f..373874f: 108 commits (jsmn work, merges, handoff and README commits); 51 files changed (+13,649/-14):
  34 Lean modules added (31 under Demo/XLang/Jsmn; generated Demo/Gen/Cir/Jsmn/Jsmn and Demo/Gen/Aeneas/JsmnRs/
  {Types,Funs}), 15 example files added (examples/cir/jsmn 6, examples/rust/jsmn_rs 9), README.md and
  HANDOFF_20261023.md modified. No other file changed; no existing Lean module changed (namestatus_751764f_373874f.txt).

## Statement (fresh process; statement/check_statement.out)
- jsmn_equiv : EquivOn (fun x => Long x ∨ CUB cRunI x) (Same C.toksOf) rustRun cRunI, with
  Input = Slice U8 × U32 (the text's bytes and num_tokens), Long x = 2^28 ≤ length, CUB x = ¬ Safe (cRunI x).
- In words: for every byte string js shorter than 2^28 bytes and every num_tokens below 2^32 on which the C run
  terminates without undefined behaviour in cirlean 28e2380's semantics, the Rust run terminates without a panic and
  both give the same outcome: C returns the int that Rust's jsmn_parse returns, and the first max(ret, 0) records of
  C's token array, read as (type, start, end, size), equal Rust's first max(ret, 0) tokens. EquivOn is Equiv for every
  input outside the excluded set; Equiv is simulation both ways (Sim R t s = Safe s -> Safe t and every outcome of t
  has an R-related outcome of s); Safe of a cirlean result = it is .ok; Same of a Rust .error is False.
- The C run (C.cRun): evalCall of jsmn_run (the harness: jsmn_init, then one jsmn_parse) from the module's initial
  memory plus three blocks: the parser (stack, fields undef), the text (read-only array of len signed chars holding
  the bytes; loads of bytes 128-255 give the signed char value, not UB: CBase load_byte) and the token array (stack,
  num_tokens records with undef fields). The Rust run: Aeneas extraction of jsmn_rs: jsmn_init, then jsmn_parse on
  the slice and num_tokens tokens (Undefined, 0, 0, 0).
- Rust.rust_spec: for every input with fewer than 2^28 bytes the Rust run returns .ok with the model's observation
  (no exclusion). C.jsmn_parse_pspec: for byte lists < 2^28 and every n, a C run that returns .ok has the model's return
  value and leaves the model's tokens at the start of the array (partial correctness).
- Out of scope (as stated by the equiv-lean maintainer session and in the model's header): tokens == NULL (counting mode), incremental calls on a
  parser with state, JSMN_PARENT_LINKS / JSMN_STRICT.

## Axioms (fresh process per module; axcheck/axcheck.tsv)
- 32/32 named rows std: jsmn_equiv, Rust.rust_spec, rust_rspec, C.jsmn_parse_pspec, C.parse_string_pspec,
  C.jsmn_parse_primitive_pspec, the 9 TinyRegex rows and the 17 Modernize rows of the equiv-lean maintainer session's RESULT.md (lines 13-44).
- The 34 jsmn sources contain no sorry, admit, native_decide, axiom, implemented_by, extern, unsafe or
  skipKernelTC (only `simp (config := { decide := true })`, kernel-checked).

## Kernel replay (leancheck1.sh via lake env in the copy; pjobs_v3 2 450 150 2)
- Closure of jsmn_equiv's module = union closure of the six theorem modules: 340 modules (EquivLean 49 incl. the 34
  jsmn modules, Aeneas 249, CIR 42).
- delta_reuse.py against eq-20261025T1449Z (pass list = its 86 replayed + 876 reused): 92 replayed, 92/92 rc 0;
  248 reused (olean and closure oleans byte-identical, passed before). Replayed: all 34 jsmn modules, 47 Aeneas/CIR
  import-only roots never replayed before (leanchecker takes them as prefixes, so `Aeneas` re-checked the whole
  Aeneas package, 231 s), EquivLean.Core.Sim (olean differs from my earlier copy although its source is unchanged;
  fresh build) and the 10 modules above it. Slowest jsmn module CString 13.1 s (elaboration 1013 s in the equiv-lean maintainer session's build).
- Negative control through the same wrapper (leancheck1lp.sh): BadCtl rc=1 (kernel rejects), GoodCtl rc=0.
- Not replayed here: the modules of the 26 other named rows outside the jsmn closure (sources unchanged since 751764f;
  replayed at eqA8/eqT on 10-25; their oleans in this tree come from the equiv-lean maintainer session's fresh build).

## Provenance
- jsmn.h = zserge/jsmn 25647e6's jsmn.h byte for byte (c04533e9..., from `git show` in ~/veriforch/targets/jsmn);
  LICENSE identical. jsmn_run.c f06d1101... (5-line harness, JSMN_STATIC, default flags).
- C side (cregen/): the pinned ClangIR clang (upstream-4955d32b, gen.sh flags) on my copies of jsmn_run.c and the
  upstream jsmn.h gives jsmn_run.cir equal to the committed one (98defaed...) after normalising the source-path strings
  (808 occurrences); cir2lean of cirlean 28e2380 (binary 12d2c1ba..., the copy's vendor pin) on the committed .cir gives
  Demo/Gen/Cir/Jsmn/Jsmn.lean except the header comment line; from my .cir also except the module's `name :=` path.
  jsmn_run.cir, jsmn.h and the Gen module are unchanged since 675dedc (my cirpun scan, checks/r5jsmn-scan-20261026:
  7 functions, all counts 0).
- Rust side (rustregen/): Charon + Aeneas (~/equivlean_work/dl/rel/aeneas_bin, nightly-2026-09-17, offline) on my copy
  of the crate: jsmn_rs.llbc identical to the committed file; Types.lean and Funs.lean identical. src/lib.rs
  (4545d817..., 305 lines): no unsafe code (the one occurrence of the word is in a doc comment).
- RustDefs.lean sha256 dbe91c19... = the byte copy named in commit d6421cd.

## Proof size (code lines: non-blank, non-comment, rule of tools/proof_lines.py; jsmn_lines_freeze.tsv)
- Mine: model 798 (Model, ModelLemmas, ModelStep), C side 3,207 (19 C* modules), Rust side 1,980 (RustBase, RustDefs,
  RustMain, RustPrim, RustScan, RustStep), glue 91 (Equiv, Final, RustGlue); total 6,076.
- The equiv-lean maintainer session: model 798, C 3,207, Rust 1,949, glue 122; total 6,076. The split differs only in RustDefs (31 code lines: the
  Rust run and observation), which the equiv-lean maintainer session counts as glue.
- Generated: C module 1,575 lines (1,538 code lines); Aeneas extraction 844 lines (Types 51, Funs 793).

## Tests (re-run from my copies; difftest/)
- Differential test seed 1 (N = 30000): 32,245 cases (39 test calls and 385 literals of jsmn's test/tests.c at 25647e6,
  plus random documents); C harness (gcc 15.2.0, upstream jsmn.h) and Rust driver (rustc 1.99.0, offline) outputs
  identical. Not re-run: seed 2 (202,245 cases; 32,245 + 202,245 = the reported 234,490) and the model-vs-C-binary run
  (322,775 inputs, ASan+UBSan).

## Comparison with the equiv-lean maintainer session's report and RESULT.md (freeze_kit/runs/373874f-r5final-20261026T132255Z)
- Agree: commit; statement; axioms of the six jsmn theorems and 32/32 rows; scope; ClangIR identical at 675dedc and
  373874f; check-time rows (jsmn_equiv closure 34 modules / 4334 s, CString 1013 s, CPStepOpen 922 s, rust_spec 61 s
  over 9 modules) as recorded there; proof-line total. Producer records only (not re-run by me): clean build 877/877,
  sweep Demo+Test 4816 (4808 std + 8 Popcount), Modernize 5827/5827, 7.14 core-h, cost ~$330.

## Wording notes for the paper
1. The report and README say "the only case the proof met is the harness's: num_tokens >= 2^32". That is a fact about
   the proof script's case split, not a theorem: in jsmn_equiv num_tokens is a U32, so that case is outside the
   domain, and the C side's statement is partial, so no theorem says on which inputs the C run is safe. Write the
   exclusion as "unless the C run has undefined behaviour or does not terminate in cirlean's semantics", without
   naming which inputs those are (as for tiny-regex-c).
2. Proof size: quote the total (6,076) or name the RustDefs placement if the split is shown.

## Questions for producers (non-blocking)
- The equiv-lean maintainer session: path and hash of the model-vs-C-binary test records (322,775 inputs) and of the seed-2 difftest outputs, if the
  paper cites them.

## Compute
- About 0.36 core-h (guards in logs/: copy 0.007, lake --no-build 0.001, replay 0.314, axcheck + statement + control
  0.019, Rust regeneration 0.012, C regeneration and difftest < 0.001), all 1-core jobs, at most 2 Lean jobs at a time.
