# Proof-Carrying Modernization

Lean 4 semantics, front ends, relational verification library, orchestrator, and verification records for the paper
*Proof-Carrying Modernization: LLM Translations of COBOL Batch Programs, Each Proved Against the Original in Lean* by
Tejasvi Singh Tomar (2026).

The paper shows that LLM translations of whole, unmodified COBOL programs into Rust and Java can be proved in Lean 4 to
behave like our executable semantics of the originals on every admissible input: a bounded number of well-formed
records, among other premises. For the eight standalone batch programs of AWS CardDemo that our COBOL front end covered
at the version of the study, all 16 translations are proved, as equivalences for Rust and as refinements with partial
correctness for Java; on a later version of our Java semantics, the Java translations are also proved totally correct.
The verification stack also covers C and C++ (through ClangIR) and a statically typed subset of TypeScript.

- **Paper:** https://doi.org/10.5281/zenodo.23996134 (v1: https://doi.org/10.5281/zenodo.23996135)
- **Full multi-snapshot archive and technical report (63 pages):** https://doi.org/10.5281/zenodo.23996137

## Repository layout

This repository unpacks one snapshot of each component from the Zenodo archive (the latest snapshot of `equiv-lean`,
`coblean`, `JimpleLean`, `cirlean`, and `veriforch`, and the latest `StrictTS` snapshot pinned by `equiv-lean`) so that
the Lean formalizations, front ends, proofs, and check records can be browsed directly:

| Path | Snapshot | Contents |
|---|---|---|
| `equiv-lean/` | `equiv-lean` `5b7bf49` | Relational verification library (`Sim`, `Equiv`, `EquivOn`), cross-language bridges (`EquivLean/Bridge/`), statement generator (`tools/modernize/genstmt.py`), CardDemo migration and composite theorems (`EquivLean/Modernize/`), C-to-Rust ports (`EquivLean/Demo/XLang/`), Apache Thrift wire-format theorems (`EquivLean/Demo/Thrift/`), and relational TypeScript proofs (`EquivLean/Demo/TS/`). |
| `coblean/` | `coblean` `20261029T0854Z` | COBOL front end (`tools/cobolfe`), Lean loader, executable COBOL semantics (`Cobol/Sem/`), symbolic-execution tactic, extracted CardDemo IR files (`examples/carddemo/`), and COBOL-side theorems for the eight standalone CardDemo batch programs (`Examples/`). |
| `jimplelean/` | `JimpleLean` `20261026T2035Z` | Java semantics on Soot's Jimple representation (`Jimple/`), library models, verification-condition generator, and termination calculus (`Jimple/Termination.lean`). |
| `cirlean/` | `cirlean` `7c73739` | C and C++ semantics on ClangIR (`CIR/`), library models, and symbolic executor. |
| `strictts/` | `StrictTS` `6c1f00c` | Statically typed TypeScript subset (`StrictTS/`), TypeScript-to-Lean front end, loop summarization tactics, and semantic diff tool (`tools/difftool/`). |
| `veriforch/` | `veriforch` `T3_final_20261025T173358Z` | Repository-level orchestrator used for the random-sample, security-fix, and Thrift studies. |
| `evidence/` | — | Pre-registrations, addenda, and deviation log (`evidence/prereg/`); per-check summaries and SHA-256 manifests (`evidence/checks/`, starting at `evidence/checks/EARLY_FREEZE_SUMMARY.md`); frozen technical-report hash list (`evidence/freeze/`); and exploratory COBOL run list (`evidence/coblean_runs/`). |
| `harness_study/` | — | Sources and records behind the fuzzing-harness theorems (`sec_ub_artifact.tar.gz` and `sec_ub_artifact_INDEX.txt`). |
| `sources/` | — | Version table (`sources/SNAPSHOTS.tsv`), exclusion counts (`sources/EXCLUDED*.tsv`), and pre/post-normalization SHA-256 table (`sources/NORMALIZED_HASHES.tsv`) for all snapshots in the Zenodo archive. |
| `NORMALIZATION.md` | — | Verbatim copy of the Zenodo archive's normalization record (using the archive's `<component>-<version>/` directory prefixes and `paper/technical_report*` paths). |
| `LICENSE`, `LICENSE-CC-BY-4.0.txt`, `THIRD_PARTY.md`, `third_party_licenses/` | — | Licences (`THIRD_PARTY.md` uses the Zenodo archive's `<component>-<version>/` prefixes). |

The Zenodo archive (https://doi.org/10.5281/zenodo.23996137) additionally contains `paper/technical_report.pdf` (the
63-page technical report) and its LaTeX source (`paper/technical_report_src/`), the archive-level `SHA256SUMS`, and the
full `sources/*.tar.xz` bundles holding every commit and frozen-directory snapshot listed in `sources/SNAPSHOTS.tsv`.
Those bundles include the migration versions on which the primary migration study and Table 4 of the paper ran
(`equiv-lean` `751764f` and `a572cf6`, `coblean` `20261024T2306Z`, `JimpleLean` `20261025T0149Z`), the Java termination
version (`equiv-lean` `9f0e5fb`, `JimpleLean` `20261025T2312Z`), the joint build (`equiv-lean` `04d2599`), the
COBOL-side snapshots for `CBSTM03B`, `CBSTM03A`+`CBSTM03B`, `CSUTLDTC`, and `COBSWAIT` (`pin2306Z-*`, `pinM3-*`,
`pinM7-*`), the C-to-Rust pin (`cirlean` `28e2380`), the standalone `es-toolkit` snapshot (`StrictTS` `10ec829`), and
the final L5 snapshot (`StrictTS` `4bef3c4`).

## Where the CardDemo migration theorems live

In `equiv-lean/EquivLean/Modernize/`, each of the eight standalone CardDemo batch programs (`Cbact01c`, `Cbact02c`,
`Cbact03c`, `Cbact04c`, `Cbcus01c`, `Cbtrn01c`, `Cbtrn02c`, `Cbtrn03c`) has its generated statements and translation
proofs (five of the eight programs—`Cbact01c`, `Cbact04c`, `Cbtrn01c`, `Cbtrn02c`, `Cbtrn03c`—also pass through a
shared field-value model `Model.lean`, with a separate `Glue.lean` in four of them):

- **Rust equivalence theorems (`Equiv`):** `EquivLean.Modernize.<Prog>.Rust.rust`. For `Cbact04c` and `Cbtrn02c`, the
  full-domain theorems reported in Table 1 of the paper are `EquivLean.Modernize.Cbact04c.Every.Rust.rust` and
  `EquivLean.Modernize.Cbtrn02c.Any.Rust.rust`; `Cbact04c.Rust.rust` and `Cbtrn02c.Rust.rust` are the earlier
  restricted-domain theorems (excluding the `DEFAULT` disclosure-group retry in CBACT04C and duplicate transaction IDs
  in CBTRN02C).
- **Java partial-correctness refinement theorems (`Sim`):** `EquivLean.Modernize.<Prog>.Java.java` for the seven
  programs other than `Cbtrn02c`, and the full-domain theorems `EquivLean.Modernize.Cbact04c.Every.Java.java` and
  `EquivLean.Modernize.Cbtrn02c.Any.Java.java` (`Cbact04c.Java.java` is the restricted-domain theorem; for `Cbtrn02c` in
  Java, only the full-domain statement `Cbtrn02c.Any.Java.java` was proved).
- **Java termination (`MTerm`) and contract total-correctness theorems:** `run_term` states `MTerm` for each Java
  program, and `run_total` states total correctness of the Java entry method against its Java contract `runSpec`
  (`EquivLean.Modernize.<Prog>.Java.{run_term,run_total}` for the seven programs other than `Cbtrn02c`, and the
  full-domain theorems `Cbact04c.Every.Java.{run_term,run_total}` and `Cbtrn02c.Any.Java.{run_term,run_total}`).
- **Composite theorems (COBOL safety + target normal termination + equivalence/refinement under the generated
  statement's hypotheses):** `rust_composite` and `java_composite` in `equiv-lean/EquivLean/Modernize/Composite.lean`
  (and `EquivLean.Modernize.Cbact04c.Java.java_composite` in
  `equiv-lean/EquivLean/Modernize/CompositeRestricted.lean`).
- **Exploratory theorems for `CBSTM03B` and `CBSTM03A` (`Cbstm03b/`, `Cbstm03a/`, and COBOL-side copies in
  `EquivLean/Demo/Cobol/`):** `Cbstm03b.{Rust.rust,Java.java,Java.java_terminates,Java.java_total}` proves a single
  `CALL` of the file-access subroutine under a hand-written `Domain` (CP037 digit keys for keyed `ACCTFILE` reads) and
  `OPEN` failure codes `< 100`. `Cbstm03a.{Rust.rust,Java.java,Java.java_terminates,Java.java_total}` (proved on later
  package versions) relates the translations of `CBSTM03A` to the linked pair over a restricted domain (non-empty sorted
  transactions with `≤ 50` card groups of `≤ 10` records each, `< 10^5` cross-references, and successful
  customer/account lookups in the main theorem plus two abort theorems) and omits the 11 `DISPLAY` lines of the initial
  z/OS control-block walk.
- **Mutant refutations:** `equiv-lean/EquivLean/Modernize/MutantRefutations.lean` contains formal `¬ Statement`
  refutations on the termination version of `JimpleLean` for the 3 Java mutants (`J4`, `M2`, `M5r`) that timed out,
  while the other 97 of the 100 seeded mutants fail directly with a Lean error when substituted into the unchanged proof
  scripts.

See `equiv-lean/README.md` for the full theorem table and per-component details.

## Building and checking theorems with `lean` and `leanchecker`

All Lean packages target **Lean `v4.35.0`** (`leanprover/lean4:v4.35.0`). Each package pins its Lean dependencies
(including Mathlib `v4.35.0` where used) in its `lake-manifest.json`. The Rust extractions use Charon `de8736f` and
Aeneas `fdebf20` (providing the `aeneas` Lean backend library), and the C/C++ front end uses ClangIR from `llvm-project`
`4955d32b`; the pre-generated `.llbc`/Aeneas `.lean` files, Soot `.jimple` directories, `.cir` files, and COBOL `.json`
representations used by the proofs are checked into the package trees.

1. **Standalone semantics packages (`coblean/`, `jimplelean/`, `cirlean/`, `strictts/`):**
   In any of these directories, build the library and its example theorems with Lake:
   ```sh
   lake build
   lake build Examples
   ```
2. **Relational library and migration theorems (`equiv-lean/`):**
   In `equiv-lean/` (`5b7bf49`), both `lakefile.toml` and `lake-manifest.json` (as well as `scripts/lean1.sh`) point by
   relative path (`../equivlean_work/vendor/...` and `../equivlean_work/dl/aeneas/backends/lean`) to the five pinned
   encoding packages: `cirlean-7c73739`, `strictts-a15926a`, `coblean-20261028T0109Z`, `JimpleLean-20261026T2035Z`, and
   Aeneas `fdebf20`'s `backends/lean` (`coblean-20261028T0109Z` and `strictts-a15926a` are in `sources/coblean.tar.xz`
   and `sources/strictts.tar.xz` of the Zenodo archive; the unpacked `coblean/` and `strictts/` directories here are the
   later `20261029T0854Z` and `6c1f00c` snapshots).
   - Clean from-scratch `lake build` runs were performed for the migration snapshot `equiv-lean` `751764f` and the joint
     build `04d2599` (in `sources/equiv-lean.tar.xz` of the Zenodo archive; note that compiling `TinyRegex.CCompile` and
     `Jsmn.CString` requires ~90 GiB and ~80 GiB of RAM).
   - The `equiv-lean` `5b7bf49` (`unified-next3`) snapshot unpacked here was checked by recompiling modified modules
     against carried-over `.olean` files from earlier rounds rather than by a clean from-scratch `lake build` (specifically,
     `TinyRegex.Model`'s carried-over `.olean` differs in renumbered match auxiliaries referenced by downstream
     `TinyRegex` modules; see `evidence/checks/next3el2-20261030T174813Z/SUMMARY.md` and
     `evidence/checks/next3el3-20261030T215554Z/SUMMARY.md`).
   - Once the pinned dependencies are placed at the paths in `lakefile.toml` and `lake-manifest.json` (and `W` in
     `scripts/lean1.sh` is pointed at your work directory), check individual modules with `lake env lean <path/to/File.lean>`
     or `scripts/lean1.sh <path/to/File.lean>`.
3. **Axiom check and kernel replay (`leanchecker`):**
   - Printing a theorem's axioms with `#print axioms <TheoremName>` should list only Lean's three standard axioms
     (`propext`, `Classical.choice`, `Quot.sound`) for every theorem reported as a result in the paper and technical
     report (one un-reported theorem in `coblean` outside the migration closure uses `bv_decide`'s native-evaluation
     axiom, and `Demo/Aeneas/Popcount.lean` in `equiv-lean` tests `bv_decide`).
   - To replay the compiled `.olean` modules in the kernel from scratch, run:
     ```sh
     lake env leanchecker --fresh <ModuleName>
     ```
     (or `lake env leanchecker` across the package's build directory).

## Licences

Our code is licensed under the Apache License 2.0 (`LICENSE`). The check records and documentation in `evidence/` are
licensed under CC BY 4.0 (`LICENSE-CC-BY-4.0.txt`). Third-party files keep their own licences (`THIRD_PARTY.md` and
`third_party_licenses/`).
