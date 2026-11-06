# Addendum M, JimpleLean (PREREG_M_v1)

Written by the paper's evidence owner at 2026-10-25T16:24:18Z, before any population mutant is built. This file is never edited;
changes go to DEVIATIONS.md. Copies of the files named here are in `M/jimplelean/`.

- Pin: JimpleLean snapshot 20261025T0300Z (~/jimplelean_work/snapshots/JimpleLean-20261025T0300Z):
  Jimple/Semantics.lean sha256 132f7ef88f84005a3e884dd888e880da9404423b39724723d80883ffbc6cb26e, Jimple/Numeric.lean
  42d9dde774906d0f3eaa8ea8fdb1e25bb18d003cdf09149ce5d0d4dfeebf495d.
- Enumeration tool: enumerate_sites_v2.py, sha256 362a69aa700840345ddc01fe698a9028f5cbadef7168e0da0856ee1f30c876c9.
  The operator maps are in its docstring: ROR, AOR, LOG, NEG, CND, LIT (n -> n + 1), and the Java families FUN and EXC.
- Candidate list: population_v2.tsv, sha256 fa8a182d3017c1334567cfbcd8e5ffaaa80945879b0be914e1e426fa3ccfca09, 452
  candidates. Semantics.lean: AOR 38, CND 27, EXC 8, FUN 4, LIT 38, LOG 13, NEG 2, ROR 34. Numeric.lean: AOR 67, CND 41,
  FUN 10, LIT 113, LOG 3, NEG 18, ROR 36. The evidence owner re-ran the tool on the pinned files and got an identical
  list; every candidate lies inside a def, and every LIT candidate is n -> n + 1.
- Order (M/draw_m.py, bridge jimplelean): order_v2.tsv (columns order, id), sha256
  789b413be987ea3a35fa07cb3e8ef212b722a15c90b07d540571e51079a04ed3. The id column defines the order. In
  order_v2_full.tsv (ee5f8d1aa9ac8ba44fcd69e0d409d80e5871a573de779238c38387a36195283a) the other columns are
  informational, and CSV quoting has dropped the quotes around the EXC strings.
- Suite: corpus_v1, 44 programs (difftest/src 41, difftest/regex 3), each with the JVM's stdout and exit status.
  SHA256SUMS ed5ab379fe1591d222750b3f620020340323cf147fcb4fea7b5c0565f9df6f06 (425 files, checked by the evidence
  owner), MANIFEST.tsv 294cb62419b04059e1fd15dea035ac933ba4ebac83f12a9543ea20376bedb415.
- Runner: run_mutants_v2.py, sha256 396729092a271319f11d2ec68776d3760f8f8112e99067305699dde4e29d98ee (it supersedes
  c8ae7792...). It works on the dedicated tree copy mutants/ws_v1 (equal to 0300Z) and requires the unmutated build to
  match all 44 programs. It takes ids in the order above until 30 mutants have been built. A stillborn mutant (an error
  outside proofs, or a build over 60 minutes) is recorded and skipped. A theorem, lemma or example that fails only
  because of the mutation gets `sorry`, and the replacements are counted (validated on all 18 theorems in jimple-run's
  build closure). Killed means that some program's stdout or exit status differs from the JVM's, a timeout included.
  Each mutant is restored after its run, and the whole run is under coreh_guard_v2 with a 20 core-hour cap.
- Controls (runs/controls_v2_1619.jsonl, sha256 67a3733e7bd820dadfa2d94f6996a0da05f70c65b3f39f0932a0546b1505f6ae;
  controls_v2.tsv 5ca59c3581a7d299f4a71e3beed664f635a9a4f5dc659faf852d6efd7b3acfad): baseline 44/44 at
  2026-10-25T16:20:19Z; a no-op (a docstring edit, Semantics.lean line 70) survived; a known-bad edit outside the
  population (Native.lean line 1288, String.length + 1) was killed, with 22 programs differing.
