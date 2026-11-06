# equiv-lean: relational verification across five Lean encodings

equiv-lean proves that two programs behave the same,

    ∀ x, f_target x ≈ f_source x,

when the programs come from different Lean front ends:

| language | front end | Lean meaning of a function |
|---|---|---|
| C / C++ | cir2lean (ClangIR) | `CIR.evalCall ctx f args m : Res (Exit × Mem)` |
| COBOL | coblean (`cobol_program`) | `Cobol.Program.run P env fuel st : Signal × State` |
| Java | jimple2lean (Soot + `jimple_import`) | `Jimple.MExec P m args σ o` (big-step relation) |
| TypeScript | ts2lean (StrictTS) | `JS.exec (callFun I P f vs) w : Option (Except Exc α × World)` |
| Rust | Aeneas (Charon) | `f x : Aeneas.Std.Result α` |

It covers both use cases with the same theorems and tactics:

* **same-language changes** (a pull request, a refactor, a library upgrade): old ≡ new, or
  "new differs from old only where old was wrong";
* **migrations** between languages: COBOL → Java, COBOL → Rust, C → Rust, TypeScript ↔ Rust.

None of the encodings is modified. equiv-lean depends on pinned copies of them and works on
their native representations; each one keeps its own symbolic executor, which equiv-lean
drives.

## The idea in one paragraph

Every encoding's program meaning is wrapped in an outcome semantics, `Behaves C O`. It has
two predicates: `Runs c o` (the program can finish with observable outcome `o`) and
`Safe c` (it cannot go wrong).
Equivalence is a property of two such semantics,

    Sim R t s  :=  Safe s → Safe t ∧ ∀ ot, Runs t ot → ∃ os, Runs s os ∧ R ot os
    Equiv R t s := Sim R t s ∧ Sim R⁻¹ s t

so one statement covers a Rust function against a COBOL program, or two versions of a C++
function. A proof runs the source forward, in a hypothesis `wp s P`, and the target
backward, in the goal `wp t (fun ot => ∃ os, P os ∧ R ot os)`, each with its own
encoding's executor. When both reach a loop, the loops are paired into one product loop
with a coupling invariant. The pairing is the lemma `wp_loop_rel`: when the source is
known to terminate it needs no variant, because the source's termination bounds the
target's iterations (the standard lock-step argument; see "Related work"). Branches of the two programs are aligned by case splitting, and
contradictory pairs of paths are pruned automatically. What is left are pure leaf goals
about values (`Int`, `BitVec`, `Decimal`, `List`), closed by `simp`, `omega` or
`bv_decide`.

## What a theorem means

`Sim R t s` is a statement about the runs on which the **source** cannot go wrong. What
"going wrong" means is fixed per encoding by its `Behaves` instance:

| encoding | outcome (observable) | goes wrong (no obligation) |
|---|---|---|
| cirlean | `Exit × Mem`: return value or exception, final memory | undefined behaviour, divergence |
| Aeneas | `Except Error α`: value or panic (overflow, bounds, …) | divergence |
| StrictTS | `Except Exc α × World`: value, thrown exception or panic, final world | divergence |
| coblean | `Signal × State`: stop/normal, abends `invalidData`/`divByZero` | out of fuel, undefined faults (size error result undefined, overlap, range, unsupported) |
| JimpleLean | normal return or uncaught exception, final state | `wrong`; **divergence is invisible** (big-step), so a Jimple *target* gives partial correctness |

So `Equiv (· = ·) f_new f_old` says: on every input, the two versions are safe on the same
inputs, and where they are safe they have the same outcomes, panics and exceptions included.
For two total deterministic programs, equivalence is equality of outcomes wherever either
side is defined (`Equiv.runs_iff`, `Equiv.option_eq`). If both sides go wrong on an input, it
carries no obligation (as for undefined behaviour in C). Use `EquivOn Bad` to state
explicitly which inputs are excluded. `EquivOn.changed_subset` is its contrapositive: the
versions differ only on `Bad`.

## Results on real front-end output

Every theorem below is about code produced by the actual front end (clang -fclangir +
cir2lean, Charon + Aeneas, the StrictTS translator, `cobol_program` on the IR JSON, javac +
Soot + `jimple_import`), not hand-written models. "Std" = only Lean's standard axioms.

| file | statement | kind |
|---|---|---|
| `Demo/Cir/StraightLine.lean` | C++ `clamp`/`max3`: if-chains ≡ `std::min`/`std::max` (one-line `equiv_cir`) | PR diff, branches, library models |
| `Demo/Cir/LoopRefactor.lean` | C++ `sum_below`: `for` ≡ `while` | PR diff, lockstep loops, no variant |
| `Demo/Cir/EarlyExit.lean` | C++ search loop with early `return` refactored | PR diff, early exit in a loop |
| `Demo/Cir/VectorLoop.lean` | C++ `std::vector` index loop ≡ range-`for` (iterator models), no overflow assumption: both overflow at the same element | PR diff, containers, lockstep |
| `Demo/Cir/AutoCouple.lean` | the same C++ refactors with NO coupling written (plain `equiv_cir`): `for`≡`while`, a bit-count loop with an extra guarded branch | automatic product construction |
| `Demo/Cir/{AutoEarlyExit,AutoBound,AutoCountBits}.lean` | with NO coupling written: the early-return loop (both directions; the generated coupling keeps `r = -1`), `i < n` → `i != n` (the generated bound `i ≤ n`), and the guarded bit-count loop as a full `Equiv` | automatic product construction |
| `Demo/Cir/AutoVector.lean` | with NO coupling written: the `std::vector` index loop ≡ range-`for` of `VectorLoop.lean`, `Equiv` by plain `equiv_cir` (the iterator paired with the index, bounded by the caller vector's length) | automatic product construction, containers |
| `Demo/Cir/BugFix.lean` | C++ average: `EquivOn Bad` with Bad = old version's overflow (UB) inputs | conditional equivalence |
| `Demo/Cir/PtrArgs.lean` | pointer arguments, with NO coupling or memory fact written (plain `equiv_cir`): `sum_arr` (`for` → `while` over `a[i]`), `swap` with its writes in the other order (`a` and `b` may alias), `get_or` (`if (p == 0)` → `p ? *p : d`); each pointer only bounded to the caller's blocks | PR diff, caller memory, aliasing |
| `Demo/Aeneas/AutoCouple.lean` | Rust PR diffs with NO coupling written (plain `equiv_aeneas [defs]`): SumPR and FindPR both directions (the generated couplings are the hand-written ones), and `examples/rust/autopr`: loop variables reordered with `!=`, flag + `break` instead of early return, a temporary hoisted out of the loop | automatic product construction |
| `Demo/Aeneas/SpecAuto.lean` | Rust functions against Lean specifications with NO loop invariant written (`aeneas_spec`): record maps/filters/folds/lookups building `Vec`s, CBACT04C's lookups, a CBACT02C-shaped listing (`Vec<Vec<u8>>` lines, zero-padded digits) | spec proofs for the CardDemo translations |
| `Demo/Aeneas/SumPR.lean` | Rust `sum` v2 ≡ v1, identical panics included; saturating v3: `EquivOn Bad`, Bad = exactly where v1 panics | PR diff, loops, panics |
| `Demo/Aeneas/SumUnroll.lean` | Rust loop unrolled by 2 ≡ original, via `sim_loop_stutter` | asynchronous product |
| `Demo/Aeneas/{FindPR,VecPR,MidPR}.lean` | early `return`, `Vec::push` + strength reduction, midpoint overflow fix | PR diffs |
| `Demo/Aeneas/{Popcount,Fnv,AcctIntSpec}.lean` | loop vs closed form (SWAR, fold), Rust `accrue` = model | loop vs specification |
| `Demo/TS/PrDiff.lean` | TypeScript `sum` (index loop ≡ `for…of`), `contains` (early `return` ≡ flag + `break`), equal outcomes (NaN, ±0, exceptions) | PR diff, lockstep loops |
| `Demo/TS/DoWhile.lean` | TypeScript `do…while` refactor, every F64 input (both sides diverge on +∞) | PR diff, divergence |
| `Demo/TS/{ScaleFresh,FilterLoop}.lean` | map fusion; `filter`+`map` → one loop with `push`: equivalent modulo fresh allocation (`ArrObs`), while plain equality of worlds provably fails | PR diff, allocation |
| `Demo/TS/EsToolkit.lean` | es-toolkit's perf commits 4ec747ea (`difference`) and 576b136a (`intersection`): `firstArr.filter(x => !secondArr.includes(x))` → a `Set` built from `secondArr` and `has`, equivalent modulo the fresh `Set` (`Equiv (ArrObs w.next)`) at `T := number`, see below | real library history, `Set` model, allocation |
| `Demo/TS/AutoCouple.lean` | TS `sum`, `contains`, `do…while` refactors with NO coupling written (`equiv_ts_auto`) | automatic product construction |
| `Demo/TS/{AutoFnvXLang,AutoPolyHash}.lean` | TypeScript ↔ Rust migrations with NO coupling written (`equiv_ts_rust`): FNV-1a (u32 path) and a polynomial byte hash (`Math.imul`, `| 0` against i32 `wrapping_*`); the TS slots are paired with the Rust loop state, as the doubles of the Rust integers | automatic product construction across languages |
| `Demo/TS/FnvXLang.lean` | TypeScript FNV-1a (`Math.imul` over `Uint8Array`) ≡ Rust `fnv1a32` | migration, lockstep across languages |
| `Demo/Cobol/AcctIntPatch.lean` | COBOL patch `COMPUTE … ROUNDED = A / B` → `DIVIDE A BY B GIVING … ROUNDED`: behaviour-preserving on every valid record (different intermediate precision, same result); the wrong patch (no `ROUNDED`) fails | PR diff (IR of the patched program derived from the extractor output) |
| `Demo/Cobol/AcctIntAeneas.lean` | COBOL ACCTINT (PIC/COMP-3, ROUNDED, SIZE ERROR) ≡ Rust scaled-integer rewrite; Rust never panics on valid records | migration, PIC ↔ Decimal ↔ i64 |
| `Demo/Cobol/RecSumAeneas.lean` | COBOL RECSUM batch loop (`PERFORM … UNTIL` end of file) ≡ Rust loop over the records, the two loops paired in lockstep across languages; Rust never panics on files ≤ 9999 records | migration, cross-language product loop |
| `Demo/Cobol/Cbact04cRust/Sim.lean` | COBOL CBACT04C (CardDemo, unmodified) → a Rust port of its business logic (slices and `Vec`, `i64` cents, `u128`/`u16` keys; Charon + Aeneas): for **every** input the Rust function never panics and returns exactly the COBOL program's `REWRITE` records, decoded, in order, and its number of transaction records; `Equiv` (`cbact04c_rust_equiv`; for every input Rust slices holding the same records exist, `cbact04c_rust_equiv_exists`), the same COBOL theorem as the Java migration | migration of a real program to a second target, all inputs, keyed files ↔ slices |
| `Demo/Jimple/{AutoStats,AutoSearch}.lean` | Java PR diffs with NO pairs or coupling written (`equiv_jimple`): PrDiffStats both ways and `Equiv`, and an early `return` → flag + `break` search; loop heads paired in order, the coupling found by running both methods on sampled inputs in JimpleLean's interpreter, then proved | automatic product construction (data-driven, kernel-checked) |
| `Demo/Jimple/PrDiffStats.lean` | Java `total`: index loop → enhanced `for` over `int[]` (real javac + Soot output): `Equiv (· = ·)`, same result and final state, `int` overflow included; lockstep at paired cut points, no termination assumption | PR diff, loops (Jimple relational product) |
| `Demo/Jimple/PrDiffClamp.lean` | Java `clamp`: explicit ifs → `Math.max(lo, Math.min(x, hi))` (real javac + Soot output): `Equiv (· = ·)` for `lo ≤ hi`, both directions through the Jimple relational product (`ProdVC`, `sim_of_prodVC`); the source executed through the `Math.min`/`Math.max` models | PR diff, library calls (partial correctness) |
| `Demo/Jimple/AcctIntMigration.lean` | COBOL ACCTINT → Java rewrite (`BigDecimal`, HALF_UP; real javac 17 + Soot output): the Java method simulates the COBOL run, fields ↔ `BigDecimal` via the shared `Decimal` model | migration, PIC ↔ BigDecimal (partial correctness on the Java side) |
| `Demo/Jimple/Cbact04c/Migration.lean` | COBOL CBACT04C, AWS CardDemo's interest calculator, unmodified (five files, keyed reads, `REWRITE`) → a Java port of its business logic (files as arrays and results; javac 17 + Soot): for **every** input (any number of accounts, each with any number of category balances; any rates, storage, clock), every terminating run of the Java method returns, in order, the COBOL program's `REWRITE` records decoded and its number of transaction records (`cbact04c_sim`; for every input a Java heap holding the same records exists, `cbact04c_sim_exists`); both leave the last account unposted (the defect of CardDemo issue #64); COBOL side: coblean's `cbact04c_all` | migration of a real program, all inputs, keyed files ↔ objects, `long` ↔ `PIC S9(n)V99` (partial correctness on the Java side) |
| `Demo/Jimple/Cbact04c/Fixed/Migration.lean` | the same COBOL program → a Java port with the defect fixed (after the loop it posts the last account): for **every** input, every terminating run returns the COBOL program's `REWRITE` records (decoded, in order), then the last account posted by coblean's own `Acc.posted` (`missedRewrite`), and the COBOL program's number of transaction records (`cbact04c_fixed_sim`, `cbact04c_fixed_sim_exists`): the fix changes exactly the defect | migration with a bug fix, the difference stated exactly (partial correctness on the Java side) |
| `Demo/XLang/Cbact04cJavaRust.lean` | the Java port ⊑ the Rust port of CBACT04C, by `Sim.trans` through the COBOL program: for **every** input of coblean's `cbact04c_all`, every terminating run of the Java method returns, in order, the accounts the Rust function returns (`long` fields = the Rust integers, the group id the same EBCDIC bytes as UTF-16 units and as a `u128`) and its transaction count; the statement mentions no COBOL value (`cbact04c_java_rust`, `cbact04c_java_rust_exists`) | composition of two migrations across three encodings (partial correctness on the Java side) |
| `Demo/XLang/Crc32/Equiv.lean` | TypeScript ↔ Rust on real library code: pako 1.0.11's `crc32` (as TypeScript, StrictTS front end; the table computed when the module loads) ≡ crc32fast 1.4.2's baseline `update` (unmodified Charon + Aeneas output: slice-by-16 unrolled ×4 over a 16 × 256 table, then a byte loop), for **every** start value and byte range (`crc32_equiv`, `crc32_equiv_init`); each side is proved equal to zlib's CRC-32 (`Crc32/TS.lean` `crc32_spec`, also the module's exact console output; `Crc32/Rust.lean` `update_fast_16_eq`: never panics, slice-by-16 by GF(2) linearity) | migration, loops of different shapes through a specification |
| `Demo/XLang/ReverseBits.lean` | C `reverse_bits` → Rust, loops paired in lockstep, coupling "same words" only | migration, product loop, BitVec |
| `Demo/XLang/Point.lean` | C `struct Point` → Rust `struct Point`: Rust refines C; `Equiv` off C's UB inputs | migration, structs |
| `Demo/XLang/VecSum.lean` | C++ `std::vector<int>` sum → Rust `Vec<i32>` sum, loops in lockstep; `Equiv` off C++'s overflow inputs | migration, collections |
| `Demo/XLang/TinyRegex/Final.lean` | kokke/tiny-regex-c (C, unmodified) → safe Rust (an LLM translation): `re_match` equal on every pair of C strings with the text shorter than 2^28 bytes, off the C's UB inputs; the Rust never panics on any input (see below) | migration of a real C library, recursion, static buffers |
| `Demo/XLang/Jsmn/Final.lean` | zserge/jsmn (C, unmodified, default configuration) → safe Rust (written by equiv-lean's agents in an Aeneas-friendly form): after `jsmn_init`, one `jsmn_parse` returns the same value and fills the same tokens on every input shorter than 2^28 bytes, off the C's UB inputs; the Rust never panics there (see below) | migration of a real C library, token arrays, nested containers |
| `Demo/XLang/Adler32/Final.lean` | zlib's Adler-32 (`adler32.c` of zlib 1.3.1, unmodified, default configuration) → safe Rust (written by equiv-lean's agents in an Aeneas-friendly form): `adler32_z` and `adler32` return the same value on every input with `len` < 2^28 except `Z_NULL` with `len == 1` (the C's only undefined behaviour there), `adler32_combine` and `adler32_combine64` on every input; on all of these the C run returns and the Rust never panics (see below) | migration of a real C library, checksums, 64-bit unsigned arithmetic |

### tiny-regex-c, C → safe Rust (`EquivLean/Demo/XLang/TinyRegex/`)

kokke/tiny-regex-c (`examples/cir/tinyregex/re.c` @ f2632c6: `re_compile` into static buffers, a matcher
whose `matchpattern`, `matchstar`, `matchplus` and `matchquestion` call each other recursively), translated
into safe Rust by verif-orchestrator's guided LLM arm (`examples/rust/tiny_regex`, unchanged; the style
guide fixes the API and the subset Aeneas accepts) and checked by its differential runs. `re_match_equiv`:
for every pattern and text that are C strings (no NUL byte) with the text shorter than 2^28 bytes, the
Rust `re_match` returns exactly the C `re_match`'s value and final `*matchlength` (the C called from
program start, cirlean's semantics), unless the C run has undefined behaviour (`CUB`: here matchstar's
`text--` before the start of the text, and `&re_compiled[31]` after a fully matched 29-object pattern).
Both sides are proved against one functional model of the C algorithm (`Model.lean`, validated against
the C binary): the Rust side through Aeneas (`RustFinal.re_match_spec`; `re_compile_eq` for every pattern;
`RustNoPanic.re_match_total`: no panic on any input at all), the C side with the C run in the hypothesis
(`C.re_compile_spec`, `C.matchpattern_pspec` by induction over the pattern index, `C.re_match_pspec`).
Bytes ≥ 0x80 in a `CHAR` token never match (signed `char`), and `*matchlength` keeps its value after a
failed match: both are part of the C's behaviour, and the Rust reproduces them.

### jsmn, C → safe Rust (`EquivLean/Demo/XLang/Jsmn/`)

zserge/jsmn (`examples/cir/jsmn/jsmn.h` @ 25647e6, byte for byte: a header-only JSON tokenizer that fills a
caller's array of tokens in one pass, keeping the current parent in `toksuper` and searching back for the open
object or array at `}`, `]` and `,`) in its default configuration (neither `JSMN_PARENT_LINKS` nor
`JSMN_STRICT`), translated into safe Rust by equiv-lean's agents in an Aeneas-friendly form
(`examples/rust/jsmn_rs`: no `unsafe`, loops as `while` over explicit state with no early return inside them,
the tokens as `&mut [JsmnTok]`), unlike tiny-regex-c's pipeline translation; the two agree on 234,490 inputs
run natively (jsmn's tests and random, mutated and truncated JSON). `jsmn_equiv`: for every byte string shorter
than 2^28 bytes and every `num_tokens`, `jsmn_init` followed by one `jsmn_parse(parser, js, len, tokens,
num_tokens)` gives in Rust exactly what it gives in C (cirlean's semantics): the same return value and the same
first `min(max(ret, 0), num_tokens)` tokens (type, start, end, size), unless the C run has undefined behaviour
(`CUB`; the only case the proof met is the harness's: `num_tokens` ≥ 2^32 does not fit `jsmn_parse`'s
`unsigned int`). As in the C, a NUL byte ends the text. Out of scope by design: the counting mode
(`tokens == NULL`), incremental calls on a parser that already holds state, and the non-default flags. Both
sides are proved against one functional model that follows `jsmn.h` function by function (`Model.lean`;
`parse js n` is the observation itself), validated against the C binary on 322,775 inputs (jsmn's test calls
and every prefix of them, every byte string up to length 4 over 15 symbols and of length 5 over 10, and 105,000
random JSON-like texts; identical outputs, and an ASan+UBSan build reports nothing). The Rust side goes through
Charon + Aeneas fdebf20 (`Rust.rust_spec`: below 2^28 bytes the Rust run returns, so it does not panic, with the
model's observation); the C side through ClangIR (clang upstream-4955d32b `-fclangir -O0`, cir2lean of cirlean
28e2380) with the C run in the hypothesis: contracts for `jsmn_parse_string`, `jsmn_parse_primitive` and the
token allocation, then `jsmn_parse`'s loop by an invariant with one lemma per byte class, ending in
`C.jsmn_parse_pspec`; `rust_equiv_c_of` and `cspec_of_pspec` compose them. The ClangIR's only pointer casts are
the null pointer constants of the `tokens == NULL` tests, so no width-mismatched scalar access arises: cirlean
treats those as undefined behaviour, see Limits. Proof size in code lines (Gen excluded): model 798, C side
3,207, Rust side 1,949, glue 122.

### zlib adler32, C → safe Rust (`EquivLean/Demo/XLang/Adler32/`)

zlib's Adler-32 checksum (madler/zlib v1.3.1 at tag commit 51b7f2a: `examples/cir/zlib_adler32/adler32.c` byte for
byte, with zlib's own `zlib.h`, `zconf.h` and `zutil.h`) in its default configuration (no `NO_DIVIDE`, so `MOD` is
`% BASE`) on x86_64 LP64 (`uLong` is 64 bits): `adler32_z(adler, buf, len)`, its `uInt` wrapper `adler32`, and
`adler32_combine` / `adler32_combine64`. The C splits the checksum into two sums, adds at most NMAX = 5552 bytes
between two reductions modulo BASE = 65521 (unrolled as `DO16`), and takes two shortcuts that reduce by subtracting
BASE once: from both sums when `len == 1`, from the first sum when `len < 16` (the second sum takes `% BASE` there).
Translated into safe Rust by equiv-lean's agents in an Aeneas-friendly form (`examples/rust/adler32_rs`: no
`unsafe`, `while` loops with no `return` inside, `Option<&[u8]>` for `buf`, the unrolled sums as a helper that adds
the same bytes in the same order). A re-runnable native differential test (`difftest/run.sh`: gcc -O2 on the
unmodified `adler32.c` against cargo --release) finds the two identical on 27,383 cases (seed 20261027) and 207,383
cases (seed 2). It reports FAIL on a copy with `% BASE` in place of the `len == 1` subtraction.
`Final.lean` has one theorem per function, in cirlean's semantics. `adler32_z_equiv_explicit` and
`adler32_equiv_explicit`: for every `adler` and every buffer, or `Z_NULL` with any `len`, the Rust returns exactly
the C's value, except on a buffer of 2^28 bytes or more (or `Z_NULL` with `len` ≥ 2^28) and on `Z_NULL` with
`len == 1`, where the C reads `buf[0]` and the Rust returns 1. On every other input the C run returns, with no
undefined behaviour (`C.cub_z_iff`, `C.cub_32_iff`); `adler32_z_equiv` and `adler32_equiv` state the same with
`CUB` (the C has undefined behaviour) in place of the `Z_NULL` case. `adler32_combine_equiv` and
`adler32_combine64_equiv`: for every `adler1`, `adler2` and `len2`, the C run returns and the Rust returns exactly
the C's value. The Rust never panics on any of these inputs. Both sides are proved against one functional model
that follows `adler32.c`'s paths (`Model.lean`: `adler32z` and `combine`). The model keeps the single subtractions
of the `len == 1` and `len < 16` paths, which differ from `% BASE` when an initial sum is at least BASE. It was
validated against the gcc build on 11,936 cases (the lengths 0, 1, 2, 15, 16, 17, 5551, 5552, 5553, 11104 and
11105 with random buffers, and random initial values including sums ≥ BASE): identical outputs, and an
ASan+UBSan build reports nothing.
`ModelLemmas.lean` gives the NMAX-block invariant: after each block, the sums are closed forms modulo BASE. The Rust
side goes through Charon + Aeneas fdebf20. The generated functions return pure functions of the numbers on every
argument whose `buf` holds `len` bytes or is `Z_NULL`, so they never panic (`adler32_z_eq`, `adler32_eq`,
`adler32_combine_eq`, `adler32_combine64_eq`). These pure functions are the model (`rustZ_eq`, `rustCombine_eq`;
the sides' theorems `z_rspec`, `run32_rspec`, `cb_rspec`, `cb64_rspec`). The C side goes through ClangIR (clang
upstream-4955d32b `-fclangir -O0` with zlib's own defines for `adler32.o`, `-D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN`;
`-O0` replaces zlib's `-O3`, as for jsmn and musl; cir2lean of cirlean 28e2380), with total contracts that hold
from any memory and leave the caller's blocks unchanged. `C.adler32_z_buf`: on a read-only array of fewer than
2^28 bytes, `adler32_z` returns the model's value, by the code's paths (one byte; fewer than 16; 16 or more: the
loop over blocks of NMAX bytes with its sixteen-byte inner loop, then the remaining bytes), with loop invariants
that state the model's sums of the bytes read so far. On `Z_NULL` it returns 1 when `len ≠ 1`
(`C.adler32_z_null`) and has no outcome when `len == 1` (`C.adler32_z_null_one`). `adler32` calls `adler32_z`
(`C.adler32_buf`, `C.adler32_null`, `C.adler32_null_one`). `C.adler32_combine__spec` covers `adler32_combine_` for
every input: the symbolic executor runs each of its paths (the sign of `len2`, then each conditional subtraction
of BASE or 2·BASE). `adler32_combine` and `adler32_combine64` call it (`C.adler32_combine_spec`,
`C.adler32_combine64_spec`). On the Rust side's inputs, run from the module's initial memory, these give
`C.cspec_z`, `C.cspec_32`, `C.ctotal_cb` and `C.ctotal_cb64`; `rust_equiv_c_of` and `rust_equiv_c_total_of`
compose the two sides. Proof size in code lines (Gen excluded): model 157, C side 837, Rust side 825, glue 117.

### CardDemo's batch layer, modernized and certified (`EquivLean/Modernize/`)

Nine COBOL batch programs of AWS CardDemo and its file-access subprogram CBSTM03B, unmodified, are each
translated to Java and to Rust by an LLM pipeline (verif-orchestrator's guided arm; javac + Soot +
`jimple_import`, Charon + Aeneas). Each translation is proved to behave as the COBOL run (coblean's
`cobol_program` on the IR JSON).

The statements are generated, not written. `tools/modernize/genstmt.py` derives the schemas, the initial
storage, the input relations and `Rel` from the copybook ↔ record mapping and coblean's IR.
`tools/modernize/genall.sh` regenerates all of them, and `git diff` must stay empty. `Rel` relates the
DISPLAY lines (CP037 text), the records written and rewritten (decoded), RETURN-CODE and the abend flag;
for CBSTM03B it relates the state kept between calls instead, and for CBSTM03A it drops the 11 DISPLAY lines
of the initial z/OS control-block walk (`PSA → TCB → TIOT`; see below).

Rust: `theorem rust : Statement`, an `Equiv` (inputs below 2^28 records, Aeneas' `usize`). Java:
`theorem java : Statement`, a `Sim` (every terminating run; JimpleLean's big-step semantics; inputs below
2^27 elements, Java's `int`-indexed collections; classes initialized). Every theorem uses only `propext`,
`Classical.choice`, `Quot.sound`.

| program | inputs covered (coblean's all-input theorem) | Rust (s) | Java (s) |
|---|---|---|---|
| CBACT01C | every account file; OCCURS items as arrays, variable-length records, the COBDATFT call | 276 | 3364 |
| CBACT02C | every card file (listing) | 65 | 383 |
| CBACT03C | every cross-reference file (listing) | 134 | 851 |
| CBACT04C | every input of `cbact04c_every`: < 999 999 category balances, account runs contiguous; the DEFAULT disclosure-group retry, the abends | 1109 | 1468 |
| CBCUS01C | every customer file (listing) | 94 | 355 |
| CBTRN01C | every daily transaction file with its lookups | 122 | 557 |
| CBTRN02C | every input of `cbtrn02c_any`: < 10^9 transactions, repeated ids included (the WRITE fails, the program abends) | 615 | 3112 |
| CBTRN03C | every input of `cbtrn03c_every`: < 10^7 transactions and a date record; failed lookups abend | 961 | 10010 |
| CBSTM03B (subprogram) | one CALL, for every input of `cbstm03b_call`: any state kept between calls (four files, their FD record areas and FILE STATUS items), any parameter area, any OPEN outcomes; under the premises listed below | 91 | 4173 |
| CBSTM03A (with CBSTM03B) | every input of `stm_run_sorted` / `stm_run_abort_cust` / `stm_run_abort_acct`: non-empty sorted transactions (≤ 50 card groups, ≤ 10 per group), < 10^5 cross-references; z/OS control-block walk, `SET ADDRESS OF`, `ALTER`, `STRING`, plain-text and HTML statements, failed lookups abend | 328 | 2280 |

Theorem names: `EquivLean.Modernize.<Prog>.Rust.rust` and `….Java.java` (with composite safety + termination +
equivalence/simulation theorems `rust_composite` and `java_composite` in `EquivLean/Modernize/Composite.lean`).
The two widened statements use `Cbact04c.Every.*` and `Cbtrn02c.Any.*`; the narrower `Cbact04c.{Rust,Java}` and
`Cbtrn02c.Rust` theorems are kept.

Check time is the summed build times of the theorem's own modules: the COBOL theorem copy, statement,
model, glue, generated code and translation proof. It is measured on one core from a clean checkout of
751764f; for CBSTM03B and CBSTM03A, with lean1 on r4-cbstm03b and r4-cbstm03a.

Each program has three parts (`Modernize/<Prog>/`, `tools/modernize/RECIPE.md`):
- a field-value model mirroring the translation (for the nine batch programs, also validated against
  coblean's interpreter);
- glue from coblean's theorem to the model;
- the translation proved against the model.

Mutation test of the eight batch programs' certificates: about six seeded semantic mutants per translation
(rounding mode, loop bound off by one, truncation width, swapped field, dropped fallback or abend), each
changing the output on a valid input. Every one makes its unchanged theorem fail: Rust 50 of 50, Java 50
of 50 (`EquivLean/Modernize/MutantRefutations.lean` also gives formal `¬ Statement` refutation proofs for the
hardest semantic mutants). The narrow CBACT04C and CBTRN02C theorems miss the mutants on their excluded paths
(the dropped DEFAULT retry, an unreachable duplicate-id abend); the widened ones reject them.

#### The Java translations, totally correct

The theorems above prove the Java side for terminating runs (`Sim`). Their total-correctness companions
keep those theorems unchanged and add, for each program, that the Java translation also terminates. They need
JimpleLean's termination modules (since 20261025T2312Z): `Jimple/Termination.lean` and `Jimple/TermSplit.lean`
define must-termination `MTerm P m args σ` (every execution of the call terminates, `.choose` branches included)
with its verification conditions. `run_total` (or `java_total`) states: for every argument list and state that
meet `runSpec.pre`, the precondition under which `java` applies the contract of the translation's entry method,
the method has an outcome (`∃ o, MExec Gen.prog runRef args σ o`) and every outcome meets `runSpec.post`. It is
`total_of_sat_mterm` of the partial-correctness contract and `MTerm`, proved by a thin twin of each proof
segment (the same invariants, plus a variant that decreases from cut point to cut point) and a termination proof
for every callee contract. JimpleLean's session wrote these proofs; each file names its source in its first line.

| program | total-correctness companion of `java` |
|---|---|
| CBACT01C | `EquivLean.Modernize.Cbact01c.Java.run_total` |
| CBACT02C | `EquivLean.Modernize.Cbact02c.Java.run_total`, from JimpleLean's `run_total` over its own contract (`Modernize/JL/`) |
| CBACT03C | `EquivLean.Modernize.Cbact03c.Java.run_total`, likewise from `c3_run_total` |
| CBACT04C | `EquivLean.Modernize.Cbact04c.Every.Java.run_total`; for the narrower statement `Cbact04c.Java.run_total` |
| CBCUS01C | `EquivLean.Modernize.Cbcus01c.Java.run_total`, likewise from `cu_run_total` |
| CBTRN01C | `EquivLean.Modernize.Cbtrn01c.Java.run_total` |
| CBTRN02C | `EquivLean.Modernize.Cbtrn02c.Any.Java.run_total` |
| CBTRN03C | `EquivLean.Modernize.Cbtrn03c.Java.run_total` |
| CBSTM03B | `EquivLean.Modernize.Cbstm03b.Java.java_total`, with `java_terminates` (one call; see below) |
| CBSTM03A | `EquivLean.Modernize.Cbstm03a.Java.java_total`, with `java_terminates` (see below) |

#### CBSTM03B: one call of a subprogram

CBSTM03B is the file-access subprogram of CardDemo's statement job. Its caller, CBSTM03A, is covered as the
full statement job below; here CBSTM03B is proved by itself for one call (`genstmt.py --subprogram`), since its
storage and files persist from one CALL to the next.

Each translation keeps a state between calls:
- one struct / object per file, with `open`, `recs`, `pos` and `eof`;
- the four FD record areas;
- the four FILE STATUS items.

The call is passed the parameter area `LK-M03B-AREA` (DD name, operation, return code, key, key length,
record buffer) and the environment's OPEN outcomes.

The statement says: take any environment, storage `m` and files `fs` meeting the hypotheses of coblean's
`cbstm03b_call` (record lengths; for a keyed READ, a key length of 1 to 25 and a numeric ACCTFILE key), and
any translation state, area and OPEN outcomes related to them. Then the call and the COBOL run, which ends
with `GOBACK`, correspond, and leave states related in the same way. The relations, all generated, are:
- per file: open flag ↔ open mode, records ↔ encoded records, read position, end-of-file flag;
- the FD record areas and FILE STATUS items at their storage offsets;
- the area's fields at theirs;
- each OPEN outcome ↔ `Env.openError`.

Rust: `Equiv Rel (cbstm03b.call oe st q1) (run …)`. Java: `Sim (Rel st q1) (Call … call(Integer[], State,
LkM03bArea) …) (run …)`. The number of records is bounded only by the containers: a `Vec`, or a Java array
below 2^31 elements.

Every premise of the two statements, as generated (`RustStatement.lean`, `JavaStatement.lean`), and where it
comes from. Both statements:
- `m.size = 2248`: the callee's storage has the program's size (coblean's `cbstm03b_call`).
- Every record of TRNXFILE, XREFFILE, CUSTFILE and ACCTFILE has its FD record's length: 350, 50, 500 and 300
  bytes (`cbstm03b_call`).
- For a keyed READ (`K`) of CUSTFILE or ACCTFILE, `LK-M03B-KEY-LN` decodes to `k` with `1 ≤ k ≤ 25`
  (`cbstm03b_call`).
- For a keyed READ of ACCTFILE, the key's first `k` bytes decode as an unsigned number `v` (`cbstm03b_call`).
- For a keyed READ of ACCTFILE, those bytes are the CP037 digits `0xF0`–`0xF9` (the domain, `Domain.lean`).
- The COBOL side is coblean's run from the callee state `st0 m fs` with fuel 50. That is the fuel of
  `cbstm03b_call`, within which the run ends with `GOBACK`.
- Each OPEN outcome is the environment's (`Env.openError`), and every failure is below 100 (the generator).
- Every field value of a file record, an FD record area and the parameter area is valid for its schema: a
  numeric value fits its PIC, and an alphanumeric one has the field's length (`Schema.Valid`; the generator).
- The translation's state and area hold the callee's COBOL state (the generator's relations):
  - per file: open flag, records (encoded), read position and end-of-file flag;
  - the FD record areas and the area's fields at their storage offsets;
  - the FILE STATUS items' bytes.

The Rust statement has no other premise: its containers bound themselves (fixed-size arrays, `Vec`s within
`usize`). The Java statement adds:
- The 11 classes (`Cbstm03b`, `Cbstm03b$State`, the four file classes, the four record classes,
  `Cbstm03b$LkM03bArea`) are initialized, `σ.initOf … = .done` (the generator, from the Jimple classes; none
  has a static initializer).
- Each file's record array has fewer than 2^31 elements, and its read position is below 2^31 (the JVM: array
  lengths and `int`).
- The OPEN-outcome array has 4 elements, each null or a boxed `Integer` (the translation's interface; the
  generator).
- A FILE STATUS item is the `String` of the CP037 text of its two bytes (the generator).
- The FD record object of CUSTFILE or ACCTFILE is not one of that file's record objects (the generator).

Three of these premises exclude counterexamples found during the proofs:
1. OPEN failures are FILE STATUS values below 100 (IBM statuses are two digits). The Rust translation
   treats status 255 as "no error", and the Java one keeps a status mod 100.
2. In Java, the FD record object of a file read by key (CUSTFILE, ACCTFILE) is not one of the file's record
   objects. The translation stores the key into that object before searching, so a shared object would
   corrupt the record. Reads store fresh copies, so the translation keeps this. Rust needs nothing here
   (ownership).
3. The domain (`Modernize/Cbstm03b/Domain.lean`, the one hand-written part of the statements): for a keyed
   READ of ACCTFILE, the key's first `k` bytes are CP037 digits. coblean's `decodeNum` also accepts an
   overpunched last digit, which neither translation implements; account keys are digit strings in
   CardDemo.

The proof splits as for the eight programs:
- `Model.call`, a field-value model of one call;
- `Glue.call_run`, the model against coblean's run, from `cbstm03b_call`;
- `RustProof.statement_of_call` and `JavaProof.statement_of_sat`, the statements from the translations'
  equations against the model;
- the equations themselves: Rust's `call_spec` (`RustCall.lean`), and Java's Jimple contract of `call` with
  its termination (`Java/`, `Java/Term/`, by JimpleLean's session).

`EquivLean.Modernize.Cbstm03b.Rust.rust` and `EquivLean.Modernize.Cbstm03b.Java.java` are proved, and the Java
translation is also totally correct. `Java.java_terminates`, which has no hypotheses beyond the contract's
precondition, says `call` terminates on every input of its contract. `Java.java_total` then says there is an
outcome and every outcome meets the contract.

#### CBSTM03A: the statement job (inlining CBSTM03B)

CBSTM03A is CardDemo's monthly statement batch driver, calling CBSTM03B for all file I/O. At startup it walks the
z/OS control blocks `PSA → TCB → TIOT` (`Cobol.Stm.asp`) through `POINTER` items and `SET ADDRESS OF`, displaying
11 fixed diagnostic lines; it then reads `TRNXFILE` into an in-memory 50 × 10 two-dimensional array of transaction
groups, and for each `XREFFILE` record looks up the customer in `CUSTFILE` and account in `ACCTFILE` (abending with
`CALL 'CEE3ABD'` if either key is missing), formats the customer name and address with `STRING … DELIMITED BY` and
`ALTER`-redirected `GO TO` paragraphs (`8100-FILE-OPEN`), and writes both an 80-column plain-text statement
(`STMT-FILE`) and a 100-column HTML statement (`HTML-FILE`).

The domain (`Modernize/Cbstm03a/Domain.lean`) matches coblean's `stm_run_sorted`, `stm_run_abort_cust` and
`stm_run_abort_acct`: `TRNXFILE` is non-empty, sorted by card number (`CardsSorted`), with at most 50 card groups
and at most 10 transactions per group (the dimensions of `WS-TRNX-TABLE`), and `XREFFILE` has fewer than 10^5
records (bounding the output line `Vec`s below `Usize.max` on 32-bit targets). The generated statements
(`RustStatement.lean`, `JavaStatement.lean`) drop the 11 fixed control-block walk lines from the COBOL `DISPLAY`
list (`(displays os.2).drop 11`) and relate the remaining `DISPLAY` lines, all `STMT-FILE` writes (file 1), all
`HTML-FILE` writes (file 2), and `abended`.

`EquivLean.Modernize.Cbstm03a.Rust.rust` (`rust_composite`) and `EquivLean.Modernize.Cbstm03a.Java.java`
(`java_terminates`, `java_total`, `java_composite`) are proved on standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

### Apache Thrift's wire protocol in C++, Java and Rust (`EquivLean/Demo/Thrift/`)

T4 of the pre-registration. Apache Thrift (f0eb8b84e) implements its compact and binary protocols separately in
`lib/cpp`, `lib/java` and `lib/rs`. Each implementation is checked, as the library's own code, against one Lean
specification of the wire format, `EquivLean/Demo/Thrift/Spec.lean` (t4-spec f93f948: the encodings, the
decoders, and named malformed inputs with the specification's verdict on each). E: for every value, the writer
appends exactly the specification's bytes. D: on the specification's bytes followed by any `rest`, the reader
returns the value and leaves exactly `rest`. M: the reader's behaviour on malformed input, beside the
specification's verdict; a difference between the languages is a discrepancy, shown by the same bytes run on each
language's semantics. The code comes in through each language's front end: the C++ templates instantiated on
`TTransport`, compiled to ClangIR and translated by cirlean 28e2380's cir2lean (`Demo/Gen/Cir/Thrift/ProtoTT/`);
the Java library compiled by `javac --release 8`, its jar's classes as Soot 4.7.1 Jimple read by JimpleLean's
`jimple_import` (`Demo/Gen/Jimple/thrift/`); the Rust crate through Charon and Aeneas fdebf20
(`Demo/Gen/Aeneas/ThriftRs/`). Each theorem holds for every program that contains the code and every transport
that meets the transport contracts. Any other library code enters only through contracts or models that are
marked and listed per language below, and a pair that needs one is "proved under library contracts". Every
theorem uses only `propext`, `Classical.choice`, `Quot.sound`.

| pair | C++ | Java | Rust |
|---|---|---|---|
| compact varint32 w/r | discrepancy exhibited (E, D proved) | proved | proved under library contracts |
| compact varint64 w/r | proved | proved | proved under library contracts |
| zigzag i32 both ways | proved | proved | proved under library contracts (D proved) |
| zigzag i64 both ways | proved | proved | proved under library contracts (D proved) |
| compact field header w/r | discrepancy exhibited | discrepancy exhibited | discrepancy exhibited |
| compact list/set header w/r | proved (M under library contracts) | discrepancy exhibited | proved under library contracts |
| compact string/binary length w/r | not finished (E under library contracts) | not finished | proved under library contracts |
| binary i16 w/r | not finished | proved | proved under library contracts |
| binary i32 w/r | not finished | proved | proved under library contracts |
| binary i64 w/r | not finished | proved | proved under library contracts |
| binary i32 length prefix w/r | not finished | not finished | proved under library contracts |

The discrepancies, each stated as a theorem on the same bytes in every language ("after n": the previous field
id; the input names are the specification's):

| input | C++ | Java | Rust | specification |
|---|---|---|---|---|
| write field id 15 after 0, type I32 (`exDelta15`) | `F5` (`writeFieldBeginInternal_exDelta15`) | `F5` (`wfb_exDelta15`) | `05 1E` (`write_field_header_exDelta15`) | `F5` |
| write field id -32768 after 32767, type I32 (`exI16Overflow`) | `05 FF FF 03` (`writeFieldBeginInternal_exI16Overflow`) | `05 FF FF 03` (`wfb_exI16Overflow`) | panics on the `i16` subtraction (`write_field_header_exI16Overflow`; a release build writes `15`) | `05 FF FF 03` |
| read `15` after 32767 | (I32, -32768) (`readFieldBegin_exI16Overflow_short`) | (I32, -32768) (`rfb_I16Overflow_short`) | error "field id overflow" (`read_field_begin_exI16Overflow_short`) | rejects |
| read `10` after 0 (`exStopNibble`) | STOP, id 0 (`readFieldBegin_exStopNibble`) | STOP, id 1 (`rfb_exStopNibble`) | STOP (`rust_exStopNibble`) | rejects |
| read `05 80 80 04` after 0 (`exIdOutOfRange`) | (I32, -32768) (`readFieldBegin_exIdOutOfRange`) | (I32, -32768) (`rfb_exIdOutOfRange`) | (I32, -32768) (`rust_exIdOutOfRange`) | rejects |
| read `80 80 80 80 80` and nothing after (`exVarint32Overlong`) | the transport's end-of-input exception (`readVarint32_exVarint32Overlong`) | `TProtocolException` (`rv32_exVarint32Overlong`) | `InvalidData` (`rust_exVarint32Overlong`) | overlong |
| read `80 80 80 80 80 00` | 0, after reading 6 bytes (`readVarint32_overlong6`) | `TProtocolException` (`rv32_exVarint32Overlong`: any continuation) | `InvalidData` (`rust_exVarint32Overlong`: any continuation) | overlong |
| read the list header `0D` (size 0, element type UUID) | (UUID, 0) (`readListBegin_D` at element nibble 13) | `TTransportException` "unrecognized type code" (`rlb_uuid`: `getMinSerializedSize` has no UUID case) | (Uuid, 0) (`read_list_set_begin_D`) | (UUID, 0) |

In general C++ reads 6- to 10-byte varint32s as the value modulo 2^32 (`readVarint32_ok`), which Java and Rust
reject after 5 bytes. The languages agree on `exVarint32Exceeds` (5), `exVarint64Exceeds` (0), `05 1E` after 0
(I32, 15) and `exNegSize`, a list size of 2^31, which all three reject: C++ `TProtocolException(NEGATIVE_SIZE)`
(`readListBegin_exNegSize`), Java `TProtocolException` (`rlb_exNegSize`), Rust `NegativeSize` (`rust_exNegSize`).

#### Rust (`EquivLean/Demo/Thrift/Rust*.lean`)

`lib/rs/src/protocol/{compact,binary}.rs` through veriforch's renamed drop-in `EquivLean/Demo/Gen/Aeneas/ThriftRs/`
(plus modules taken from its manifest). The transports are generic (`TReadTransport` / `TWriteTransport`) under
the transport contracts `ReadContract` / `WriteContract`; library code that the extraction keeps opaque, or cannot
extract, enters only through the MARKED library contracts and the two MARKED model modules listed below. Names are
in `EquivLean.Demo.Thrift.Rust`. Byte lists are compared as values (`(·.val)` against `UInt8.toNat`).

| pair | theorems: E / D / M | outcome | library contracts |
|---|---|---|---|
| compact varint32 w/r | E: the writer is varint-rs `write_u32_varint` (not extractable), whose model bytes are `Spec.varint n` for every `n` (`leb128_eq_varint`); D: `read_varint32_D` (every `n < 2^32`); M, every input: `read_varint32_spec` (the value modulo 2^32, `InvalidData` "Variable-length int over 5 bytes.", or `EndOfFile`), `rust_exVarint32Exceeds` (→ 5), `rust_exVarint32Overlong` (→ `InvalidData` whatever follows, also nothing: no sixth byte is needed) | proved under library contracts | Std, Varint, F_v_anon13 |
| compact varint64 w/r | E: as varint32 (`write_u64_varint`); D: `read_varint64_D` (every `n < 2^64`); M: `read_varint64_spec` (10 bytes, modulo 2^64), `rust_exVarint64Exceeds` (→ 0) | proved under library contracts | Std, Varint, F_v_anon13 |
| zigzag i32 both ways | E: `zigzag32_val` (varint-rs's zigzag = `Spec.zigzag`, `zz_eq_zigzag`), `write_i32_E` (compact `write_i32` appends `Spec.varint (Spec.zigzag v)`); D: `zigzag_to_i32_val` (= `Spec.unzigzag`, `unzz_eq_unzigzag`, every `u32`, no contract), `read_i32_D`; `zigzag32_roundtrip` | proved under library contracts (D of `zigzag_to_i32`: proved) | Shift, Std, F_v_anon13 |
| zigzag i64 both ways | as i32: `zigzag64_val`, `write_i64_E`, `zigzag_to_i64_val`, `read_i64_D`, `zigzag64_roundtrip` | proved under library contracts (D of `zigzag_to_i64`: proved) | Shift, Std, F_v_anon13 |
| compact field header w/r | E: `write_field_header_E` (= `Spec.fieldHeader` for every type nibble and every `i16` delta except 15); DISCREPANCY: `write_field_header_delta15`, `write_field_header_exDelta15` (`Spec.exDelta15`: Rust `[0x05, 0x1E]`, spec `[0xF5]`); M: `write_field_header_overflow`, `write_field_header_exI16Overflow` (an `i16` delta overflow panics; a release build wraps to `[0x15]`); D: `read_field_begin_D` (every `Spec.fieldHeader last id ty`, nibbles 1..13), `read_field_begin_exDelta15_short` (`[0xF5]` → (I32, 15)), `read_field_begin_exDelta15_long` (`[0x05, 0x1E]` → (I32, 15)); M: `read_field_begin_exI16Overflow_short` (`[0x15]` after 32767 → "field id overflow"), `rust_exStopNibble` (→ STOP), `rust_exIdOutOfRange` (→ (I32, -32768)) | discrepancy exhibited | Std, Option, Shift, F_v_anon13 |
| compact list/set header w/r | E: `write_list_set_begin_E` (= `Spec.listHeader` for every count ≥ 0 and element nibble); D: `read_list_set_begin_D` (sizes < 2^31 inside the configured limits); M: `rust_exNegSize` (→ `NegativeSize`) | proved under library contracts | Std, Varint, F_v_anon13; Fmt (M) |
| compact string/binary length w/r | E: `write_bytes_E` (= `Spec.lenPrefix`, length < 2^32); D: `read_binary_len_D`, `read_bytes_D` (inside the configured string limit); M: `read_binary_len_overlong_example`, `read_bytes_trunc` (`EndOfFile`); lengths ≥ 2^31: accepted when the limit allows (the default limit is 100 MiB) | proved under library contracts | Std, Varint, F_v_anon13 |
| binary i16 w/r | E: `bin_write_i16_E` (= `Spec.beI16`); D: `bin_read_i16_D` (`bin_read_i16_ok`: the big-endian value of any two bytes); M: `bin_read_i16_eof` (fewer than 2 bytes → `EndOfFile`) | proved under library contracts | Byteorder, LibModel_byteorder; Std (M) |
| binary i32 w/r | `bin_write_i32_E`, `bin_read_i32_D` (`bin_read_i32_ok`), `bin_read_i32_eof` | proved under library contracts | Byteorder, LibModel_byteorder; Std (M) |
| binary i64 w/r | `bin_write_i64_E`, `bin_read_i64_D` (`bin_read_i64_ok`), `bin_read_i64_eof` | proved under library contracts | Byteorder, LibModel_byteorder; Std (M) |
| binary i32 length prefix w/r | E: `bin_write_bytes_E` (= `Spec.binLenPrefix` for every slice: `len as i32` wraps modulo 2^32, as `Spec.beI32`); D: `bin_read_binary_len_D`, `bin_read_bytes_D` (length < 2^31 inside the limit); M: `bin_read_binary_len_neg` (→ `NegativeSize`), `bin_read_binary_len_eof`, `bin_read_bytes_trunc` (→ `EndOfFile`) | proved under library contracts | Byteorder, LibModel_byteorder, Std; Fmt (M) |

Files: `RustContracts.lean` (the contracts), `RustRead.lean`, `RustZigzag.lean`, `RustWrite.lean`, `RustField.lean`,
`RustFieldD.lean`, `RustList.lean`, `RustBytes.lean`, `RustCompactInt.lean`, `RustBinary.lean`, `RustMalformed.lean`.

##### Rust contracts

Transport contracts (the prereg's; not library contracts): `ReadContract inst rem`: on a `TReadTransport` holding
the bytes `rem t`, `read_exact` into an `n`-byte buffer returns the next `n` bytes and leaves the rest, or, with
fewer than `n` bytes left, an error of kind `UnexpectedEof`. `WriteContract inst sent`: `write` and `write_all`
append all their bytes to `sent t`.

| MARKED library contract or model | what is assumed | source (rustc library: nightly-2026-09-17, the extraction's toolchain) |
|---|---|---|
| `StdContract` | `Result::map` on `Ok` applies the closure, on `Err` returns the error; `String::from(&str)` returns; `io::Error::to_string` returns | core/src/result.rs l.832-834; alloc/src/string.rs l.3185 (`From<&str>`), l.2965 (`ToString` blanket) |
| `OptionContract` | `Option::ok_or_else`: `Some v` gives `Ok v`, `None` gives `Err` of the closure's value | core/src/option.rs l.1361-1363 |
| `ShiftContract` | `Shl<i32>` / `Shr<i32>` for `&i16`, `&i32`, `&i64`, shift below the width: the left shift wrapping, the right shift arithmetic | core/src/ops/bit.rs l.518 (via internal_macros.rs l.27) |
| `VarintContract` | varint-rs 2.2.1 `VarintWriter::write_u32_varint` / `write_u64_varint` (trait defaults, opaque) = the `write_varint!` macro: one `write` per LEB128 byte, the first error returned | vendor/varint-rs/src/lib.rs l.362, 374 (defaults), l.270-290 (`write_varint!`) |
| `FmtContract` | `alloc::fmt::format` (`format!`) returns a string; `core::hint::must_use` returns its argument | alloc/src/fmt.rs l.651; core/src/hint.rs l.613 |
| `ByteorderContract` | byteorder 1.5.0, `BigEndian`, any writer / reader: `WriteBytesExt::write_i16/i32/i64` = `write_all` of the big-endian bytes of `n as uN`; `ReadBytesExt::read_i16/i32/i64` = `read_exact` into `[0; w]`, its error returned, else the big-endian value `as iN` | vendor/byteorder/src/io.rs l.1178, 1286, 1394 and l.139, 243, 347; lib.rs l.546, 590, 634, 770, 814, 858; `BigEndian` l.1940-1952, 1978-1990 |
| model `ThriftRs/F_v_anon13.lean` | replaces veriforch's generated F_v_anon13 (sha256 7189b336…, kept uncompiled as `F_v_anon13.lean.veriforch`; it does not check): std `io::Cursor<&mut [u8]>` (the buffer and the position; `new`, `position`, `slice_write`, `write_all`'s `WriteZero`) and varint-rs `impl<W: io::Write> VarintWriter for W` (its generated `write`; `write_uN_varint` as `write_varint!`; the signed methods the generated defaults) | core/src/io/cursor.rs l.101, 185, 363-394; vendor/varint-rs/src/lib.rs l.270-290, 404-419 |
| model `ThriftRs/LibModel_byteorder.lean` | defines the three constants veriforch's binary modules name and no generated module defines: `BigEndian`'s `impl ByteOrder` (derived traits of an uninhabited enum, `Default` panics, methods unknown) and the blanket `ReadBytesExt` / `WriteBytesExt` impls (their `io::Read` / `io::Write`; methods unknown); the seven binary modules that name them are veriforch's with one added import of this module, marked in each file | vendor/byteorder/src/lib.rs l.1812-1819, io.rs l.1049, 1579 |
#### C++ (`EquivLean/Demo/Thrift/Cpp/*.lean`)

`lib/cpp/src/thrift/protocol/{TCompactProtocol,TBinaryProtocol}.tcc`, instantiated on `TTransport`, through
veriforch's drop-in `EquivLean/Demo/Gen/Cir/Thrift/ProtoTT/`. The program `ctx` is any one containing the
protocol's functions; the transport is reached only through `TTransport`'s entry points, under the transport
contracts listed below. The one library model used, cirlean's `std::string` (for `writeBinary_E` and the
exception message in `readListBegin_exNegSize`), is listed there too. Names are in `EquivLean.Demo.Thrift.Cpp`.
Bytes are the numbers `0..255` the C++ memory holds; the specification's are mapped by `UInt8.toNat`.

| pair | theorems: E / D / M | outcome | library contracts |
|---|---|---|---|
| compact varint32 w/r | E: `writeVarint32_E` (every `uint32_t n`: appends `varint n` = `Spec.varint n`, `varint_eq_spec`); D: `readVarint32_D` (every `n < 2^32`); M, every input whose first ≤ 10 bytes are a varint: `readVarint32_ok` (`readVarint32` is `readVarint64` then `(int32_t)`: the value modulo 2^32), `readVarint32_overlong6` (`80 80 80 80 80 00` → 6 bytes read, 0; Rust: `InvalidData`, `rust_exVarint32Overlong`), `readVarint32_exceeds5` (`FF FF FF FF 1F` → -1), `readVarint32_exVarint32Exceeds` (→ 5, as Rust), `readVarint32_exVarint32Overlong` (`80 80 80 80 80`, nothing after → the transport's end-of-input exception, under `EofContract`; Rust `InvalidData`), `readVarint32_eof` (every source ending inside a ≤ 10-byte varint) | discrepancy exhibited (E, D: proved) | none |
| compact varint64 w/r | E: `writeVarint64_E`; D: `readVarint64_D` (every `n < 2^64`), through each answer of `borrow` (the transport's buffer, the caller's `buf`, `NULL` and one `readAll` per byte); M: `readVarint64_ok` (every ≤ 10-byte varint: the value modulo 2^64), `readVarint64_exceeds`, `readVarint64_exceeds10` (`FF`×9 `7F` → -1), `readVarint64_exVarint64Exceeds` (→ 0, as Rust), `readVarint64_eof` (a source ending inside a ≤ 10-byte varint → the transport's end-of-input exception); more than 10 bytes: not stated (the "over 10 bytes" throw builds a `std::string` message) | proved | none |
| zigzag i32 both ways | E: `i32ToZigzag_E` (every `int32_t`: `zigzag n` = `Spec.zigzag n`, `zigzag_eq_spec`); D: `zigzagToI32_D` (every `uint32_t`: `unzigzag`); `unzigzag_zigzag` | proved | none |
| zigzag i64 both ways | `i64ToZigzag_E`, `zigzagToI64_D` | proved | none |
| compact field header w/r | E: `writeFieldBeginInternal_E` (= `Spec.fieldHeader last id c` for every TType with a compact nibble `c`, every `int16_t` id and previous id, delta 15 included; callees `getCompactType_E`, `writeByte_E`, `writeI16_E`); `writeFieldBeginInternal_exDelta15` (`Spec.exDelta15` → `F5`; Rust `05 1E`), `writeFieldBeginInternal_exI16Overflow` (→ `05 FF FF 03`: C++ compares the ids as `int`); D: `readFieldBegin_D` (every `Spec.fieldHeader last id ty`, nibbles with a TType); M: `readFieldBegin_exI16Overflow_short` (`15` after 32767 → (I32, -32768); Rust "field id overflow"), `readFieldBegin_exDelta15_long` (`05 1E` after 0 → (I32, 15)), `readFieldBegin_exStopNibble` (`10` → STOP: C++ tests the type nibble), `readFieldBegin_exIdOutOfRange` (`05 80 80 04` → (I32, -32768)); the three header forms `readFieldBegin_stop`, `_short`, `_long` | discrepancy exhibited | none |
| compact list/set header w/r | E: `writeCollectionBegin_E` (= `Spec.listHeader size c`, every `int32_t` size ≥ 0); D: `readListBegin_D`, `readSetBegin_D` (sizes < 2^31; when `container_limit_` does not reject the size and the rest holds the `size * minSize t` bytes of the transport's message size check); M: `readListBegin_exNegSize` (`Spec.exNegSize` = `F5 80 80 80 80 08`, size `2^31`: the `int32_t` size is -2^31 and C++ throws `TProtocolException` with type `NEGATIVE_SIZE`, TCompactProtocol.tcc l.578-580; Rust `NegativeSize`) | proved (M: under library contracts) | none (E, D); cirlean's `std::string` model (M, the exception's message) |
| compact string/binary length w/r | E: `writeBinary_E` (= `Spec.lenPrefix bs` for every `std::string` holding `bs`, length < 2^31; `size()` / `data()` by cirlean's model of `std::string`, transport contract `WriteVecContract`); D: not finished: `readBinary` (TCompactProtocol.tcc l.696-731) reads into `string_buf_` (`std::realloc`, l.720) and copies with `std::string::assign(const char*, size)` (l.728), which cirlean does not model | not finished (E: proved under library contracts) | cirlean's `std::string` model (E) |
| binary i16 w/r | not finished: `writeI16` (TBinaryProtocol.tcc l.147-150) passes the `int16_t`'s object representation to the transport (`(uint8_t*)&net`) and `readI16` (l.377-385) reads the bytes back through a `union { uint8_t b[2]; int16_t all; }`: cirlean ≤ 28e2380 has no byte-level memory (a width-mismatched access gets a one-element meaning, and is UB after cirlean's fix 2d65713) | not finished | — |
| binary i32 w/r | not finished: as i16, `writeI32` l.154-157, `readI32` l.388-396 | not finished | — |
| binary i64 w/r | not finished: as i16, `writeI64` l.161-164, `readI64` l.399-407 | not finished | — |
| binary i32 length prefix w/r | not finished: `writeString` (l.180-190) writes the size by `writeI32` (as above) and the bytes from `std::string::data()`; `readStringBody` (l.446-) assigns them to a `std::string` | not finished | — |

Files: `Transport.lean` (the contracts), `Bits.lean`, `Varint.lean`, `Zigzag.lean`, `ReadLemmas.lean`,
`VarintRead.lean`, `VarintRead32.lean`, `FieldHeader.lean`, `FieldRead.lean`, `ListHeader.lean`, `ListRead.lean`, `NegSize.lean`, `Eof.lean`, `StringWrite.lean`.

##### C++ contracts

Transport contracts (the prereg's; not library contracts), for one transport object `tp` whose footprint `Fp` (its
object and buffers) only its own code changes; each call changes no block outside `Fp` except the ones it is
given. `WriteContract tp Fp sinkOf` (`sinkOf m`: the bytes written so far): `TTransport::write(buf, len)` with
`len` bytes of a `uint8_t` array appends them; `write1`: `write(&c, 1)` on one `int8_t`/`uint8_t` object appends
`c mod 256`. `ReadContract tp Fp srcOf` (`srcOf m`: the bytes not read yet, numbers below 256):
`readAll(&c, 1)` (`readAll1`; `readAll1a` into a `uint8_t` array element) with a byte left stores it and drops it;
`borrow(buf, &len)` returns `NULL`, or a pointer to at least `len` of the next bytes (in the transport's buffers or
in the caller's `buf`), consuming nothing; `consume(n)` with `n` bytes left drops them. `CheckContract tp srcOf`:
`TTransport::checkReadBytesAvailable(n)` returns, changing nothing, when the transport holds `n` bytes.
`EofContract tp Fp srcOf eofExn`: `readAll(&c, 1)` with no byte left throws the transport's end-of-input exception
(`eofExn`; `TTransportException(END_OF_FILE)` for Thrift's transports). `WriteVecContract tp Fp sinkOf`: `write(p, len)`
with `p` at a character of a `std::string` object (cirlean's model: a container value) appends the `len` characters'
bytes.

Library models: `writeBinary_E` runs `std::string::size()` and `data()` on cirlean's built-in model of libc++'s
`std::string` (`CIR.Model.strSize`, `CIR.Model.strCStr`; cirlean 28e2380 `CIR/Std/Models.lean` l.711-714, l.744-746:
the object is a container value of its characters and a terminating 0); `readListBegin_exNegSize` runs `std::string()`
(the exception's message) on the same model (`CIR.Model.strCtorDefault`, l.694). No other library model or contract
is used.

Hypotheses on the program and the protocol object (no library models): the constant table `TTypeToCType` holds its
initializer (`cTypeTable`); the protocol object is a constructed `TCompactProtocolT<TTransport>`: its `trans_` is
`tp`, `lastFieldId_` an `int16_t`, `container_limit_` an `int32_t`, its vptr (through the nested base subobjects)
the address point of the class's vtable constant (`vtProto`); the program's record and global declarations that the
code looks up (`TList`, the vtable, the virtual targets; for the `NEGATIVE_SIZE` throw, `ExnProgram`: the exception
classes' constructors, vtables, records and their base-class / vptr paths).

#### Java (`EquivLean/Demo/Thrift/Java/`)

`lib/java` through veriforch's drop-in `EquivLean/Demo/Gen/Jimple/thrift/`: the 277 classes of the jar
(`thrift-java-f0eb8b84.jar`, sha256 `d7b84d858ad0d6c6bcc18a305c08a5e85e351199b76e31ff4e1a4e8ea77bb143`: its 262
classes and the 15 lambda classes Soot adds). Every theorem holds in every program `P` that contains the classes
it names (`Contains P [...]`) and whose
transport classes satisfy the transport contracts (`Valid P (tContracts R).env`, for a representation
`R : TRep` of the transport's bytes); no library contract is used. The field header theorems call their
callees through the callees' proved contracts and add the program hypothesis `NoRedeclR` / `NoRedeclW` (no
application subclass of `TCompactProtocol` redeclares a callee); `ThriftProg.lean` proves it, and `Contains`,
for Thrift's own program `EquivLean.Gen.ThriftJ.prog` by kernel evaluation (`thrift_fh_hyps`;
`thrift_classes_length`: 277 classes). Java's `byte`, `short` and `int` are 32-bit `BitVec`s, `long` a 64-bit
one. Names are in `EquivLean.Demo.Thrift.Java`.

| pair | theorems: E / D / M | outcome | library contracts |
|---|---|---|---|
| compact varint32 w/r | E: `wv32_E` (every `int` `x`: `writeVarint32(x)` returns normally after appending `Spec.varint (toU 32 x)`); D: `rv32_D` (on `Spec.varint (toU 32 x) ++ rest`: returns `x`, leaves `rest`); M: `rv32_M_overlong` (5 continuation bytes → `TProtocolException`), `rv32_M_truncated` (the input ends inside the varint → the transport's `TTransportException`), `rv32_M_exceeds` (a varint of at most 5 bytes with value ≥ 2^32 is read, modulo 2^32), `rv32_exVarint32Exceeds` (→ 5), `rv32_exVarint32Overlong` (→ `TProtocolException`, whatever follows) | proved | none |
| compact varint64 w/r | E: `wv64_E` (rusttrn, `Wv64.lean`: every `long` `x`, appends `Spec.varint (toU 64 x)`); D: `rv64_D`; M: `rv64_M_overlong`, `rv64_M_truncated`, `rv64_M_exceeds` (modulo 2^64), `rv64_exVarint64Exceeds` (→ 0) | proved | none |
| zigzag i32 both ways | E: `zz32_E` (`intToZigZag(n)` = `Spec.zigzag n`); D: `uzz32_D` (`zigzagToInt(zigzag x)` = `x`); M: `uzz32_M` (every `int` pattern `u` → `Spec.unzigzag u`) | proved | none |
| zigzag i64 both ways | as i32: `zz64_E`, `uzz64_D`, `uzz64_M` | proved | none |
| compact field header w/r | E: `wfb_E` (`writeFieldBeginInternal(f, ty)`, `ty` a compact type nibble, the ids `short`s: appends `Spec.fieldHeader last id ty`, `lastFieldId_ = id`), `wfb_exDelta15` (`Spec.exDelta15` → `[0xF5]`, as specified), `wfb_exI16Overflow` (`Spec.exI16Overflow` → `[0x05, 0xFF, 0xFF, 0x03]`, as specified: `id - last` is computed in `int`); D: `rfb_D` (`readFieldBegin()` on `Spec.fieldHeader last id ty ++ rest`, nibbles 1..13: a new `TField` of type `ttypeOfCompact ty` and id `id`, `lastFieldId_ = id`, `rest` left), `rfb_exDelta15_long` (`[0x05, 0x1E]` after 0 → (I32, 15)); M, each beside the spec's verdict (malformed): `rfb_exStopNibble` (`[0x10]` after 0 → `TField(STOP, 1)`, `lastFieldId_ = 1`), `rfb_I16Overflow_short` (`[0x15]` after 32767 → `TField(I32, -32768)`), `rfb_exIdOutOfRange` (→ `TField(I32, -32768)`); the nibbles 14 and 15 (`Java/Term/`, by JimpleLean's session): `getTType` on every nibble (`gttAll_total`: a `TProtocolException` for 14 and 15, its message built through `StringBuilder`) and `readFieldBegin()` on every header byte (`rfbAll_total`); M: `rfb_nib1415_total` (a header byte `≠ 0` with type nibble 14 or 15: every run throws a `TProtocolException`); against the specification `rfb_nib1415_spec_total` (the specification reads `fieldHeader last id ty` for `ty` 14 or 15, Java throws: a difference between the language models, not run on the native library); not finished: `writeFieldBegin`'s override `-1` (the static table `ttypeToCompactType`) | discrepancy exhibited | none (program hypothesis `NoRedeclR` / `NoRedeclW`, proved for Thrift's program) |
| compact list/set header w/r | E: `wcb_E` (rusttrn, `WcbP.lean`: `writeCollectionBegin(ty, size)` appends `Spec.listHeader size c` for every `size ≥ 0` and every TType with compact nibble `c`; the static table `ttypeToCompactType` as `<clinit>` leaves it); D: `rlb_D`, `rsb_D` (on `Spec.listHeader size ety ++ rest`, size < 2^31 inside the container limit, every known nibble except 13: a `TList` / `TSet` of that type and size, `rest` left); M: `rlb_exNegSize`, `rsb_exNegSize` (`Spec.exNegSize` → `TProtocolException`, as the spec rejects); DISCREPANCY `rlb_uuid` (`Spec.listHeader size 13 ++ rest`, e.g. `[0x0D]`: the spec reads a UUID list, Java throws `TTransportException(UNKNOWN, "unrecognized type code")`: `getMinSerializedSize` has no UUID case, TCompactProtocol.java l.906-935); the nibbles 14 and 15: `readListBegin()` and `readSetBegin()` on every header byte (`rlbAll_total`, `rsbAll_total`); M: `rlb_nib1415_total`, `rsb_nib1415_total` (a valid size and element nibble 14 or 15: every run throws a `TProtocolException`); against the specification `rlb_nib1415_spec_total`, `rsb_nib1415_spec_total` (the specification reads `listHeader size ety` for `ety` 14 or 15, Java throws: a difference between the language models, not run on the native library) | discrepancy exhibited | none (program hypotheses proved for Thrift's program: `thrift_coll_hyps`, `ThriftProgC.lean`) |
| compact string/binary length w/r | `writeBinary` / `readBinary` / `writeString` / `readString` go through `java.nio.ByteBuffer` and UTF-8 `String` conversion, library code without a marked model | not finished | — |
| binary i16 w/r | E: `wi16_E` (rusttrn, `BinW.lean`: appends `Spec.beI16 x`); D: `ri16_D` (`BinR.lean`: on `Spec.beI16 v ++ rest`, `InI16 v`, returns `v`, leaves `rest`); M: `ri16_M` (fewer than 2 bytes → the transport's `TTransportException`) | proved | none |
| binary i32 w/r | `wi32_E`, `ri32_D`, `ri32_M` (4 bytes) | proved | none |
| binary i64 w/r | `wi64_E`, `ri64_D` (`BinR64.lean`), `ri64_M` (8 bytes) | proved | none |
| binary i32 length prefix w/r | as the compact length prefix (`ByteBuffer`) | not finished | — |

Files: `Tr.lean`, `TrL.lean`, `Cp.lean` (the contracts and the protocol object), `Rb.lean`, `Wv32.lean`,
`Rv32*.lean`, `Rv64*.lean`, `Zz*.lean`, `Gam.lean`, `Gam2.lean`, `Sel.lean` (callee contracts and their
validity), `Gtt.lean`, `Rfi*.lean`, `Rfb*.lean`, `FhR*.lean` (field header reader), `WfD.lean`, `Wbd.lean`,
`Wi16.lean`, `Wfb*.lean` (field header writer), `ThriftProg.lean`; rusttrn's `Wv64.lean`, `Bp.lean`,
`BinW.lean`, `BinR.lean`, `BinR64.lean` (branch t4-java-rt) and `Wcb*.lean`, `Rlb*.lean`, `Rsb*.lean`, `Ccrl.lean`,
`Crba.lean`, `ThriftProgC.lean` (list/set header, branch t4-java-coll).

##### Java contracts

Transport contracts (the prereg's; not library contracts), `Tr.lean`: a representation `R : TRep` gives each
transport object `t` the bytes written to it (`sink`), the bytes it has to read (`src`), its buffer view and
the objects it uses (`owns`), with laws (`local_`: the representation depends only on `t` and the objects it
uses; `inv_buf`: the buffer holds the next bytes of `src`). `tContracts R`: `write(buf, off, len)` appends
`buf[off, off + len)` to `sink`; `readAll(buf, off, len)` fills `buf[off, off + len)` with the next `len` bytes of
`src`, or throws a `TTransportException` when fewer are left; `getBuffer`, `getBufferPosition`,
`getBytesRemainingInBuffer` and `consumeBuffer` read and advance the buffer view; `checkReadBytesAvailable(n)`
returns and changes nothing. A call changes only `t`, the objects it uses and the array passed (`TFrame`).

MARKED library contracts: none. Program hypotheses: `Contains P [...]` and, for the field header,
`NoRedeclR` / `NoRedeclW` (`thrift_fh_hyps`), for the list/set header `NoRedeclL` (`readListBegin`), `NoRedeclS`
(`readSetBegin`) and `NoRedeclW` (`thrift_coll_hyps`), all proved for `EquivLean.Gen.ThriftJ.prog`. State
preconditions: the protocol object over `t` (`CPAt`), class initialization of the classes a method allocates or
reads statics of (`TProtocolException`, `TCompactProtocol`, `TField`), and, for `readFieldBegin`, a first header
byte that is 0 or has a known type nibble.

##### The Java column, totally correct

The Java column above is proved for terminating runs only (as frozen at ac65118). Branch `t4-java-total`
(613c77c) keeps those theorems unchanged and adds, for every E/D/M theorem of the Java table above, that the
Java code also terminates: `<thm>_total` has the
premises of `<thm>` (without the run `hm`) and states that a run exists (`∃ o, MExec P m args σ o`) and that every
run ends as `<thm>` states. Each method's contract gets the same (`<m>_total`). The proofs (`Java/Term/`, by
JimpleLean's session; each file names its source in its first line) pair each partial-correctness VC with a thin
twin: the same invariants, plus a variant that decreases from cut point to cut point. They are linked by
`TermVC.of_thinX` (JimpleLean's `Jimple/TermSplitX.lean`, which took over this package's `Term/TermX.lean` in
20261026T2035Z), which also checks an
extra premise at every contracted call. The statements name three premises:

* `TransportTerm P R`: the transport's methods terminate under their contracts; a hypothesis, as the transport
  contracts are.
* `TConc P args σ` (`BConc` for `TBinaryProtocol`): the protocol object's transport object has a concrete class.
  A virtual call answered by a contract terminates only for a concrete receiver class, and no T4 precondition
  says so for the transport object.
* `TRepConc P R`: every working transport object (`R.inv σ t`) has a concrete class; used for `readFieldBegin`,
  `readListBegin`, `readSetBegin`, `writeFieldBeginInternal` and `writeCollectionBegin`, which make one protocol
  call after another (the contracts' frames leave the transport object open, so `TConc` at the entry does not
  reach the second call; `TRepConc` gives `TConc` wherever `CPAt` holds).

Zigzag, `getTType` and `checkContainerReadLength` call nothing and need no premise.

The nibbles 14 and 15 are covered on every header byte (`gttAll_total`, `rfbAll_total`, `rlbAll_total`,
`rsbAll_total`), with the premises of the other field and list/set totals (`getTType` needs none): their contracts
drop the known-nibble precondition (`NibbleOK`, `NibbleOKL`) of `rfb_body`/`rlb_body`/`rsb_body` and add
`getTType`'s exception; invariants and closers are the earlier proofs' (two closers of `rlb_body` restated without
the nibble fact).

| pair | total versions (premise) |
|---|---|
| compact varint32 w/r | `wv32_E_total`, `rv32_D_total`, `rv32_M_overlong_total`, `rv32_M_truncated_total`, `rv32_M_exceeds_total`, `rv32_exVarint32Exceeds_total`, `rv32_exVarint32Overlong_total`; contracts `wv32_total`, `rv32_total` (`TConc`) |
| compact varint64 w/r | `wv64_E_total`, `rv64_D_total`, `rv64_M_overlong_total`, `rv64_M_truncated_total`, `rv64_M_exceeds_total`, `rv64_exVarint64Exceeds_total`; contracts `wv64_total`, `rv64_total` (`TConc`) |
| zigzag i32/i64 | `zz32_E_total`, `uzz32_D_total`, `uzz32_M_total`, `zz64_E_total`, `uzz64_D_total`, `uzz64_M_total` (none) |
| compact field header w/r | `wfb_E_total`, `wfb_exDelta15_total`, `wfb_exI16Overflow_total`, `rfb_D_total`, `rfb_exDelta15_long_total`, `rfb_exStopNibble_total`, `rfb_I16Overflow_short_total`, `rfb_exIdOutOfRange_total`; contracts `wfb_total`, `rfb_total` (`TRepConc`); every header byte `rfbAll_total`, `rfb_nib1415_total`, `rfb_nib1415_spec_total` (`TRepConc`), `gttAll_total` (none) |
| compact list/set header w/r | `wcb_E_total`, `rlb_D_total`, `rsb_D_total`, `rlb_exNegSize_total`, `rsb_exNegSize_total`, `rlb_uuid_total`; contracts `wcb_total`, `rlb_total`, `rsb_total` (`TRepConc`); callees `crba_total` (`TConc`), `ccrl_total` (none); every header byte `rlbAll_total`, `rsbAll_total`, `rlb_nib1415_total`, `rsb_nib1415_total`, `rlb_nib1415_spec_total`, `rsb_nib1415_spec_total` (`TRepConc`) |
| binary i16/i32/i64 w/r | `wi16_E_total`, `ri16_D_total`, `ri16_M_total`, `wi32_E_total`, `ri32_D_total`, `ri32_M_total`, `wi64_E_total`, `ri64_D_total`, `ri64_M_total`; contracts `bwi16_total`, `ri16_total`, `wi32_total`, `ri32_total`, `wi64_total`, `ri64_total` (`BConc`) |

### es-toolkit perf commits, TypeScript, proved equivalent (`EquivLean/Demo/TS/EsToolkit.lean`)

Two performance commits from es-toolkit's history (`examples/ts/es-toolkit/`: the old and new
`src/array/*.ts` slices with their `meta.json`), for which StrictTS's own pipeline (strictts-diff) reports
UNKNOWN (array callbacks, `Map` operations, allocation differs) and its fuzzing finds no difference. 4ec747ea
"perf(difference)" replaced `firstArr.filter(item => !secondArr.includes(item))` by
`const secondSet = new Set(secondArr); firstArr.filter(item => !secondSet.has(item))`; 576b136a
"perf(intersection)" did the same without the negation. `difference_equiv` and `intersection_equiv`: for every
world `w` and every two argument arrays allocated below `w.next` (any contents, NaN and ±0 included; the two
may be the same array; no length bound), the old and the new function are `Equiv (ArrObs w.next)`, old first.
The new version allocates the `Set` before the result array, so the final worlds differ, but the caller sees
the same cells below `w.next`, the same console output and oracle positions, and a fresh result array with the
same contents. Both versions use SameValueZero (`includes` and `Set` keys); the proof shows that SameValueZero
on numbers is an equivalence that the `Set` key normalisation (`-0` stored as `+0`) keeps, and that
`new Set(ys).has(x)` is `ys.includes(x)` (`Bridge/TS/Sets.lean`, with a `filter` lemma for a callback that
reads the heap). Limit: es-toolkit's functions are generic, and the pinned translator (StrictTS a15926a)
instantiates generics at their call sites, so each version is translated through an agent-written wrapper
(`examples/ts/es-toolkit/*/inst.ts`) at `T := number`; the theorems are about `difference<number>` and
`intersection<number>`. Check (`scripts/lean1.sh`, one thread): `Bridge/TS/Sets.lean` 1.2 s,
`Demo/TS/EsToolkit.lean` 2.2 s.

## Related work and positioning

The ingredients are standard; the combination is what is specific here.

* **Loop rules.** Lock-step loop simulation without a variant when the abstract side
  terminates, asynchronous alignment and path-pair pruning are standard: Lammich's
  `WHILET_refine` (AFP Refine_Monadic), seL4's `whileLoop_terminates_cross` (l4v CorresWhile),
  CompCert's lock-step simulations (Leroy 2009), the Split rule of Sewell–Myreen–Klein; for
  same-language diffs, regression verification (Godlin–Strichman, REVE), SymDiff and
  differential assertion checking.
* **Cross-language equivalence on real compiler output** exists outside proof assistants:
  SAW proves C ≡ Java on clang and javac output since 2013 (SAT/SMT, loops unrolled), Keq
  (Kasampalis et al., ASPLOS 2021) is parametric in two K semantics, Sewell–Myreen–Klein
  (PLDI 2013) relate C source to gcc binaries with an SMT checker, Ciobâcă–Lucanu–Rusu–Roşu
  (2016) give a proof system parametric in two languages' semantics, and the libm port
  (TACAS 2025) compares C and Rust through LLVM.
* **In proof assistants**, kernel-checked equivalence on real front-end output has been
  same-language (REM2.0 for Rust in Coq; the hax loop example in Lean); the one cross-language
  Lean precedent we know, lean-pl-verify, relates a hand-written TypeScript AST and Charon
  output on toy functions with numbers as integers.

What equiv-lean adds:
* one kernel-checked relation (`Sim`/`Equiv`/`EquivOn`) over five **independently developed**
  encodings of real languages, each driven by its own symbolic executor, none of them modified;
* real front-end output on **both** sides of cross-language pairs (`clang -fclangir` → Charon +
  Aeneas, the COBOL extractor → javac + Soot and → Charon + Aeneas, the StrictTS translator ↔
  Charon + Aeneas);
* COBOL → Java and COBOL → Rust equivalence proofs, including batch loops over files paired in
  lockstep across languages;
* a non-toy TypeScript ↔ Rust result (FNV-1a over byte arrays, IEEE-754 `number` semantics with
  `Math.imul`);
* equivalence off the source's undefined-behaviour/overflow inputs (`EquivOn`) for C++ under a
  ClangIR semantics.

## Layout

| path | content |
|---|---|
| `EquivLean/Core/Behaves.lean` | `Behaves`, `wp`, `Total`/`Det`; instances for `Id`, `Except`, `Option` (and through `.run`, for `StateT`/`ExceptT` stacks) |
| `EquivLean/Core/Sim.lean` | `Sim`, `Equiv`, `FSim`, `EquivOn` (conditional equivalence), the `Simulates` typeclass (`⊑`) and `Equivalent` (`≈`), composition (`Sim.trans`), the cut rule `Sim.wp_cut` |
| `EquivLean/Core/Loop.lean` | `LoopShape`, `LoopShape.Terminates`; `wp_loop` (one loop), `sim_loop` (lockstep with a variant), `sim_loop_of_terminates`/`wp_loop_rel` (lockstep, no variant), `sim_loop_stutter` (asynchronous alignment: unrolled, split, peeled loops) |
| `EquivLean/Core/OptionLoop.lean` | `optLoop`, a reference loop for plain Lean code; it shows the shape and termination proofs on the smallest example |
| `EquivLean/Repr/` | representation refinement: `Corr` and structural instances, `ListRel` (containers), machine integers (`BitVec` ↔ `Int`/`Nat`, wrapping, ranges), `Decimal` (scaled decimals with every rounding mode: COBOL `PIC`, `BigDecimal`, Rust scaled integers), finite maps by lookup |
| `EquivLean/Tactic/` | `equiv_split`, `equiv_intro`, `equiv_exec`, `equiv_loop`, `equiv_cut`, `equiv_cases`, `equiv_body`, `equiv_leaf`, `equiv_close`, `equiv_prune` |
| `EquivLean/Bridge/<E>/` | one bridge per encoding: `Behaves` instance, loop shapes and termination, observation relations, `Corr` lemmas, an `equiv_<e>` tactic (each has a `STATUS.md`) |
| `EquivLean/Demo/` | equivalence proofs on real front-end output (`Demo/Gen/` holds the generated Lean, `examples/` the sources) |
| `EquivLean/Test/Toy.lean` | tests of the generic layer on plain Lean loops (lockstep, automated, unrolled) |

## Stating equivalence

```lean
-- Two versions of a function, all inputs:
theorem pr_ok : ∀ x, Equiv (· = ·) (f_new x) (f_old x)
-- Only where the old version was not wrong (e.g. no UB, no overflow); equivalently, the set
-- of inputs on which the versions differ is contained in Bad (EquivOn.changed_subset):
theorem fix_ok : EquivOn Bad (· = ·) f_new f_old
-- A migration, with representation relations on inputs and outcomes:
theorem migrate_ok : FSim RIn ROut java_method cobol_program
```

`Sim.trans` chains steps (COBOL → specification → Java). Inputs on which the source goes
wrong carry no obligation.

## Checking your own change

1. **Generate Lean for both versions with the real front end** (all tools are pinned; the
   scripts write only inside this repository and `../equivlean_work/scratch`):
   * C/C++: `examples/cir/gen.sh` (clang -fclangir with the libc++ headers, then cir2lean into
     `EquivLean/Demo/Gen/Cir/<Mod>.lean`);
   * Rust: `examples/rust/regen.sh <crate-dir> <Name>` (Charon + Aeneas into
     `EquivLean/Demo/Gen/Aeneas/<Name>/{Types,Funs}.lean`);
   * TypeScript: `node <strictts>/frontend/dist/cli.js --namespace … -o EquivLean/Demo/Gen/TS/X.lean x.ts`;
   * Java: `examples/java/build_jimple.sh NAME` (javac `--release 17` + Soot), then
     `jimple_import "…" as Foo` in Lean;
   * COBOL: `cobol_program P from "p.ir.json"` on the extracted IR.
2. **State** `Equiv R new old` (or `EquivOn Bad R new old` when the change is a bug fix, or
   `Sim R target source` for a migration), with the outcome relation `R` of the bridge
   (`Cir.ObsEq m`, `(· = ·)` on Aeneas/TS outcomes, a field/record relation across languages).
3. **Prove** with the bridge tactic (`equiv_cir`, `equiv_aeneas`, `equiv_ts`, …). For loops of the
   same shape, plain `equiv_cir`, `equiv_aeneas [defs]`, `equiv_ts_auto` and `equiv_jimple [defs]`
   generate the coupling;
   otherwise give a coupling invariant (`using I`); `equiv_loop_auto I` pairs any two registered
   loops, `equiv_loop_async I V sched` loops that do not correspond one to one.
4. **Check** with `scripts/lean1.sh F.lean` (or `lake build`).

## Limits and open items

* Jimple targets give partial correctness (big-step semantics cannot see divergence); termination
  is a separate proof (`MTerm`, JimpleLean's `Jimple/Termination.lean`), done for the eight CardDemo
  translations and for the T4 Java column.
* COBOL: the patched program's IR is derived from the extractor output of the original
  (`examples/cobol/acctint2/mk_acctint2.py`); with coblean re-pinned (20261023T2346Z) both
  versions could now come from its front end.
* Loops that differ in structure beyond a scheduler (`equiv_loop_async`) need a functional
  specification on one side (`Sim.of_wp_pair`, the bridges' `wp_loop` forms).
* Heap equivalence modulo fresh allocation: CIR compares caller-visible blocks (`ObsEq`); a
  pointer argument needs the bound `∀ b p, x = .loc b p → b < m.next` (a block of the caller, not
  one of the callee's locals); writes through pointers in another order are matched at leaf
  positions (`Val.set?_swap`); records passed by value with pointer fields, and returning freshly
  allocated C++ objects, are not covered. StrictTS has a partial bijection (`Bridge/TS/Obs.lean`).
* Pins: cirlean e6ac99a (cirlean's `next`: punning2, unionpun, hexfp, ilp32, fuzzer266; the frozen headline
  commit 751764f pins 28e2380: static zero-initialisation, integer pointers, `--link`, faster symbolic
  execution, `cir.stepHeartbeats`), coblean
  20261024T2306Z (a frozen snapshot of the coblean session; the CardDemo all-input theorems copied into
  `Demo/Cobol/`), StrictTS a15926a (external calls, dictionaries and `unknown` values; the
  caller-visible relation of `Bridge/TS/Obs.lean` compares the oracle positions, see
  `Bridge/TS/STATUS.md`; f64eval is later, master b3ab7f9), JimpleLean 20261026T2035Z (the frozen
  headline commit 751764f pins 20261025T0149Z: static method contracts, faster inlining, contracts on abstract states
  behind `jimple.modelContracts`, used by CBTRN03C's Java proof; 2312Z adds the Character/CharSequence
  models, `jsimp` unfolding `argSeq`/`seqCharAt`, closers without the `BitVec.toInt_xor/_and/_or` lemmas,
  the `Double.compare` NaN fix and the termination modules; 2035Z adds `Jimple/TermSplitX.lean`, formerly T4's
  `Term/TermX.lean`, and implementing classes in `jcontract_term`), Aeneas fdebf20.
* cirlean has element-typed memory without bytes. Up to 28e2380 it gave a scalar access of another width
  (`*(u32*)p` on a `char` array) the meaning of a one-element access. Our musl work found this; e6ac99a
  (punning2) fixes it: a scalar load or store whose type does not match the block's element type is undefined
  behaviour (`Mem.punnedAccess`).
  - musl's word paths are such accesses (GCC defines them through `__may_alias__`), so they are undefined
    behaviour in cirlean. The musl contracts cover the byte paths; `musl_strlen_aligned_ub` and
    `musl_memcpy_cex_ub` state that the word paths have no outcome.
  - Specs that left a block's type free now state the element type the C code assumes. tiny-regex-c's lemmas
    say that the class buffer, the pattern and the text are arrays of 8-bit integers; their conclusions and
    `re_match_equiv` are unchanged.
  - None of the C/C++ programs above has such an access: a scan of all 22 ClangIR files for pointer casts
    between scalar types of different widths finds none. The only two casts, in tiny-regex-c, are
    `unsigned char*` → `char*`, the same width, which stays defined. The scan predates zlib adler32. Its C
    side was built at 28e2380, and this branch's kit re-checks it at e6ac99a.
* Files read while elaborating (the `.jimple` of `jimple_import`, the IR JSON of `cobol_program`,
  the `.hex` of `cobol_mem_hex`) are not tracked by Lake: after changing one, touch the importing
  module. Release builds start from a clean checkout.

## Building

```sh
scripts/lrun.sh lake build          # 1 Lean thread, nice 10, 64 GiB cap, 10 min timeout
scripts/lean1.sh F.lean             # check one file without Lake (no lock)
```

Lean v4.35.0. Aeneas brings Mathlib v4.35.0 (prebuilt cache). The pinned encodings live in
`../equivlean_work/vendor` and `../equivlean_work/dl/aeneas`; see `DESIGN.md`.

## Status (2026-10-27)

* Clean build of the frozen headline commit 751764f from an empty `.lake/build` (a fresh checkout; pinned
  dependencies prebuilt): 843 of 843 modules, 7.69 core-hours on single-threaded Lean processes, whole
  workspace up to date (2830 jobs). Axiom audit of every theorem: Demo and Test 4480, of which 4472 use only
  `propext`, `Classical.choice`, `Quot.sound` (the other 8 are the `bv_decide` lemmas of
  `Demo/Aeneas/Popcount.lean` and the theorems built on them); Modernize 5827 of 5827. No `sorry`.
* master merges six branches on top of 751764f, all checked together at a14a095:
  - `java-total` (9f0e5fb: JimpleLean 20261025T2312Z and the eight Java total-correctness companions);
  - `t4-final` (ac65118: T4, Apache Thrift's wire protocol in C++, Java and Rust against one specification);
  - `t4-java-total` (613c77c: the T4 Java column's total correctness; on 2312Z one Java zigzag proof needed a
    raised `maxRecDepth`, `Java/ZzB.lean`);
  - `r5-final` (373874f: jsmn), `ledger` (4c2a8db) and `musl` (65c47df).

  On 2026-10-27 it merges four more:
  - the pin replay (`int-trial`, 7e7f28d): JimpleLean 20261026T2035Z, which takes over T4's `Term/TermX.lean`
    (`jl2035`, 8e47011); cirlean e6ac99a with the restated tiny-regex-c and musl specs (`cirnext-frozen-fix`,
    a9f829b); the T4 Java nibbles; and `scripts/lean1.sh` reading the pins from `lakefile.toml`. Kit run
    7e7f28d-replay2: GREEN.
  - `r7-final` (ff07aac): zlib adler32.
  - `r4-cbstm03b` (5d852da): CardDemo's CBSTM03B.
  - `ts-esdiff` (92f75e6): es-toolkit's perf commits.

  adler32's C side and CBSTM03B's Java side were built at the older pins (cirlean 28e2380, JimpleLean 2312Z). This
  branch's kit re-checks them at e6ac99a and 2035Z. 751764f, 9f0e5fb, ac65118, 613c77c, 373874f, a14a095 and
  7e7f28d each have a clean build and axiom audit, recorded with the build, outside the commit. Each result below
  names its own.
* CardDemo's batch layer: all 16 translations (8 programs × Java and Rust) proved, see above; the 8 Java
  translations also totally correct.
* CardDemo's subprogram CBSTM03B, one call per statement (its premises are listed above): both translations
  proved, the Java one also totally correct (0fd209e at JimpleLean 2312Z, kit run 0fd209e-r4t GREEN; 5d852da
  adds only the README's premise list), see above.
* tiny-regex-c C → safe Rust: `re_match_equiv` proved (751764f; check 1942 s over its 37 modules), see above.
* jsmn C → safe Rust: `jsmn_equiv` proved (373874f; check 4334 s over its 34 modules), see above.
* zlib adler32 C → safe Rust: `adler32_z_equiv`, `adler32_equiv`, `adler32_combine_equiv` and
  `adler32_combine64_equiv` proved (ff07aac at cirlean 28e2380), see above. Kit run ff07aac-r7b built all 1826
  modules and its sweep is clean. Its one failed headline row, `C.adler32_combine__spec`, was a clash of audit file
  names on the double underscore; audited alone, it uses only the standard axioms.
* Apache Thrift's wire protocol in C++, Java and Rust against one specification, the Java column also
  totally correct, the compact nibbles 14 and 15 included (a9c8e23 at JimpleLean 2312Z, kit run a9c8e23-t4nib
  GREEN; at 2035Z in the replay), see above.
* es-toolkit's perf commits 4ec747ea (`difference`) and 576b136a (`intersection`), TypeScript:
  `difference_equiv` and `intersection_equiv` proved (92f75e6 at StrictTS a15926a, kit run 92f75e6-esdiff GREEN),
  see above.
* musl 1.2.5's generic C `strlen` and `memcpy` against cirlean's library models (`Demo/Cir/Musl/`; statements
  and scope in `examples/cir/musl/README.md`), on the byte paths: since cirlean e6ac99a the word paths are
  undefined behaviour, see Limits.
* `#ledger` (`EquivLean/Tactic/Ledger.lean`, imports only Lean): for a theorem, the Prop binders of its
  statement, the axioms and opaque constants of its closure, and per bridge the library-model, oracle and
  external-model constants it relies on.
* COBOL → Java and COBOL → Rust on a real program for every input: CardDemo's CBACT04C against
  a Java port (`Demo/Jimple/Cbact04c/Migration.lean`, `cbact04c_sim`, `cbact04c_sim_exists`) and a Rust
  port (`Demo/Cobol/Cbact04cRust/Sim.lean`, `cbact04c_rust_equiv`, `cbact04c_rust_equiv_exists`), one
  COBOL theorem for both. A third port fixes CardDemo's defect (issue #64) and provably differs from
  the COBOL program by exactly the missed rewrite (`Demo/Jimple/Cbact04c/Fixed/Migration.lean`). The
  Java and Rust ports agree with each other (`Demo/XLang/Cbact04cJavaRust.lean`, `Sim.trans`).
* TypeScript ↔ Rust on real library code from both ecosystems: pako's `crc32` ≡ crc32fast's
  baseline `update` (`Demo/XLang/Crc32/`), byte loop against slice-by-16, every input.
* Automatic coupling invariants for same-shape loops: plain `equiv_cir` (C/C++; names, kinds,
  positions, entry values, loop bounds, vector lengths), `equiv_ts_auto` (TypeScript) and plain
  `equiv_aeneas [defs]` (Rust; names, types, positions, entry values, loop bounds) and
  `equiv_jimple [defs]` (Java; the coupling found by running both methods on sampled inputs in
  JimpleLean's interpreter, `Demo/Jimple/{AutoStats,AutoSearch}.lean`) generate the coupling and fall back to `using I` / `ts_lockstep J, R` only when that fails
  (`Demo/Cir/{AutoCouple,AutoEarlyExit,AutoBound,AutoCountBits,AutoVector}.lean`,
  `Demo/TS/AutoCouple.lean`, `Demo/Aeneas/AutoCouple.lean`); across languages, `equiv_ts_rust`
  generates the coupling of a TypeScript loop and a Rust loop (`Demo/TS/{AutoFnvXLang,AutoPolyHash}.lean`).
* Pointer arguments in C/C++: plain `equiv_cir` with a caller-block bound per pointer
  (`Demo/Cir/PtrArgs.lean`: array sum, `swap` with reordered writes and aliasing, guarded read).
* Per-bridge details: `EquivLean/Bridge/*/STATUS.md`; state and next steps:
  `HANDOFF_20261023.md`.
