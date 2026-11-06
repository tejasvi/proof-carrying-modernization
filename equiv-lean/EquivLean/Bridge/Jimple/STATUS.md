# JimpleLean (Java) bridge: status (2026-10-24, JimpleLean 20261024T1029Z)

Pin (10-24 12:2xZ, master 16caded): snapshot `JimpleLean-20261024T1029Z` (vendor copy
`../equivlean_work/vendor/JimpleLean-20261024T1029Z`; static method contracts: `ContractOK` has
`P.staticDecl sig = false →` on the implementing-class part, so `jground` closes it for static
callees, see `Demo/Jimple/Cbact04c/JavaCallees.lean`; faster inlining; jverify fixes). Before that:
snapshot `JimpleLean-20261024T0159Z` (vendor copy `../equivlean_work/vendor/JimpleLean-20261024T0159Z`,
SHA256SUMS verified; `lake build Jimple` there: 69 jobs, 88 s). What changed since 20261023T1820Z, as
far as this bridge sees it: `Program` has the field `index : ClassTree` (every lookup goes through
`P.findClass`; `{ classes := … }` still works, the anonymous constructor does not); `jimple_import`
stores the index precomputed and adds a `MethodRef` constant `Foo.C.«m(sig)».ref` per method (it is
`mref Foo.prog "C" "m"` by `rfl`); the library is precompiled (`precompileModules`): Lake loads
`libJimpleLean_Jimple.so` into the modules that import it, `scripts/lean1.sh` passes it with
`--load-dynlib`. The definitions of `MExec`, `bodyWP`, `callWP`, `bexec_ok` are unchanged (the
semantics now also models the `invokedynamic` of records' `ObjectMethods`). The re-pin needed no
change to the bridge files or to the existing proofs; the generated programs are re-imported by the
new importer when `Demo/Gen/Jimple/*.lean` is elaborated (the Soot output is the same).

Times are Lake's (`LEAN_NUM_THREADS=4`, host load average 170-240). Every theorem of
`EquivLean.Bridge.Jimple.*` and `EquivLean.Demo.Jimple.*` (349, each checked with `#print axioms`)
depends only on `propext`, `Classical.choice`, `Quot.sound` (or a subset of them). No `sorry`, no
native axioms. Core, vendor and sibling repositories were not modified.

| file | time | contents |
|---|---|---|
| `Bridge/Jimple/Behaves.lean` | 1 s | `Call` (P, m, args, σ), `Out` (normal / exc), `instBehavesCall`: `Runs` = `MExec` with a non-wrong outcome, `Safe` = no `MExec` run ends in `wrong`. **Partial correctness**: no `Total` instance (big-step cannot see divergence). `wp_iff`, `liftQ`, `specOf`, `sat_specOf_iff`, `methodVC_sat` (any inlining depth), `sim_of_sat`, `sim_of_methodVC` (Sim against a deterministic safe source = a `jverify` goal), `wp_of_sim`, `sim_symm_of_runs`, `equiv_of_sim_of_runs` (needs a run, e.g. `runs_of_runM`), `mref` |
| `Bridge/Jimple/Corr.lean` | 1 s | `IntVal`/`LongVal` (`SRepr`), `toRM`, `roundRat_toRM`, `divRound_toRM`; `ofBigDec`/`toBigDec`, `val_ofBigDec` (`toRat` = `Decimal.val`), `instCorrBigDecDecimal`, `ofBigDec_add/mul/negate`, `setScale_toRM` (= `Decimal.rescale`), `divScale_toRM` (= `Decimal.div`), `units_eq_roundRat`, `units_eq_divRound` (JimpleLean's COBOL rounding = shared/coblean half-up `divRound`) |
| `Bridge/Jimple/Rel.lean` | 1 s | relational product for two Jimple bodies: `ewpR`/`bodyEWP` (existential source execution, `jbodyEWP` dsimproc), `ewpR_sound`, `bodyEWP_sound`, `wpR_mono`/`bodyWP_mono`/`callWP_mono`, `ProdVC` (target `bodyWP` whose cut assertions/postcondition are the source's `bodyEWP` to the paired cut point / a `RelO`-related end), `prod_sound` (from JimpleLean's `bexec_ok`), `sim_of_prodVC` (Java ≡ Java `Sim`; the source's run is built in lockstep, no termination assumption) |
| `Demo/Gen/Jimple/AcctInt.lean`, `acctint/*.jimple` | <1 s | `jimple_import` of Soot output for `examples/java/acctint/AcctInt.java` (javac --release 17) |
| `Demo/Jimple/AcctIntJava.lean` | 145 s | `accrue_sat`, `accrue_null_sat`: every terminating run of `AcctInt.accrue` returns an `AcctInt$Result` holding `accrueD` (a `BigDec` reference; non-null and `null` balance); `jvc` with checkpoints at statements 15 and 31 |
| `Demo/Jimple/AcctIntMigration.lean` | 4 s | **COBOL → Java**: `acctint_java_sim`, `acctint_java_sim_lowvalues` : `Sim AcctRelJ (Call … AcctInt.accrue …) (EquivLean.Cobol.run AcctIntCobJ {} 20 (initState m))`; also `link` (JimpleLean reference = coblean transcription), `acctint_cob` (coblean's proof re-run) |
| `Demo/Gen/Jimple/PrDiff.lean`, `prdiff_{old,new}/*.jimple` | <1 s | Soot output for the loop PR diff (`examples/java/prdiff_{old,new}/Stats.java`: index loop vs enhanced for) |
| `Demo/Gen/Jimple/PrClamp.lean`, `prclamp_{old,new}/*.jimple` | 1 s | Soot output for the loop-free PR diff (`examples/java/prclamp_{old,new}/Clamp.java`) |
| `Demo/Jimple/PrDiffStats.lean` | 12 s | **Java PR diff with a loop**: `stats_equiv` : `Equiv (· = ·)` (new `Stats.total`, enhanced `for`) (old, index loop) on every non-null `int[]`; directions `stats_sim`, `stats_sim_rev` via `ProdVC` (`stats_vc`, `stats_vc_rev`: lockstep pairs `(0,0)`,`(4,3)` resp. `(0,0)`,`(3,4)`) + `sim_of_prodVC`; no termination assumption on either loop |
| `Demo/Jimple/PrDiffClamp.lean` | 25 s | **Java PR diff (loop-free, library calls)**: `clamp_equiv` : `Equiv (· = ·)` (new `Clamp.clamp`, `Math.max(lo, Math.min(x, hi))`) (old, explicit comparisons) for `lo ≤ hi`; directions `clamp_sim` (`clamp_vc`; source half `old_phase`) and `clamp_sim_rev` (`clamp_vc_rev`; source half `new_phase`: the new code executed existentially through the `Math.min`/`Math.max` models, one lemma per statement `newStep0` … `newStep5`, composed in `new_run`) |

Real front-end output: `examples/java/build_jimple.sh NAME` (javac --release 17, Soot 4.7.1 with the
difftest flags, 1 CPU, scratch tmpdir). `AcctRelJ`: Java returns normally; the `balance`/`interest`
`BigDecimal`s have the values (`Corr BigDec Decimal`) of `fieldDec` of `ACCT-BALANCE`/`WS-INTEREST`;
status char = CP037 of `WS-STATUS`; COBOL ends with `GOBACK`. The Java rewrite has no records (a final
nested class); its constants are locals, so the method does not depend on `AcctInt`'s class
initialization; the precondition assumes `AcctInt$Result` initialized (`initOf = done`).

## Proof recipe for `ProdVC`

Prove the source segments first (`tgtPost …`/`tgtAssert …` lemmas, the source executed existentially
with `jbodyEWP`), then inside the `ProdVC` proof `generalize` the target's `tgtAssert …`/`tgtPost …`
and run `jvc` on the target; close the cut-point leaves with the source lemmas (a separately stated
target lemma does not unify: the elaborator unfolds `bodyWP`).

### Source halves through library calls (the clamp reverse direction)

`jvc [tgtPost, RelO, jbodyEWP, bodyEWPStep, ewpR_ret]` over the whole new body (as `old_phase` does
for the old one) elaborates, but the kernel rejects the proof with deep recursion, also with
`maxRecDepth 1000000` and an unlimited stack (6 min). Kernel-checking the sub-terms of the proof one
by one located it: an `Eq.trans` whose middle terms are `ewpR P (.ret (.next 4 fr σ)) K` and
`ewpR P (step P b 4 fr σ) K'`, the two ends of the definitional steps (`ewpR_ret` is an `rfl` lemma,
`jbodyEWP` a dsimproc) between statements 3 and 4. The kernel compares the arguments of `ewpR`
first, evaluates `step … 4` (the `Math.max` call) and does not come back. Explicit-proof versions of
`ewpR_ret` and of `jbodyEWP` leave the same `Eq.trans` (the reduction happens inside `jvc`).

What works (`PrDiffClamp.lean`):
1. one lemma per statement at a symbolic fuel `n`,
   `bodyEWP P b [] Post n (k+1) fr' σ → bodyEWP P b [] Post (n+1) k fr σ`, proved by
   `rw [bodyEWP_succ]; simp only [bodyEWPStep]; jvc [ewpR_ret]` (with `n` symbolic no step reaches
   the next statement, so no such kernel check arises; the `Math.min`/`Math.max` steps take 0.4 s);
2. the frames between statements written out (`nfr0` … `nfr5`, abbreviations);
3. the composition with `attribute [local irreducible] bodyEWP` and the fuel written as
   `0 + 1 + … + 1` (with `bodyEWP` reducible the elaborator computes the `whnf` of the expected type
   of each step application, i.e. runs the program, and times out);
4. the value equation (`oldVal_eq`) as a separate lemma.

## Open gaps
- Loops in a source that calls library models: the per-statement recipe above with the loop head as
  a cut point; not tried.
- `jvc` on `bodyEWP` with fuel 20 explodes inside one simp pass (fuel 6 is fine); `jvc` slows down
  sharply when a goal mentions a second program (`tgtPost P₂ …`): `generalize` such terms first
  (measured on 20261023T1820Z).
- No `Loops.lean`/`LoopShape` for Jimple (loops go through cut points in `bodyWP`/`ProdVC`), no
  `Tactic.lean` wrapper beyond `jvc` + `jbodyEWP`.
- JimpleLean's new `jverify_body` / `jfacts` / `jcontract_ok` prove single-program obligations
  (`BodyVC`: a contract over every program with given lookup facts, cacheable per body; `ContractOK`
  for linking). They do not apply to `ProdVC` (two programs, existential source). `AcctIntJava` could
  state its contract as a `BodyVC` over `Contains P [AcctInt, AcctInt$Result]`; not done (its
  `MethodVC` proof builds, and `accrue_sat` is what the migration uses).
- jverify notes: inlining needs `inlineFuel` unfolded; `Fields.get`/`List.lookup`/`bne` must be
  passed to `jvc`; cut assertions and postconditions must be opaque definitions (else simp
  `maxSteps`); `omega` fails on `Cobol.units` atoms in some leaf contexts (use explicit lemmas);
  outcome relations must project (`os.1`) rather than match a COBOL result (whnf runs the program).

## CBACT04C: COBOL → Java on every input (2026-10-24, main + helper; `Demo/Jimple/Cbact04c/`)
- Target: `examples/java/cbact04c/Cbact04c.java`, a port of the business logic of AWS CardDemo's
  CBACT04C: the category-balance records in file order, the account and disclosure-group records
  (looked up by key like the keyed `READ`s) as arrays; the rewritten accounts and the transaction count
  as the result; cents and hundredths of a percent in `long`, the field truncations explicit
  (`S9(9)V99` = `% 10^11`, `S9(10)V99` = `% 10^12`); like the COBOL program, the last account is not
  posted (CardDemo issue #64). javac 17 + Soot 4.7.1 (`Demo/Gen/Jimple/cbact04c/`).
- Source: coblean's `cbact04c_all` (all inputs), in `Demo/Cobol/Cbact04c/` (copied unchanged from
  coblean's frozen snapshot 20261024T0857Z: coblean's and JimpleLean's libraries are both named
  `Examples`, so the original module cannot be imported here).
- Files: `Model` (records, heap predicates `CatAt`/`AcctAt`/`DiscAt`, the loop as a fold `jStep`/`jRun`,
  contracts), `JavaLib`/`JavaCallees` (contracts of `readAccount`, `readRate`, `post`: `callees_valid`),
  `JavaRunDefs`/`JavaRunCalls`/`JavaRunLoop`/`JavaRun` (`run_sat : Sat … run runSpec`: every
  terminating run returns `jRun`; cut points 12, 21, 28, 29, 33; the `Result` constructor inlined),
  `Arith` (Java `sdiv`/`srem`/`+` = coblean's `divRound .truncation`/`fitNum` within the field sizes:
  `jtotal_step`, `jpost_bal`), `Pure` (`jRun_cbact04c`: `jRun` on the input records = coblean's
  rewrites `accs.dropLast.map (·.posted (totalInt …))` and `nTxA`), `Decode` (`decodeAcct_posted`),
  `Glue` (`cbact04c_post`), `KeyRate` (`rate_of_key`: the rates of `cbact04c_all` depend only on the
  disclosure key), `NonVacuous` (`runPre_exists`: a Java heap holding the records exists), `Migration`
  (`CbRel`, `cbact04c_sim_of`, **`cbact04c_sim`**: `Sim CbRel (Java call) (EquivLean.Cobol.run
  CardDemo.Cbact04c …)`, and **`cbact04c_sim_exists`**: for every input of `cbact04c_all` such a heap
  exists and the simulation holds from it).
- Scope of the relation: the Java account holds id, balance, cycle credit and debit, group; the other
  fields of the COBOL record (status, limits, dates, ZIP, filler) are neither represented in Java nor
  compared; transaction records are compared by number only (their `TRAN-ID`/`TRAN-DESC` tails come
  from uninitialized storage in the COBOL program). Partial correctness on the Java side.
- The fixed port (`Fixed/`): `examples/java/cbact04c_fixed/Cbact04cFixed.java` is `Cbact04c` with the
  last account posted after the loop. Its classes are `Cbact04cFixed$…`, so `Fixed/Model` states the
  heap predicates for any class name (`CatAtC`/`AcctAtC`/`DiscAtC`/`idOfC`; `CatAt = CatAtC
  "Cbact04c$Cat"` by `rfl`), the contracts for the new classes, `jRunFix` (the rewrites of `jRun`, then
  the current account posted) and `runFixSpec`. `Fixed/Java*` (`runFix_sat`: cut points 13, 22, 30,
  31, 35, 48; Soot's local numbering changed with the class name), `Fixed/NonVacuous`
  (`runPreF_exists`), `Fixed/Migration` (**`cbact04c_fixed_sim`**: `Sim (CbRelFix (missedRewrite rate
  accs))`, the rewrites are the COBOL program's `REWRITE` records followed by the last account posted
  by coblean's `Acc.posted`, the transaction count unchanged; **`cbact04c_fixed_sim_exists`**). The
  pure step: `jRunFix_cbact04c` (`PureFix`).
- Open: termination of the Java methods (JimpleLean is partial correctness).
- Axioms: every theorem `[propext, Classical.choice, Quot.sound]`.

## Generated product proofs (2026-10-24, helper; `Bridge/Jimple/{Align,Auto}.lean`)
- Stage 1, `jprod_vc [defs]`: proves a `ProdVC` goal from the pairs and couplings alone. The target
  runs with `jvc`; each target leaf (pair × target path) becomes its own source goal, closed by
  `jvc [jbodyEWP, …]` in the leaf's context. Unfolding the couplings only in hypotheses (not inside
  the source's `tgtAssert … pairs …`) is what keeps it fast (7.3 s against 22.8 s for both
  directions of PrDiffStats); `IsWrong` is unfolded only in leftover goals (kernel 0.55 s vs 12.8 s).
- Stage 2, `equiv_jimple [defs]`: `Sim R (Call.mk …) (Call.mk …)` or `Equiv` with no pairs and no
  couplings written. Loop heads (targets of backward jumps) are paired in order; both methods run
  on 12 sampled inputs through JimpleLean's interpreter inside the tactic (candidates only: the
  proof is checked by the kernel as usual); the coupling keeps the facts true at every aligned
  loop-head visit: locals equal across the two sides (Soot's renumbering does not matter), entry
  values (an argument, an array argument's length, a constant such as a flag that is 0 at every
  head), bounds `0 ≤ i ≤ length`, equal heaps (and the entry heap when nothing writes it). Two
  weaker variants are tried when the first fails.
- Demos: `Demo/Jimple/AutoStats.lean` (PrDiffStats: `stats_vc`, `stats_vc_rev` by `jprod_vc`;
  `stats_sim`, `stats_sim_rev`, `stats_equiv` by `equiv_jimple`, PrDiffStats' statements; 25.6 s) and
  `Demo/Jimple/AutoSearch.lean` (`examples/java/search_{old,new}`: early `return` → flag + `break`;
  `search_sim`, `search_sim_rev`, `search_equiv`, any key; 18.3 s). Std axioms.
- Tested in scratch only: a `long` accumulator, two loops in sequence, an instance method reading a
  field (all `Equiv`), a loop writing the array (one direction). Correctly fails on a count-down vs
  count-up sum (no lockstep coupling exists), a wrong refactoring (counterexample shown), loops not
  in lockstep. Clamp old ⊑ new hits the kernel deep recursion documented above for sources that go
  through library calls.
