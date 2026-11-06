# Headline A recipe: proving an LLM translation of a CardDemo batch program equivalent to the COBOL run

One program at a time. Inputs: veriforch's delivery `~/veriforch/runs/modernize/<PROG>/`
(`mapping.json`, `init_mem.hex`, `<prog>.ir.json`, `versions.json` → the final guided Java and Rust
translation) and coblean's all-input theorem for the program (frozen snapshot under
`~/coblean_snapshots/`). Output: two theorems, `EquivLean.Modernize.<Prog>.Java.Statement` and
`….Rust.Statement`, each proved from three parts: COBOL side, glue, translation side.

## 1. Import

- Java: copy the final guided translation to `examples/java/mod_<prog>/`, run
  `examples/java/build_jimple.sh mod_<prog>` (javac --release 17 + Soot → `EquivLean/Demo/Gen/Jimple/mod_<prog>/`),
  and write `EquivLean/Modernize/<Prog>/JavaGen.lean` (`jimple_import`; `setup_listing.sh` writes it).
- Rust: copy the crate to `examples/rust/mod_<prog>/`, run `examples/rust/regen.sh examples/rust/mod_<prog> Mod<Prog>`
  (charon + aeneas → `EquivLean/Demo/Gen/Aeneas/Mod<Prog>/`). If the crate name clashes with a Lean
  namespace already in use, rename the crate in its Cargo.toml (CBACT04C: `cbact04c_t`).
- `init_mem.hex` → `EquivLean/Modernize/<Prog>/`.
- COBOL: coblean's `Examples/<Prog>.lean` → `EquivLean/Demo/Cobol/<Prog>/Prog.lean`, unchanged
  except the IR path. coblean and JimpleLean both have a library named `Examples`, so the module
  cannot be imported directly. Re-copy it from each new snapshot (`diff` against the snapshot must
  show only the path line).

## 2. Statement (generated; never edited by hand)

Add one line to the table in `tools/modernize/genall.sh`: the program, coblean's theorem, the file
it is in, and any options. Then run `tools/modernize/genall.sh <prog>`.
`genstmt.py` reads only `mapping.json`, the IR, the harness storage and the fuel form `n + c` of
coblean's theorem. It writes `JavaStatement.lean` and `RustStatement.lean`, which contain:
- record schemas from coblean's layout (`cobol_schema`). Their field names follow the naming rule,
  and `rust_record_vals` checks every Rust struct against it;
- the harness storage (`cobol_mem_hex`);
- the input relations, one per file in SELECT order;
- `Rel`: the displays as CP037 text, the records written or rewritten (decoded by the FROM
  record's schema), and `abended` (CEE3ABD);
- `Statement`, which quantifies over all valid field values, linkage values, the clock and the fuel:
  - Java: `Sim Rel (Call.mk Gen.prog runRef args σ) (EquivLean.Cobol.run P env (n+c) (P.initState mem files))`;
  - Rust: `Equiv Rel (crate.run …) (…)`.

Options:
- `--ksds`: adds `KsdsValid P f recs` for each indexed input file. This is coblean's model
  assumption made explicit (record keys ascending and unique, alternate keys without DUPLICATES
  unique), taken from the program's own file declarations. Use it only when coblean's theorem
  needs it (CBACT04C).
- `--domain D --domain-module M`: adds a hypothesis `D inputs…`. `D` is written by hand in its own
  module and is the only part of a statement that is not generated. Use it only while coblean's
  theorem leaves some paths out (CBACT04C, until the INVALID KEY paths are proved).
- `--subprogram`: the statement of ONE call of a CALLed subprogram whose storage and files persist
  between calls (CBSTM03B). The COBOL side is coblean's per-call theorem
  `P.run env fuel (state) = (.stop .goback, …)`; the statement copies its binders and hypotheses
  from its source. The translation keeps a state between calls (one struct / object per file with
  `open`, `recs`, `pos`, `eof`; the FD record areas; the FILE STATUS items) and is passed the
  parameter areas (linkage items) and the OPEN outcomes. Generated relations: one per file,
  `StateRel` / `StateAt`, one per parameter area, `EnvRel` / `EnvAt`, and `Rel` (the call returns,
  COBOL ends with GOBACK, the results related again). Rust: `Equiv Rel (crate.call oe st q…) run`;
  Java: `Sim (Rel st q…) (Call.mk … call(Integer[], State, Area…) …) run`. Input files only.
  Java `StateAt` also says that the FD record object of a file read by key (IR access random or
  dynamic) is not one of the file's record objects (`NotRecOf`): a keyed READ stores the key in the
  record area before the search. With `--domain D`, the statement gets the premise `D x…` over the
  theorem's named binders (CBSTM03B: `D env m fs k v`).
  Helpers: `Schema.At` / `Schema.BytesAt` (`EquivLean/Bridge/Cobol/Sub.lean`).

Check: `genall.sh` with no arguments regenerates every program, and `git diff` must be empty.

## 3. COBOL side

This is coblean's theorem, instantiated at the harness storage and at the encodings of the field
values: `r.1 = .stop .goback ∧ displays r.2 = …`, or for CBACT04C the whole event list.
`initMem_size` is generated. `Schema.length_encode` gives the record lengths coblean's theorem
asks for.

## 4. Glue: what the translation shows equals the CP037 text of coblean's bytes

Use the kit in `EquivLean/Bridge/Cobol/Records.lean`:

| need | lemma |
|---|---|
| record text, unsigned DISPLAY numerics | `Schema.text`, `Schema.text_eq` (`text_unsigned`: zero-padded digits) |
| record text, signed DISPLAY (trailing overpunch) | `Schema.textS`, `Schema.textS_eq` (`text_signed`, `overpunch`) |
| bytes of one field of an encoded record | `Schema.bytes_encode_getD`, `Forall2.getD` |
| keyed READ (coblean `Sem.findKey`) vs the translation's first-match search | `findKey_map`, `findKey_lt'` |
| decode ∘ encode, record length | `Schema.decode_encode`, `Schema.length_encode` |
| `encodeNum` one-to-one on a picture's values | `encodeNum_beq` |
| message literals | `msg.map cp037Code = txt "…"` by `decide +kernel` |

Program shapes:
- Listing programs (one input file; every record DISPLAYed, possibly twice): run
  `tools/modernize/setup_listing.sh <prog> <RecClass> <FdCamel> <recLen> <memSize> <thm>`. It
  instantiates `JavaProof.lean`/`RustProof.lean` from CBACT02C's. If the program displays each
  record k times, adjust `runSpec` to use `flatMap` (CBACT03C, CBCUS01C).
- Other programs: write `Model.lean` with the translation-level model, i.e. the lines (and records)
  as code points, a function of the field values, computed the way the translations compute them
  (a search with `List.find?`, a fold for running state). Prove it equal to coblean's lines mapped
  by `cp037Code` (CBTRN01C: `Model.displayText`, `displayText_eq`). Then `JavaProof.lean` holds
  `runSpec` (lines mapped by `jline`) and `statement_of_sat`, and `RustProof.lean` holds `RunSpec`
  and `statement_of_run`. Both follow the CBTRN01C skeleton, about 100 lines each.

## 5. Translation side

- Rust: `RunSpec` is an equation `crate.run inputs = .ok out` plus facts about `out`. For loops
  over slices, use `aeneas_spec [defs]` (`Bridge/Aeneas/SpecAuto.lean`), which generates the loop
  invariants: `take i`-prefixes of `map`/`filter`/`foldl`/`find?`. Prove counter loops (`zero_pad`)
  by hand, with `wp_aeneas_loop` and an invariant.
- Java: `run_sat : Sat Gen.prog runRef runSpec` (partial correctness).
  1. Give each helper method (fixed-width text, zero padding, overpunch) a contract, proved once
     with `jverify`. Pattern (JimpleLean, CBACT02C):
     - state the result as a function of the argument (`argText σ sv`);
     - define it recursively in loop order (`fixStr s (i+1) = fixStr s i ++ [s.getD i ' ']`);
     - the loop-head invariant holds the builder contents for the prefix, plus `0 ≤ i ≤ n` and
       `Grows σ0 σ`.
  2. Prove `run` against the helper contracts with one read-loop invariant. The loop is
     flag-driven: `endOfFile` "N"/"Y", the position, and the displays so far equal to the model on
     `take pos`. Put lookup success and similar facts in the precondition when the statement's
     domain allows it.
  3. Loops that index an input array: `jspec_auto [defs]` (`Bridge/Jimple/SpecAuto.lean`) generates
     the invariant.
  For big methods (CBACT04C), split the method into segments proved one by one (`run_seg*`, as in
  `Demo/Jimple/Cbact04c/`) and make each lookup a callee contract.
- Final theorems: `theorem java : Statement := statement_of_sat run_sat` and
  `theorem rust : Statement := statement_of_run run_spec`. Then `#print axioms` (only `propext`,
  `Classical.choice` and `Quot.sound` are allowed) and the module check time. Write
  `~/veriforch/runs/modernize/<PROG>/proof_<lang>.json` and report to the paper session.

## 6. Translations that change behaviour (fixed ports)

When a translation fixes a COBOL defect, do not claim equivalence. State and prove:
- that it equals the COBOL run off the changed set (`EquivOn`, or `Sim` with the COBOL behaviour
  transformed);
- the exact changed set.

Pattern: `Demo/Jimple/Cbact04c/Fixed/Migration.lean`. There, the COBOL rewrites are followed by the
last account posted (`missedRewrite`, issue #64), and `cbact04c_fixed_sim` is the theorem.
